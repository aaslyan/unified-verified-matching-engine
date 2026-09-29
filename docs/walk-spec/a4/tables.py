import re, collections
S='docs/walk-spec/a4'
rows=[l.rstrip('\n').split('\t') for l in open(S+'/decls.tsv')]
D=[dict(n=r[0],m=r[1],a=int(r[2]),b=int(r[3]),w=r[4]=='true',d=r[5]=='true') for r in rows if int(r[2])>0]
AUTO=re.compile(r'\.(rec|recOn|casesOn|noConfusion|noConfusionType|mk|mk\.inj|mk\.injEq|inj|injEq|sizeOf_spec|ctorIdx)$|\.eq_\d+$|match_\d+|\._')
SPEC=re.compile(r'\b(spec|rest|rest_step|rest_step_done|rest_done|rest_empty|rest_noprice|rest_start|term|mr|mrOf|afterMatch|dispose|processWithId|inc|strades|contra|RL|AtHead|IncShape|aggr|decInc|drop1|mm_drop1|mm_head|fillTrade|conflict_iff|conflict_of|policy_of|canMatch_iff|canMatch_shape|cview|stopT|levelView|orderView|bookView|absSide|restSide|absLevel|book_rest|book_norest|restOrd|restOrd_view|view_update|view_update_st|hcontra|hlv|hro|hrv|hpx|book_step|wr_split|view_drop|view_setRem|acct_iff|sideL|innerStep|outerStep|innerRun|outerRun|innerTest|outerTest|mkTrade|restOrder|postOnlyCross|crosses|crosses_iff|rest_accept|insSpec|insSpec_views|side_views|htr|hside|hL0|hpv|hos|hlp|hbook|hpop|mr_rest|term_bids_asks|postOnlyCode|wouldCross|step_\w+|hs)\b|st\.book|st.\.book|hW\.book|hW.\.book|hW1\.book')
STORE=re.compile(r'\b(InvM|Inv|count|levelsUsed|Frame|frame_drop|frame_setRem|dropDb|setRemDb|freeDb|dropS|dropS_facts|writeOrder|WF|wf|queue|hash|restingCount|ClientInv|ClientInvM|clientInv|orders_resting|levels_resting|liveO|liveL|queuedB|readOrder|readLevel|tree|levelPrice|invM_drop|invM_setRem|wcore|core_facts|sinv_drop|sinv_setRem|WCore|Core|best_frame|umin|umin_toNat|free_clientInv|free_absSide|free_absSide_other|free_restingCount|free_tree_length|free_levels_resting|hcnt\w*|hlu\w*|hw\w*|hv\w*|hq\w*|hh\w*|rest_run|rest_inv|rest_book)\b')
GLUE=re.compile(r'\b(Eval|ev_\w+|lsimp|block_cons_normal|block_cons_ret|LoopRun|seq_through|ite_inv|seq_inv|emit_inv|loopRun_of_eval|when_true|when_false|ite_true|ite_false|retcode|mkSt)\b')
def split(lines):
    c=collections.Counter()
    for ln in lines:
        s=ln.strip()
        if not s or s.startswith('--') or s.startswith('/-') or s.startswith('-/') or s.startswith('·') and len(s)<3: c['glue']+=1; continue
        if SPEC.search(s): c['spec']+=1
        elif STORE.search(s): c['store']+=1
        else: c['glue']+=1
    return c
src={}
def lines_of(m,a,b):
    if m not in src: src[m]=open('lean/'+m.replace('.','/')+'.lean').read().split('\n')
    return src[m][a-1:b]
def uniq(xs):
    seen={}
    for x in sorted(xs,key=lambda x:(x['a'],len(x['n']))):
        k=(x['m'],x['a'],x['b'])
        if AUTO.search(x['n']): continue
        if k in seen: continue
        seen[k]=x
    # drop ranges strictly contained in a larger one (structure fields)
    out=[]
    for k,x in seen.items():
        if any(y is not x and y['m']==x['m'] and y['a']<=x['a'] and x['b']<=y['b'] and (y['a'],y['b'])!=(x['a'],x['b']) for y in seen.values()): continue
        out.append(x)
    return sorted(out,key=lambda x:(x['m'],x['a']))
NOT_DIRECT={'MatcherInner.IInv':'content: the continuation invariant','MatcherInner.SInv':'content: store part of the invariant, tied to the reference contra list','MatcherInner.OCtx':'content: fixed data incl. the final result `mr`','MatcherInner.OCtx.Ok':'content','MatcherInner.imeasure':'content: loop measure','MatcherOuter.OInv':'content: the continuation invariant','MatcherOuter.MCtx':'content: fixed data incl. `mr`','MatcherOuter.MCtx.Ok':'content','MatcherOuter.omeasure':'content: loop measure','MatcherInner.HeadFacts':'content: head facts incl. `AtHead` and `aggr`'}
WALK_NOT={'Walk.book_step':'not mechanical (A3a)','Walk.WF_of_Inv':'not mechanical: the unique-ids clause'}
def cls_walk(x):
    m=x['m']
    if x['n'] in WALK_NOT: return WALK_NOT[x['n']]
    if m in ('Walk.EquivEntry','Walk.EquivMatch','Walk.Equiv'): return 'A2 content'
    if m=='Walk.Spec': return 'spec artifact (definition)'
    if m=='Walk.Basic':
        return 'not mechanical: potential argument' if x['n'] in ('Walk.innerRun_ok','Walk.outerRun_ok','Walk.run_fuel_sufficient') else 'mechanical'
    return 'mechanical'
trap={'Walk.w_inner_body_trap','Walk.seq_through','Walk.w_inner_run_none','Walk.w_outer_body_trap','Walk.w_outer_run_none'}
def short(n): return n.split('.',1)[1] if n.count('.')>=1 and n.split('.')[0] in ('MatcherInner','MatcherOuter','MatcherAccept','MatcherRest','Walk','Matcher') else n
tot=collections.defaultdict(collections.Counter)
out=[]
out.append("### Direct route: direct-specific lemmas (used by `main`'s `matcher_refines`, not by the walk route)\n")
out.append("| File | Lemma | Lines | store | spec-rel | glue | Class |")
out.append("|---|---|---|---|---|---|---|")
for x in uniq([x for x in D if x['m'] in ('Matcher.Inner','Matcher.Outer','Matcher.Rest','Matcher.Accept') and x['d'] and not x['w']]):
    L=lines_of(x['m'],x['a'],x['b']); c=split(L); n=x['b']-x['a']+1
    cl=NOT_DIRECT.get(x['n'],'mechanical given the invariant')
    tot['direct-specific']+=c
    out.append(f"| {x['m'].split('.')[1]} | `{short(x['n'])}` | {n} | {c['store']} | {c['spec']} | {c['glue']} | {cl} |")
t=tot['direct-specific']; out.append(f"| | **total** | **{sum(t.values())}** | **{t['store']}** | **{t['spec']}** | **{t['glue']}** | |\n")
for bucket,title in [('walk',"### Walk route: walk-specific lemmas"),('extra',"### Walk route: extra (spec artifact, its fuel proof, the trap direction)")]:
    out.append(title+"\n")
    out.append("| File | Lemma | Lines | store | spec-rel | glue | Class |")
    out.append("|---|---|---|---|---|---|---|")
    for x in uniq([x for x in D if x['m'].startswith('Walk') and x['m']!='Walk.Check']):
        isextra = x['m'] in ('Walk.Spec','Walk.Basic','Walk.LogicInv') or x['n'] in trap
        if (bucket=='extra')!=isextra: continue
        if bucket=='walk' and not x['w']: continue
        L=lines_of(x['m'],x['a'],x['b']); c=split(L); n=x['b']-x['a']+1
        tot[bucket]+=c
        cl=cls_walk(x) if not (x['m']=='Walk.LogicInv' or x['n'] in trap) else 'mechanical (trap direction)'
        out.append(f"| {x['m'].split('.')[1]} | `{short(x['n'])}` | {n} | {c['store']} | {c['spec']} | {c['glue']} | {cl} |")
    t=tot[bucket]; out.append(f"| | **total** | **{sum(t.values())}** | **{t['store']}** | **{t['spec']}** | **{t['glue']}** | |\n")
# shared, per file, with split
out.append("### Shared lemmas inside the direct route's files (used by both routes), per file\n")
out.append("| File | Declarations | Lines | store | spec-rel | glue |")
out.append("|---|---|---|---|---|---|")
for m in ('Matcher.Inner','Matcher.Outer','Matcher.Rest','Matcher.Accept'):
    xs=uniq([x for x in D if x['m']==m and x['w']]); c=collections.Counter()
    for x in xs: c+=split(lines_of(m,x['a'],x['b']))
    tot['shared']+=c
    out.append(f"| {m.split('.')[1]} | {len(xs)} | {sum(c.values())} | {c['store']} | {c['spec']} | {c['glue']} |")
t=tot['shared']; out.append(f"| **total** | | **{sum(t.values())}** | **{t['store']}** | **{t['spec']}** | **{t['glue']}** |\n")
open(S+'/tables.md','w').write('\n'.join(out))
for k,v in tot.items(): print(k, sum(v.values()), dict(v))
