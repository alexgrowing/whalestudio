import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidGen
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidExact
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EquivTripleProductOfIso

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdFlatten
open GlobalTheory.LocGL.ProjLine (quot quotMk)

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Emb {n : ℕ} (A C : BR k n) : Prop := ∃ f : A.ρ.IntertwiningMap C.ρ, Function.Injective f

def Sq {n : ℕ} (A C : BR k n) : Prop := IsSubquotient A.ρ C.ρ

def FL {n : ℕ} (A : BR k n) : Prop := HasFiniteLength A.ρ

theorem emb_trans {n : ℕ} {A C D : BR k n} (h : Emb A C) (h' : Emb C D) : Emb A D :=
  let ⟨f, hf⟩ := h; let ⟨g, hg⟩ := h'; ⟨g.comp f, hg.comp hf⟩

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem emb_of_iso {n : ℕ} {A C : BR k n} (h : Iso A C) : Emb A C :=
  let ⟨e⟩ := h; ⟨e.toIntertwiningMap, e.toLinearEquiv.injective⟩

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem embedding_middle_factor_triple {nA nB m m' N : ℕ} (h2 : m + nB = m') (h1 : nA + m' = N) (A : BR k nA) (B : BR k nB) {M M' : BR k m}
    (h : Emb M M') : Emb (two h1 A (two h2 M B)) (two h1 A (two h2 M' B)) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨tripleProductMap h2 h1 A.ρ B.ρ f, (tripleProductMap_injective h2 h1 A.ρ B.ρ f (quotMk f.range) hf fun y => ?_).1⟩
  show f.range.toSubmodule.mkQ y = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem mid_br {nA nB m m' : ℕ} (x : IrrGL k) (h2 : m + nB = m') (h1 : nA + m' = x.1) (A : BR k nA) (B : BR k nB) (M : BR k m)
    (hM : FL M) (hs : Sm M) (h : Emb (one x) (two h1 A (two h2 M B))) :
    ∃ c : IrrCl (GL (Fin m) k), Sq (one ⟨m, c⟩) M ∧ Emb (one x) (two h1 A (two h2 (one ⟨m, c⟩) B)) :=
  let ⟨f, hf⟩ := h
  mid_gen (fun τ => ⟨_, T3 h2 h1 A.ρ B.ρ τ⟩) (fun f => tripleProductMap h2 h1 A.ρ B.ρ f) (fun f g => tripleProductMap_injective h2 h1 A.ρ B.ρ f g) hM hs x.2 f hf

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem emb_pr_iff (x : IrrGL k) {a : ℕ} (z : Fin a → IrrGL k) (hd : ∑ i, (z i).1 = x.1) :
    Emb (one x) (pr z hd) ↔ ∃ f : x.rep.IntertwiningMap (prodIrr z hd), Function.Injective f := Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem sq_pr_iff (x : IrrGL k) {a : ℕ} (z : Fin a → IrrGL k) (hd : ∑ i, (z i).1 = x.1) :
    Sq (one x) (pr z hd) ↔ IsSubquotient x.rep (prodIrr z hd) := Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem fl_pr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {a N : ℕ} (z : Fin a → IrrGL k) (hd : ∑ i, (z i).1 = N) : FL (pr z hd) :=
  GlobalTheory.T.product_irreducible_finite_length hA z hd

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem iso_one_pr (x : IrrGL k) (hd : ∑ _ : Fin 1, x.1 = x.1) : Iso (one x) (pr (fun _ : Fin 1 => x) hd) :=
  nonempty_equiv_prodIrr_one x hd

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem iso_pr_of {a b N : ℕ} (z : Fin a → IrrGL k) (w : Fin b → IrrGL k) (hz : ∑ i, (z i).1 = N) (hw : ∑ i, (w i).1 = N)
    (h : Nonempty ((prodIrr z hz).Equiv (prodIrr w hw))) : Iso (pr z hz) (pr w hw) := h

attribute [irreducible] Emb Sq FL

theorem embL_iff (x : IrrGL k) (l : List (IrrGL k)) : EmbL x l ↔ ∃ hd, Emb (one x) (pr l.get hd) :=
  exists_congr fun hd => (emb_pr_iff x l.get hd).symm

theorem deg3 (A M B : List (IrrGL k)) :
    ∑ a, ((A ++ M ++ B).get a).1 = ∑ a, (A.get a).1 + (∑ a, (M.get a).1 + ∑ a, (B.get a).1) := by
  simp only [sum_get_eq', List.map_append, List.sum_append, add_assoc]

theorem iso_single (σ : IrrGL k) (h : ∑ a, ([σ].get a).1 = σ.1) : Iso (one σ) (pr [σ].get h) :=
  iso_trans (iso_one_pr σ (by simp)) (pr_congr (by simp) _ h)

theorem embL_block {x : IrrGL k} {A M M' B : List (IrrGL k)} {m : ℕ} (hM : ∑ a, (M.get a).1 = m) (hM' : ∑ a, (M'.get a).1 = m)
    (h : Emb (pr M.get hM) (pr M'.get hM')) (hx : EmbL x (A ++ M ++ B)) : EmbL x (A ++ M' ++ B) := by
  obtain ⟨hd, e⟩ := (embL_iff _ _).1 hx
  have h1 : ∑ a, (A.get a).1 + (m + ∑ a, (B.get a).1) = x.1 := by rw [← hM, ← deg3, hd]
  have hd' : ∑ a, ((A ++ M' ++ B).get a).1 = x.1 := by rw [deg3, hM', h1]
  exact (embL_iff _ _).2 ⟨hd', emb_trans (emb_trans (emb_trans e (emb_of_iso (stage3_iso A M B hd rfl hM rfl rfl h1)))
    (embedding_middle_factor_triple rfl h1 _ _ h)) (emb_of_iso (iso_symm (stage3_iso A M' B hd' rfl hM' rfl rfl h1)))⟩

variable (k) in
theorem refineP' : RefineP k := fun x σ A M B hσ hx => by
  obtain ⟨hd, e⟩ := (embL_iff _ _).1 hσ
  have h : ∑ a, ([σ].get a).1 = σ.1 := by simp
  exact embL_block h hd (emb_trans (emb_of_iso (iso_symm (iso_single σ h))) e) hx

variable (k) in
theorem swapP' (h : GlobalTheory.BZSeg.LUnlinkedComm k) : SwapP k := fun x a b A B Δ Γ ha hb hl hx => by
  have hd : ∑ i, (![a, b] i).1 = a.1 + b.1 := by simp [Fin.sum_univ_two]
  have hd' : ∑ i, (![b, a] i).1 = a.1 + b.1 := by simp [Fin.sum_univ_two, add_comm]
  have h1 : ∑ i, ([a, b].get i).1 = a.1 + b.1 := by simp [sum_get_eq']
  have h2 : ∑ i, ([b, a].get i).1 = a.1 + b.1 := by simp [sum_get_eq', add_comm]
  exact embL_block h1 h2 (emb_of_iso (iso_trans (pr_congr (by simp [List.ofFn_succ]) h1 hd)
    (iso_trans (iso_pr_of _ _ hd hd' (h Δ Γ a b _ hd hd' hl ha hb)) (pr_congr (by simp [List.ofFn_succ]) hd' h2)))) hx

variable (k) in
theorem midP' (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) : MidP k := fun x A M B hx => by
  obtain ⟨hd, e⟩ := (embL_iff _ _).1 hx
  obtain ⟨m, hM⟩ : ∃ m, ∑ a, (M.get a).1 = m := ⟨_, rfl⟩
  have h1 : ∑ a, (A.get a).1 + (m + ∑ a, (B.get a).1) = x.1 := by rw [← hM, ← deg3, hd]
  obtain ⟨c, hc, e'⟩ := mid_br x rfl h1 _ _ _ (fl_pr hA M.get hM) (sm_pr M.get hM)
    (emb_trans e (emb_of_iso (stage3_iso A M B hd rfl hM rfl rfl h1)))
  have hs : ∑ a, ([(⟨m, c⟩ : IrrGL k)].get a).1 = m := by simp
  have hd' : ∑ a, ((A ++ [(⟨m, c⟩ : IrrGL k)] ++ B).get a).1 = x.1 := by rw [deg3, hs, h1]
  refine ⟨⟨m, c⟩, ⟨hM, (sq_pr_iff ⟨m, c⟩ M.get hM).1 hc⟩, (embL_iff _ _).2 ⟨hd', ?_⟩⟩
  exact emb_trans (emb_trans e' (embedding_middle_factor_triple rfl h1 _ _ (emb_of_iso (iso_single ⟨m, c⟩ hs))))
    (emb_of_iso (iso_symm (stage3_iso A [⟨m, c⟩] B hd' rfl hs rfl rfl h1)))

end PositivityTheory.Exh

end
