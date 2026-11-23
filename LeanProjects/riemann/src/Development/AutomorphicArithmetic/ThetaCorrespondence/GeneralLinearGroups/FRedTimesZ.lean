import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FRedUnique
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FProdStart
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FZfirst
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FFirstProd

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

namespace UpperTheory.Lit.Full.RedTimesZ

open GlobalTheory.ProdFlatten

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

unseal one GlobalTheory.ProdFlatten.two mp pr Iso Sm in

private theorem two_unit_left {r t : ℕ} (e : t + r = r) (A : BR k r) (hA : Sm A) (y : Fin 0 → IrrGL k)
    (hy : ∑ i, (y i).1 = t) : Iso (two e (pr y hy) A) A :=
  GlobalTheory.ProdReorder.ind₂_unit_left k r t e A.V A.ρ hA (fun i => (y i).1) (fun i => (y i).2.rep.V)
    (fun i => (y i).rep) (stdBlocks _ hy)

unseal one GlobalTheory.ProdFlatten.two mp pr Iso Sm in
private theorem iso_one_pr {h : ℕ} {x : IrrGL k} {y : Fin h → IrrGL k} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) : Iso (pr y hy) (one x) := ⟨φ⟩

unseal one GlobalTheory.ProdFlatten.two mp pr Iso Sm in
private theorem equiv_of_iso {h c N : ℕ} {x : Fin c → IrrGL k} {y : Fin h → IrrGL k} {hx : ∑ i, (x i).1 = N}
    {hy : ∑ i, (y i).1 = N} (H : Iso (pr x hx) (pr y hy)) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := H

private theorem pr_single {c : ℕ} {w : Fin c → IrrGL k} {z : IrrGL k} (hl : List.ofFn w = [z])
    (hw : ∑ i, (w i).1 = z.1) : Iso (pr w hw) (one z) := by
  have h0 : ∑ i : Fin 0, ((fun i => i.elim0 : Fin 0 → IrrGL k) i).1 = 0 := by simp
  exact iso_trans (pr_cons (x := fun i : Fin 0 => i.elim0) (by simpa using hl) h0 hw rfl)
    (two_unit_pr rfl _ (sm_one z) _ h0)

private theorem pr_snoc {h c r N : ℕ} (y : Fin h → IrrGL k) (z : IrrGL k) (w : Fin c → IrrGL k)
    (hl : List.ofFn w = List.ofFn y ++ [z]) (hy : ∑ i, (y i).1 = r) (hw : ∑ i, (w i).1 = N) (e : r + z.1 = N) :
    Iso (pr w hw) (two e (pr y hy) (one z)) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have hN : N = z.1 := by
      have : r = 0 := by simpa using hy.symm
      omega
    subst hN
    exact iso_trans (pr_single (by simpa using hl) hw) (iso_symm (two_unit_left e _ (sm_one z) y hy))
  · have h1 : ∑ i, (![z] i).1 = z.1 := by simp
    exact iso_trans (pr_append y ![z] w (by simpa using hl) (Or.inl hh.ne') hy h1 hw e)
      (two_congr e (iso_refl _) (pr_single (by simp) h1))

private theorem equiv_snoc {h N : ℕ} {x : IrrGL k} {y : Fin h → IrrGL k} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) (z : IrrGL k) (hd : ∑ a, (![x, z] a).1 = N)
    (hw : ∑ i, ((Fin.snoc y z : Fin (h + 1) → IrrGL k) i).1 = N) :
    Nonempty ((prodIrr (Fin.snoc y z : Fin (h + 1) → IrrGL k) hw).Equiv (prodIrr ![x, z] hd)) := by
  have e : x.1 + z.1 = N := by simpa using hd
  have h1 : ∑ i, (![z] i).1 = z.1 := by simp
  refine equiv_of_iso (iso_trans (pr_snoc y z _ (by rw [List.ofFn_succ']; simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]) hy hw e) ?_)
  refine iso_trans (two_congr e (iso_one_pr φ) (iso_symm (pr_single (w := ![z]) (by simp) h1))) ?_
  exact iso_symm (pr_cons (by simp) h1 hd e)

private theorem exists_class {h : ℕ} (y : Fin h → IrrGL k) (hirr : (prodIrr y rfl).IsIrreducible) :
    ∃ (x : IrrGL k) (hy : ∑ i, (y i).1 = x.1), Nonempty ((prodIrr y hy).Equiv x.rep) :=
  ⟨IrrGL.of (prodIrr y rfl) (isSmooth_prodIrr y rfl) hirr, rfl, ⟨IrrGL.equivOf _ _ _⟩⟩

private theorem irr_snoc {h N : ℕ} {x : IrrGL k} {y : Fin h → IrrGL k} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) (z : IrrGL k) (hd : ∑ a, (![x, z] a).1 = N)
    (H : ∀ hw : ∑ i, ((Fin.snoc y z : Fin (h + 1) → IrrGL k) i).1 = N,
      (prodIrr (Fin.snoc y z : Fin (h + 1) → IrrGL k) hw).IsIrreducible) :
    (prodIrr ![x, z] hd).IsIrreducible := by
  have hw : ∑ i, ((Fin.snoc y z : Fin (h + 1) → IrrGL k) i).1 = N := by
    rw [Fin.sum_univ_castSucc, ← hd]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.sum_univ_two, hy]
    rfl
  obtain ⟨ψ⟩ := equiv_snoc φ z hd hw
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv ψ (H hw)

private theorem isSubquotient_of_equiv {h : ℕ} {x : IrrGL k} {y : Fin h → IrrGL k} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) : IsSubquotient x.rep (prodIrr y hy) :=
  .of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective

private theorem jhMult_ne_zero {h : ℕ} {x : IrrGL k} {y : Fin h → IrrGL k} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) : jhMult x.rep (prodIrr y hy) ≠ 0 :=
  jhMult_ne_zero_iff.2 (isSubquotient_of_equiv φ)

private theorem snoc_rel {α β : Type*} (R : α → β → Prop) {h : ℕ} {D : Fin h → α} {y : Fin h → β} {a : α} {b : β}
    (H : ∀ i, R (D i) (y i)) (H' : R a b) (i : Fin (h + 1)) :
    R ((Fin.snoc D a : Fin (h + 1) → α) i) ((Fin.snoc y b : Fin (h + 1) → β) i) := by
  induction i using Fin.lastCases with
  | last => rw [Fin.snoc_last, Fin.snoc_last]; exact H'
  | cast i => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact H i

end UpperTheory.Lit.Full.RedTimesZ

open UpperTheory.Lit.Full.RedTimesZ in
theorem UpperTheory.Lit.Full.redTimesZ :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (x z : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, z] a).1 = N), SuppIn x (up Δ.first) → FirstIn x {Δ.first} → IsZSeg Δ z.rep → (prodIrr ![x, z] hd).IsIrreducible := by
  intro hG hB hZ k _ _ _ _ Δ x z N hd hs hf hz
  obtain ⟨T, hT, hup⟩ := hs
  obtain ⟨⟨𝔪, h𝔪, hfirst⟩, huniq⟩ := UpperTheory.Lit.Full.redUnique hG hB hZ k Δ.first Δ.isCusp_first T hup x hT hf
  obtain ⟨L, rfl⟩ := Quotient.exists_rep 𝔪
  let D : Fin L.length → Segment k := L.get
  have hD : ∀ i, (D i).first = Δ.first := fun i => hfirst _ (Multiset.mem_coe.2 (List.get_mem L i))
  have hsum : ∑ i, (D i).ms = T := by
    rw [← h𝔪, ← List.sum_ofFn]
    have : List.ofFn (fun i => (D i).ms) = L.map Segment.ms := by
      conv_rhs => rw [← List.ofFn_get L, List.map_ofFn]
      rfl
    rw [this]
    simp [msupp, Multiset.bind, Multiset.join]
  choose y hy using fun i => (UpperTheory.Lit.Full.zfirst hG hB hZ k (D i)).1
  have hirr : (prodIrr y rfl).IsIrreducible :=
    UpperTheory.Lit.Full.prodStart hG hB hZ k Δ.first _ _ D y rfl Δ.isCusp_first hD hy
  obtain ⟨x', hyx, ⟨φ⟩⟩ := exists_class y hirr
  have hx' : x' = x := by
    refine huniq x' ?_ ?_
    · rw [← hsum]
      exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (hd := hyx) (fun i => (hy i).hasSupport)
        x'.2.rep.irr (isSubquotient_of_equiv φ)
    · refine UpperTheory.Lit.Full.firstProd hG hB k _ _ y x' hyx
        (fun i => hD i ▸ (UpperTheory.Lit.Full.zfirst hG hB hZ k (D i)).2 _ (hy i)) ?_
      exact jhMult_ne_zero φ
  subst hx'
  refine irr_snoc φ z hd fun hw => ?_
  refine UpperTheory.Lit.Full.prodStart hG hB hZ k Δ.first _ _ (Fin.snoc D Δ) _ hw Δ.isCusp_first ?_
    (snoc_rel (fun (Γ : Segment k) (w : IrrGL k) => IsZSeg Γ w.rep) hy hz)
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simpa using hD i
