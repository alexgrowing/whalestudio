import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem crdH_injective : Function.Injective (crdH X) := by
  intro y y' h
  rw [← vecOf_crdH X y, h, vecOf_crdH]

theorem mul_eOf_Pc_apply (u : D.what₂.Word)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    (γ * GlobalTheory.SgAlg.eOf (Pc X u)) i a = (γ *ᵥ crdH X (X.eX a)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, GlobalTheory.SgAlg.eOf, Pc]

theorem eOf_Pc_mul_apply (u : D.what₂.Word) (ν : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    (GlobalTheory.SgAlg.eOf (Pc X u) * ν) i a = crdH X (∑ b, ν b a • X.eX b) i := by
  rw [← coordEquiv_symm_apply, map_sum]
  simp [Matrix.mul_apply, GlobalTheory.SgAlg.eOf, Pc, coordEquiv_symm_apply, Finset.sum_apply, mul_comm]

theorem xflag_Fu (u : D.what₂.Word) (j : ℕ) :
    Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j = Submodule.span D.host.E (X.eX '' {i | i.1 < j}) := by
  show (X.Fu u).Xa j = _
  unfold FlagG.Xa
  rw [X.Fu_e]

theorem flag_iff {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) :
    (∀ y, crdH X (n y) = γ *ᵥ crdH X y) →
    ((∃ ν, GlobalTheory.SgAlg.IsUp ν ∧ γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν) ↔
      ∀ j, ∀ x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j) := by
  intro hγ
  have hcol : ∀ ν : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν ↔ ∀ a, n (X.eX a) = ∑ b, ν b a • X.eX b := by
    intro ν
    constructor
    · intro h a
      apply crdH_injective X
      funext i
      rw [← eOf_Pc_mul_apply, ← h, mul_eOf_Pc_apply, hγ]
    · intro h
      ext i a
      rw [mul_eOf_Pc_apply, eOf_Pc_mul_apply, ← h, hγ]
  simp only [xflag_Fu]
  constructor
  · rintro ⟨ν, hν, h⟩
    have h1 := (hcol ν).1 h
    have hstep : ∀ a : Fin D.R.rS,
        n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}) := by
      intro a
      rw [h1 a]
      have hs : ∑ b, ν b a • X.eX b - X.eX a = ∑ b, (ν b a - if b = a then 1 else 0) • X.eX b := by
        simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
      rw [hs]
      refine Submodule.sum_mem _ fun b _ => ?_
      rcases lt_trichotomy b a with hb | rfl | hb
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
      · simp [(hν b b).2 rfl]
      · simp [(hν b a).1 hb, hb.ne']
    intro j x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hij : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hsub : {k : Fin D.R.rS | k.1 < i.1} ⊆ {k : Fin D.R.rS | k.1 < j} :=
        fun k (hk : k.1 < i.1) => (lt_of_lt_of_le hk hij : k.1 < j)
      exact Submodule.span_mono (Set.image_mono hsub) (hstep i)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      convert Submodule.add_mem _ hx hy using 1
      abel
    | smul c x _ hx =>
      rw [map_smul]
      convert Submodule.smul_mem _ c hx using 1
      rw [smul_sub]
  · intro h
    have ha : ∀ a : Fin D.R.rS, ∃ l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.1 < a.1},
        Finsupp.linearCombination D.host.E X.eX l = n (X.eX a) - X.eX a := by
      intro a
      rw [← Finsupp.mem_span_image_iff_linearCombination]
      exact h a.1 (X.eX a) (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
    choose l hl hl2 using ha
    refine ⟨fun b a => l a b + if b = a then 1 else 0, ?_, (hcol _).2 fun a => ?_⟩
    · intro i j
      constructor
      · intro hji
        have h0 : l j i = 0 := (Finsupp.mem_supported' _ _).1 (hl j) i (fun hh => absurd (hh : i.1 < j.1) (not_lt.2 (le_of_lt hji)))
        simp [h0, (ne_of_lt hji).symm]
      · rintro rfl
        have h0 : l i i = 0 := (Finsupp.mem_supported' _ _).1 (hl i) i (fun hh => lt_irrefl i.1 hh)
        simp [h0]
    · have hlc := hl2 a
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
      simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hlc]
      abel

end GlobalTheory.CovDomGrp
