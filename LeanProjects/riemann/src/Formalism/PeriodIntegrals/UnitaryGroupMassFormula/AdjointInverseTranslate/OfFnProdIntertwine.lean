import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OpModel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.DetTransposeApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Imports

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem ofFn_prod_intertwine {A : Type*} [Ring A] (ρ : A) :
    ∀ (t : ℕ) (X Y : Fin t → A), (∀ k, X k * ρ = ρ * Y k) →
      (List.ofFn X).prod * ρ = ρ * (List.ofFn Y).prod := by
  intro t
  induction t with
  | zero =>
    intro X Y _
    simp
  | succ t ih =>
    intro X Y h
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      ih (fun i => X i.succ) (fun i => Y i.succ) (fun i => h i.succ), ← mul_assoc, h 0, mul_assoc]

theorem qminor_intertwine {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E E' : Fin n → Fin n → A) (ρ : A)
    (h : ∀ a b, E a b * ρ = ρ * E' a b) (a b : Fin t → Fin n) (u : ℂ) :
    qminor E a b u * ρ = ρ * qminor E' a b u := by
  unfold qminor
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [mul_assoc, ofFn_prod_intertwine ρ t _ _ (fun k => ?_), ← mul_assoc, ← mul_assoc,
    (Int.cast_commute _ ρ).eq]
  simp only [Tm, add_mul, mul_add, h]
  split_ifs
  · rw [Algebra.commutes]
  · rw [zero_mul, mul_zero]

theorem herm_mul_bvec {N : ℕ} (H g s : Matrix (Fin N) (Fin N) ℂ) (c : Fin N) (w : Fin N → ℂ) :
    herm H ((g * s) *ᵥ bvec c) w = ∑ d, s d c * herm H (g *ᵥ bvec d) w := by
  unfold herm
  have hcol : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (e : Fin N), M *ᵥ bvec e = fun i => M i e := by
    intro M e
    funext i
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hcol]
  simp only [Matrix.mulVec_mulVec]
  simp only [hcol, dotProduct, Matrix.mul_apply (M := H * g), Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun i _ => ?_))
  ring

theorem inv_mul_apply {N : ℕ} (g s : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) (c : Fin N) :
    ((g * s)⁻¹ *ᵥ v) c = ∑ d, s⁻¹ c d * (g⁻¹ *ᵥ v) d := by
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  rfl

theorem rightAA_of (hM : OpModel) (hA : AlgAA) (hAv : AlgAAv) (hH : HpkInvol) (hUH : SsetUH)
    (hIC : SsetInvCol) (hRS : SsetRowStar) : RightAA := by
  unfold RightAA
  intro E _ _ k r z' m hm u ell f s' g hf hs' hg
  obtain ⟨M, cls, Eh, hGl, hQ, hR⟩ := hM E (2 * r + k + 1) (Hpk k r) (hH k r)
  have hsU : inUH (Hpk k r) s' := hUH k r z' s' hs'
  obtain ⟨ρ, hρcls, hρev, hρE⟩ := hR s' hsU
  have hgs : inUH (Hpk k r) (g * s') := ana_mul hg hsU
  have hfs : SmoothOnH (Hpk k r) (fun x => f (x * s')) :=
    smooth_right' _ (Hpk k r) E f s' (hH k r) hsU hf
  have hQP : s' * s'⁻¹ = 1 := ana_mul_inv (hH k r) hsU
  have hint : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (w : ℂ),
      qminor Eh a b w * ρ = ρ * qminor (fun i j => ∑ c, ∑ d, (s'⁻¹ c i * s' j d) • Eh c d) a b w :=
    fun a b w => qminor_intertwine Eh _ ρ hρE a b w
  have hev : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (w : ℂ),
      qminorOp (EabH (Hpk k r)) a b w (fun x => f (x * s')) g =
        (qminor (fun i j => ∑ c, ∑ d, (s'⁻¹ c i * s' j d) • Eh c d) a b w (cls f)).1
          ⟨g * s', hgs⟩ := by
    intro t a b w
    rw [hQ t a b w _ g hg hfs, hρcls f hf, ← Module.End.mul_apply, hint, Module.End.mul_apply]
    exact hρev _ g hg (g * s') hgs rfl
  have hev2 : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (w : ℂ),
      qminorOp (EabH (Hpk k r)) a b w f (g * s') = (qminor Eh a b w (cls f)).1 ⟨g * s', hgs⟩ :=
    fun a b w => hQ _ a b w f (g * s') hgs hf
  have hevsum : ∀ (S : (Fin m → Fin (2 * r + k + 1)) → Prop) [DecidablePred S]
      (α : (Fin m → Fin (2 * r + k + 1)) → ℂ) (T : (Fin m → Fin (2 * r + k + 1)) → Module.End ℂ M),
      ((∑ c, if S c then α c • T c else 0 : Module.End ℂ M) (cls f)).1 ⟨g * s', hgs⟩ =
        ∑ c, if S c then α c • (T c (cls f)).1 ⟨g * s', hgs⟩ else 0 := by
    intro S _ α T
    rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    split_ifs <;> simp
  constructor
  · have hdet : ∀ C : Fin m → Fin (2 * r + k + 1),
        (Matrix.of fun a l : Fin m => ∑ d, s' d (C l) *
          herm (Hpk k r) (g *ᵥ bvec d) (bvec (eI k r (Fin.castLE hm a)))) =
        Matrix.of fun a l : Fin m => herm (Hpk k r) ((g * s') *ᵥ bvec (C l)) (bvec (eI k r (Fin.castLE hm a))) := by
      intro C
      ext a l
      simp only [Matrix.of_apply]
      rw [herm_mul_bvec]
    have hA' := hA (Module.End ℂ M) k r m hm Eh s'⁻¹ s'
      (fun a j => herm (Hpk k r) (g *ᵥ bvec j) (bvec (eI k r (Fin.castLE hm a)))) u hGl hQP
      (hIC k r z' s' hs')
    have h1 := congrArg (fun T : Module.End ℂ M => (T (cls f)).1 ⟨g * s', hgs⟩) hA'
    beta_reduce at h1
    rw [hevsum, hevsum] at h1
    simp only [hdet] at h1
    simp only [AAop, hev, hev2]
    convert h1
  · have hdetv : ∀ C : Fin m → Fin (2 * r + k + 1),
        (Matrix.of fun a l : Fin m => ∑ d, s'⁻¹ (C l) d * (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) d) =
        Matrix.of fun a l : Fin m => ((g * s')⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (C l) := by
      intro C
      ext a l
      simp only [Matrix.of_apply]
      rw [inv_mul_apply]
    have hA' := hAv (Module.End ℂ M) k r m hm Eh s'⁻¹ s'
      (fun a j => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) j) (ell + (m : ℂ) - 1) hGl hQP
      (hRS k r z' s' hs')
    have h1 := congrArg (fun T : Module.End ℂ M => (T (cls f)).1 ⟨g * s', hgs⟩) hA'
    beta_reduce at h1
    rw [hevsum, hevsum] at h1
    simp only [hdetv] at h1
    simp only [AAvop, hev, hev2]
    convert h1

end AAInvW
