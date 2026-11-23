import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermZeroRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.SdUniqW
open scoped TensorProduct

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LW (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun {_ _} hx hy i => Submodule.add_mem _ (hx i) (hy i)
  zero_mem' := fun _ => Submodule.zero_mem _
  neg_mem' := fun {_} hx i => Submodule.neg_mem _ (hx i)

theorem coe_LW (a : ℕ) : (LW v Λ a : Set (TupV (E := E) v n a)) = LamT v Λ a := rfl

theorem smul_mem_LW {a : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {X : TupV (E := E) v n a} (hX : X ∈ LW v Λ a) : s • X ∈ LW v Λ a :=
  fun i => Submodule.smul_mem _ (⟨s, hs⟩ : v.adicCompletionIntegers F) (hX i)

def TopW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsCompact (LamT (E := E) v Λ a) ∧ IsOpen (LamT (E := E) v Λ a)

def DualW (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    {Y : TupV (E := E) v n a | ∀ X ∈ LamT v Λ a,
      dV v * BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F} =
      (smulSub (dV v)⁻¹ (LW v Λ a) : Set (TupV (E := E) v n a))

def IdxW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    UnramAt (E := E) v →
    ((LW v Λ a).relIndex (smulSub (dV v)⁻¹ (LW v Λ a)) : ℝ) = absV v (dV v) ^ (-(2 * ((n : ℝ) * a)))

theorem sdVolW_of_top (a : ℕ) (hC : CondV σ J ψ v) (hT : TopW v Λ a) (hD : DualW σ J ψ v Λ a)
    (hI : IdxW v Λ a) : SdVolW σ J ψ v Λ a := by
  intro hS hL hSD hU hμ
  have hd0 := dV_ne_zero v
  have hμsd : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
    simp only [dX, dif_pos hμ]
    exact hμ.choose_spec
  have := hμsd.1
  set μ := dX σ J ψ v a with hμdef
  set L := LW v Λ a with hLdef
  set L' := smulSub (dV v)⁻¹ L with hL'def
  obtain ⟨hLc, hLo⟩ := hT hL
  rw [← coe_LW] at hLc hLo
  have hL'c : IsCompact (L' : Set (TupV (E := E) v n a)) := isCompact_smulSub _ L hLc
  have hL'o : IsOpen (L' : Set (TupV (E := E) v n a)) := isOpen_smulSub _ (inv_ne_zero hd0) L hLo
  have hχ : ∀ x t y : TupV (E := E) v n a, psiV F ψ v (BR (Fv F v) σ J (t + x) y) =
      psiV F ψ v (BR (Fv F v) σ J t y) * psiV F ψ v (BR (Fv F v) σ J x y) := by
    intro x t y
    rw [BR_add, psiV_add]
  have h0 : ∀ y : TupV (E := E) v n a, psiV F ψ v (BR (Fv F v) σ J y 0) = 1 := by
    intro y
    have e := SdDualW.BR_smul_right v σ J 0 y y
    rw [zero_smul, zero_mul] at e
    rw [e, psiV_zero]
  have hA : ann (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) (L : Set (TupV (E := E) v n a)) = L' := by
    rw [Sd.ann_eq_cond v (psiV F ψ v) (dV v) (BR (Fv F v) σ J) _ (hC hS)]
    · exact hD hS hL hSD hU
    · intro s hs x hx
      exact ⟨s • x, smul_mem_LW v Λ hs hx, fun y => SdDualW.BR_smul_left v σ J s x y⟩
  have hle : L ≤ L' := by
    intro X hX
    rw [hL'def, mem_smulSub]
    refine ⟨dV v • X, smul_mem_LW v Λ (dV_int v) hX, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hN1 := hI hL hU
  have hNz : L.relIndex L' ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN1
    have := Real.rpow_pos_of_pos (absV_dV_pos v) (-(2 * ((n : ℝ) * a)))
    linarith
  have key := Sd.vol_sq_mul_index hμsd hχ h0 L L' hLc hLo hL'c hL'o hA hle hNz
  rw [hN1] at key
  have hp := absV_dV_pos v
  have e1 : absV v (dV v) ^ (-(2 * ((n : ℝ) * a))) = (absV v (dV v) ^ (2 * ((n : ℝ) * a)))⁻¹ :=
    Real.rpow_neg hp.le _
  have e2 : (absV v (dV v) ^ ((n : ℝ) * a)) ^ 2 = absV v (dV v) ^ (2 * ((n : ℝ) * a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    ring_nf
  have hA2 : 0 < absV v (dV v) ^ (2 * ((n : ℝ) * a)) := Real.rpow_pos_of_pos hp _
  rw [e1] at key
  have e3 : μ.real (L : Set (TupV (E := E) v n a)) ^ 2 = (absV v (dV v) ^ ((n : ℝ) * a)) ^ 2 := by
    rw [e2]
    field_simp at key
    rw [key, mul_assoc]
  have hvol := (pow_left_inj₀ measureReal_nonneg (Real.rpow_pos_of_pos hp _).le two_ne_zero).1 e3
  rw [← coe_LW, ← ENNReal.ofReal_toReal hLc.measure_lt_top.ne, ← measureReal_def, hvol]

end Steps

end PI.OmLocU
