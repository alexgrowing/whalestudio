import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective

open PowerSeries Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

open PowerSeries TensorProduct in

theorem _root_.GlobalTheory.HWL.mem_smul_of_projective_comp {D A M : Type} [CommRing D] [IsDomain D] [CommRing A]
    [AddCommGroup M] [Module A M] (f : D⟦X⟧ →+* A)
    (hp : @Module.Projective D⟦X⟧ _ M _ (Module.compHom _ f)) (c : D) (hc : c ≠ 0) {a b : A}
    (ha : f (C c) = a) (hb : f X = b) (x y : M) (h : a • x = b • y) : ∃ z : M, x = b • z := by
  letI : Module D⟦X⟧ M := Module.compHom M f
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.WachFree.mem_X_smul_of_projective c hc x y (by
    change f (C c) • x = f X • y
    rw [ha, hb]
    exact h)
  refine ⟨z, ?_⟩
  rw [hz]
  change f X • z = b • z
  rw [hb]

open PowerSeries TensorProduct in
private theorem isSMulRegular_of_projective_powerSeries_comp_lemma {D A M : Type} [CommRing D]
    [IsDomain D] [CommRing A] [AddCommGroup M] [Module A M] (f : D⟦X⟧ →+* A)
    (hp : @Module.Projective D⟦X⟧ _ M _ (Module.compHom _ f)) {b : A} (hb : f X = b) :
    IsSMulRegular M b := by
  letI : Module D⟦X⟧ M := Module.compHom M f
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (R := D⟦X⟧) (M := M)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero : (X : D⟦X⟧) ≠ 0))
  intro x y h
  apply hreg
  change f X • x = f X • y
  rw [hb]
  exact h

open PowerSeries TensorProduct in
set_option maxHeartbeats 1600000 in

theorem _root_.GlobalTheory.HWL.lattice_free : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P) (K : _root_.Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), _root_.Formalism.BasicNotions.Loc.Good K s LL → ∀ (Γ : _root_.GlobalTheory.HWL.GamS P K s LL) (R : _root_.GlobalTheory.HWL.WSer Γ) (I : _root_.GlobalTheory.HWL.IoS AI R), _root_.GlobalTheory.HWL.IoW I → ∀ (E : _root_.GlobalTheory.HWL.WEt I) (Mo : _root_.GlobalTheory.HWL.NS E) (T : _root_.Formalism.BasicNotions.LocLat ↥(_root_.Formalism.BasicNotions.Loc.GK K) ℚ_[l] ↥LL.1 ↥(_root_.Formalism.BasicNotions.Loc.OL LL)), _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(_root_.Formalism.BasicNotions.Loc.OL LL) ↥T.L.T)) (_root_.Formalism.BasicNotions.LetA ↥(_root_.Formalism.BasicNotions.Loc.OL LL) (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K))) ↥(Mo.N T)) := by
  intro l _ P AI K s LL _ Γ R I _ E Mo T hc
  obtain ⟨_, -, hl⟩ := _root_.GlobalTheory.FinExtIntegers.dvr_complete LL
  have hfree := E.DD_free T
  haveI := hfree.1
  haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) := by
    haveI := K.2
    have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ ↑K := inf_le_left
    exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).toRingHom.injective
  haveI : NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : Module.Finite _ (Mo.N T) :=
    Module.Finite.iff_fg.mpr (Mo.N_fg T)
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hzX : _root_.Formalism.BasicNotions.Loc.zlA LL (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) X = fun _ => X := by
    ext1; simp [_root_.Formalism.BasicNotions.Loc.zlA]
  have hzC : _root_.Formalism.BasicNotions.Loc.zlA LL (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) (C (l : ℤ_[l])) =
      fun _ => C (l : _root_.Formalism.BasicNotions.Loc.OL LL) := by
    ext1; simp [_root_.Formalism.BasicNotions.Loc.zlA]
  have key := _root_.GlobalTheory.WachFree.basis_of_regular R.EE_inj
    (Mo.N T).subtype (Mo.N_base T hc) (l : _root_.Formalism.BasicNotions.Loc.OL LL) ?_ hl ?_ ?_
  · rwa [hfree.2] at key
  · intro h0
    haveI : CharZero ↥LL.1 :=
      charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
    have hcast : ((l : _root_.Formalism.BasicNotions.Loc.OL LL) : ↥LL.1) = 0 := by rw [h0]; rfl
    push_cast at hcast
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hcast)
  · exact isSMulRegular_of_projective_powerSeries_comp_lemma _ (Mo.N_proj T) hzX
  · intro x y h
    exact _root_.GlobalTheory.HWL.mem_smul_of_projective_comp (_root_.Formalism.BasicNotions.Loc.zlA LL _) (Mo.N_proj T)
      (l : ℤ_[l]) hl0 hzC hzX x y h

end GlobalTheory.HWL
