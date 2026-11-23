import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem exists_linRetraction_of_isTorsionFree {R S : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    [Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S))] :
    ∃ r : S →ₗ[R] R, r 1 = 1 := by
  set N := LinearMap.range (Algebra.linearMap R S) with hN
  haveI : Module.Free R (S ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let φ : S →ₗ[R] S := LinearMap.id - s ∘ₗ N.mkQ
  have hφ : ∀ x, φ x ∈ N := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    have this' : (Submodule.Quotient.mk (s (Submodule.Quotient.mk x)) : S ⧸ N) = Submodule.Quotient.mk x := this
    simp [φ, Submodule.Quotient.mk_sub, this']
  have hinj' : Function.Injective (Algebra.linearMap R S) := hinj
  let e := LinearEquiv.ofInjective (Algebra.linearMap R S) hinj'
  refine ⟨e.symm.toLinearMap ∘ₗ φ.codRestrict N hφ, ?_⟩
  have h1 : (1 : S) ∈ N := ⟨1, map_one (algebraMap R S)⟩
  have hφ1 : φ 1 = 1 := by
    have : N.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero N).2 h1
    simp [φ, this]
  apply hinj'
  have := congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict N hφ 1))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_apply] at this
  rw [this, LinearMap.codRestrict_apply, hφ1, Algebra.linearMap_apply, map_one]

theorem isTorsionFree_quot_range {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (H : ∀ a : R, a ≠ 0 → ∀ (b : R) (z : S), algebraMap R S b = algebraMap R S a * z → ∃ c, algebraMap R S c = z) :
    Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S)) := by
  refine ⟨fun a ha => ?_⟩
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with | _ x => ?_
  induction y using Submodule.Quotient.induction_on with | _ y => ?_
  have hxy' : (Submodule.Quotient.mk (a • x) : S ⧸ LinearMap.range (Algebra.linearMap R S)) =
      Submodule.Quotient.mk (a • y) := hxy
  rw [Submodule.Quotient.eq] at hxy' ⊢
  obtain ⟨b, hb⟩ := hxy'
  rw [← smul_sub, Algebra.smul_def] at hb
  obtain ⟨c, hc⟩ := H a ha.ne_zero b (x - y) hb
  exact ⟨c, hc⟩

end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem incO_injective {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    Function.Injective (incO h) := by
  intro a b hab
  have := congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hab
  exact Subtype.ext (Subtype.ext this)

theorem incO_div {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {a b : ↥(OL LL)} (ha0 : a ≠ 0)
    {z : ↥(OL LL')} (hb : incO h b = incO h a * z) : ∃ c, incO h c = z := by
  have haL : ((a : ↥LL.1) : Om l) ≠ 0 := fun e => ha0 (Subtype.ext (Subtype.ext e))
  have hb' : ((b : ↥LL.1) : Om l) = ((a : ↥LL.1) : Om l) * ((z : ↥LL'.1) : Om l) :=
    congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hb
  have hz : ((z : ↥LL'.1) : Om l) = ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) := by
    rw [eq_div_iff haL, mul_comm]
    exact hb'.symm
  have hc : (b : ↥LL.1) / (a : ↥LL.1) ∈ OL LL := by
    rw [Formalism.BasicNotions.Examples₂.LB.mem_OL]
    have hz1 := (Formalism.BasicNotions.Examples₂.LB.mem_OL LL' (z : ↥LL'.1)).1 z.2
    rw [hz] at hz1
    simpa using hz1
  refine ⟨⟨_, hc⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) = ((z : ↥LL'.1) : Om l)
  rw [hz]

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_intRetraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1),
    ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  intro l _ LL LL' h
  letI A : Algebra ↥(OL LL) ↥(OL LL') := (incO h).toAlgebra
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  haveI T : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq (fun x => by
    apply Subtype.ext; apply Subtype.ext; rfl)
  haveI : Module.Finite ℤ_[l] ↥(OL LL') := Formalism.BasicNotions.Examples₂.LB.OL_finite LL'
  haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := isTorsionFree_quot_range (R := ↥(OL LL)) (S := ↥(OL LL')) (fun a ha b z hb => incO_div h ha hb)
  obtain ⟨r, hr⟩ := exists_linRetraction_of_isTorsionFree (R := ↥(OL LL)) (S := ↥(OL LL')) (incO_injective h)
  refine ⟨r.toAddMonoidHom, fun a x => ?_, hr⟩
  show r (incO h a * x) = a * r x
  have e1 : incO h a * x = a • x := (Algebra.smul_def a x).symm
  rw [e1, map_smul, smul_eq_mul]

end GlobalTheory.UseLoc
