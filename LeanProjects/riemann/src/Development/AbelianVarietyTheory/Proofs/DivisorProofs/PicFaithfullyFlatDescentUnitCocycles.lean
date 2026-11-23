import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraMapEqOfFaithfullyFlatIncludeLeftEqIStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopMulDescendedSubmoduleOfUnitCocycleEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDescentCocycleDescendedSubmoduleEqStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.PicCech

section
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem descMod_mul_le (u v : (B ⊗[A] B)ˣ) : descMod A B u * descMod A B v ≤ descMod A B (u * v) := by
  refine Submodule.mul_le.2 fun x hx y hy => ?_
  simp only [descMod, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply] at hx hy ⊢
  rw [map_mul, map_mul, Units.val_mul, ← hx, ← hy]; ring

theorem descMod_one_le [Module.FaithfullyFlat A B] : descMod A B 1 ≤ 1 := by
  intro b hb
  simp only [descMod, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, Units.val_one, one_mul] at hb
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B b hb.symm
  exact Submodule.mem_one.2 ⟨a, ha⟩

theorem uCoc_mul {u v : (B ⊗[A] B)ˣ} (hu : UCoc A B u) (hv : UCoc A B v) : UCoc A B (u * v) := by
  unfold UCoc at *
  simp only [Units.val_mul, map_mul, hu, hv]
  ring

theorem uCoc_inv {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) : UCoc A B u⁻¹ := by
  unfold UCoc at *
  set f13 := (Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B))
  set f12 := (Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B))
  set f23 := (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))
  have key : Units.map f13.toMonoidHom u = Units.map f12.toMonoidHom u * Units.map f23.toMonoidHom u :=
    Units.ext hu
  have key' := congrArg (fun x => ((x⁻¹ : (B ⊗[A] (B ⊗[A] B))ˣ) : B ⊗[A] (B ⊗[A] B))) key
  simp only [mul_inv, ← map_inv] at key'
  simpa [mul_comm] using key'

theorem descMod_mul_inv [Module.FaithfullyFlat A B] {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    descMod A B u * descMod A B u⁻¹ = 1 := by
  have hle : descMod A B u * descMod A B u⁻¹ ≤ 1 :=
    (descMod_mul_le u u⁻¹).trans (by rw [mul_inv_cancel]; exact descMod_one_le)
  refine le_antisymm hle ?_
  have htop : (⊤ : Submodule A B) * (descMod A B u * descMod A B u⁻¹) = ⊤ := by
    rw [← mul_assoc, GlobalTheory.T.top_mul_descendedSubmoduleOfUnitCocycle_eq_top A B u hu, GlobalTheory.T.top_mul_descendedSubmoduleOfUnitCocycle_eq_top A B u⁻¹ (uCoc_inv hu)]
  set J : Ideal A := (descMod A B u * descMod A B u⁻¹).comap (Algebra.linearMap A B) with hJ
  have hJtop : J • (⊤ : Submodule A B) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Submodule A B) = ⊤ * (descMod A B u * descMod A B u⁻¹) := htop.symm
      _ ≤ J • (⊤ : Submodule A B) := Submodule.mul_le.2 fun b _ p hp => ?_
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 (hle hp)
    have ha : a ∈ J := hp
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hJ1 : J = ⊤ := ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A B).1 inferInstance).2 J hJtop
  have h1 : (1 : A) ∈ J := hJ1 ▸ Submodule.mem_top
  rw [Submodule.one_le]
  simpa [hJ] using h1

theorem descMod_eq_span_iff [Module.FaithfullyFlat A B] {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    (∃ x : Bˣ, Submodule.spanSingleton A (x : B) = descMod A B u) ↔
      ∃ w : Bˣ, (u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) w =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) w := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hmem : (x : B) ∈ descMod A B u := hx ▸ Submodule.mem_span_singleton_self _
    simpa [descMod, LinearMap.mem_eqLocus] using hmem
  · rintro ⟨w, hw⟩
    refine ⟨w, le_antisymm ?_ ?_⟩
    · refine (Submodule.span_le).2 ?_
      rintro _ rfl
      simpa [descMod, LinearMap.mem_eqLocus] using hw
    · intro b hb
      have hwi : ((w⁻¹ : Bˣ) : B) ∈ descMod A B u⁻¹ := by
        simp only [descMod, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          AlgHom.toLinearMap_apply]
        have e1 : (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (w : B) *
            (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have e2 : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (w : B) *
            (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have e3 : (u : B ⊗[A] B) * ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = 1 := Units.mul_inv u
        calc ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B)
            = ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B) *
              ((u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (w : B) *
                (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B)) := by
              rw [hw, e2, mul_one]
          _ = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B) := by
              linear_combination (((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) * (u : B ⊗[A] B) * (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B)) * e1 + ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) ((w⁻¹ : Bˣ) : B)) * e3
      have hp : b * ((w⁻¹ : Bˣ) : B) ∈ descMod A B u * descMod A B u⁻¹ := Submodule.mul_mem_mul hb hwi
      rw [descMod_mul_inv hu] at hp
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 hp
      refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
      rw [Algebra.smul_def, ha, mul_assoc, Units.inv_mul, mul_one]

theorem isUnit_descMod [Module.FaithfullyFlat A B] {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    IsUnit (descMod A B u) :=
  IsUnit.of_mul_eq_one _ (descMod_mul_inv hu)

theorem descMod_mul [Module.FaithfullyFlat A B] {u v : (B ⊗[A] B)ˣ} (hu : UCoc A B u)
    (hv : UCoc A B v) : descMod A B (u * v) = descMod A B u * descMod A B v := by
  refine le_antisymm ?_ (descMod_mul_le u v)
  calc descMod A B (u * v) = descMod A B (u * v) * (descMod A B u * descMod A B u⁻¹) := by
        rw [descMod_mul_inv hu, mul_one]
    _ = descMod A B u * (descMod A B (u * v) * descMod A B u⁻¹) := by ring
    _ ≤ descMod A B u * descMod A B (u * v * u⁻¹) := by
        gcongr; exact descMod_mul_le _ _
    _ = descMod A B u * descMod A B v := by
        congr 2; rw [mul_comm u v, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_descMod_eq [Module.FaithfullyFlat A B] (I : (Submodule A B)ˣ) :
    ∃ u, UCoc A B u ∧ descMod A B u = I :=
  GlobalTheory.T.exists_unitDescentCocycle_descendedSubmodule_eq A B descMod_one_le I

theorem uCoc_map {B' : Type} [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B') {u : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) : UCoc A B' (Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u) := by
  unfold UCoc at *
  have h13 : ∀ x, (Algebra.TensorProduct.map (AlgHom.id A B') (Algebra.TensorProduct.includeRight : B' →ₐ[A] B' ⊗[A] B'))
      (Algebra.TensorProduct.map φ φ x) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ)
        ((Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)) x) := by
    intro x; induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have h12 : ∀ x, (Algebra.TensorProduct.map (AlgHom.id A B') (Algebra.TensorProduct.includeLeft : B' →ₐ[A] B' ⊗[A] B'))
      (Algebra.TensorProduct.map φ φ x) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ)
        ((Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) x) := by
    intro x; induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have h23 : ∀ x, (Algebra.TensorProduct.includeRight : B' ⊗[A] B' →ₐ[A] B' ⊗[A] (B' ⊗[A] B'))
      (Algebra.TensorProduct.map φ φ x) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ)
        ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) x) := by
    intro x; simp
  have e : ((Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u : (B' ⊗[A] B')ˣ) : B' ⊗[A] B') =
      Algebra.TensorProduct.map φ φ (u : B ⊗[A] B) := rfl
  rw [e, h13, h12, h23, hu, map_mul]

theorem descMod_map_le {B' : Type} [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B') (u : (B ⊗[A] B)ˣ) :
    (descMod A B u).map φ.toLinearMap ≤ descMod A B' (Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u) := by
  rintro _ ⟨b, hb, rfl⟩
  simp only [descMod, LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, Units.coe_map, MonoidHom.coe_coe] at hb ⊢
  have := congrArg (Algebra.TensorProduct.map φ φ) hb
  simpa using this

theorem nonempty_descMod_equiv [Module.FaithfullyFlat A B] {B' : Type} [CommRing B'] [Algebra A B']
    [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    Nonempty (descMod A B u ≃ₗ[A] descMod A B' (Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u)) := by
  set u' := Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u
  have hu' : UCoc A B' u' := uCoc_map φ hu
  haveI : Module.Invertible A (descMod A B u) :=
    inferInstanceAs (Module.Invertible A ((isUnit_descMod hu).unit : Submodule A B))
  haveI : Module.Invertible A (descMod A B' u') :=
    inferInstanceAs (Module.Invertible A ((isUnit_descMod hu').unit : Submodule A B'))
  have hmap := descMod_map_le φ u
  let f : descMod A B u →ₗ[A] descMod A B' u' :=
    (φ.toLinearMap.restrict (p := descMod A B u) (q := descMod A B' u')
      fun b hb => hmap (Submodule.mem_map_of_mem hb))
  have hinv : (descMod A B u⁻¹).map φ.toLinearMap ≤ descMod A B' u'⁻¹ := by
    have := descMod_map_le φ u⁻¹
    rwa [map_inv] at this
  set P := (descMod A B u).map φ.toLinearMap
  have h1 : (1 : Submodule A B') ≤ P * descMod A B' u'⁻¹ := by
    calc (1 : Submodule A B') = (1 : Submodule A B).map φ.toLinearMap := (Submodule.map_one φ).symm
      _ = P * (descMod A B u⁻¹).map φ.toLinearMap := by
          rw [← descMod_mul_inv hu, Submodule.map_mul]
      _ ≤ P * descMod A B' u'⁻¹ := by gcongr
  have hle : descMod A B' u' ≤ P := by
    calc descMod A B' u' = descMod A B' u' * 1 := (mul_one _).symm
      _ ≤ descMod A B' u' * (P * descMod A B' u'⁻¹) := by gcongr
      _ = P * (descMod A B' u' * descMod A B' u'⁻¹) := by ring
      _ = P := by rw [descMod_mul_inv hu', mul_one]
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb, rfl⟩ := hle hy
    exact ⟨⟨b, hb⟩, rfl⟩
  exact ⟨LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hsurj)⟩

end

def δ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (u : (B ⊗[A] B)ˣ) : CommRing.Pic A := by
  classical
  exact if h : Module.Invertible A (descMod A B u) then CommRing.Pic.mk A (descMod A B u) else 1

theorem δ_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {u : (B ⊗[A] B)ˣ} (hu : UCoc A B u) :
    δ A B u = Submodule.unitsToPic A B (isUnit_descMod hu).unit := by
  have : Module.Invertible A (descMod A B u) := inferInstanceAs (Module.Invertible A ((isUnit_descMod hu).unit : Submodule A B))
  rw [δ, dif_pos this, Submodule.unitsToPic_apply]
  rfl

end GlobalTheory.PicCech

open GlobalTheory.PicCech in

theorem GlobalTheory.pic_cech_descent : ∀ (A : Type) [CommRing A], ∃ δ : ∀ (B : Type) [CommRing B] [Algebra A B], (B ⊗[A] B)ˣ → CommRing.Pic A, ∀ (B : Type) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B], (∀ u v, UCoc A B u → UCoc A B v → δ B (u * v) = δ B u * δ B v) ∧ (∀ u, UCoc A B u → (δ B u = 1 ↔ ∃ w : Bˣ, (u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) w = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) w)) ∧ (∀ c : CommRing.Pic A, CommRing.Pic.mapAlgebra A B c = 1 → ∃ u, UCoc A B u ∧ δ B u = c) ∧ (∀ u, UCoc A B u → ∃ _ : Module.Invertible A (descMod A B u), CommRing.Pic.mk A (descMod A B u) = δ B u) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : (B ⊗[A] B)ˣ) (u' : (B' ⊗[A] B')ˣ), UCoc A B u → (u' : B' ⊗[A] B') = Algebra.TensorProduct.map φ φ (u : B ⊗[A] B) → δ B' u' = δ B u := by
  intro A _
  refine ⟨fun B _ _ u => δ A B u, fun B _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u v hu hv
    have huv : UCoc A B (u * v) := uCoc_mul hu hv
    dsimp only
    rw [δ_eq hu, δ_eq hv, δ_eq huv, ← map_mul]
    congr 1
    exact Units.ext (descMod_mul hu hv)
  · intro u hu
    dsimp only
    rw [δ_eq hu, ← MonoidHom.mem_ker, Submodule.ker_unitsToPic, ← descMod_eq_span_iff hu]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, congrArg Units.val hx⟩
    · rintro ⟨x, hx⟩; exact ⟨x, Units.ext hx⟩
  · intro c hc
    obtain ⟨I, rfl⟩ : c ∈ (Submodule.unitsToPic A B).range := by
      rw [Submodule.range_unitsToPic]; exact hc
    obtain ⟨u, hu, hI⟩ := exists_descMod_eq I
    refine ⟨u, hu, ?_⟩
    dsimp only
    rw [δ_eq hu]; congr 1; exact Units.ext hI
  · intro u hu
    refine ⟨inferInstanceAs (Module.Invertible A ((isUnit_descMod hu).unit : Submodule A B)), ?_⟩
    dsimp only
    rw [δ_eq hu, Submodule.unitsToPic_apply]; rfl
  · intro B' _ _ _ φ u u' hu hu'
    have hu'' : u' = Units.map (Algebra.TensorProduct.map φ φ).toMonoidHom u := Units.ext hu'
    subst hu''
    dsimp only
    rw [δ_eq hu, δ_eq (uCoc_map φ hu), Submodule.unitsToPic_apply, Submodule.unitsToPic_apply,
      CommRing.Pic.mk_eq_mk_iff]
    exact (nonempty_descMod_equiv φ hu).map LinearEquiv.symm
