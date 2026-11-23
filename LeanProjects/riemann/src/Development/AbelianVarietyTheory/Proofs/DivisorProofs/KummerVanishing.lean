import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraMapEqOfFaithfullyFlatIncludeLeftEqIStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneSectionsEqRootsOfUnityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem uCoc_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : UCoc A B 1 := by
  unfold UCoc
  simp [Algebra.TensorProduct.one_def]

theorem uCoc_mul {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u v : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (hv : UCoc A B v) : UCoc A B (u * v) := by
  unfold UCoc at *
  simp only [Units.val_mul, map_mul, hu, hv]
  ring

theorem uCoc_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (n : ℕ) : UCoc A B (u ^ n) := by
  induction n with
  | zero => simpa using uCoc_one A B
  | succ n ih => rw [pow_succ]; exact uCoc_mul ih hu

theorem kummer_vanishing : B6h1 := by
  intro q _ A _ hq hu hp
  suffices h : ∀ x : Ht q (sp A) 1 1, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover (ZMod q) (Spec (CommRingCat.of A)) (tw q 1) 1 one_pos x
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of A) Y f hfe hfs
  letI : Algebra A B := g.hom.toAlgebra
  haveI : Algebra.Etale A B := hg.1
  haveI : Module.FaithfullyFlat A B := hg.2
  have hxB : pull (ZMod q) (spMap (algebraMap A B)) (tw q 1) 1 x = 0 := by
    have : spMap (algebraMap A B) = sch.map h ≫ sch.map f := by
      rw [← sch.map_comp, hhf]; rfl
    rw [this, pull_comp, hx, map_zero]
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.etale_cocycle_coboundary_iff (ZMod q) (tw q 1) A
  obtain ⟨hγ0, hγs, -, -⟩ := hγ B
  obtain ⟨u, rfl⟩ := hγs x hxB
  rw [hγ0]

  obtain ⟨e, he⟩ := GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity q
  have hqB : IsUnit (q : (B : Type)) := by simpa using hq.map (algebraMap A B)
  have hqBB : IsUnit (q : B ⊗[A] B) := by simpa using hq.map (algebraMap A (B ⊗[A] B))
  have hqBBB : IsUnit (q : B ⊗[A] (B ⊗[A] B)) := by simpa using hq.map (algebraMap A (B ⊗[A] (B ⊗[A] B)))
  have hUq : ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) ^ q = 1 :=
    (mem_rootsOfUnity _ _).1 (Additive.toMul (e _ hqBB u.1)).2
  have hUc : UCoc A B ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) := by
    have h2 := u.2
    change _ = _ at h2
    have h3 := congrArg (fun y => ((Additive.toMul (e _ hqBBB y) : rootsOfUnity q _) : (B ⊗[A] (B ⊗[A] B))ˣ)) h2
    simp only [AddMonoidHom.add_apply, map_add, toMul_add, Subgroup.coe_mul, LinearMap.toAddMonoidHom_coe] at h3
    rw [he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB] at h3
    have h4 := congrArg Units.val h3
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.coe_toRingHom] at h4
    exact h4

  set U := ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) with hUdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A
  obtain ⟨hmul, hone, -, -, -⟩ := hδ B
  have hδ1 : δ B 1 = 1 := by
    have := hmul 1 1 (uCoc_one A B) (uCoc_one A B)
    rw [mul_one] at this
    simpa using this
  have hδpow : ∀ n : ℕ, δ B (U ^ n) = δ B U ^ n := by
    intro n
    induction n with
    | zero => simpa using hδ1
    | succ n ih => rw [pow_succ, hmul _ _ (uCoc_pow hUc n) hUc, ih, pow_succ]
  have hδU : δ B U = 1 := hp _ (by rw [← hδpow, hUq, hδ1])
  obtain ⟨w, hw⟩ := (hone U hUc).1 hδU
  let iL : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  have hwU : U * Units.map iR.toRingHom.toMonoidHom w = Units.map iL.toRingHom.toMonoidHom w :=
    Units.ext (by simpa [iL, iR] using hw)
  have hWq : Units.map iL.toRingHom.toMonoidHom (w ^ q) = Units.map iR.toRingHom.toMonoidHom (w ^ q) := by
    rw [map_pow, map_pow, ← hwU, mul_pow, hUq, one_mul]
  have hWq' : Units.map iL.toRingHom.toMonoidHom (w ^ q)⁻¹ = Units.map iR.toRingHom.toMonoidHom (w ^ q)⁻¹ := by
    rw [map_inv, map_inv, hWq]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B ((w ^ q : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq)
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B (((w ^ q)⁻¹ : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq')
  have haa : a * a' = 1 :=
    FaithfulSMul.algebraMap_injective A B (by rw [map_mul, ha, ha', Units.mul_inv, map_one])
  obtain ⟨v, hv⟩ := hu ⟨a, a', haa, by rw [mul_comm, haa]⟩
  let vB : (B : Type)ˣ := Units.map (algebraMap A B).toMonoidHom v
  have hvB : vB ^ q = w ^ q := by
    apply Units.ext
    rw [← map_pow, ← hv, Units.coe_map]
    exact ha
  have hT : (vB * w⁻¹) ^ q = 1 := by rw [mul_pow, hvB, inv_pow, mul_inv_cancel]
  let Tr : rootsOfUnity q (B : Type) := ⟨vB * w⁻¹, (mem_rootsOfUnity _ _).2 hT⟩
  have hV : Units.map iR.toRingHom.toMonoidHom vB = Units.map iL.toRingHom.toMonoidHom vB := by
    apply Units.ext
    simp [vB, iL, iR]
  refine ⟨(e _ hqB).symm (Additive.ofMul Tr), ?_⟩
  apply (e _ hqBB).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [map_sub, toMul_sub, SubgroupClass.coe_div, he _ _ _ hqB hqBB, he _ _ _ hqB hqBB, AddEquiv.apply_symm_apply]
  change U = Units.map iR.toRingHom.toMonoidHom (vB * w⁻¹) / Units.map iL.toRingHom.toMonoidHom (vB * w⁻¹)
  rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq, map_mul, map_mul, map_inv, map_inv, hV, ← hwU]
  rw [mul_inv_rev, mul_left_comm, ← mul_assoc U, mul_comm U, mul_assoc, mul_inv_cancel, mul_one]
end GlobalTheory.EtC
