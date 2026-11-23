import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingElementRingHomModuleFiniteIntStatement

open scoped TensorProduct

namespace GlobalTheory.WeightCount

open Module

theorem isNilpotent_perturb_mul {R : Type*} [Ring R] {A B a b : R} (hAB : Commute A B)
    (ha : ∀ z, Commute a z) (hb : ∀ z, Commute b z) (hA : IsNilpotent A) (hB : IsNilpotent B) :
    IsNilpotent ((A + a) * (B + b) - a * b) := by
  have e : (A + a) * (B + b) - a * b = A * (B + b) + a * B := by noncomm_ring
  rw [e]
  have h1 : Commute A (B + b) := hAB.add_right (hb A).symm
  have h3 : Commute (A * (B + b)) B := Commute.mul_left hAB ((Commute.refl B).add_left (hb B))
  have h2 : Commute (A * (B + b)) (a * B) := Commute.mul_right (ha _).symm h3
  exact h2.isNilpotent_add (h1.isNilpotent_mul_right hA) ((ha B).isNilpotent_mul_left hB)

theorem weight_isRingHom {k V C : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) (ψ : C → k)
    (hψ : (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥) : ∃ φ : C →+* k, ⇑φ = ψ := by
  classical
  set U := ⨅ d, (ρ d).maxGenEigenspace (ψ d) with hU
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ
  have hUm : ∀ m, Set.MapsTo (ρ m) U U := fun m v hv => by
    simp only [U, SetLike.mem_coe, Submodule.mem_iInf] at hv ⊢
    exact fun i => hmaps m i (ψ i) (hv i)
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hψ
  let R : C → Module.End k U := fun m => (ρ m).restrict (hUm m)
  have hRadd : ∀ x y, R (x + y) = R x + R y := fun x y => by
    ext v
    show ρ (x + y) (v : V) = ρ x (v : V) + ρ y (v : V)
    rw [map_add]; rfl
  have hRmul : ∀ x y, R (x * y) = R x * R y := fun x y => by
    ext v
    show ρ (x * y) (v : V) = ρ x (ρ y (v : V))
    rw [map_mul]; rfl
  have hR1 : R 1 = 1 := by ext v; simp [R, LinearMap.restrict_apply]
  have hR0 : R 0 = 0 := by ext v; simp [R, LinearMap.restrict_apply]
  have hRc : ∀ x y, Commute (R x) (R y) := fun x y => by
    show R x * R y = R y * R x
    rw [← hRmul, ← hRmul, mul_comm]
  have hnil : ∀ m, IsNilpotent (R m - algebraMap k _ (ψ m)) := by
    intro m
    have hsub : Set.MapsTo (ρ m - algebraMap k (Module.End k V) (ψ m)) (U : Set V) U := by
      intro v hv
      simp only [SetLike.mem_coe, LinearMap.sub_apply, Module.algebraMap_end_apply] at hv ⊢
      exact U.sub_mem (hUm m hv) (U.smul_mem _ hv)
    have hn : IsNilpotent ((ρ m - algebraMap k _ (ψ m)).restrict hsub) :=
      Module.End.isNilpotent_restrict_of_le (iInf_le _ m)
        (Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (ρ m) (ψ m))
    have e : R m - algebraMap k _ (ψ m) = (ρ m - algebraMap k _ (ψ m)).restrict hsub := by
      ext v
      simp only [R, LinearMap.sub_apply, Module.algebraMap_end_apply, Submodule.coe_sub,
        Submodule.coe_smul]
      rfl
    rw [e]
    exact hn
  have hNc : ∀ x y, Commute (R x - algebraMap k _ (ψ x)) (R y - algebraMap k _ (ψ y)) :=
    fun x y => ((hRc x y).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
      ((Algebra.commute_algebraMap_left _ _).sub_right (Algebra.commute_algebraMap_left _ _))
  have key : ∀ a : k, IsNilpotent (algebraMap k (Module.End k U) a) → a = 0 := fun a h => by
    rwa [IsNilpotent.map_iff (FaithfulSMul.algebraMap_injective k (Module.End k U)),
      isNilpotent_iff_eq_zero] at h
  refine ⟨{ toFun := ψ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, rfl⟩
  · have h := hnil 1
    rw [hR1, ← map_one (algebraMap k (Module.End k U)), ← map_sub] at h
    exact (sub_eq_zero.1 (key _ h)).symm
  · intro x y
    have h1 := isNilpotent_perturb_mul (hNc x y) (Algebra.commute_algebraMap_left (ψ x))
      (Algebra.commute_algebraMap_left (ψ y)) (hnil x) (hnil y)
    rw [sub_add_cancel, sub_add_cancel, ← hRmul, ← map_mul] at h1
    have h2 := hnil (x * y)
    have h3 := (((Commute.refl (R (x * y))).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
      ((Algebra.commute_algebraMap_left _ _).sub_right
        (Algebra.commute_algebraMap_left _ _))).isNilpotent_sub h1 h2
    have e : R (x * y) - algebraMap k _ (ψ x * ψ y) - (R (x * y) - algebraMap k _ (ψ (x * y))) =
        algebraMap k (Module.End k U) (ψ (x * y) - ψ x * ψ y) := by
      rw [map_sub]; abel
    rw [e] at h3
    exact sub_eq_zero.1 (key _ h3)
  · have h := hnil 0
    rw [hR0, zero_sub, ← map_neg] at h
    exact neg_eq_zero.1 (key _ h)
  · intro x y
    have h1 := (hNc x y).isNilpotent_add (hnil x) (hnil y)
    have h2 := hnil (x + y)
    have h3 := ((hNc (x + y) x).add_right (hNc (x + y) y)).isNilpotent_sub h2 h1
    have e : R (x + y) - algebraMap k _ (ψ (x + y)) -
        (R x - algebraMap k _ (ψ x) + (R y - algebraMap k _ (ψ y))) =
        algebraMap k (Module.End k U) (ψ x + ψ y - ψ (x + y)) := by
      rw [hRadd, map_sub, map_add]; abel
    rw [e] at h3
    exact (sub_eq_zero.1 (key _ h3)).symm

theorem exists_finset_weights {k V C : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) :
    ∃ S : Finset (C →+* k), ∀ ψ : C → k, (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥ →
      ∃ φ ∈ S, ⇑φ = ψ := by
  classical
  let U : (C → k) → Submodule k V := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ
  have hind : iSupIndep U :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun x => ρ x) hmaps
  have hfin : {ψ | U ψ ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  refine ⟨hfin.toFinset.attach.image (fun ψ => Classical.choose (weight_isRingHom ρ ψ.1
    (by have := ψ.2; rw [Set.Finite.mem_toFinset] at this; exact this))), fun ψ hψ => ?_⟩
  have hmem : ψ ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hψ
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨ψ, hmem⟩), ?_⟩
  exact Classical.choose_spec (weight_isRingHom ρ ψ hψ)

end GlobalTheory.WeightCount

namespace GlobalTheory.WeightCount

open Module

theorem maxGenEigenspace_eq_weight {k V C : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) (χ : C → k)
    (c : C) (hc : ∀ ψ : C → k, (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ χ → ψ c ≠ χ c) :
    (ρ c).maxGenEigenspace (χ c) = ⨅ d, (ρ d).maxGenEigenspace (χ d) := by
  classical
  let U : (C → k) → Submodule k V := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  have hcomm : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) μ
  have htop : ⨆ ψ, U ψ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun x => ρ x) hmaps
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top (ρ i))
  set E := (ρ c).maxGenEigenspace (χ c) with hE
  have hXE : U χ ≤ E := iInf_le _ c
  have hY : (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ≤ ⨆ μ, ⨆ (_ : μ ≠ χ c), (ρ c).maxGenEigenspace μ := by
    refine iSup₂_le fun ψ hψ => ?_
    by_cases h0 : U ψ = ⊥
    · rw [h0]; exact bot_le
    · exact le_iSup₂_of_le (f := fun μ (_ : μ ≠ χ c) => (ρ c).maxGenEigenspace μ) (ψ c)
        (hc ψ h0 hψ) (iInf_le _ c)
  have hdisj : Disjoint E (⨆ μ, ⨆ (_ : μ ≠ χ c), (ρ c).maxGenEigenspace μ) :=
    (Module.End.independent_maxGenEigenspace (ρ c)) (χ c)
  have hsup : U χ ⊔ (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) = ⊤ := by
    rw [← htop]; exact (iSup_split_single U χ).symm
  have hEY : (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E = ⊥ := (hdisj.mono_right hY).symm.eq_bot
  calc E = (U χ ⊔ ⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E := by rw [hsup, top_inf_eq]
    _ = U χ ⊔ (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E := sup_inf_assoc_of_le _ hXE
    _ = U χ := by rw [hEY, sup_bot_eq]

theorem charpoly_lmul_includeRight (k C : Type) [Field k] [CommRing C] [Module.Free ℤ C]
    [Module.Finite ℤ C] (c : C) :
    LinearMap.charpoly (Algebra.lmul k (k ⊗[ℤ] C)
      ((Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C) c)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)).map (Int.castRingHom k) := by
  have e : Algebra.lmul k (k ⊗[ℤ] C) ((Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C) c) =
      (LinearMap.mulLeft ℤ c).baseChange k := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e, LinearMap.charpoly_baseChange, algebraMap_int_eq]

theorem finrank_weight_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C]
    [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H]
    [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ),
    (∀ c : C, LinearMap.charpoly (σ c) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) →
    ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) =
      r * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace
          (χ c)) := by
  intro k _ _ C _ _ _ H _ _ _ σ r hσ χ
  classical
  let σA : C →+* Module.End k (k ⊗[ℤ] C) := (Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom
  have hA : ∀ c, LinearMap.charpoly (σA c) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)).map (Int.castRingHom k) :=
    fun c => charpoly_lmul_includeRight k C c
  obtain ⟨S1, hS1⟩ := exists_finset_weights σ
  obtain ⟨S2, hS2⟩ := exists_finset_weights σA
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_separating_element_ringHom_moduleFinite_int k C (S1 ∪ S2) χ
  have sepH : ∀ ψ : C → k, (⨅ d, (σ d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ ⇑χ → ψ c ≠ χ c := by
    intro ψ h hne
    obtain ⟨φ, hφS, rfl⟩ := hS1 ψ h
    exact hc φ (Finset.mem_union_left _ hφS) (fun e => hne (by rw [e]))
  have sepA : ∀ ψ : C → k, (⨅ d, (σA d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ ⇑χ → ψ c ≠ χ c := by
    intro ψ h hne
    obtain ⟨φ, hφS, rfl⟩ := hS2 ψ h
    exact hc φ (Finset.mem_union_right _ hφS) (fun e => hne (by rw [e]))
  show Module.finrank k ↥(⨅ d : C, (σ d).maxGenEigenspace (χ d)) =
    r * Module.finrank k ↥(⨅ d : C, (σA d).maxGenEigenspace (χ d))
  rw [← maxGenEigenspace_eq_weight σ χ c sepH, ← maxGenEigenspace_eq_weight σA χ c sepA,
    LinearMap.finrank_maxGenEigenspace_eq, LinearMap.finrank_maxGenEigenspace_eq, hσ c, hA c,
    Polynomial.map_pow, ← Polynomial.count_roots, ← Polynomial.count_roots, Polynomial.roots_pow,
    Multiset.count_nsmul]

end GlobalTheory.WeightCount
