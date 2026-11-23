import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemisimpleEquivariantProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemisimpleAnnihilatorSpanEndomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeVectorMatrixCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulUnitaryRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCocycleRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMatrixCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeSubrepresentationExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemisimpleEquivariantProjectionUniqueStatement

open GlobalTheory.LocFinIso

namespace GlobalTheory.LocFinIso

theorem isoProj_locFin : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V), (1 : G) ∈ K → (∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) → (∀ k ∈ K, k⁻¹ ∈ K) → (∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D) → (∀ x ∈ D, ∃ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ), LinearIndependent ℂ b ∧ (∀ i, b i ∈ D) ∧ x ∈ Submodule.span ℂ (Set.range b) ∧ (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) ∧ (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) ∧ ContinuousOn A K) → ∀ Φ : ↥D, ∃ (m : ℕ) (τ : G → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))), (τ 1 = 1 ∧ (∀ k ∈ K, ∀ k' ∈ K, τ (k * k') = τ k * τ k') ∧ (∀ k ∈ K, ∀ v, ‖τ k v‖ = ‖v‖) ∧ ∀ v, ContinuousOn (fun k => τ k v) K) ∧ ∃ P : ↥D →ₗ[ℂ] ↥D, P Φ = Φ ∧ (∀ x, P (P x) = P x) ∧ (∀ x y : ↥D, ∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → G), (∀ i, k i ∈ K) ∧ ((P x : ↥D) : V) = ∑ i, c i • ρ (k i) (x : V) ∧ ((P y : ↥D) : V) = ∑ i, c i • ρ (k i) (y : V) ∧ ((P y : ↥D) : V) = ∑ i, starRingEnd ℂ (c i) • ρ (k i)⁻¹ (y : V)) ∧ ∀ x : ↥D, ∃ T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] V, (∀ k ∈ K, ∀ v, T (τ k v) = ρ k (T v)) ∧ ((P x : ↥D) : V) ∈ LinearMap.range T := by
  classical
  intro G _ _ K V _ _ ρ D h1 hmul hinv hst hloc Φ
  have hloc' : ∀ x ∈ D, ∃ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ),
      LinearIndependent ℂ b ∧ (∀ i, b i ∈ D) ∧ x ∈ Submodule.span ℂ (Set.range b) ∧
      (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) ∧
      (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) := fun x hx => by
    obtain ⟨m, b, A, h1', h2, h3, h4, h5, -⟩ := hloc x hx
    exact ⟨m, b, A, h1', h2, h3, h4, h5⟩
  haveI hss := GlobalTheory.T.isSemisimpleModule_repD_of_finite_type_unitary G K V ρ D h1 hmul hinv hst hloc'
  obtain ⟨P, hPΦ, hPP, hPc, hPann⟩ :=
    GlobalTheory.T.semisimple_equivariant_projection _ _ hss ((repD ρ D K h1 hmul hst).asModuleEquiv.symm Φ)
  obtain ⟨m₀, b₀, A₀, hli₀, hbD₀, hΦ₀, hA₀, hU₀, hc₀⟩ := hloc Φ Φ.2
  obtain ⟨hA1, hAmul, -⟩ := GlobalTheory.T.unitary_cocycle_representation G K V ρ m₀ b₀ A₀ h1 hmul hinv hli₀ hA₀ hU₀
  refine ⟨m₀ * m₀, leftMul A₀, GlobalTheory.T.left_mul_unitary_representation G K m₀ A₀ hA1 hAmul hU₀ hc₀,
    toEndD ρ D K h1 hmul hst P, ?_, ?_, ?_, ?_⟩
  · rw [toEndD_apply, hPΦ]; simp
  · intro x; simp only [toEndD_apply, LinearEquiv.symm_apply_apply, hPP]
  · intro x y
    obtain ⟨m, b, A, hli, hbD, hy, hA, hU⟩ := hloc' y y.2
    obtain ⟨-, -, hAinv⟩ := GlobalTheory.T.unitary_cocycle_representation G K V ρ m b A h1 hmul hinv hli hA hU
    obtain ⟨Pm, hPm, hPms⟩ := GlobalTheory.T.semisimple_equivariant_projection_unique G K V ρ D h1 hmul hst hss P hPP hPc m b A hbD hli hA hU
    let f : Module.End (Module.End (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule)
        (repD ρ D K h1 hmul hst).asModule :=
      { toFun := P, map_add' := P.map_add, map_smul' := fun g v => hPc g v }
    obtain ⟨a, ha⟩ := jacobson_density f (insert ((repD ρ D K h1 hmul hst).asModuleEquiv.symm x)
      (Finset.univ.image fun j => (repD ρ D K h1 hmul hst).asModuleEquiv.symm ⟨b j, hbD j⟩))
    have haP : ∀ u ∈ insert ((repD ρ D K h1 hmul hst).asModuleEquiv.symm x)
        (Finset.univ.image fun j => (repD ρ D K h1 hmul hst).asModuleEquiv.symm ⟨b j, hbD j⟩),
        P u = a • u := fun u hu => ha u hu
    let ks : Fin a.coeff.support.card ≃ a.coeff.support := a.coeff.support.equivFin.symm
    have hsum : ∀ u : D, (((repD ρ D K h1 hmul hst).asModuleEquiv
        (a • (repD ρ D K h1 hmul hst).asModuleEquiv.symm u) : D) : V) =
        ∑ i, a.coeff (ks i).1 • ρ ((ks i).1 : G) (u : V) := by
      intro u
      rw [smul_val, LinearEquiv.apply_symm_apply, ← Finset.sum_coe_sort a.coeff.support]
      exact (Fintype.sum_equiv ks _ _ (fun i => rfl)).symm
    refine ⟨a.coeff.support.card, fun i => a.coeff (ks i).1, fun i => ((ks i).1 : G),
      fun i => (ks i).1.2, ?_, ?_⟩
    · rw [toEndD_apply, haP _ (Finset.mem_insert_self _ _), hsum]

    have hgen1 : ∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) =
        ∑ i, a.coeff (ks i).1 • ρ ((ks i).1 : G) (b j) := by
      intro j
      rw [toEndD_apply, haP _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))), hsum]
    have hPmeq : ∀ l j, Pm l j = ∑ i, a.coeff (ks i).1 * A ((ks i).1 : G) l j := by
      intro l j
      have h := (hPm j).symm.trans (hgen1 j)
      simp only [hA _ (ks _).1.2, Finset.smul_sum, smul_smul] at h
      rw [Finset.sum_comm] at h
      simp only [← Finset.sum_smul] at h
      exact Fintype.linearIndependent_iffₛ.1 hli _ _ h l
    have hgen2 : ∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) =
        ∑ i, starRingEnd ℂ (a.coeff (ks i).1) • ρ ((ks i).1 : G)⁻¹ (b j) := by
      intro j
      rw [hPm j]
      simp only [hA _ (hinv _ (ks _).1.2), hAinv _ (ks _).1.2, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      congr 1
      rw [← hPms, Matrix.star_apply, hPmeq, star_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.star_apply, star_mul', starRingEnd_apply, mul_comm]
    obtain ⟨t, ht⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.1 hy
    have hyD : y = ∑ j, t j • (⟨b j, hbD j⟩ : D) := by
      ext; simp [ht]
    have hlin : ∀ (F : V →ₗ[ℂ] V), (∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = F (b j)) →
        ((toEndD ρ D K h1 hmul hst P y : D) : V) = F y := by
      intro F hF
      conv_lhs => rw [hyD]
      rw [← ht, map_sum, Submodule.coe_sum, map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, Submodule.coe_smul, hF, map_smul]
    refine ⟨?_, ?_⟩
    · have := hlin (∑ i, a.coeff (ks i).1 • ρ ((ks i).1 : G)) (fun j => by rw [hgen1]; simp)
      rw [this]; simp
    · have := hlin (∑ i, starRingEnd ℂ (a.coeff (ks i).1) • ρ ((ks i).1 : G)⁻¹) (fun j => by rw [hgen2]; simp)
      rw [this]; simp
  · intro x
    obtain ⟨W, hW⟩ := GlobalTheory.T.finite_type_subrepresentation_exists G K V ρ D h1 hmul hst m₀ b₀ A₀ hbD₀ hA₀
    have hΦW : (repD ρ D K h1 hmul hst).asModuleEquiv.symm Φ ∈ W := (hW _).2 (by simpa using hΦ₀)
    have hann : ∀ a : MonoidAlgebra ℂ (subK K h1 hmul),
        (∀ j, a • (repD ρ D K h1 hmul hst).asModuleEquiv.symm ⟨b₀ j, hbD₀ j⟩ = 0) →
        a • P ((repD ρ D K h1 hmul hst).asModuleEquiv.symm x) = 0 := by
      intro a ha
      refine hPann W hΦW a (fun u hu => ?_) _
      obtain ⟨t, ht⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.1 ((hW u).1 hu)
      have hu' : (repD ρ D K h1 hmul hst).asModuleEquiv u = ∑ j, t j • (⟨b₀ j, hbD₀ j⟩ : D) := by
        ext; simp [ht]
      apply (repD ρ D K h1 hmul hst).asModuleEquiv.injective
      rw [Representation.asModuleEquiv_map_smul, hu', map_sum, map_zero]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [map_smul]
      have := congrArg (repD ρ D K h1 hmul hst).asModuleEquiv (ha j)
      rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, map_zero] at this
      rw [this, smul_zero]
    obtain ⟨f, hf⟩ := GlobalTheory.T.semisimple_annihilator_span_endomorphisms _ _ hss m₀ _ _ hann
    have hfe : ∀ j, ∀ k ∈ K, ∀ u v : D, (v : V) = ρ k u →
        ((toEndD ρ D K h1 hmul hst (f j) v : D) : V) = ρ k (toEndD ρ D K h1 hmul hst (f j) u) := by
      intro j k hk u v huv
      have hv : v = repD ρ D K h1 hmul hst ⟨k, hk⟩ u := Subtype.ext huv
      rw [hv, toEndD_apply, toEndD_apply, Representation.asModuleEquiv_symm_map_rho, (f j).map_smul,
        Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of, repD_apply]
    obtain ⟨T, hT, hTr⟩ := GlobalTheory.T.intertwiner_matrix_coefficients G K V ρ D m₀ b₀ A₀ hbD₀ (fun j => toEndD ρ D K h1 hmul hst (f j)) hA₀ hfe
    refine ⟨T, hT, ?_⟩
    convert hTr using 1
    rw [toEndD_apply, hf, map_sum, Submodule.coe_sum]
    rfl

end GlobalTheory.LocFinIso
