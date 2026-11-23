import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace CoverDenseAlt

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
  ReciprocityTheory.ChartRestriction.G.DVR.FlatBC ReciprocityTheory.ChartRestriction.G

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))

include H in
theorem exists_sec_of_flat_pull [Module.Flat R S] [CompactSpace X]
    (hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W))
    (L : LB X) (hL : L.IsLB) (σ' : LB.Sec (L.pull φ)) (y : X') (hy : y ∈ Out.nonzeroLocus σ') :
    ∃ σ : LB.Sec L, φ y ∈ Out.nonzeroLocus σ := by
  classical
  obtain ⟨n, V, c, hVa, hVc, hcov⟩ := exists_affine_chart_cover L hL
  letI instV : ∀ k, Algebra R Γ(X, V k) := fun k => (algX p (V k)).toAlgebra
  letI instW : ∀ kl : Fin n × Fin n, Algebra R Γ(X, V kl.1 ⊓ V kl.2) := fun kl => (algX p _).toAlgebra
  let δ : (∀ k, Γ(X, V k)) →ₗ[R] (∀ kl : Fin n × Fin n, Γ(X, V kl.1 ⊓ V kl.2)) :=
    { toFun := fun f kl => dfun L V c hVc f kl.1 kl.2
      map_add' := fun f g => by
        funext kl
        simp only [dfun, Pi.add_apply, map_add, mul_add]
        abel
      map_smul' := fun r f => by
        funext kl
        simp only [dfun, RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        rw [rs_mul, rs_mul, rs_algX, rs_algX]
        ring }
  have hδ : ∀ m, δ m = 0 ↔ dfun L V c hVc m = 0 := fun m => by
    constructor
    · intro h; funext k l; exact congrFun h (k, l)
    · intro h; funext kl; exact congrFun (congrFun h kl.1) kl.2
  have hV'c : ∀ k, φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤ ≤ (L.pull φ).U (fun _ => c k) := fun k y hy =>
    Set.mem_iInter.2 fun _ => hVc k hy.1
  let m' : ∀ k, Γ(X', φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤) := fun k => rs (hV'c k) (σ'.f (fun _ => c k))
  let t : (∀ k, Γ(X, V k)) ⊗[R] S := (TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))).symm
    (fun k => (eTens p p' φ H (V k) (hVa k)).symm (m' k))
  have hpt : ∀ k, (TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))) t k =
      (eTens p p' φ H (V k) (hVa k)).symm (m' k) := fun k => by
    simp only [t, LinearEquiv.apply_symm_apply]
  have ht : δ.rTensor S t = 0 := by
    apply (TensorProduct.piLeft (R := R) (N := S) (M := fun kl : Fin n × Fin n => Γ(X, V kl.1 ⊓ V kl.2))).injective
    rw [map_zero]
    funext kl
    obtain ⟨k, l⟩ := kl
    rw [piLeft_apply_eq, ← LinearMap.rTensor_comp_apply]
    have hdec : (LinearMap.proj (k, l) : (∀ kl : Fin n × Fin n, Γ(X, V kl.1 ⊓ V kl.2)) →ₗ[R] _).comp δ =
        (rsL p (V k) (V k ⊓ V l) inf_le_left).comp (LinearMap.proj k) -
          (mulL p (V k ⊓ V l) (res (pair_le L V c hVc k l) (L.g (c k) (c l))).val).comp
            ((rsL p (V l) (V k ⊓ V l) inf_le_right).comp (LinearMap.proj l)) := by
      ext f; rfl
    rw [hdec, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply,
      LinearMap.rTensor_comp_apply, ← piLeft_apply_eq, ← piLeft_apply_eq, hpt, hpt]
    apply (eTens p p' φ H (V k ⊓ V l) (hinter _ _ (hVa k) (hVa l))).injective
    rw [map_sub, eTens_rs p p' φ H (V k) (V k ⊓ V l) (hVa k) _ inf_le_left, eTens_mul,
      eTens_rs p p' φ H (V l) (V k ⊓ V l) (hVa l) _ inf_le_right, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, sub_eq_zero]
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext fun y hy => ?_
    have hyk : y ∈ (L.pull φ).U (fun _ => c k) := Set.mem_iInter.2 fun _ => hVc k hy.1.1
    have hyl : y ∈ (L.pull φ).U (fun _ => c l) := Set.mem_iInter.2 fun _ => hVc l hy.1.2
    have hyk' : y ∈ φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤ := ⟨hy.1.1, hy.2⟩
    have hyl' : y ∈ φ ⁻¹ᵁ V l ⊓ p' ⁻¹ᵁ ⊤ := ⟨hy.1.2, hy.2⟩
    have hφy : φ y ∈ V k ⊓ V l := hy.1
    simp only [m']
    rw [Geo.Tor.gs_mul _ y _ hy, Geo.Tor.gs_res _ y _ hy, Geo.Tor.gs_res _ y _ hyk', Geo.Tor.gs_res _ y _ hy,
      Geo.Tor.gs_res _ y _ hyl', Geo.Tor.gs_appLE φ _ _ _ (𝟙 _) y hy]
    erw [Category.id_comp, Geo.Tor.gs_unit _ y _ hφy, Geo.Tor.gm_res _ y _ hφy]
    erw [gs_sec (L.pull φ) σ' (fun _ => c k) (fun _ => c l) y hyk hyl,
      Geo.Tor.gm_pull_g L φ (𝟙 _) y (fun _ => c k) (fun _ => c l) hyk hyl, Category.id_comp]
  obtain ⟨x, hx⟩ := (Module.Flat.rTensor_exact S (LinearMap.exact_subtype_ker_map δ) t).1 ht
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ (⨆ k, V k : X.Opens) by rw [hcov]; trivial)
  have key : ∀ x : (LinearMap.ker δ) ⊗[R] S, y ∈ X'.basicOpen (eTens p p' φ H (V k) (hVa k)
      ((TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))) ((LinearMap.ker δ).subtype.rTensor S x) k)) →
      ∃ σ : LB.Sec L, φ y ∈ Out.nonzeroLocus σ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      intro h
      rw [map_zero, map_zero, Pi.zero_apply, (eTens p p' φ H (V k) (hVa k)).map_zero, Scheme.basicOpen_zero] at h
      exact h.elim
    | tmul m s =>
      intro h
      rw [LinearMap.rTensor_tmul, piLeft_apply_eq, LinearMap.rTensor_tmul, eTens_tmul, Scheme.basicOpen_mul] at h
      have h1 := h.1
      erw [Scheme.basicOpen_appLE] at h1
      obtain ⟨σ, hσ⟩ := exists_glue L V c hVc hL hcov m.1 ((hδ _).1 m.2)
      refine ⟨σ, GlobalTheory.basicOpen_le_nonzeroLocus σ (c k) ?_⟩
      have h2 : φ y ∈ X.basicOpen (m.1 k) := h1.2
      rw [← hσ] at h2
      simp only [ev, rs] at h2
      erw [Scheme.basicOpen_res] at h2
      exact h2.2
    | add x₁ x₂ h₁ h₂ =>
      intro h
      rw [map_add, map_add, Pi.add_apply, map_add] at h
      rcases Scheme.basicOpen_add_le _ _ _ h with h | h
      exacts [h₁ h, h₂ h]
  apply key x
  rw [hx, hpt, RingEquiv.apply_symm_apply]
  have hyk : y ∈ φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤ := ⟨hk, trivial⟩
  simp only [m', rs]
  erw [Scheme.basicOpen_res]
  exact ⟨hyk, (GlobalTheory.mem_nonzeroLocus_iff_basicOpen σ' (hV'c k hyk)).1 hy⟩

end CoverDenseAlt
