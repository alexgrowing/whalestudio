import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJStandardL
import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRepBasic
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatakeRep

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra

namespace GroundTheory.Automorphic.GJStandardLCuspidal

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

include hKc hKo in
theorem dual_idem (L : Module.Dual ℂ V) (hL : ∀ k ∈ K, ∀ u, L (ρ k u) = L u) {u : V}
    (hu : u ∈ smoothVectors ρ) :
    L (heckeAct μ ρ (idem μ hKc hKo) u) = L u := by
  rw [dual_heckeAct μ (idem μ hKc hKo).mem hu,
    integral_idem_mul hKc hKo (F := fun g => L (ρ g u)) (fun k hk => by simp [hL k hk])]
  simp

theorem abstract_form {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (B : V →ₗ[ℂ] H)
    (hinv : ∀ x u w, inner ℂ (B (ρ x u)) (B (ρ x w)) = inner ℂ (B u) (B w))
    (ξ : V) (N : ℂ) (hN : inner ℂ (B ξ) (B ξ) = N) (hN0 : N ≠ 0) :
    ∃ ℓ : Module.Dual ℂ V,
      (∀ K' : Subgroup G, ξ ∈ fixedVectors ρ K' → ℓ ∈ fixedVectors (Representation.dual ρ) K') ∧
      ℓ ξ = 1 ∧ ∀ u, ℓ u * N = inner ℂ (B ξ) (B u) := by
  let L : Module.Dual ℂ V := (innerₛₗ ℂ (B ξ)).comp B
  have hLa : ∀ u, L u = inner ℂ (B ξ) (B u) := fun u => rfl
  refine ⟨N⁻¹ • L, ?_, ?_, ?_⟩
  · intro K' hξ k hk
    refine LinearMap.ext fun u => ?_
    change N⁻¹ * L (ρ k⁻¹ u) = N⁻¹ * L u
    have hLK : L (ρ k⁻¹ u) = L u := by
      rw [hLa, hLa, ← hinv k⁻¹ ξ u, hξ _ (K'.inv_mem hk)]
    rw [hLK]
  · change N⁻¹ * L ξ = 1
    rw [hLa, hN, inv_mul_cancel₀ hN0]
  · intro u
    change N⁻¹ * L u * N = _
    rw [hLa, mul_comm N⁻¹, mul_assoc, inv_mul_cancel₀ hN0, mul_one]

include μ hKc hKo in

theorem schur_form {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (B : V →ₗ[ℂ] H)
    (hB : ∀ u, B u = 0 → u = 0)
    (hinv : ∀ x u w, inner ℂ (B (ρ x u)) (B (ρ x w)) = inner ℂ (B u) (B w))
    (R : H →ₗ[ℂ] H) (hR : ∀ x u w, inner ℂ (B (ρ x w)) (R (B (ρ x u))) = inner ℂ (B w) (R (B u)))
    (hirr : ρ.IsIrreducible) (hsm : GroundTheory.Automorphic.IsSmooth ρ)
    (hfd : FiniteDimensional ℂ (fixedVectors ρ K)) (ξ : V) (hξ : ξ ∈ fixedVectors ρ K) (hξ0 : ξ ≠ 0) :
    ∃ c : ℂ, ∀ x, inner ℂ (B ξ) (R (B (ρ x ξ))) = c * inner ℂ (B ξ) (B (ρ x ξ)) := by
  classical
  let F := fixedVectors ρ K
  let U : Submodule ℂ H := F.map B
  haveI : FiniteDimensional ℂ U := Module.Finite.map F B
  haveI : CompleteSpace U := FiniteDimensional.complete ℂ U
  have hBmem : ∀ w ∈ F, B w ∈ U := fun w hw => Submodule.mem_map_of_mem hw
  haveI : Nontrivial U := ⟨⟨⟨B ξ, hBmem ξ hξ⟩, 0, fun h => hξ0 (hB ξ (congrArg Subtype.val h))⟩⟩
  let A : Module.End ℂ U := LinearMap.codRestrict U
    ((U.starProjection : H →L[ℂ] H).toLinearMap ∘ₗ R ∘ₗ U.subtype) (fun y => U.starProjection_apply_mem _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  have hAy := hy.apply_eq_smul
  obtain ⟨y₀, hy₀F, hy₀⟩ := y.2
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    apply hy.2
    apply Subtype.ext
    rw [← hy₀, map_zero]
    rfl
  have key₀ : ∀ w ∈ F, inner ℂ (B w) (R (B y₀)) = c * inner ℂ (B w) (B y₀) := by
    intro w hw
    have h1 : U.starProjection (B w) = B w := Submodule.starProjection_eq_self_iff.2 (hBmem w hw)
    have h2 : U.starProjection (R (B y₀)) = c • B y₀ := by
      rw [hy₀]
      exact congrArg Subtype.val hAy
    calc inner ℂ (B w) (R (B y₀)) = inner ℂ (U.starProjection (B w)) (R (B y₀)) := by rw [h1]
      _ = inner ℂ (B w) (U.starProjection (R (B y₀))) := U.inner_starProjection_left_eq_right _ _
      _ = _ := by rw [h2, inner_smul_right]
  have he_mem : ∀ w', heckeAct μ ρ (idem μ hKc hKo) w' ∈ F := fun w' =>
    heckeAct_idem_mem hKc hKo (hsm w')
  have h_e : ∀ z : H, (∀ k ∈ K, ∀ u, inner ℂ z (B (ρ k u)) = inner ℂ z (B u)) → ∀ w',
      inner ℂ (B (heckeAct μ ρ (idem μ hKc hKo) w')) z = inner ℂ (B w') z := by
    intro z hz w'
    have := dual_idem μ hKc hKo ((innerₛₗ ℂ z).comp B) (fun k hk u => hz k hk u) (hsm w')
    calc inner ℂ (B (heckeAct μ ρ (idem μ hKc hKo) w')) z
        = starRingEnd ℂ (inner ℂ z (B (heckeAct μ ρ (idem μ hKc hKo) w'))) := (inner_conj_symm _ _).symm
      _ = starRingEnd ℂ (inner ℂ z (B w')) := congrArg _ this
      _ = _ := inner_conj_symm _ _
  let Y : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {u | ∀ x, ∀ w ∈ F, inner ℂ (B w) (R (B (ρ x u))) = c * inner ℂ (B w) (B (ρ x u))}
          add_mem' := fun {a b} ha hb x w hw => by
            simp only [map_add, inner_add_right]
            rw [ha x w hw, hb x w hw]; ring
          zero_mem' := fun x w hw => by simp
          smul_mem' := fun c' a ha x w hw => by
            simp only [map_smul, inner_smul_right]
            rw [ha x w hw]; ring }
      apply_mem_toSubmodule := fun g u hu x w hw => by
        rw [← Module.End.mul_apply, ← map_mul]
        exact hu (x * g) w hw }
  have hy₀Y : y₀ ∈ Y.toSubmodule := by
    intro x w hw
    have a1 : inner ℂ (B w) (R (B (ρ x y₀))) = inner ℂ (B (ρ x⁻¹ w)) (R (B y₀)) := by
      have := hR x⁻¹ (ρ x y₀) w
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
      exact this.symm
    have a2 : inner ℂ (B w) (B (ρ x y₀)) = inner ℂ (B (ρ x⁻¹ w)) (B y₀) := by
      have := hinv x⁻¹ w (ρ x y₀)
      rw [← Module.End.mul_apply (ρ x⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
      exact this.symm
    have c1 : ∀ k ∈ K, ∀ u, inner ℂ (R (B y₀)) (B (ρ k u)) = inner ℂ (R (B y₀)) (B u) := by
      intro k hk u
      have := hR k y₀ u
      rw [hy₀F k hk] at this
      rw [← inner_conj_symm (R (B y₀)) (B (ρ k u)), this, inner_conj_symm]
    have c2 : ∀ k ∈ K, ∀ u, inner ℂ (B y₀) (B (ρ k u)) = inner ℂ (B y₀) (B u) := by
      intro k hk u
      have := hinv k u y₀
      rw [hy₀F k hk] at this
      rw [← inner_conj_symm (B y₀) (B (ρ k u)), this, inner_conj_symm]
    rw [a1, a2, ← h_e _ c1, key₀ _ (he_mem _), h_e _ c2]
  rcases (show IsSimpleOrder (Subrepresentation ρ) from hirr).eq_bot_or_eq_top Y with h | h
  · exfalso
    rw [h] at hy₀Y
    exact hy0 ((Submodule.mem_bot ℂ).1 hy₀Y)
  · have hξY : ξ ∈ Y.toSubmodule := by rw [h]; trivial
    exact ⟨c, fun x => hξY x ξ hξ⟩

end Abstract

section Coeff

open AutomorphicForm CuspidalSpectrum RightCosetSpace

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem toOne_mul (g h : AdelicGLn.AdelicGL K n) : toOne (g * h) = toOne g * toOne h := by
  apply Subtype.ext
  show ((toOne (g * h) : Reduction.normOneGL K n) : AdelicGLn.AdelicGL K n) =
    (toOne g : AdelicGLn.AdelicGL K n) * (toOne h : AdelicGLn.AdelicGL K n)
  rw [coe_toOne, coe_toOne, coe_toOne, map_mul, map_mul, mul_inv_rev]
  have hc : ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      (Reduction.centralSection K n s)⁻¹ * x = x * (Reduction.centralSection K n s)⁻¹ := fun s x => by
    rw [← map_inv]; exact Reduction.centralSection_mul_comm _ x
  generalize ha : Reduction.centralSection K n (Reduction.detModule K n g) = a at *
  generalize hb : Reduction.centralSection K n (Reduction.detModule K n h) = b at *
  have h1 : a⁻¹ * h = h * a⁻¹ := by rw [← ha]; exact hc _ h
  have h2 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by rw [← ha]; exact hc _ b⁻¹
  calc g * h * (b⁻¹ * a⁻¹) = g * (h * a⁻¹) * b⁻¹ := by rw [← h2]; simp only [mul_assoc]
    _ = g * (a⁻¹ * h) * b⁻¹ := by rw [h1]
    _ = g * a⁻¹ * (h * b⁻¹) := by simp only [mul_assoc]

theorem toOne_one : toOne (1 : AdelicGLn.AdelicGL K n) = 1 :=
  Subtype.ext (by rw [coe_toOne, map_one, map_one, inv_one, mul_one]; rfl)

variable (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]

theorem T_mul (a b : AdelicGLn.AdelicGL K n) (v : cuspidalL2 μ) :
    cuspRep μ (toOne (a * b)) v = cuspRep μ (toOne a) (cuspRep μ (toOne b) v) :=
  (congrArg (fun t => cuspRep μ t v) (toOne_mul a b)).trans (UnitaryRep.map_mul_apply _ _ _ _)

theorem T_one (v : cuspidalL2 μ) : cuspRep μ (toOne (1 : AdelicGLn.AdelicGL K n)) v = v :=
  (congrArg (fun t => cuspRep μ t v) toOne_one).trans (UnitaryRep.map_one_apply _ _)

theorem inner_ae {α : Type*} [MeasurableSpace α] {m : Measure α} (a b : Lp ℂ 2 m) (A B' : α → ℂ)
    (ha : a =ᵐ[m] A) (hb : b =ᵐ[m] B') :
    ∫ q, inner ℂ (a q) (b q) ∂m = ∫ q, starRingEnd ℂ (A q) * B' q ∂m := by
  refine integral_congr_ae ?_
  filter_upwards [ha, hb] with q h1 h2
  rw [h1, h2, RCLike.inner_apply']

theorem matrixCoeff_eq_inner {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n)
    (g : AdelicGLn.AdelicGL K n) :
    GJGlobal.matrixCoeff μ (φ : AdelicGLn.AdelicGL K n → ℂ) φ g =
      inner ℂ (cuspToL2 μ φ) (cuspRep μ (toOne g) (cuspToL2 μ φ)) := by
  have hmp := measurePreserving_rightMul (Γ := Reduction.rationalGLOne K n) μ (toOne g)
  have hq : ((cuspRep μ (toOne g) (cuspToL2 μ φ) : cuspidalL2 μ) :
        Lp ℂ 2 (quotientMeasure (Reduction.rationalGLOne K n) μ)) =ᵐ[quotientMeasure (Reduction.rationalGLOne K n) μ]
      fun q => cuspQuot φ.2.1.isLeftInvariant (rightMul (Reduction.rationalGLOne K n) (toOne g) q) := by
    rw [coe_cuspRep_apply]
    exact (coeFn_rightTranslate _ _ _ _).trans
      (hmp.quasiMeasurePreserving.ae_eq (coeFn_cuspToL2 μ φ))
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  refine Eq.trans ?_ (inner_ae _ _ _ _ (coeFn_cuspToL2 μ φ) hq).symm
  have hc : Continuous (cuspQuot φ.2.1.isLeftInvariant) := continuous_cuspQuot _ φ.2.1.continuous
  have h1 : AEStronglyMeasurable (cuspQuot φ.2.1.isLeftInvariant)
      (quotientMeasure (Reduction.rationalGLOne K n) μ) := hc.aestronglyMeasurable
  rw [quotientMeasure, integral_map (measurable_mk _).aemeasurable]
  · unfold GJGlobal.matrixCoeff
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [rightMul_mk, cuspQuot_mk]
    rw [mul_comm]
    congr 1
    exact (apply_mul_toOne hφ _ g).symm
  · exact (continuous_star.comp hc).aestronglyMeasurable.mul (h1.comp_measurePreserving hmp)

end Coeff

section Places

open AutomorphicForm AdelicGLn GLnLocal

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

open Classical in
theorem fre_pi (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin n) (v.adicCompletion K))
    (w : HeightOneSpectrum (𝓞 K)) :
    finiteRestrictedEquiv K n (localEmbedding v x) w =
      Pi.mulSingle (M := fun u : HeightOneSpectrum (𝓞 K) => GL (Fin n) (u.adicCompletion K)) v x w := by
  change finiteRestrictedEquiv K n ((finiteRestrictedEquiv K n).symm _) w = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

open Classical in
theorem fre_self (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin n) (v.adicCompletion K)) :
    finiteRestrictedEquiv K n (localEmbedding v x) v = x := by
  rw [fre_pi, Pi.mulSingle_eq_same]

open Classical in
theorem fre_ne (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin n) (v.adicCompletion K))
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    finiteRestrictedEquiv K n (localEmbedding v x) w = 1 := by
  rw [fre_pi, Pi.mulSingle_eq_of_ne hw]

theorem finComp_finEmb (y : FiniteAdelicGL K n) : GJStandardL.finComp K n (finEmb K n y) = y :=
  congrArg Prod.snd (prodEquiv_finEmb y)

theorem archComp_finEmb (y : FiniteAdelicGL K n) : GJStandardL.archComp K n (finEmb K n y) = 1 :=
  congrArg Prod.fst (prodEquiv_finEmb y)

abbrev Ev (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin n) (v.adicCompletion K)) : AdelicGL K n :=
  finEmb K n (localEmbedding v x)

theorem localComp_Ev_self (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin n) (v.adicCompletion K)) :
    GJStandardL.localComp n v (Ev v x) = x := by
  show finiteRestrictedEquiv K n (GJStandardL.finComp K n (finEmb K n (localEmbedding v x))) v = x
  rw [finComp_finEmb, fre_self]

theorem localComp_Ev_ne (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin n) (v.adicCompletion K))
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    GJStandardL.localComp n w (Ev v x) = 1 := by
  show finiteRestrictedEquiv K n (GJStandardL.finComp K n (finEmb K n (localEmbedding v x))) w = 1
  rw [finComp_finEmb, fre_ne v x hw]

theorem comm_of_local_one (v : HeightOneSpectrum (𝓞 K)) {h : AdelicGL K n}
    (hv : GJStandardL.localComp n v h = 1) (z : GL (Fin n) (v.adicCompletion K)) :
    h * Ev v z = Ev v z * h := by
  apply (prodEquiv K n).injective
  rw [map_mul, map_mul, prodEquiv_finEmb]
  refine Prod.ext (by simp) ?_
  show (prodEquiv K n h).2 * localEmbedding v z = localEmbedding v z * (prodEquiv K n h).2
  apply (finiteRestrictedEquiv K n).injective
  ext w : 1
  simp only [map_mul, RestrictedProduct.mul_apply]
  by_cases hw : w = v
  · subst hw
    have h1 : finiteRestrictedEquiv K n (prodEquiv K n h).2 w = 1 := hv
    rw [h1, one_mul, mul_one]
  · rw [fre_ne v z hw, one_mul, mul_one]

end Places

section Pure

open AutomorphicForm AdelicGLn RestrictedTensor PiTensorProduct
open scoped TensorProduct Classical

variable {K : Type} [Field K] [NumberField K] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {Mx : AdelicGKModule K n V} (D : AdelicDecomposition Mx)
  (a : D.toDecomposition.W₁) (x : ∀ v, D.finite.W v) (hx : IsRestricted D.finite.ξ x)

def rmap (v : HeightOneSpectrum (𝓞 K)) : D.finite.W v →ₗ[ℂ] restrictedTensor D.finite.ξ :=
  LinearMap.codRestrict _ ((PiTensorProduct.tprod ℂ).toLinearMap x v)
    (fun y => tprod_mem_restrictedTensor (IsRestricted.update hx v y))

theorem coe_rmap (v : HeightOneSpectrum (𝓞 K)) (y : D.finite.W v) :
    ((rmap D x hx v y : restrictedTensor D.finite.ξ) : ⨂[ℂ] w, D.finite.W w) =
      PiTensorProduct.tprod ℂ (Function.update x v y) := rfl

abbrev EE : V ≃ₗ[ℂ] D.toDecomposition.W₁ ⊗[ℂ] D.toDecomposition.W₂ := D.toDecomposition.equiv.toLinearEquiv

abbrev E2 : D.toDecomposition.W₂ ≃ₗ[ℂ] restrictedTensor D.finite.ξ := D.finite.equiv.toLinearEquiv

theorem EE_tau (g : FiniteAdelicGL K n) (u : V) :
    EE D (Mx.τ g u) = TensorProduct.map LinearMap.id (D.toDecomposition.π₂ g) (EE D u) := by
  have h := Representation.IntertwiningMap.isIntertwining _ _ D.toDecomposition.equiv.toIntertwiningMap
    ((1 : FreeMonoid _), g) u
  have e1 : Mx.fullRep ((1 : FreeMonoid _), g) u = Mx.τ g u := by
    show Mx.gk.rep 1 (Mx.τ g u) = _
    rw [map_one, Module.End.one_apply]
  have e2 : outerTensor D.toDecomposition.π₁.rep D.toDecomposition.π₂ ((1 : FreeMonoid _), g) =
      TensorProduct.map LinearMap.id (D.toDecomposition.π₂ g) := by
    show TensorProduct.map (D.toDecomposition.π₁.rep 1) (D.toDecomposition.π₂ g) = _
    rw [map_one]
    rfl
  rw [← e1]
  exact h.trans (by rw [e2]; rfl)

theorem E2_intertwining (g : FiniteAdelicGL K n) (y : D.toDecomposition.W₂) :
    E2 D (D.toDecomposition.π₂ g y) =
      adelicTensorRep D.finite.π D.finite.ξ D.finite.mem_fixedVectors g (E2 D y) :=
  Representation.IntertwiningMap.isIntertwining _ _ D.finite.equiv.toIntertwiningMap g y

def Iv (v : HeightOneSpectrum (𝓞 K)) : D.finite.W v →ₗ[ℂ] V :=
  (EE D).symm.toLinearMap ∘ₗ (TensorProduct.mk ℂ _ _ a) ∘ₗ (E2 D).symm.toLinearMap ∘ₗ rmap D x hx v

theorem Iv_apply (v : HeightOneSpectrum (𝓞 K)) (y : D.finite.W v) :
    Iv D a x hx v y = (EE D).symm (a ⊗ₜ (E2 D).symm (rmap D x hx v y)) := rfl

theorem rmap_int (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (v.adicCompletion K)) (y : D.finite.W v) :
    rmap D x hx v (D.finite.π v g y) =
      adelicTensorRep D.finite.π D.finite.ξ D.finite.mem_fixedVectors (localEmbedding v g) (rmap D x hx v y) := by
  apply Subtype.ext
  show PiTensorProduct.tprod ℂ (Function.update x v (D.finite.π v g y)) =
    tensorRep _ D.finite.π (toRestricted K n (localEmbedding v g)) (PiTensorProduct.tprod ℂ (Function.update x v y))
  rw [tensorRep_tprod]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    rw [Function.update_self, Function.update_self]
    exact congrArg (fun b => D.finite.π _ b y) (fre_self w g).symm
  · rw [Function.update_of_ne hw, Function.update_of_ne hw]
    have e : (toRestricted K n (localEmbedding v g)) w = 1 := fre_ne v g hw
    rw [e, map_one]
    rfl

theorem Iv_int (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (v.adicCompletion K)) (y : D.finite.W v) :
    Iv D a x hx v (D.finite.π v g y) = Mx.τ (localEmbedding v g) (Iv D a x hx v y) := by
  apply (EE D).injective
  rw [EE_tau, Iv_apply, Iv_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  congr 1
  apply (E2 D).injective
  rw [E2_intertwining, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact rmap_int D x hx v g y

def phi : V := (EE D).symm (a ⊗ₜ (E2 D).symm ⟨PiTensorProduct.tprod ℂ x, tprod_mem_restrictedTensor hx⟩)

theorem Iv_self (v : HeightOneSpectrum (𝓞 K)) : Iv D a x hx v (x v) = phi D a x hx := by
  rw [Iv_apply, phi]
  congr 3
  apply Subtype.ext
  rw [coe_rmap, Function.update_eq_self]

theorem phi_ne (ha : a ≠ 0) (hx0 : ∀ v, x v ≠ 0) : phi D a x hx ≠ 0 := by
  have hl1 : ∀ v, ∃ l : Module.Dual ℂ (D.finite.W v), l (x v) = 1 := by
    intro v
    by_contra hcon
    push Not at hcon
    apply hx0 v
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
    by_contra hf
    apply hcon ((f (x v))⁻¹ • f)
    simp [hf]
  choose l hl using hl1
  have hl' : ∀ᶠ v in cofinite, l v (D.finite.ξ v) = 1 := by
    filter_upwards [hx] with v h
    rw [← h]
    exact hl v
  have ht : evalForm D.finite.ξ l hl' (PiTensorProduct.tprod ℂ x) = 1 := by
    rw [evalForm_tprod hx]
    simp [hl]
  have hb : (E2 D).symm ⟨PiTensorProduct.tprod ℂ x, tprod_mem_restrictedTensor hx⟩ ≠ 0 := by
    intro h
    have h0 := (E2 D).symm.map_eq_zero_iff.1 h
    have h1 : PiTensorProduct.tprod ℂ x = 0 := congrArg Subtype.val h0
    rw [h1, map_zero] at ht
    exact zero_ne_one ht
  obtain ⟨a', ha'⟩ : ∃ a' : Module.Dual ℂ D.toDecomposition.W₁, a' a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
  intro h
  have h0 := (EE D).symm.map_eq_zero_iff.1 h
  have h2 := congrArg (fun s => TensorProduct.lid ℂ _ (LinearMap.rTensor _ a' s)) h0
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h2
  exact hb ((smul_eq_zero.1 h2).resolve_left ha')

theorem tau_phi {u : FiniteAdelicGL K n}
    (hu : ∀ v, D.finite.π v (finiteRestrictedEquiv K n u v) (x v) = x v) :
    Mx.τ u (phi D a x hx) = phi D a x hx := by
  apply (EE D).injective
  rw [EE_tau, phi, LinearEquiv.apply_symm_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  congr 1
  apply (E2 D).injective
  rw [E2_intertwining, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  show tensorRep _ D.finite.π (toRestricted K n u) (PiTensorProduct.tprod ℂ x) = _
  rw [tensorRep_tprod]
  congr 1
  funext v
  exact hu v

end Pure

section Cusp

open AutomorphicForm CuspidalSpectrum AdelicGLn GLnLocal RestrictedTensor
open scoped TensorProduct Classical

theorem hR_gen {A H : Type*} [Group A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : A → H → H)
    (hTmul : ∀ a b v, T (a * b) v = T a (T b v)) (hTi : ∀ a v w, inner ℂ (T a v) (T a w) = inner ℂ v w)
    (e g : A) (hc : g * e = e * g) (p q : H) : inner ℂ (T e p) (T g (T e q)) = inner ℂ p (T g q) := by
  rw [← hTmul, hc, hTmul]
  exact hTi _ _ _

variable {K : Type} [Field K] [NumberField K] {n : ℕ}
  (P : CuspidalAutomorphicRepresentation K n) (D : AdelicDecomposition P.toModule)
  (a : D.toDecomposition.W₁) (x : ∀ v, D.finite.W v) (hx : IsRestricted D.finite.ξ x)
  (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]

def Phi0 : cuspForms K n := ((phi D a x hx : P.carrier) : cuspForms K n)

abbrev Pf : AdelicGL K n → ℂ := (Phi0 P D a x hx : cuspForms K n)

theorem central0 : Phi0 P D a x hx ∈ centralCuspForms K n := P.le_central (phi D a x hx).2

def Bv (v : HeightOneSpectrum (𝓞 K)) : D.finite.W v →ₗ[ℂ] cuspidalL2 μ :=
  (cuspToL2 μ) ∘ₗ P.carrier.subtype ∘ₗ Iv D a x hx v

theorem Bv_int (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (v.adicCompletion K)) (y : D.finite.W v) :
    Bv P D a x hx μ v (D.finite.π v g y) = cuspRep μ (toOne (Ev v g)) (Bv P D a x hx μ v y) :=
  cuspFormLp_rightTranslate_eq_rep μ (P.le_central (Iv D a x hx v y).2) (Ev v g)
    (ψ := ((Iv D a x hx v (D.finite.π v g y) : P.carrier) : cuspForms K n)) (by rw [Iv_int]; rfl)

theorem Bv_inv (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (v.adicCompletion K)) (u w : D.finite.W v) :
    inner ℂ (Bv P D a x hx μ v (D.finite.π v g u)) (Bv P D a x hx μ v (D.finite.π v g w)) =
      inner ℂ (Bv P D a x hx μ v u) (Bv P D a x hx μ v w) :=
  (congrArg₂ (inner ℂ) (Bv_int P D a x hx μ v g u) (Bv_int P D a x hx μ v g w)).trans
    (UnitaryRep.inner_map_map (cuspRep μ) _ _ _)

theorem Bv_self (v : HeightOneSpectrum (𝓞 K)) :
    Bv P D a x hx μ v (x v) = cuspToL2 μ (Phi0 P D a x hx) :=
  congrArg (fun t : P.carrier => cuspToL2 μ (t : cuspForms K n)) (Iv_self D a x hx v)

theorem Bv_zero (ha : a ≠ 0) (hx0 : ∀ v, x v ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (u : D.finite.W v)
    (h : Bv P D a x hx μ v u = 0) : u = 0 := by
  have hI : Iv D a x hx v u = 0 := by
    have h' : cuspToL2 μ ((Iv D a x hx v u : P.carrier) : cuspForms K n) = 0 := h
    have h0 : ((Iv D a x hx v u : P.carrier) : cuspForms K n) = 0 :=
      injOn_cuspToL2 μ (P.le_central (Iv D a x hx v u).2 : _) (fun _ _ => rfl)
        (h'.trans (map_zero (cuspToL2 μ)).symm)
    exact Subtype.ext h0
  let Y : Subrepresentation (D.finite.π v) :=
    { toSubmodule := LinearMap.ker (Iv D a x hx v)
      apply_mem_toSubmodule := fun g u hu => by
        show Iv D a x hx v (D.finite.π v g u) = 0
        rw [Iv_int, LinearMap.mem_ker.1 hu, map_zero] }
  rcases (show IsSimpleOrder (Subrepresentation (D.finite.π v)) from D.finite.isIrreducible v).eq_bot_or_eq_top Y
    with h1 | h1
  · have hm : u ∈ Y.toSubmodule := hI
    rw [h1] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · exfalso
    have hm : x v ∈ Y.toSubmodule := by rw [h1]; trivial
    have h2 : Iv D a x hx v (x v) = 0 := hm
    rw [Iv_self] at h2
    exact phi_ne D a x hx ha hx0 h2

abbrev Fc (g : AdelicGL K n) : ℂ := GJGlobal.matrixCoeff μ (Pf P D a x hx) (Pf P D a x hx) g

theorem Fc_eq (g : AdelicGL K n) : Fc P D a x hx μ g =
    inner ℂ (cuspToL2 μ (Phi0 P D a x hx)) (cuspRep μ (toOne g) (cuspToL2 μ (Phi0 P D a x hx))) :=
  matrixCoeff_eq_inner μ (central0 P D a x hx) g

theorem Fc_one : Fc P D a x hx μ 1 =
    inner ℂ (cuspToL2 μ (Phi0 P D a x hx)) (cuspToL2 μ (Phi0 P D a x hx)) :=
  (Fc_eq P D a x hx μ 1).trans (congrArg (inner ℂ (cuspToL2 μ (Phi0 P D a x hx))) (T_one μ _))

theorem Fc_Ev (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (v.adicCompletion K)) :
    Fc P D a x hx μ (Ev v y) = inner ℂ (Bv P D a x hx μ v (x v)) (Bv P D a x hx μ v (D.finite.π v y (x v))) := by
  have h : Bv P D a x hx μ v (D.finite.π v y (x v)) =
      cuspRep μ (toOne (Ev v y)) (cuspToL2 μ (Phi0 P D a x hx)) :=
    (Bv_int P D a x hx μ v y (x v)).trans (congrArg (cuspRep μ (toOne (Ev v y))) (Bv_self P D a x hx μ v))
  exact (Fc_eq P D a x hx μ _).trans (congrArg₂ (inner ℂ) (Bv_self P D a x hx μ v).symm h.symm)

theorem Fc_mult (ha : a ≠ 0) (hx0 : ∀ v, x v ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (y : GL (Fin n) (v.adicCompletion K)) (g' : AdelicGL K n) (hcomm : ∀ z, g' * Ev v z = Ev v z * g') :
    Fc P D a x hx μ (g' * Ev v y) * Fc P D a x hx μ 1 =
      Fc P D a x hx μ g' * Fc P D a x hx μ (Ev v y) := by
  obtain ⟨K', hKc, hKo, hKx⟩ := (mem_smoothVectors_iff _).1
    (show x v ∈ smoothVectors (D.finite.π v) from (D.finite.isAdmissible v).1 (x v))
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (GL (Fin n) (v.adicCompletion K)), ν.IsHaarMeasure :=
    ⟨Measure.haar, inferInstance⟩
  let R : cuspidalL2 μ →ₗ[ℂ] cuspidalL2 μ :=
    ((cuspRep μ (toOne g') : cuspidalL2 μ →L[ℂ] cuspidalL2 μ) : cuspidalL2 μ →ₗ[ℂ] cuspidalL2 μ)
  have hR : ∀ y' u w, inner ℂ (Bv P D a x hx μ v (D.finite.π v y' w))
      (R (Bv P D a x hx μ v (D.finite.π v y' u))) =
      inner ℂ (Bv P D a x hx μ v w) (R (Bv P D a x hx μ v u)) := by
    intro y' u w
    have h := hR_gen (fun (b : AdelicGL K n) (t : cuspidalL2 μ) => cuspRep μ (toOne b) t) (T_mul μ)
      (fun b t s => UnitaryRep.inner_map_map (cuspRep μ) _ _ _) (Ev v y') g' (hcomm y')
      (Bv P D a x hx μ v w) (Bv P D a x hx μ v u)
    exact (congrArg₂ (fun p q => inner ℂ p (cuspRep μ (toOne g') q)) (Bv_int P D a x hx μ v y' w)
      (Bv_int P D a x hx μ v y' u)).trans h
  obtain ⟨c, hc⟩ := schur_form ν hKc hKo (Bv P D a x hx μ v) (Bv_zero P D a x hx μ ha hx0 v)
    (Bv_inv P D a x hx μ v) R hR (D.finite.isIrreducible v) (D.finite.isAdmissible v).1
    ((D.finite.isAdmissible v).2 K' hKc hKo) (x v) hKx (hx0 v)
  have e1 : ∀ y', Fc P D a x hx μ (g' * Ev v y') = inner ℂ (Bv P D a x hx μ v (x v))
      (R (Bv P D a x hx μ v (D.finite.π v y' (x v)))) := by
    intro y'
    have h1 := Fc_eq P D a x hx μ (g' * Ev v y')
    have h2 : cuspRep μ (toOne (g' * Ev v y')) (cuspToL2 μ (Phi0 P D a x hx)) =
        R (Bv P D a x hx μ v (D.finite.π v y' (x v))) := by
      refine (T_mul μ g' (Ev v y') _).trans ?_
      refine congrArg (cuspRep μ (toOne g')) ?_
      exact ((Bv_int P D a x hx μ v y' (x v)).trans
        (congrArg (cuspRep μ (toOne (Ev v y'))) (Bv_self P D a x hx μ v))).symm
    exact h1.trans (congrArg₂ (inner ℂ) (Bv_self P D a x hx μ v).symm h2)
  have hEv1 : Ev v (1 : GL (Fin n) (v.adicCompletion K)) = 1 := by simp [Ev]
  have h1 : Fc P D a x hx μ (g' * Ev v y) = c * Fc P D a x hx μ (Ev v y) :=
    (e1 y).trans ((hc y).trans (congrArg (c * ·) (Fc_Ev P D a x hx μ v y).symm))
  have h2 : Fc P D a x hx μ (g' * Ev v 1) = c * Fc P D a x hx μ (Ev v 1) :=
    (e1 1).trans ((hc 1).trans (congrArg (c * ·) (Fc_Ev P D a x hx μ v 1).symm))
  rw [hEv1, mul_one] at h2
  rw [h1, h2]
  ring

theorem Fc_right (g : AdelicGL K n) {u : FiniteAdelicGL K n}
    (hu : ∀ v, D.finite.π v (finiteRestrictedEquiv K n u v) (x v) = x v) :
    Fc P D a x hx μ (g * finEmb K n u) = Fc P D a x hx μ g := by
  unfold Fc GJGlobal.matrixCoeff
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have e := tau_phi D a x hx hu
  have e2 : Pf P D a x hx ((t : AdelicGL K n) * (g * finEmb K n u)) = Pf P D a x hx ((t : AdelicGL K n) * g) := by
    have h := congrArg (fun s : P.carrier => ((s : cuspForms K n) : AdelicGL K n → ℂ) ((t : AdelicGL K n) * g)) e
    rw [← mul_assoc]
    exact h
  simp only
  rw [e2]

theorem coeff_factor (ω : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin n) (v.adicCompletion K) → ℂ)
    (hω : ∀ v y, ω v y * Fc P D a x hx μ 1 = Fc P D a x hx μ (Ev v y)) (ha : a ≠ 0) (hx0 : ∀ v, x v ≠ 0)
    (hF1 : Fc P D a x hx μ 1 ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ g : AdelicGL K n, (∀ v ∉ T, D.finite.π v (GJStandardL.localComp n v g) (x v) = x v) →
      Fc P D a x hx μ g = Fc P D a x hx μ ((prodEquiv K n).symm (GJStandardL.archComp K n g, 1)) *
        ∏ v ∈ T, ω v (GJStandardL.localComp n v g) := by
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    rw [Finset.prod_empty, mul_one]
    have e : g = (prodEquiv K n).symm (GJStandardL.archComp K n g, 1) * finEmb K n (GJStandardL.finComp K n g) := by
      apply (prodEquiv K n).injective
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply, prodEquiv_finEmb]
      exact Prod.ext (mul_one _).symm (one_mul _).symm
    conv_lhs => rw [e]
    exact Fc_right P D a x hx μ _ fun w => hg w (by simp)
  | insert v T hv ih =>
    intro g hg
    set y := GJStandardL.localComp n v g with hy
    set g' := g * (Ev v y)⁻¹ with hg'
    have hlv : GJStandardL.localComp n v g' = 1 := by
      rw [hg', map_mul, map_inv, localComp_Ev_self, ← hy, mul_inv_cancel]
    have hlw : ∀ w, w ≠ v → GJStandardL.localComp n w g' = GJStandardL.localComp n w g := by
      intro w hw
      rw [hg', map_mul, map_inv, localComp_Ev_ne v y hw, inv_one, mul_one]
    have harch : GJStandardL.archComp K n g' = GJStandardL.archComp K n g := by
      rw [hg', map_mul, map_inv, archComp_finEmb, inv_one, mul_one]
    have hgg : g' * Ev v y = g := by rw [hg', inv_mul_cancel_right]
    have hm := Fc_mult P D a x hx μ ha hx0 v y g' (comm_of_local_one v hlv)
    rw [hgg, ← hω v y] at hm
    have h1 : Fc P D a x hx μ g = Fc P D a x hx μ g' * ω v y :=
      mul_right_cancel₀ hF1 (by rw [hm]; ring)
    have hih := ih g' (fun w hw => by
      by_cases hwv : w = v
      · subst hwv; rw [hlv, map_one]; rfl
      · rw [hlw w hwv]; exact hg w (by simp [hwv, hw]))
    rw [Finset.prod_insert hv, ← hy, h1, hih, harch]
    have hprod : ∏ w ∈ T, ω w (GJStandardL.localComp n w g') = ∏ w ∈ T, ω w (GJStandardL.localComp n w g) :=
      Finset.prod_congr rfl fun w hw => by rw [hlw w (fun h => hv (h ▸ hw))]
    rw [hprod]
    ring

end Cusp

section Conclusion

open GodementJacquet GLnLocal GJStandardL NumberField.mixedEmbedding
open scoped SchwartzMap Classical

def PartialLFunctionalEquation {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 K)))
    {V : HeightOneSpectrum (𝓞 K) → Type} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ) : Prop :=
    ∃ σ : ℝ, ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∃ (φ φ' : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
        (Φ Φ' : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ) (c c' : ℂ),
        c ≠ 0 ∧ c' ≠ 0 ∧ φ' = archMatrixFourier φ ∧
        (∃ C : ℂ, C ≠ 0 ∧
          (∀ (φ₀ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
            (Φ₀ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ),
            (∀ v ∈ S₀, IsSchwartzBruhat (Φ₀ v)) →
            (∀ v ∉ S₀, Φ₀ v = integralIndicator (v.adicCompletion K) n) →
            GJMatrix.adelicMatrixFourier K (GJStandardL.matrixTensor φ₀ Φ₀) = C • GJStandardL.matrixTensor (archMatrixFourier φ₀)
              (fun v ↦ GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ₀ v))) ∧
          c = C ^ 3 * c') ∧
        (∀ v ∈ S, IsSchwartzBruhat (Φ v) ∧
          Φ' v = GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v)) ∧
        (∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n ∧
          Φ' v = integralIndicator (v.adicCompletion K) n) ∧
        (∀ v ∈ S, RatFE (v.adicCompletion K)
          (gammaFactor (v.adicCompletion K) (π v) (GroundTheory.Global.localAdelicChar K v))
          (zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)))
          (fun s ↦ zetaIntegral (localHaar n v) (Φ' v)
            (fun g ↦ Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g⁻¹) (1 - s))) ∧
        Differentiable ℂ (archZeta Measure.haar φ' (fun x ↦ fi x⁻¹)) ∧
        (∃ s, archZeta Measure.haar φ' (fun x ↦ fi x⁻¹) s ≠ 0) ∧
        (∀ v ∈ S, ∃ a : ℂ, a ≠ 0 ∧ ∃ g₀ : GL (Fin n) (v.adicCompletion K), ∀ s : ℂ,
          zetaIntegral (localHaar n v) (Φ' v)
            (fun g ↦ Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g⁻¹) s =
            a * detPow g₀ (s + ((n : ℂ) - 1) / 2)) ∧
        ∀ s : ℂ, σ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
            LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) s) (partialL S π s) ∧
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
            LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (contragredient (π v)) s)
            (dualPartialL S π s) ∧
          partialL S π s ≠ 0 ∧ dualPartialL S π s ≠ 0 ∧
          Λ s = c * archZeta Measure.haar φ fi s *
            (∏ v ∈ S, zetaIntegral (localHaar n v) (Φ v)
              (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s) * partialL S π s ∧
          Λ (1 - s) = c' * archZeta Measure.haar φ' (fun x ↦ fi x⁻¹) s *
            (∏ v ∈ S, zetaIntegral (localHaar n v) (Φ' v)
              (fun g ↦ Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g⁻¹) s) *
            dualPartialL S π s

end Conclusion

section Final

open AutomorphicForm CuspidalSpectrum AdelicGLn GLnLocal RestrictedTensor
open scoped TensorProduct Classical

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_ne_zero_of_irr {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hirr : ρ.IsIrreducible) : ∃ u : V, u ≠ 0 := by
  by_contra h
  push Not at h
  have hs : IsSimpleOrder (Subrepresentation ρ) := hirr
  have e : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    show (⊥ : Submodule ℂ V) = ⊤
    exact eq_top_iff.2 fun y _ => (Submodule.mem_bot ℂ).2 (h y)
  exact bot_ne_top e

theorem exists_pureTensor (P : CuspidalAutomorphicRepresentation K n) (D : AdelicDecomposition P.toModule) :
    ∃ (a : D.toDecomposition.W₁) (x : ∀ v, D.finite.W v), IsRestricted D.finite.ξ x ∧ a ≠ 0 ∧ ∀ v, x v ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := P.exists_mem_ne_zero
  have ha : ∃ a : D.toDecomposition.W₁, a ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∀ s : D.toDecomposition.W₁ ⊗[ℂ] D.toDecomposition.W₂, s = 0 := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => rfl
      | tmul m b => rw [h m, TensorProduct.zero_tmul]
      | add p q hp hq => rw [hp, hq, add_zero]
    have h1 : (⟨φ, hφ⟩ : P.carrier) = 0 := (EE D).map_eq_zero_iff.1 (hz _)
    exact h0 (congrArg Subtype.val h1)
  obtain ⟨a, ha⟩ := ha
  choose w hw using fun v => exists_ne_zero_of_irr (D.finite.isIrreducible v)
  refine ⟨a, fun v => if D.finite.ξ v ≠ 0 then D.finite.ξ v else w v, ?_, ha, fun v => ?_⟩
  · show ∀ᶠ v in cofinite, _ = _
    filter_upwards [D.finite.ne_zero] with v h
    simp only [if_pos h]
  · by_cases h : D.finite.ξ v ≠ 0
    · simp only [if_pos h]; exact h
    · simp only [if_neg h]; exact hw v

section Sph

open scoped Classical

theorem exists_pureTensor_spherical (P : CuspidalAutomorphicRepresentation K n) (D : AdelicDecomposition P.toModule) :
    ∃ (a : D.toDecomposition.W₁) (x : ∀ v, D.finite.W v), IsRestricted D.finite.ξ x ∧ a ≠ 0 ∧ (∀ v, x v ≠ 0) ∧
      ∀ v, fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) ≠ ⊥ →
        x v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) := by
  obtain ⟨a, x₀, -, ha, hx0⟩ := exists_pureTensor P D
  have hw : ∀ v, ∃ w : D.finite.W v, w ≠ 0 ∧
      (fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) ≠ ⊥ →
        w ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n)) := by
    intro v
    by_cases h : fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) = ⊥
    · exact ⟨x₀ v, hx0 v, fun h' => absurd h h'⟩
    · obtain ⟨w, hw, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact ⟨w, h0, fun _ => hw⟩
  choose w hw0 hwf using hw
  refine ⟨a, fun v => if D.finite.ξ v ≠ 0 ∧
    D.finite.ξ v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) then D.finite.ξ v else w v,
    ?_, ha, fun v => ?_, fun v hv => ?_⟩
  · show ∀ᶠ v in cofinite, _ = _
    filter_upwards [D.finite.ne_zero, D.finite.mem_fixedVectors] with v h1 h2
    exact if_pos (And.intro h1 h2)
  · dsimp only
    split_ifs with h
    · exact h.1
    · exact hw0 v
  · dsimp only
    split_ifs with h
    · exact h.2
    · exact hwf v hv

theorem matrixCoeff_factorization_of_pureTensor (P : CuspidalAutomorphicRepresentation K n) (D : AdelicDecomposition P.toModule)
    (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure] (a : D.toDecomposition.W₁)
    (x : ∀ v, D.finite.W v) (hx : IsRestricted D.finite.ξ x) (ha : a ≠ 0) (hx0 : ∀ v, x v ≠ 0) :
    ∃ (ℓ : ∀ v, Module.Dual ℂ (D.finite.W v)) (fi : InfiniteAdelicGL K n → ℂ),
      (∀ v, ℓ v ∈ smoothVectors (Representation.dual (D.finite.π v))) ∧ (∀ v, ℓ v (x v) = 1) ∧
      (∀ v, x v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) →
        ℓ v ∈ fixedVectors (Representation.dual (D.finite.π v)) (integralGL (v.adicCompletion K) n)) ∧
      (∀ g, Fc P D a x hx μ g = fi (GJStandardL.archComp K n g) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v)
          (GJStandardL.localComp n v g)) ∧
      Fc P D a x hx μ 1 ≠ 0 := by
  have hφ0 : Phi0 P D a x hx ≠ 0 := fun h => phi_ne D a x hx ha hx0 (Subtype.ext h)
  have hF1 : Fc P D a x hx μ 1 ≠ 0 := fun h => hφ0 (eq_zero_of_petersson_inner_self_eq_zero μ
    (central0 P D a x hx) ((Fc_one P D a x hx μ).symm.trans h))
  have hl := fun v => abstract_form (Bv P D a x hx μ v) (Bv_inv P D a x hx μ v) (x v)
    (Fc P D a x hx μ 1)
    ((congrArg₂ (inner ℂ) (Bv_self P D a x hx μ v) (Bv_self P D a x hx μ v)).trans
      (Fc_one P D a x hx μ).symm) hF1
  choose ℓ hℓ hℓ1 hℓ2 using hl
  have hS : ∀ᶠ v in cofinite, x v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) := by
    filter_upwards [hx, D.finite.mem_fixedVectors] with v h1 h2
    rw [h1]
    exact h2
  refine ⟨ℓ, fun y => Fc P D a x hx μ ((prodEquiv K n).symm (y, 1)), fun v => ?_, hℓ1,
    fun v hv => hℓ v _ hv, fun g => ?_, hF1⟩
  · obtain ⟨K', -, hKo, hKx⟩ := (mem_smoothVectors_iff _).1
      (show x v ∈ smoothVectors (D.finite.π v) from (D.finite.isAdmissible v).1 (x v))
    exact smooth_of_mem_fixedVectors hKo (hℓ v K' hKx)
  · have hT : ∀ᶠ v in cofinite, D.finite.π v (GJStandardL.localComp n v g) (x v) = x v := by
      filter_upwards [hS, GJStandardL.eventually_localComp_mem g] with v h1 h2
      exact h1 _ h2
    have hT' := Filter.eventually_cofinite.1 hT
    have hfac := coeff_factor P D a x hx μ (fun v y => ℓ v (D.finite.π v y (x v)))
      (fun v y => (hℓ2 v _).trans (Fc_Ev P D a x hx μ v y).symm) ha hx0 hF1 hT'.toFinset g
      (fun v hv => by
        by_contra h
        exact hv (hT'.mem_toFinset.2 h))
    refine hfac.trans (congrArg _ ?_)
    refine (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
    intro v hv
    by_contra hvT
    apply hv
    have hk : D.finite.π v (GJStandardL.localComp n v g) (x v) = x v := by
      by_contra h
      exact hvT (hT'.mem_toFinset.2 h)
    show ℓ v (D.finite.π v (GJStandardL.localComp n v g) (x v)) = 1
    rw [hk, hℓ1 v]

end Sph

theorem matrixCoeff_factorization_cuspidal (P : CuspidalAutomorphicRepresentation K n)
    (D : AdelicDecomposition P.toModule) (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure] :
    ∃ (φ : cuspForms K n) (ξ : ∀ v, D.finite.W v) (ℓ : ∀ v, Module.Dual ℂ (D.finite.W v))
      (fi : InfiniteAdelicGL K n → ℂ) (S₀ : Finset (HeightOneSpectrum (𝓞 K))),
      φ ∈ P.carrier ∧ φ ≠ 0 ∧ (∀ v, ξ v ∈ smoothVectors (D.finite.π v)) ∧
      (∀ v, ℓ v ∈ smoothVectors (Representation.dual (D.finite.π v))) ∧
      (∀ v ∉ S₀, ξ v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1) ∧
      (∀ v ∉ S₀, ℓ v ∈ fixedVectors (Representation.dual (D.finite.π v)) (integralGL (v.adicCompletion K) n)) ∧
      (∀ g, GJGlobal.matrixCoeff μ (φ : AdelicGL K n → ℂ) φ g = fi (GJStandardL.archComp K n g) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (ξ v) (ℓ v)
          (GJStandardL.localComp n v g)) ∧
      ∃ g, GJGlobal.matrixCoeff μ (φ : AdelicGL K n → ℂ) φ g ≠ 0 := by
  obtain ⟨a, x, hx, ha, hx0⟩ := exists_pureTensor P D
  obtain ⟨ℓ, fi, hℓs, hℓ1, hℓK, hf, hF1⟩ := matrixCoeff_factorization_of_pureTensor P D μ a x hx ha hx0
  have hS : ∀ᶠ v in cofinite, x v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) := by
    filter_upwards [hx, D.finite.mem_fixedVectors] with v h1 h2
    rw [h1]
    exact h2
  have hfin := Filter.eventually_cofinite.1 hS
  have hnot : ∀ v ∉ hfin.toFinset, x v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) := by
    intro v hv
    by_contra h
    exact hv (hfin.mem_toFinset.2 h)
  exact ⟨Phi0 P D a x hx, x, ℓ, fi, hfin.toFinset, (phi D a x hx).2,
    fun h => phi_ne D a x hx ha hx0 (Subtype.ext h), fun v => (D.finite.isAdmissible v).1 (x v), hℓs,
    fun v hv => ⟨hnot v hv, hℓ1 v⟩, fun v hv => hℓK v (hnot v hv), hf, ⟨1, hF1⟩⟩

end Final

end

end GroundTheory.Automorphic.GJStandardLCuspidal
