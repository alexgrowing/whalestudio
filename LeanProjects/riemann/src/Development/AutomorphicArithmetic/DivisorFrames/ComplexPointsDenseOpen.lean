import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section
open TopologicalSpace GlobalTheory.CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct Topology GlobalTheory.AffinePoints

private theorem one_tmul_mem_nonZeroDivisors {k A : Type} [CommRing k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra k ℂ] [Module.Flat k ℂ] {f : A} (hf : f ≠ 0) :
    ((1 : ℂ) ⊗ₜ[k] f) ∈ nonZeroDivisors (ℂ ⊗[k] A) := by
  have hinj : Function.Injective (LinearMap.mulLeft k f) := mul_right_injective₀ hf
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) _ hinj
  have h3 (x : ℂ ⊗[k] A) : LinearMap.lTensor ℂ (LinearMap.mulLeft k f) x = ((1 : ℂ) ⊗ₜ[k] f) * x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => rw [map_add, hx, hy, mul_add]
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  apply h2
  rw [h3, hx, map_zero]

private theorem mem_closure_basicOpen {k : Type} [CommRing k] [Algebra k ℂ] [Module.Flat k ℂ]
    {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) [LocallyOfFiniteType p]
    {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)} (hf : f ≠ 0)
    (y : GlobalTheory.CxPts p (algebraMap k ℂ)) (hy : y ∈ ptsIn p (algebraMap k ℂ) U) :
    y ∈ closure (ptsIn p (algebraMap k ℂ) (X.basicOpen f)) := by
  let : Algebra k Γ(X, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType k Γ(X, U) := hft
  have : Nonempty U := ⟨⟨_, mem_ptsIn.1 hy⟩⟩
  have : IsDomain Γ(X, U) := inferInstance
  let ψ : Γ(X, U) →ₐ[k] ℂ :=
    { evHom hy with commutes' := fun a => (ev_eq hy _).symm.trans (ev_algX hy a) }
  let q₀ : ℂ ⊗[k] Γ(X, U) →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) ψ fun _ _ => Commute.all _ _
  have : (RingHom.ker q₀).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := RingHom.ker q₀) bot_le
  have : P.IsPrime := hP.1.1
  have hfP : ((1 : ℂ) ⊗ₜ[k] f) ∉ P := fun h =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h hP (one_tmul_mem_nonZeroDivisors hf)
  let φ (q : ((ℂ ⊗[k] Γ(X, U)) ⧸ P) →ₐ[ℂ] ℂ) : Γ(X, U) →+* ℂ :=
    (q.toRingHom.comp (Ideal.Quotient.mk P)).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := ℂ)).toRingHom
  have hφa (q) (a) : φ q a = q (Ideal.Quotient.mk P (1 ⊗ₜ a)) := rfl
  have hφ (q) (a : k) : φ q (algX p U a) = algebraMap k ℂ a := by
    have : ((1 : ℂ) ⊗ₜ[k] algX p U a) = algebraMap ℂ (ℂ ⊗[k] Γ(X, U)) (algebraMap k ℂ a) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := k) (A := ℂ) (B := Γ(X, U)) a).symm
    rw [hφa, this, Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
    rfl
  let s (q : ((ℂ ⊗[k] Γ(X, U)) ⧸ P) →ₐ[ℂ] ℂ) : GlobalTheory.CxPts p (algebraMap k ℂ) := ofHom hU (φ q) (hφ q)
  have hsU (q) : s q ∈ ptsIn p _ U := ofHom_mem _ _ _
  have hsv (q) (a) : ev p _ U a (s q) = q (Ideal.Quotient.mk P (1 ⊗ₜ a)) := ev_ofHom _ _ _ a
  have hs : Continuous s := by
    refine continuous_iff_continuousAt.2 fun q => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hsU q) (Filter.Eventually.of_forall hsU) fun a => ?_)
    have h : Continuous (ev p _ U a ∘ s) := by
      have : ev p _ U a ∘ s = fun q => q (Ideal.Quotient.mk P (1 ⊗ₜ a)) := funext fun q => hsv q a
      rw [this]
      exact GlobalTheory.AffinePoints.continuous_eval _
    exact h.continuousAt
  have hd : Dense (s ⁻¹' ptsIn p _ (X.basicOpen f)) := by
    have hf' : Ideal.Quotient.mk P ((1 : ℂ) ⊗ₜ[k] f) ≠ 0 := fun h => hfP (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine (GlobalTheory.AffinePoints.dense_nonvanishing hf').mono fun q hq => ?_
    refine (mem_ptsIn_basicOpen (hsU q) f).2 ?_
    rw [hsv]
    exact hq
  let q₁ : ((ℂ ⊗[k] Γ(X, U)) ⧸ P) →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ P q₀ fun a ha => hPq ha
  have hy' : s q₁ = y := by
    refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hsU q₁) hy fun a => ?_)
    refine (hsv q₁ a).trans ?_
    have : q₁ (Ideal.Quotient.mk P (1 ⊗ₜ a)) = q₀ (1 ⊗ₜ a) := rfl
    rw [this]
    simp only [q₀, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (ev_eq hy a).symm
  rw [← hy']
  exact hs.closure_preimage_subset _ (hd q₁)

end

theorem UpperTheory.complex_points_dense_open :
    ∀ (K : Type) [Field K] [NumberField K] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) [AlgebraicGeometry.LocallyOfFiniteType p] (σ : K →+* ℂ) (W : X.Opens), (W : Set X).Nonempty → Dense (GlobalTheory.CxPts.ptsIn p (σ.comp (algebraMap (𝓞 K) K)) W) := by
  intro K _ _ X _ p _ σ W hW y
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have hinj : Function.Injective (algebraMap (𝓞 K) ℂ) :=
    σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have : FaithfulSMul (𝓞 K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.Flat (𝓞 K) ℂ := inferInstance
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ)))
  obtain ⟨f, hf, hfW⟩ := GlobalTheory.CxPtsDense.exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ hW
  exact closure_mono (GlobalTheory.CxPts.ptsIn_mono hfW)
    (mem_closure_basicOpen p hU hf y (GlobalTheory.CxPts.mem_ptsIn.2 hx))
