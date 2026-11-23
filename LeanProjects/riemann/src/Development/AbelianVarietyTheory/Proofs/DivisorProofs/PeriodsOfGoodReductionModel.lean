import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodDet

theorem multilinear_ext_of {K M N : Type} [CommSemiring K] [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    {J : Type} [Fintype J] [DecidableEq J] (S : Set M)
    (hS : ∀ l₁ l₂ : M →ₗ[K] N, (∀ x ∈ S, l₁ x = l₂ x) → l₁ = l₂)
    (f g : MultilinearMap K (fun _ : J ↦ M) N) (h : ∀ v, (∀ i, v i ∈ S) → f v = g v) : f = g := by
  have key : ∀ s : Finset J, ∀ v : J → M, (∀ i ∉ s, v i ∈ S) → f v = g v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; exact h v (fun i ↦ hv i (by simp))
    | insert i s hi ih =>
      intro v hv
      have hl := hS (f.toLinearMap v i) (g.toLinearMap v i) (fun x hx ↦ by
        simp only [MultilinearMap.toLinearMap_apply]
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst hji; simpa using hx
        · rw [Function.update_of_ne hji]; exact hv j (by simp [hji, hj]))
      have h2 := LinearMap.congr_fun hl (v i)
      simpa [MultilinearMap.toLinearMap_apply, Function.update_eq_self] using h2
  ext v
  exact key Finset.univ v (by simp)

open GlobalTheory.RealMult.Obj in

theorem exists_detGen_isDet : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (L : Set E) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap R.subtype) p →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i)) →
    ∀ (δ₀ : X₀.DetGen) (u₀ : R), u₀ ≠ 0 →
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 →
    ∃ δ : X.DetGen, Obj.DetCorr R.subtype p δ₀.1 δ.1 ∧ U.IsDet δ.1 ((∏ i, a i) / (u₀ : ℂ)) := by
  intro _hAb E _ _ _ I _ φ L 𝔠 R _ X₀ X U p hp e a ha δ₀ u₀ hu₀ heq
  classical
  letI : Algebra R ℂ := R.subtype.toAlgebra
  obtain ⟨δ, hδ, -⟩ := Obj.IsPullBy.existsUnique_detGen R.subtype hp δ₀
  obtain ⟨eL, heL, -⟩ := Obj.exists_lieEquiv (R := R) (R' := ℂ) (φ := p) hp
  obtain ⟨h1, h2⟩ := UnifTangent.tangent_bijection U.u X.dim
  have hb : ∀ k : Fin (Module.finrank ℚ (FR E)), ∃ t : X.Lie, U.u.IsDiff (Pi.single k 1) t.hom := fun k ↦ by
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := h2 (Pi.single k 1)
    exact ⟨Serre.Lie.mk X.rm t ht, hd⟩
  choose b hb using hb
  let T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] X.Lie := Fintype.linearCombination ℂ b
  have hT : ∀ w, U.u.IsDiff w (T w).hom := fun w ↦ by
    have hc : IsLieComb w (fun k ↦ (b k).hom) (T w).hom := by
      rw [Serre.Lie.isLieComb_iff]
      simp [T, Fintype.linearCombination_apply]
    have := UnifDifferential.isDiff_of_isLieComb X.A (X.diag U.c) _ _ U.u (fun k ↦ Pi.single k 1) (fun k ↦ (b k).hom) w
      (T w).hom (fun k ↦ (b k).isTangent) hb hc
    convert this using 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hTu : ∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : X.Lie), U.u.IsDiff w v.hom → v = T w := fun w v hw ↦
    Serre.Lie.ext ((h2 w).unique ⟨v.isTangent, hw⟩ ⟨(T w).isTangent, hT w⟩)
  have hTinj : Function.Injective T := fun w w' h ↦
    (h1 (T w).hom (T w).isTangent).unique (hT w) (h ▸ hT w')
  have hTsurj : Function.Surjective T := fun v ↦ by
    obtain ⟨w, hw, -⟩ := h1 v.hom v.isTangent
    exact ⟨w, (hTu w v hw).symm⟩
  let Te := LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩
  have hS : ∀ l₁ l₂ : X.Lie →ₗ[ℂ] ℂ, (∀ x ∈ Set.range (fun y : X₀.Lie ↦ eL (1 ⊗ₜ y)), l₁ x = l₂ x) → l₁ = l₂ := by
    intro l₁ l₂ h
    have hc : l₁ ∘ₗ eL.toLinearMap = l₂ ∘ₗ eL.toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro x y
      have hx : x ⊗ₜ[R] y = x • ((1 : ℂ) ⊗ₜ[R] y) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hx, map_smul]
      rw [h _ ⟨y, rfl⟩]
    refine LinearMap.ext fun x ↦ ?_
    simpa using LinearMap.congr_fun hc (eL.symm x)
  let eh : I → X.Lie →ₗ[ℂ] ℂ := fun i ↦
    (LinearMap.liftBaseChange ℂ ((Algebra.linearMap R ℂ) ∘ₗ e i)) ∘ₗ eL.symm.toLinearMap
  have heh : ∀ i y, eh i (eL (1 ⊗ₜ y)) = ((e i y : R) : ℂ) := by
    intro i y
    simp [eh, LinearMap.liftBaseChange_tmul]
    rfl

  have hper : ∀ i, eh i = (a i • LinearMap.proj (U.e.symm i)) ∘ₗ Te.symm.toLinearMap := by
    intro i
    apply hS
    rintro _ ⟨y, rfl⟩
    have hW : U.u.IsDiff (Te.symm (eL (1 ⊗ₜ y))) (eL (1 ⊗ₜ y)).hom := by
      have h3 := hT (Te.symm (eL (1 ⊗ₜ y)))
      have h4 : T (Te.symm (eL (1 ⊗ₜ y))) = eL (1 ⊗ₜ y) := Te.apply_symm_apply _
      rwa [h4] at h3
    rw [heh]
    have h5 := ha i y (eL (1 ⊗ₜ y)) _ ((heL _ _).2 rfl) hW
    rw [h5]
    simp
  let D : X.DetOmega := Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ eh (U.e k))
  have hD : ((u₀ : ℂ) • δ.1 : X.DetOmega) = D := by
    apply AlternatingMap.coe_multilinearMap_injective
    apply PeriodDet.multilinear_ext_of _ hS
    intro v hv
    choose y hy using hv
    obtain rfl : v = fun j ↦ eL (1 ⊗ₜ y j) := funext fun j ↦ (hy j).symm
    have hc := hδ y (fun j ↦ eL (1 ⊗ₜ y j)) (fun j ↦ (heL _ _).2 rfl)
    have hq : (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) y =
        (u₀ • δ₀.1) y := DFunLike.congr_fun heq y
    have hD1 : D (fun j ↦ eL (1 ⊗ₜ y j)) =
        R.subtype ((Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) y) := by
      change Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (eL (1 ⊗ₜ y j))) =
        R.subtype (Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ e (U.e k)) (y j)))
      refine Eq.trans ?_ (RingHom.map_det R.subtype _).symm
      congr 1
      ext j k
      exact heh _ _
    simp only [AlternatingMap.coe_multilinearMap, AlternatingMap.smul_apply, smul_eq_mul]
    rw [hc, hD1, hq]
    simp
  refine ⟨δ, hδ, fun v W hW ↦ ?_⟩
  have hv : ∀ j, Te.symm (v j) = W j := fun j ↦ by
    rw [hTu (W j) (v j) (hW j)]
    exact Te.symm_apply_apply (W j)
  have hu : (u₀ : ℂ) ≠ 0 := fun h ↦ hu₀ (Subtype.ext h)
  have hDv : D v = (∏ i, a i) * W.det := by
    change Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (v j)) = _
    have hM : (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (v j)) = Matrix.of fun j k ↦ a (U.e k) * W j k := by
      funext j k
      rw [Matrix.of_apply, LinearMap.pi_apply, hper]
      simp [hv]
    rw [hM, Matrix.det_mul_row, Equiv.prod_comp U.e a]
  have h6 := DFunLike.congr_fun hD v
  rw [AlternatingMap.smul_apply, hDv, smul_eq_mul] at h6
  field_simp
  linear_combination h6

end GlobalTheory.PeriodDet
