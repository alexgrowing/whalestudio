import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroSmulMem

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn HasGram IsGram cuspW cuspOn_le latW suppOn
  normW petW petAt petE muOn muPart classesOver ptN rdU_eq_zero mem_latOn modelWt)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

section Gram

open Matrix Module
open scoped MatrixOrder ComplexOrder

theorem sum_norm_sq_eq {n : ℕ} (u : Fin n → ℂ) : ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem cnorm_mulVec_eq {n n' m : ℕ} {A : Matrix (Fin n) (Fin m) ℂ} {Y : Matrix (Fin n') (Fin m) ℂ} (h : Aᴴ * A = Yᴴ * Y)
    (u : Fin m → ℂ) : Formalism.HermitianLatticesTheory.cnorm (Y *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (A *ᵥ u) := by
  have key : ∀ {k : ℕ} (B : Matrix (Fin k) (Fin m) ℂ), star (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = star u ⬝ᵥ ((Bᴴ * B) *ᵥ u) := fun B => by
    have e0 : star u ⬝ᵥ (Bᴴ *ᵥ (B *ᵥ u)) = (star u ᵥ* Bᴴ) ⬝ᵥ (B *ᵥ u) := dotProduct_mulVec _ _ _
    rw [← mulVec_mulVec, e0, star_mulVec]
  have e : ∑ i, ‖(Y *ᵥ u) i‖ ^ 2 = ∑ i, ‖(A *ᵥ u) i‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [sum_norm_sq_eq, sum_norm_sq_eq, key, key, h]
  simp only [Formalism.HermitianLatticesTheory.cnorm, e]

theorem cnorm_smul {n : ℕ} {t : ℝ} (ht : 0 < t) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((t : ℂ) • u) = t * Formalism.HermitianLatticesTheory.cnorm u := by
  simp only [Formalism.HermitianLatticesTheory.cnorm, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem exists_unit_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  refine ⟨B, ?_, by simpa [star_eq_conjTranspose] using hB⟩
  have h1 : A.det ≠ 0 := hA.det_pos.ne'
  rw [hB, star_eq_conjTranspose, det_mul] at h1
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)

theorem hasGram_of_injective {N : (K →+* ℂ) → V → ℝ} (h : HasGram N) (φ : W →ₗ[K] V) (hφ : Function.Injective φ)
    {N' : (K →+* ℂ) → W → ℝ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (hN : ∀ (v : InfinitePlace K) (x : W), N' v.embedding x = t v * N v.embedding (φ x)) : HasGram N' := by
  classical
  obtain ⟨n, ⟨b, X⟩, hX⟩ := h
  dsimp only at hX
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  haveI : FiniteDimensional K W := FiniteDimensional.of_injective φ hφ
  let b' := Module.finBasis K W
  let B : Matrix (Fin n) (Fin (finrank K W)) K := LinearMap.toMatrix b' b φ
  obtain ⟨g, hg⟩ := φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hφ)
  let C : Matrix (Fin (finrank K W)) (Fin n) K := LinearMap.toMatrix b b' g
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  have key : ∀ v : InfinitePlace K, ∃ Y : Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ, IsUnit Y.det ∧
      ((X v)⁻¹ * B.map v.embedding)ᴴ * ((X v)⁻¹ * B.map v.embedding) = Yᴴ * Y := fun v => by
    have hu := (hX v).1
    have hL : (C.map v.embedding * X v) * ((X v)⁻¹ * B.map v.embedding) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (X v), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ← Matrix.map_mul, hCB,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hinj : Function.Injective ((X v)⁻¹ * B.map v.embedding).mulVec := fun y z hyz => by
      have := congrArg (C.map v.embedding * X v).mulVec hyz
      simpa only [mulVec_mulVec, hL, one_mulVec] using this
    exact exists_unit_factor (PosDef.conjTranspose_mul_self _ hinj)
  choose Y hY hYG using key
  have hu : ∀ v, IsUnit (((t v : ℂ)) • Y v).det := fun v => by
    rw [det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (by exact_mod_cast (ht v).ne'))).mul (hY v)
  refine IsGram.hasGram (b := b') (X := fun v => ((t v : ℂ) • Y v)⁻¹) fun v => ⟨?_, fun x => ?_⟩
  · exact Matrix.isUnit_nonsing_inv_det _ (hu v)
  · have e1 : Formalism.HermitianLatticesTheory.vecAt b v (φ x) = B.map v.embedding *ᵥ Formalism.HermitianLatticesTheory.vecAt b' v x := by
      funext i
      have e := congrFun (LinearMap.toMatrix_mulVec_repr b' b φ x) i
      show v.embedding (b.repr (φ x) i) = _
      rw [← e]
      exact RingHom.map_mulVec v.embedding _ _ i
    rw [hN v x, ← (hX v).2 (φ x)]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu v), smul_mulVec, cnorm_smul (ht v), e1, mulVec_mulVec,
      cnorm_mulVec_eq (hYG v)]

theorem HasGram_eq_zero {N : (K →+* ℂ) → V → ℝ} (h : HasGram N) (v : InfinitePlace K) {x : V} (hx : N v.embedding x = 0) :
    x = 0 := by
  obtain ⟨n, ⟨b, X⟩, hX⟩ := h
  dsimp only at hX
  have h0 := (hX v).2 x
  rw [hx] at h0
  have h1 : ∑ i, ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h0
  have h2 : Formalism.HermitianLatticesTheory.fcoord b X v x = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h1 i (Finset.mem_univ i)
    simpa using this
  have h3 : Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    have := congrArg (X v).mulVec h2
    simpa only [Formalism.HermitianLatticesTheory.fcoord, mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v).1, one_mulVec, mulVec_zero] using this
  apply b.repr.map_eq_zero_iff.1
  ext i
  have := congrFun h3 i
  simpa [Formalism.HermitianLatticesTheory.vecAt] using this

theorem exists_smul_mem_of_mem_span [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {L : Submodule (𝓞 K) V} {x : V}
    (hx : x ∈ Submodule.span K (L : Set V)) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarMultipleMembership.exists_ne_zero_smul_mem ..)

theorem fg_of_injective [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (φ : W →ₗ[K] V) (hφ : Function.Injective φ) {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) W}
    (hL : ∀ f ∈ L', φ f ∈ L) (hfg : L.FG) : L'.FG := by
  have hN : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian _ hfg
  let ψ : W →ₗ[𝓞 K] V := φ.restrictScalars (𝓞 K)
  have hle : L'.map ψ ≤ L := by
    rintro _ ⟨f, hf, rfl⟩
    exact hL f hf
  exact Submodule.fg_of_fg_map_injective ψ hφ (isNoetherian_submodule.1 hN _ hle)

theorem span_eq_top_of_injective [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (φ : W →ₗ[K] V) {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) W} (hL : ∀ f, φ f ∈ L → f ∈ L')
    (hsp : Submodule.span K (L : Set V) = ⊤) : Submodule.span K (L' : Set W) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hf : φ f ∈ Submodule.span K (L : Set V) := hsp ▸ Submodule.mem_top
  obtain ⟨a, ha, hm⟩ := exists_smul_mem_of_mem_span hf
  have h1 : a • f ∈ L' := hL _ (by rwa [LinearMap.map_smul_of_tower])
  have hA : algebraMap (𝓞 K) K a ≠ 0 := fun h => ha (IsFractionRing.injective (𝓞 K) K (h.trans (map_zero _).symm))
  have e : f = (algebraMap (𝓞 K) K a)⁻¹ • (a • f) := by
    rw [← algebraMap_smul K a f, smul_smul, inv_mul_cancel₀ hA, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Gram

section Norms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

section One

variable {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) (V : TH.HSp D)
  (dict : Formalism.L2.Theta.GA D V → Σ k, FD.Frame (U.X k).Ψ r) (Z : Comp Xo c) (G : WTZ E)

theorem support_ptN_subset {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    Function.support (fun q : AutQ V => ptN (modelWt U G) (rdU U f) (dict q.out)) ⊆
      classesOver V dict (framesOn U Z) := fun q hq => by
  by_contra h
  apply hq
  have h0 := rdU_eq_zero U hf (z := dict q.out) h
  show ‖rdU U f (dict q.out).1 (dict q.out).2‖ * _ = 0
  rw [h0, norm_zero, zero_mul]

theorem petAt_muOn {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    petAt U x V dict (muOn U V dict Z) G f =
      (((muQ1 V (classesOver V dict (framesOn U Z)))⁻¹ ^ (1 / (2 : ENNReal)).toReal).toReal) *
        petAt U x V dict (muQ1 V) G f := by
  unfold petAt petE muOn muPart
  rw [ProbabilityTheory.cond, MeasureTheory.eLpNorm_smul_measure_of_ne_top (by simp),
    MeasureTheory.eLpNorm_restrict_eq_of_support_subset (support_ptN_subset U V dict Z G hf), smul_eq_mul, ENNReal.toReal_mul]
  ring

theorem petAt_eq_zero {f : Rul Xo c} (hf : f ∈ suppOn Z) (h0 : muQ1 V (classesOver V dict (framesOn U Z)) = 0) :
    petAt U x V dict (muQ1 V) G f = 0 := by
  unfold petAt petE
  rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset (support_ptN_subset U V dict Z G hf),
    MeasureTheory.Measure.restrict_eq_zero.2 h0, MeasureTheory.eLpNorm_measure_zero]
  simp

end One

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E)

theorem goodOn_of_goodW (h : GoodW U x V dict G) : GoodOn U x V dict Z G := by
  obtain ⟨hg, hfg, hsp⟩ := h
  let φ : cuspOn U Z G →ₗ[c.F] cuspW Xo c U G := Submodule.inclusion (cuspOn_le U Z G)
  have hφ : Function.Injective φ := Submodule.inclusion_injective _
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : ∃ v : InfinitePlace c.F, muQ1 (V (goodOf c v.embedding))
        (classesOver (V (goodOf c v.embedding)) (dict (goodOf c v.embedding)) (framesOn (U (goodOf c v.embedding)) Z)) = 0
    · obtain ⟨v, hv⟩ := h0
      have hz : ∀ f : cuspOn U Z G, f = 0 := fun f => hφ (by
        rw [map_zero]
        exact HasGram_eq_zero hg v (petAt_eq_zero _ x _ _ Z G f.2.2 hv))
      refine hasGram_of_injective hg φ hφ (fun _ => 1) (fun _ => one_pos) fun w f => ?_
      obtain rfl := hz f
      rw [map_zero, one_mul]
      have a1 := GlobalTheory.AllWt.petOn_smul U x V dict Z G w.embedding 0 0
      have a2 := GlobalTheory.AllWt.petW_smul U x V dict G w.embedding 0 0
      simp only [zero_smul, map_zero, norm_zero, zero_mul] at a1 a2
      exact a1.trans a2.symm
    · push_neg at h0
      refine hasGram_of_injective hg φ hφ (fun v => (((muQ1 (V (goodOf c v.embedding))
        (classesOver (V (goodOf c v.embedding)) (dict (goodOf c v.embedding)) (framesOn (U (goodOf c v.embedding)) Z)))⁻¹ ^
          (1 / (2 : ENNReal)).toReal).toReal)) (fun v => ?_) fun v f => ?_
      · rw [← ENNReal.toReal_rpow]
        refine Real.rpow_pos_of_pos (ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 (MeasureTheory.measure_ne_top _ _))
          (ENNReal.inv_ne_top.2 (h0 v))) _
      · exact petAt_muOn _ x _ _ Z G f.2.2
  · exact fg_of_injective φ hφ (fun _ h => h) hfg
  · exact span_eq_top_of_injective φ (fun _ h => h) hsp

end Norms

theorem goodOn_of_goodAt : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (G : WTZ D.host.E), Y.GoodAt G →
      GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z G :=
  fun _ _ _ Y _ _ _ _ Z G hG => goodOn_of_goodW Y.U _ _ Y.dict Z G hG

end GlobalTheory.HSApp
