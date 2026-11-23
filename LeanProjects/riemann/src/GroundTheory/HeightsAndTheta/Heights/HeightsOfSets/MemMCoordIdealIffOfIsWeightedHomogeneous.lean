import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Height
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveIsOrbit
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.NoCommonZeroComplex
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem mConeMap_monomial {Ω : Type*} [Field Ω] (y : Coord n → Ω) (d : Coord n →₀ ℕ) (c : ℤ) :
    Geo.mConeMap (ι := blockIdx n) y (monomial d c) =
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (coordDeg n) d))
        (aeval y (monomial d c)) := by
  rw [Geo.mConeMap, aeval_monomial, aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ d p =
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (coordDeg n) d)) 1 := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ d ⟨k, i⟩ = _
    show _ = (X k : MvPolynomial ι Ω) ^ (Finsupp.weight (coordDeg n) d k)
    rw [Finset.prod_pow_eq_pow_sum, weight_coordDeg_apply]
  rw [hX, MvPolynomial.algebraMap_apply, ← mul_assoc, ← map_mul, C_mul_monomial, mul_one]

theorem mConeMap_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    Geo.mConeMap (ι := blockIdx n) y g =
      monomial (Finsupp.equivFunOnFinite.symm m) (aeval y g) := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [mConeMap_monomial, hg (mem_support_iff.mp hd)]

theorem mem_mCoordIdeal_iff_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y g = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isWeightedHomogeneous y hg, monomial_eq_zero]

def compDegs (f : MvPolynomial (Coord n) ℤ) : Finset (ι → ℕ) :=
  (weightedHomogeneousComponent_finsupp (w := coordDeg n) f).toFinset

omit [Fintype ι] in

theorem sum_compDegs (f : MvPolynomial (Coord n) ℤ) :
    ∑ m ∈ compDegs f, weightedHomogeneousComponent (coordDeg n) m f = f := by
  rw [compDegs, ← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f),
    sum_weightedHomogeneousComponent]

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_zero_of_mem_mCoordIdeal {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ Geo.mCoordIdeal (ι := blockIdx n) y) :
    aeval y f = 0 := by
  have key : ∀ g : MvPolynomial (Coord n) ℤ,
      eval (fun _ ↦ (1 : Ω)) (Geo.mConeMap (ι := blockIdx n) y g) = aeval y g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p v hp =>
      rw [map_mul, map_mul, hp, map_mul]
      simp [Geo.mConeMap]
  rw [← key, Geo.mCoordIdeal, RingHom.mem_ker] at *
  rw [hf, map_zero]

theorem mem_mCoordIdeal_iff {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (f : MvPolynomial (Coord n) ℤ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔
      ∀ m, aeval y (weightedHomogeneousComponent (coordDeg n) m f) = 0 := by
  classical
  constructor
  · intro hf m₀
    by_cases h0 : weightedHomogeneousComponent (coordDeg n) m₀ f = 0
    · rw [h0, map_zero]
    have hm₀ : m₀ ∈ compDegs f := (Set.Finite.mem_toFinset _).mpr h0
    have hk := congrArg (coeff (Finsupp.equivFunOnFinite.symm m₀))
      (show Geo.mConeMap (ι := blockIdx n) y f = 0 from hf)
    rw [← sum_compDegs f, map_sum, coeff_sum, coeff_zero,
      Finset.sum_eq_single m₀] at hk
    · rwa [mConeMap_of_isWeightedHomogeneous y
        (weightedHomogeneousComponent_isWeightedHomogeneous m₀ f), coeff_monomial, if_pos rfl] at hk
    · intro m _ hm
      rw [mConeMap_of_isWeightedHomogeneous y
        (weightedHomogeneousComponent_isWeightedHomogeneous m f), coeff_monomial, if_neg]
      exact fun h ↦ hm (Finsupp.equivFunOnFinite.symm.injective h)
    · exact fun h ↦ absurd hm₀ h
  · intro h
    rw [← sum_compDegs f]
    refine Ideal.sum_mem _ fun m _ ↦ ?_
    exact (mem_mCoordIdeal_iff_of_isWeightedHomogeneous y
      (weightedHomogeneousComponent_isWeightedHomogeneous m f)).mpr (h m)

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_flatCone {F : Type*} [CommRing F] (x : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    aeval (flatCone x) f = evalCone x f := by
  rw [aeval_def, algebraMap_int_eq]
  rfl

theorem mem_orbitIdeal_iff_of_isWeightedHomogeneous (x : Cone n (AlgebraicClosure ℚ))
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ orbitIdeal x ↔ evalCone x g = 0 := by
  rw [orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hg, aeval_flatCone]

theorem mem_points_iff_le_orbitIdeal (P : ArithVariety n) (x : Cone n (AlgebraicClosure ℚ)) :
    x ∈ P.points (AlgebraicClosure ℚ) ↔ BlockNonzero x ∧ P.ideal ≤ orbitIdeal x := by
  refine and_congr Iff.rfl ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · rw [orbitIdeal, mem_mCoordIdeal_iff]
    intro m
    rw [aeval_flatCone]
    exact h _ (P.homogeneous f hf m)
  · rw [← aeval_flatCone]
    exact aeval_eq_zero_of_mem_mCoordIdeal _ (h hf)

theorem zariskiDense_iff_orbitIdeal (P : ArithVariety n) (S : Set (Cone n (AlgebraicClosure ℚ))) :
    P.ZariskiDense S ↔ Geo.IsZariskiDense (ι := blockIdx n) P.ideal (orbitIdeal '' S) := by
  constructor
  · rintro h f ⟨a, ha⟩ hfP
    by_contra hne
    have ha' := (geoMultiHomog_iff f a).mp ha
    refine hfP (h a f ha' fun z hz ↦ ?_)
    refine (mem_orbitIdeal_iff_of_isWeightedHomogeneous z ha').mp ?_
    by_contra hz'
    exact hne ⟨_, ⟨z, hz, rfl⟩, hz'⟩
  · intro h m f hf hvan
    by_contra hfP
    obtain ⟨W, ⟨z, hz, rfl⟩, hfW⟩ := h f ⟨m, (geoMultiHomog_iff f m).mpr hf⟩ hfP
    exact hfW ((mem_orbitIdeal_iff_of_isWeightedHomogeneous z hf).mpr (hvan z hz))

def ArithVariety.genericPt (P : ArithVariety n) : Coord n → P.FunField :=
  fun v ↦ P.mkF (X v)

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_eval₂_int {Ω : Type*} [Field Ω] (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    aeval y f = eval₂ (Int.castRingHom Ω) y f := by
  rw [aeval_def, algebraMap_int_eq]

omit [Fintype ι] in

theorem ArithVariety.eval₂_genericPt (P : ArithVariety n) (f : MvPolynomial (Coord n) ℤ) :
    eval₂ (Int.castRingHom P.FunField) P.genericPt f = P.mkF f := by
  have : eval₂Hom (Int.castRingHom P.FunField) P.genericPt = P.mkF :=
    MvPolynomial.ringHom_ext
      (fun a ↦ DFunLike.congr_fun
        (RingHom.ext_int ((eval₂Hom (Int.castRingHom P.FunField) P.genericPt).comp C)
          (P.mkF.comp C)) a)
      (fun p ↦ eval₂_X _ _ _)
  exact DFunLike.congr_fun this f

omit [Fintype ι] in

theorem ArithVariety.eval₂_genericPt_eq_zero_iff (P : ArithVariety n)
    (f : MvPolynomial (Coord n) ℤ) :
    eval₂ (Int.castRingHom P.FunField) P.genericPt f = 0 ↔ f ∈ P.ideal := by
  rw [P.eval₂_genericPt, P.mkF_eq_zero_iff]

theorem ArithVariety.mCoordIdeal_genericPt (P : ArithVariety n) :
    Geo.mCoordIdeal (ι := blockIdx n) P.genericPt = P.ideal := by
  ext f
  rw [mem_mCoordIdeal_iff]
  constructor
  · intro h
    rw [← sum_compDegs f]
    exact Ideal.sum_mem _ fun m _ ↦
      (P.eval₂_genericPt_eq_zero_iff _).mp (by rw [← aeval_eq_eval₂_int]; exact h m)
  · intro hf m
    rw [aeval_eq_eval₂_int]
    exact (P.eval₂_genericPt_eq_zero_iff _).mpr (P.homogeneous f hf m)

namespace HermLine

omit [DecidableEq ι] in
theorem ofGeo_deg (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B) :
    (ofGeo B hB).deg = B.a := rfl

omit [DecidableEq ι] in
theorem ofGeo_metric (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B) (z : Cone n ℂ) :
    (ofGeo B hB).metric z = B.h (flatCone z) := rfl

theorem ofGeo_toGeo_metric (A : HermLine n) {z : Cone n ℂ} (hz : BlockNonzero z) :
    (ofGeo A.toGeo A.isSmoothHerm_toGeo).metric z = A.metric z :=
  toGeo_h_of_blockNonzero A (w := flatCone z) hz

theorem log_div_toGeo_h (A A' : HermLine n) {z : Cone n ℂ} (hz : BlockNonzero z) :
    Real.log (A.toGeo.h (flatCone z) / A'.toGeo.h (flatCone z)) =
      Real.log (A.metric z) - Real.log (A'.metric z) := by
  rw [toGeo_h_of_blockNonzero A (w := flatCone z) hz,
    toGeo_h_of_blockNonzero A' (w := flatCone z) hz]
  exact Real.log_div (A.metric_pos z hz).ne' (A'.metric_pos z hz).ne'

end HermLine

theorem metricBound_iff (P : ArithVariety n) (A A' : HermLine n) (c : ℝ) :
    (∀ z ∈ Geo.mcPts (ι := blockIdx n) P.ideal,
        |Real.log (A.toGeo.h z / A'.toGeo.h z)| ≤ c) ↔
      ∀ z ∈ P.points ℂ, |Real.log (A.metric z) - Real.log (A'.metric z)| ≤ c := by
  constructor
  · intro h z hz
    rw [← HermLine.log_div_toGeo_h A A' hz.1]
    exact h _ ((P.mem_mcPts_iff _).mpr hz)
  · intro h w hw
    have hz := (P.mem_mcPts_iff w).mp hw
    have := h _ hz
    rwa [← HermLine.log_div_toGeo_h A A' hz.1] at this

omit [DecidableEq ι] in

theorem height_congr_metric {A A' : HermLine n} (hdeg : A.deg = A'.deg)
    (hm : ∀ z : Cone n ℂ, BlockNonzero z → A.metric z = A'.metric z)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) : height A x = height A' x := by
  unfold height
  rw [hdeg]
  congr 2
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [hm _ (blockNonzero_sigma hx σ)]

section Curves

variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]

omit [∀ k, Fintype (κ k)] in

theorem ptsIntegral_congr (P : Ideal (Geo.MRing κ)) {e : ℕ} (φ : Fin e → ((Σ k, κ k) → ℂ) → ℝ)
    {g g' : ((Σ k, κ k) → ℂ) → ℝ} (hg : ∀ z ∈ Geo.mcPts P, g z = g' z) :
    Geo.ptsIntegral P φ g = Geo.ptsIntegral P φ g' := by
  unfold Geo.ptsIntegral Geo.ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold Geo.sheetDensity
    split_ifs with hγ
    · have hs := hγ.choose_spec
      unfold Geo.IsSheet at hs
      congr 1
      exact hg _ hs.2.self_of_nhds.2.1
    · rfl
  · rfl

omit [∀ k, Fintype (κ k)] in

theorem arInt_congr (P : Ideal (Geo.MRing κ)) (s : Geo.MRing κ) {e : ℕ}
    (L : Fin e → Geo.HermLine κ) {A A' : Geo.HermLine κ}
    (hh : ∀ z ∈ Geo.mcPts P, A.h z = A'.h z) : Geo.arInt P s A L = Geo.arInt P s A' L := by
  unfold Geo.arInt
  exact ptsIntegral_congr P _ fun z hz ↦ by rw [Geo.logNorm, Geo.logNorm, hh z hz]

omit [∀ k, Fintype (κ k)] in

theorem recR_congr (I : Ideal (Geo.MRing κ) → (m : ℕ) → (Fin m → Geo.HermLine κ) → ℝ)
    (P : Ideal (Geo.MRing κ)) {e : ℕ} (L : Fin e → Geo.HermLine κ) (s : Geo.MRing κ)
    {A A' : Geo.HermLine κ} (hh : ∀ z ∈ Geo.mcPts P, A.h z = A'.h z) :
    Geo.recR I P L A s = Geo.recR I P L A' s := by
  unfold Geo.recR
  rw [arInt_congr P s L hh]

end Curves

theorem inter_congr_of_curve
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (hII : Geo.IsIntersectionFamily II) {W : Ideal (MvPolynomial (Coord n) ℤ)}
    (hW : Geo.IsArithVar (ι := blockIdx n) W 1) {B B' : Geo.HermLine (blockIdx n)}
    (hB : Geo.IsSmoothHerm B) (hB' : Geo.IsSmoothHerm B') (ha : B.a = B'.a)
    (hh : ∀ z ∈ Geo.mcPts W, B.h z = B'.h z) : II W 1 ![B] = II W 1 ![B'] := by
  obtain ⟨-, hAdd, hR⟩ := hII
  have hW' : Geo.IsArithVar (ι := blockIdx n) W (0 + 1) := hW
  have hprime : W.IsPrime := hW.2.1.1
  have hrel : ∀ k, ∃ i, (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∉ W := hW.2.1.2.2
  let c : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose
  have hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ W := fun k ↦ (hrel k).choose_spec
  have hmon : ∀ d : ι → ℕ, chartMonomial c d ∉ W := by
    intro d h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k (hprime.mem_of_pow_mem _ hk)
  have hsnoc : ∀ C : Geo.HermLine (blockIdx n),
      (Fin.snoc (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) C : Fin 1 → _) = ![C] := by
    intro C
    funext i
    fin_cases i
    rfl
  have hL : ∀ j : Fin 0, Geo.IsSmoothHerm ((Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) j) :=
    fun j ↦ j.elim0
  have key : ∀ (C C' : Geo.HermLine (blockIdx n)) (d : ι → ℕ), Geo.IsSmoothHerm C →
      Geo.IsSmoothHerm C' → (∀ k, C.a k = d k) → (∀ k, C'.a k = d k) →
      (∀ z ∈ Geo.mcPts W, C.h z = C'.h z) → II W 1 ![C] = II W 1 ![C'] := by
    intro C C' d hC hC' hd hd' hCC
    have hs := (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d)
    have h1 := hR W 0 Fin.elim0 C (chartMonomial c d) d hW' hL hC hd hs (hmon d)
    have h2 := hR W 0 Fin.elim0 C' (chartMonomial c d) d hW' hL hC' hd' hs (hmon d)
    rw [hsnoc] at h1 h2
    rw [h1, h2, recR_congr II W Fin.elim0 (chartMonomial c d) hCC]
  let m : ι → ℕ := fun k ↦ (B.a k).natAbs
  let S : Geo.HermLine (blockIdx n) := (HermLine.standardPow (n := n) m).toGeo
  have hS : Geo.IsSmoothHerm S := HermLine.isSmoothHerm_toGeo _
  have hSa : ∀ k, S.a k = m k := fun k ↦ rfl
  have hBS : Geo.IsSmoothHerm (B.tensor S) := ContDiffOn.mul hB hS
  have hBS' : Geo.IsSmoothHerm (B'.tensor S) := ContDiffOn.mul hB' hS
  have hsum := key (B.tensor S) (B'.tensor S) (fun k ↦ (B.a k + m k).toNat) hBS hBS'
    (fun k ↦ by
      show B.a k + S.a k = _
      rw [hSa]
      simp only [m]
      omega)
    (fun k ↦ by
      show B'.a k + S.a k = _
      rw [hSa, ← ha]
      simp only [m]
      omega)
    (fun z hz ↦ by
      show B.h z * S.h z = B'.h z * S.h z
      rw [hh z hz])
  have hadd := hAdd W 0 Fin.elim0 B S hW' hL hB hS
  have hadd' := hAdd W 0 Fin.elim0 B' S hW' hL hB' hS
  rw [hsnoc, hsnoc, hsnoc] at hadd hadd'
  linarith

theorem height_eq_intersectionHeight [Nonempty ι] (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement)
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (hII : Geo.IsIntersectionFamily II) (A : HermLine n) {x : Cone n (AlgebraicClosure ℚ)}
    (hx : BlockNonzero x) : height A x = IndefiniteRowSideFullHecke.HeightsSet.height II A.toGeo (orbitIdeal x) :=
  HeightAsIntersection.proof h₁ h₂ h₃ ι n II hII A x hx

theorem intersectionHeight_eq_height [Nonempty ι] (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement)
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (hII : Geo.IsIntersectionFamily II) (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    IndefiniteRowSideFullHecke.HeightsSet.height II B (orbitIdeal x) = height (HermLine.ofGeo B hB) x := by
  rw [height_eq_intersectionHeight h₁ h₂ h₃ II hII _ hx]
  unfold IndefiniteRowSideFullHecke.HeightsSet.height
  rw [inter_congr_of_curve II hII (h₁ ι n x hx) hB (HermLine.isSmoothHerm_toGeo _) rfl
    fun z hz ↦ (HermLine.toGeo_ofGeo_h B hB ((blockNonzero_unflatCone_iff z).mpr hz.1)).symm]

section Sections

variable {Ω : Type*} [Field Ω]

theorem ArithVariety.mem_iff_aeval_eq_zero (P : ArithVariety n) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) {g : MvPolynomial (Coord n) ℤ}
    {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ P.ideal ↔ aeval y g = 0 := by
  rw [← hy]
  exact mem_mCoordIdeal_iff_of_isWeightedHomogeneous y hg

omit [Fintype ι] in

theorem ArithVariety.aeval_eq_zero_of_mem (P : ArithVariety n) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) {f : MvPolynomial (Coord n) ℤ}
    (hf : f ∈ P.ideal) : aeval y f = 0 :=
  aeval_eq_zero_of_mem_mCoordIdeal y (by rw [hy]; exact hf)

omit [Fintype ι] in

theorem ArithVariety.X_notMem_of_mem_points (P : ArithVariety n) {F : Type*} [CommRing F]
    {z : Cone n F} (hz : z ∈ P.points F) {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0)
    (k : ι) : (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal :=
  fun h ↦ hc k (by simpa [evalCone] using hz.2 _ h)

omit [Fintype ι] in

theorem ArithVariety.mem_points_map (P : ArithVariety n) (τ : AlgebraicClosure ℚ →+* ℂ)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : x ∈ P.points (AlgebraicClosure ℚ)) :
    (fun k i ↦ τ (x k i)) ∈ P.points ℂ :=
  ⟨fun k hk ↦ hx.1 k (funext fun i ↦ (map_eq_zero_iff τ τ.injective).mp (congrFun hk i)),
    fun f hf ↦ by rw [evalCone_map, hx.2 f hf, map_zero]⟩

def algClosureEmbedding : AlgebraicClosure ℚ →+* ℂ :=
  let _ : Algebra.IsAlgebraic ℤ (AlgebraicClosure ℚ) := ⟨fun r ↦
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r)⟩
  (IsAlgClosed.lift (R := ℤ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom

namespace IntegralSection

variable {P : ArithVariety n} {a : ι → ℤ}

omit [Fintype ι] [DecidableEq ι] in

def valueAt (s : IntegralSection P a) (y : Coord n → Ω) : Ω :=
  aeval y s.num / aeval y s.den

theorem aeval_den_ne_zero (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) : aeval y s.den ≠ 0 :=
  fun h ↦ s.den_not_mem ((P.mem_iff_aeval_eq_zero hy s.den_isHomogeneous).mpr h)

theorem valueAt_mem_chartLat (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) :
    s.valueAt y ∈ Geo.chartLat (ι := blockIdx n) y a 1 :=
  s.value_mem_chartLat y (fun _ hf ↦ P.aeval_eq_zero_of_mem hy hf) (s.aeval_den_ne_zero hy)

theorem aeval_chartForm (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) {c : (k : ι) → Fin (n k + 1)}
    {d : ι → ℕ} {e : MvPolynomial (Coord n) ℤ} (hce : IsChartForm P a s.num s.den c d e) :
    aeval y e = s.valueAt y * aeval y (chartMonomial c d) := by
  have h := P.aeval_eq_zero_of_mem hy hce.2
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  rw [valueAt, div_mul_eq_mul_div, eq_div_iff (s.aeval_den_ne_zero hy), ← h]
  ring

theorem sub_mem_of_chartForm (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) {dg dh : ι → ℕ}
    {g h : MvPolynomial (Coord n) ℤ} (hg : IsWeightedHomogeneous (coordDeg n) g dg)
    (hh : IsWeightedHomogeneous (coordDeg n) h dh) (hd : ∀ k, (dg k : ℤ) = dh k + a k)
    (hgh : aeval y g = s.valueAt y * aeval y h) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (hce : IsChartForm P a s.num s.den c d e) :
    g * chartMonomial c d - h * e ∈ P.ideal := by
  obtain ⟨δ, he, hδ⟩ := hce.1
  have hdeg : dh + δ = dg + d := by
    funext k
    have h1 := hd k
    have h2 := hδ k
    simp only [Pi.add_apply]
    omega
  have h1 := hg.mul (isWeightedHomogeneous_chartMonomial c d)
  have h2 := hh.mul he
  rw [hdeg] at h2
  have hhom : IsWeightedHomogeneous (coordDeg n) (g * chartMonomial c d - h * e) (dg + d) :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
  rw [P.mem_iff_aeval_eq_zero hy hhom, map_sub, map_mul, map_mul, hgh, s.aeval_chartForm hy hce]
  ring

omit [Fintype ι] in

theorem evalCone_rel {F : Type*} [CommRing F] {z : Cone n F} (hz : z ∈ P.points F)
    {g h m e : MvPolynomial (Coord n) ℤ} (hq : g * m - h * e ∈ P.ideal) :
    evalCone z g * evalCone z m = evalCone z h * evalCone z e := by
  have := hz.2 _ hq
  simp only [evalCone, eval₂_sub, eval₂_mul] at this ⊢
  exact sub_eq_zero.mp this

theorem isSectionBounded_iff_supNormLE (A : HermLine n) (s : IntegralSection P A.deg)
    {y : Coord n → Ω} (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) (C : ℝ) :
    IndefiniteRowSideFullHecke.HeightsSet.IsSectionBounded (ι := blockIdx n) P.ideal y A.toGeo (s.valueAt y)
      (Real.exp C) ↔ s.SupNormLE A C := by
  constructor
  · intro hb z hz c d e hce hc
    obtain ⟨δ, he, hδ⟩ := hce.1
    have hmon : evalCone z (chartMonomial c d) ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
    have hbd := hb δ d e (chartMonomial c d) (flatCone z) ((geoMultiHomog_iff e δ).mpr he)
      ((geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d))
      (fun k ↦ by rw [HermLine.toGeo_a]; have := hδ k; omega) (s.aeval_chartForm hy hce)
      ((P.mem_mcPts_iff _).mpr hz)
    rw [eval_map_flatCone, eval_map_flatCone,
      HermLine.toGeo_h_of_blockNonzero A (w := flatCone z) hz.1] at hbd
    rw [div_le_iff₀ (mul_pos (norm_pos_iff.mpr hmon) (A.metric_pos z hz.1))]
    calc ‖evalCone z e‖ ≤ Real.exp C * ‖evalCone z (chartMonomial c d)‖ * A.metric z := hbd
      _ = _ := by ring
  · intro hs dg dh g h w hg hh hd hgh hw
    have hz : unflatCone w ∈ P.points ℂ := (P.mem_mcPts_iff w).mp hw
    obtain ⟨c, hc⟩ := exists_chart hz.1
    obtain ⟨d, e, hce⟩ := s.regular c (P.X_notMem_of_mem_points hz hc)
    have hrel := evalCone_rel hz (s.sub_mem_of_chartForm hy ((geoMultiHomog_iff g dg).mp hg)
      ((geoMultiHomog_iff h dh).mp hh) hd hgh hce)
    have hmon : evalCone (unflatCone w) (chartMonomial c d) ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
    have hsup := hs (unflatCone w) hz c d e hce hc
    rw [show eval w (map (Int.castRingHom ℂ) g) = evalCone (unflatCone w) g from
        eval_map_flatCone (unflatCone w) g,
      show eval w (map (Int.castRingHom ℂ) h) = evalCone (unflatCone w) h from
        eval_map_flatCone (unflatCone w) h,
      HermLine.toGeo_h_of_blockNonzero A hz.1]
    rw [div_le_iff₀ (mul_pos (norm_pos_iff.mpr hmon) (A.metric_pos _ hz.1))] at hsup
    have hkey : ‖evalCone (unflatCone w) g‖ * ‖evalCone (unflatCone w) (chartMonomial c d)‖ ≤
        (Real.exp C * ‖evalCone (unflatCone w) h‖ * A.metric (unflatCone w)) *
          ‖evalCone (unflatCone w) (chartMonomial c d)‖ := by
      rw [← norm_mul, hrel, norm_mul]
      calc ‖evalCone (unflatCone w) h‖ * ‖evalCone (unflatCone w) e‖ ≤
          ‖evalCone (unflatCone w) h‖ * (Real.exp C *
            (‖evalCone (unflatCone w) (chartMonomial c d)‖ * A.metric (unflatCone w))) :=
            mul_le_mul_of_nonneg_left hsup (norm_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_right hkey (norm_pos_iff.mpr hmon)

theorem nonzeroAt_of_noCommonZero {J : ℕ} (s : Fin J → IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) (τ : AlgebraicClosure ℚ →+* ℂ)
    (h : IndefiniteRowSideFullHecke.HeightsSet.NoCommonZero (ι := blockIdx n) P.ideal y a fun j ↦ (s j).valueAt y) :
    ∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x := by
  intro x hx
  have hz := P.mem_points_map τ hx
  obtain ⟨j, dg, dh, g, h, hg, hh, hd, hgh, hg0, -⟩ :=
    h (flatCone fun k i ↦ τ (x k i)) ((P.mem_mcPts_iff _).mpr hz)
  rw [eval_map_flatCone] at hg0
  obtain ⟨c, hc⟩ := exists_chart hx.1
  obtain ⟨d, e, hce⟩ := (s j).regular c (P.X_notMem_of_mem_points hx hc)
  refine ⟨j, c, d, e, hce, hc, fun he0 ↦ ?_⟩
  have hrel := evalCone_rel hz ((s j).sub_mem_of_chartForm hy ((geoMultiHomog_iff g dg).mp hg)
    ((geoMultiHomog_iff h dh).mp hh) hd hgh hce)
  rw [evalCone_map τ x e, he0, map_zero, mul_zero] at hrel
  have hmon : evalCone (fun k i ↦ τ (x k i)) (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ ((map_ne_zero τ).mpr (hc k))
  exact hg0 ((mul_eq_zero.mp hrel).resolve_right hmon)

theorem exists_multihomog_witness_of_nonzeroAt (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) (τ : AlgebraicClosure ℚ →+* ℂ)
    {x : Cone n (AlgebraicClosure ℚ)} (hxs : s.NonzeroAt x) :
    ∃ (dg dh : ι → ℕ) (g h : MvPolynomial (Coord n) ℤ),
      Geo.IsMultiHomog (ι := blockIdx n) g dg ∧ Geo.IsMultiHomog (ι := blockIdx n) h dh ∧
      (∀ k, (dg k : ℤ) = dh k + a k) ∧ aeval y g = s.valueAt y * aeval y h ∧
      eval (flatCone fun k i ↦ τ (x k i)) (map (Int.castRingHom ℂ) g) ≠ 0 ∧
      eval (flatCone fun k i ↦ τ (x k i)) (map (Int.castRingHom ℂ) h) ≠ 0 := by
  obtain ⟨c, d, e, hce, hc, he⟩ := hxs
  obtain ⟨δ, hδe, hδ⟩ := hce.1
  refine ⟨δ, d, e, chartMonomial c d, (geoMultiHomog_iff e δ).mpr hδe,
    (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d),
    fun k ↦ by have := hδ k; omega, s.aeval_chartForm hy hce, ?_, ?_⟩
  · rw [eval_map_flatCone, evalCone_map]
    exact (map_ne_zero τ).mpr he
  · rw [eval_map_flatCone, evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ ((map_ne_zero τ).mpr (hc k))

end IntegralSection

end Sections

theorem exists_point_of_curve (hC : CurveIsOrbit.Statement) (P : ArithVariety n)
    {W : Ideal (MvPolynomial (Coord n) ℤ)} (hW : Geo.IsArithVar (ι := blockIdx n) W 1)
    (hPW : P.ideal ≤ W) : ∃ x ∈ P.points (AlgebraicClosure ℚ), W = orbitIdeal x := by
  obtain ⟨x, hx, rfl⟩ := hC ι n W hW
  exact ⟨x, (mem_points_iff_le_orbitIdeal P x).mpr ⟨hx, hPW⟩, rfl⟩

theorem orbitIdeal_curve_of_mem_points [Nonempty ι] (h₁ : OrbitCurve.Statement)
    (P : ArithVariety n) {x : Cone n (AlgebraicClosure ℚ)}
    (hx : x ∈ P.points (AlgebraicClosure ℚ)) :
    Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) 1 ∧ P.ideal ≤ orbitIdeal x :=
  ⟨h₁ ι n x hx.1, ((mem_points_iff_le_orbitIdeal P x).mp hx).2⟩

theorem IntegralSection.noCommonZero_of_nonzeroAt (hS : NoCommonZeroComplex.Statement)
    {P : ArithVariety n} {a : ι → ℤ} {J : ℕ} (s : Fin J → IntegralSection P a)
    {Ω : Type*} [Field Ω] {y : Coord n → Ω} (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal)
    (h : ∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x) :
    IndefiniteRowSideFullHecke.HeightsSet.NoCommonZero (ι := blockIdx n) P.ideal y a fun j ↦ (s j).valueAt y := by
  intro w hw
  have hz := (P.mem_mcPts_iff w).mp hw
  obtain ⟨j, c, d, e, hce, hc, he⟩ := hS ι n P a (Fin J) s h _ hz
  obtain ⟨δ, hδe, hδ⟩ := hce.1
  refine ⟨j, δ, d, e, chartMonomial c d, (geoMultiHomog_iff e δ).mpr hδe,
    (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d),
    fun k ↦ by have := hδ k; omega, (s j).aeval_chartForm hy hce, ?_, ?_⟩
  · rw [show eval w (map (Int.castRingHom ℂ) e) = evalCone (unflatCone w) e from
      eval_map_flatCone (unflatCone w) e]
    exact he
  · rw [show eval w (map (Int.castRingHom ℂ) (chartMonomial c d)) =
        evalCone (unflatCone w) (chartMonomial c d) from
      eval_map_flatCone (unflatCone w) (chartMonomial c d), evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

theorem IntegralSection.noCommonZero_iff (hS : NoCommonZeroComplex.Statement)
    {P : ArithVariety n} {a : ι → ℤ} {J : ℕ} (s : Fin J → IntegralSection P a)
    {Ω : Type*} [Field Ω] {y : Coord n → Ω} (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) :
    IndefiniteRowSideFullHecke.HeightsSet.NoCommonZero (ι := blockIdx n) P.ideal y a (fun j ↦ (s j).valueAt y) ↔
      ∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x :=
  ⟨IntegralSection.nonzeroAt_of_noCommonZero s hy algClosureEmbedding,
    IntegralSection.noCommonZero_of_nonzeroAt hS s hy⟩

example : Geo.mCoordIdeal (ι := blockIdx (fun _ : Unit ↦ 1)) (ArithVariety.whole _).genericPt = ⊥ :=
  (ArithVariety.whole _).mCoordIdeal_genericPt

example : (HermLine.ofGeo (HermLine.standard (fun _ : Unit ↦ 1)).toGeo
      (HermLine.isSmoothHerm_toGeo _)).deg = (fun _ ↦ 1) ∧
    (HermLine.ofGeo (HermLine.standard (fun _ : Unit ↦ 1)).toGeo
      (HermLine.isSmoothHerm_toGeo _)).metric (fun _ ↦ ![1, 2]) =
    (HermLine.standard (fun _ : Unit ↦ 1)).metric (fun _ ↦ ![1, 2]) := by
  refine ⟨rfl, HermLine.ofGeo_toGeo_metric _ fun _ h ↦ ?_⟩
  have := congrFun h 0
  simp at this

example : (IntegralSection.chartSection (ArithVariety.whole (fun _ : Unit ↦ 1)) (fun _ ↦ 0)).valueAt
      (ArithVariety.whole _).genericPt ∈
      Geo.chartLat (ι := blockIdx (fun _ : Unit ↦ 1)) (ArithVariety.whole _).genericPt
        (fun _ ↦ 1) 1 ∧
    IndefiniteRowSideFullHecke.HeightsSet.IsSectionBounded (ι := blockIdx (fun _ : Unit ↦ 1)) (ArithVariety.whole _).ideal
      (ArithVariety.whole _).genericPt (HermLine.standard _).toGeo
      ((IntegralSection.chartSection (ArithVariety.whole (fun _ : Unit ↦ 1)) (fun _ ↦ 0)).valueAt
        (ArithVariety.whole _).genericPt) (Real.exp 0) :=
  ⟨IntegralSection.valueAt_mem_chartLat _ (ArithVariety.whole _).mCoordIdeal_genericPt,
    (IntegralSection.isSectionBounded_iff_supNormLE _ _
      (ArithVariety.whole _).mCoordIdeal_genericPt 0).mpr (chartSection_supNormLE _ _)⟩

end

end GroundTheory.Heights₂.Heights
