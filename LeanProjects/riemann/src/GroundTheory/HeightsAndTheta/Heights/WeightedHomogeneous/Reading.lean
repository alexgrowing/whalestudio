import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Examples
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def HermLine.ConjInvariant (A : HermLine n) : Prop :=
  ∀ z : Cone n ℂ, BlockNonzero z → A.metric (fun k i ↦ starRingEnd ℂ (z k i)) = A.metric z

theorem HermLine.conjInvariant_iff (A : HermLine n) :
    A.ConjInvariant ↔ Geo.IsConjInvariantH A.toGeo := by
  have hb : ∀ w : Coord n → ℂ, BlockNonzero (unflatCone fun p ↦ starRingEnd ℂ (w p)) ↔
      BlockNonzero (unflatCone w) := by
    intro w
    simp only [blockNonzero_unflatCone_iff, ne_eq, map_eq_zero]
  constructor
  · intro h w
    by_cases hw : BlockNonzero (unflatCone w)
    · rw [A.toGeo_h_of_blockNonzero hw, A.toGeo_h_of_blockNonzero ((hb w).mpr hw)]
      exact h _ hw
    · simp only [toGeo, if_neg hw, if_neg (fun h' ↦ hw ((hb w).mp h'))]
  · intro h z hz
    have hz' : BlockNonzero (unflatCone (flatCone z)) := hz
    have := h (flatCone z)
    rw [A.toGeo_h_of_blockNonzero hz', A.toGeo_h_of_blockNonzero ((hb _).mpr hz')] at this
    exact this

def HermLine.ofGeo (N : Geo.HermLine (blockIdx n)) (hN : Geo.IsSmoothHerm N) : HermLine n where
  deg := N.a
  metric z := N.h (flatCone z)
  metric_pos z hz := N.pos _ ((blockNonzero_unflatCone_iff _).mp hz)
  metric_smul c z hc _ := N.smul c (flatCone z) hc
  metric_smooth := by
    have hu : ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ flatCone z) :=
      contDiff_pi.2 fun p ↦ ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n p.1 + 1) ↦ ℂ) p.2).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun k ↦ Fin (n k + 1) → ℂ) p.1)).contDiff
    exact hN.comp hu.contDiffOn fun z hz ↦ (blockNonzero_unflatCone_iff _).mp hz

theorem HermLine.toGeo_ofGeo_h (N : Geo.HermLine (blockIdx n)) (hN : Geo.IsSmoothHerm N)
    {w : Coord n → ℂ} (hw : BlockNonzero (unflatCone w)) : (HermLine.ofGeo N hN).toGeo.h w = N.h w :=
  HermLine.toGeo_h_of_blockNonzero _ hw

namespace ArithVariety

variable (P : ArithVariety n)

def IsSmallFor (A : HermLine n) (t : P.FunField) : Prop :=
  ∀ (p q : MvPolynomial (Coord n) ℤ) (δp δq : ι → ℕ), IsWeightedHomogeneous (coordDeg n) p δp →
    IsWeightedHomogeneous (coordDeg n) q δq → (∀ k, (δp k : ℤ) = δq k + A.deg k) →
    P.mkF p = t * P.mkF q → ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ ‖evalCone z q‖ * A.metric z

structure IsNormalSection (a : ι → ℤ) (t : P.FunField) : Prop where
  degree : P.IsOfDegree a t
  integral : ∀ c, P.IsLive c → t / P.chartPow c a ∈ integralClosure (P.chartRing c) P.FunField

def Reads {Ω : Type} [Field Ω] (y : Coord n → Ω) (a : ι → ℤ) (s : Ω) (t : P.FunField) : Prop :=
  ∀ (g h : MvPolynomial (Coord n) ℤ) (δg δh : ι → ℕ), IsWeightedHomogeneous (coordDeg n) g δg →
    IsWeightedHomogeneous (coordDeg n) h δh → (∀ k, (δg k : ℤ) = δh k + a k) →
    (aeval y g = s * aeval y h ↔ P.mkF g = t * P.mkF h)

end ArithVariety

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

def plusCoord {Ω : Type} (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) : Coord D.extSizes → Ω
  | ⟨none, j⟩ => x' j
  | ⟨some k, i⟩ => y ⟨k, i⟩

def oldFlat {F : Type*} (w : Coord D.extSizes → F) : Coord n → F := fun p ↦ w ⟨some p.1, p.2⟩

structure BlockReading {Ω : Type} [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) : Prop where
  ideal_eq : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y
  ext_eq : D.extIdeal = Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')
  reads : ∀ j, P.Reads y D.deg (x' j) (D.elt j)

def InducesMetric {Ω : Type} [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω)
    (N : Geo.HermLine (blockIdx n)) (Ap : Geo.HermLine (blockIdx D.extSizes)) : Prop :=
  ∀ (j : Fin (D.size + 1)) (g m : MvPolynomial (Coord n) ℤ) (dg dm : ι → ℕ),
    Geo.IsMultiHomog (ι := blockIdx n) g dg → Geo.IsMultiHomog (ι := blockIdx n) m dm →
    (∀ k, (dg k : ℤ) = dm k + N.a k) → aeval y g = aeval y m * x' j →
    ∀ z ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')),
      ‖z ⟨none, j⟩‖ * ‖eval (D.oldFlat z) (map (Int.castRingHom ℂ) m)‖ * N.h (D.oldFlat z) =
        ‖eval (D.oldFlat z) (map (Int.castRingHom ℂ) g)‖ * Ap.h z

end AddBlockData

def IsSupSmallBlock {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    (y : Coord n' → Ω) (k₀ : κ) (A : Geo.HermLine (blockIdx n')) (τ : ℕ) (s : Ω) : Prop :=
  ∀ f : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι := blockIdx n') f (Pi.single k₀ τ) →
    aeval y f = s → ∀ z ∈ Geo.mcPts (ι := blockIdx n') (Geo.mCoordIdeal (ι := blockIdx n') y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤ A.h z ^ τ

def monomialValues {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) : Set Ω :=
  {s | ∃ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = d k) ∧ s = ∏ p, y p ^ μ p}

theorem ArithVariety.isSmallH_iff {Ω : Type} [Field Ω] {y : Coord n → Ω} (P : ArithVariety n)
    (A : HermLine n) (τ : ℕ) {s : Ω} {t : P.FunField} (hR : P.Reads y (τ • A.deg) s t) :
    Geo.IsSmallH (ι := blockIdx n) P.ideal y A.toGeo τ s ↔ P.IsSmallFor (A.pow τ) t := by
  constructor
  · intro hs p q δp δq hp hq hd hpq z hz
    have hgp := (geoMultiHomog_iff p δp).mpr hp
    have hgq := (geoMultiHomog_iff q δq).mpr hq
    have hd' : ∀ k, (δp k : ℤ) = δq k + (τ • A.deg) k := hd
    have hy := (hR p q δp δq hp hq hd').mpr hpq
    have hzm : flatCone z ∈ Geo.mcPts (ι := blockIdx n) P.ideal := (P.mem_mcPts_iff _).mpr hz
    have := hs δp δq p q (flatCone z) hgp hgq
      (fun k ↦ by have := hd' k; simpa [HermLine.toGeo] using this) hy hzm
    rw [eval_map_flatCone, eval_map_flatCone,
      HermLine.toGeo_h_of_blockNonzero A (show BlockNonzero (unflatCone (flatCone z)) from hz.1)] at this
    simpa [HermLine.pow] using this
  · intro hs δp δq p q z hp hq hd hy hz
    have hp' := (geoMultiHomog_iff p δp).mp hp
    have hq' := (geoMultiHomog_iff q δq).mp hq
    have hd' : ∀ k, (δp k : ℤ) = δq k + (τ • A.deg) k := fun k ↦ by
      have := hd k
      simpa [HermLine.toGeo] using this
    have hF := (hR p q δp δq hp' hq' hd').mp hy
    have hz' := (P.mem_mcPts_iff z).mp hz
    have := hs p q δp δq hp' hq' hd' hF (unflatCone z) hz'
    rw [← eval_map_flatCone, ← eval_map_flatCone] at this
    rw [HermLine.toGeo_h_of_blockNonzero A hz'.1]
    simpa [HermLine.pow] using this

theorem AddBlockData.oldFlat_mem_mcPts {P : ArithVariety n} (D : AddBlockData P) {Ω : Type} [Field Ω]
    (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) (z : Coord D.extSizes → ℂ)
    (hz : z ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x'))) :
    D.oldFlat z ∈ Geo.mcPts (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) := by
  refine ⟨fun k ↦ hz.1 (some k), fun f hf ↦ ?_⟩
  have hmem : D.liftOld f ∈ Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x') := by
    have hf0 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
    rw [Geo.mCoordIdeal, RingHom.mem_ker]
    have key : Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x') (D.liftOld f) =
        rename some (Geo.mConeMap (ι := blockIdx n) y f) := by
      have h : ((Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x')).toRingHom.comp
            (D.liftOld).toRingHom) =
          (rename (R := Ω) (some : ι → Option ι)).toRingHom.comp
            (Geo.mConeMap (ι := blockIdx n) y).toRingHom := by
        refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ ?_)
        simp [Geo.mConeMap, AddBlockData.liftOld, AddBlockData.oldCoord, AddBlockData.plusCoord]
      exact congrArg (fun φ : _ →+* _ ↦ φ f) h
    rw [key, hf0, map_zero]
  have h3 := hz.2 _ hmem
  rw [eval_map] at h3 ⊢
  rw [AddBlockData.liftOld, eval₂_rename] at h3
  exact h3

section Examples

variable (n)

omit [Fintype ι] [DecidableEq ι] in

theorem mCoordIdeal_eq_ker {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    Geo.mCoordIdeal (ι := blockIdx n) y =
      RingHom.ker (eval₂Hom (Int.castRingHom (MvPolynomial ι Ω)) fun v : Coord n ↦ C (y v) * X v.1) := by
  ext f
  rw [Geo.mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, Geo.mConeMap, aeval_def]
  rfl

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_of_hom {Ω : Type} [Field Ω] (φ : MvPolynomial (Coord n) ℤ →+* Ω)
    (f : MvPolynomial (Coord n) ℤ) : aeval (fun v ↦ φ (X v)) f = φ f := by
  have h : (aeval (fun v ↦ φ (X v)) : _ →ₐ[ℤ] Ω).toRingHom = φ :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ by simp)
  exact congrArg (fun ψ : _ →+* _ ↦ ψ f) h

omit [Fintype ι] [DecidableEq ι] in

theorem mCoordIdeal_of_aeval_injective {Ω : Type} [Field Ω] (y : Coord n → Ω)
    (hy : Function.Injective (aeval y : MvPolynomial (Coord n) ℤ →ₐ[ℤ] Ω)) :
    Geo.mCoordIdeal (ι := blockIdx n) y = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun f hf ↦ hy ?_
  have h1 : (aeval (fun _ : ι ↦ (1 : Ω))).toRingHom.comp
      (Geo.mConeMap (ι := blockIdx n) y).toRingHom = (aeval y : _ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ by simp [Geo.mConeMap])
  have h2 := congrArg (fun φ : _ →+* _ ↦ φ f) h1
  have h3 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3, map_zero] at h2
  rw [← h2, map_zero]

def wholePoint : Coord n → (ArithVariety.whole n).FunField := fun v ↦ (ArithVariety.whole n).mkF (X v)

omit [Fintype ι] in
theorem mCoordIdeal_wholePoint :
    Geo.mCoordIdeal (ι := blockIdx n) (wholePoint n) = ⊥ :=
  mCoordIdeal_of_aeval_injective n _ fun f g h ↦ by
    have hf := aeval_of_hom n (ArithVariety.whole n).mkF f
    have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
    exact ArithVariety.whole_mkF_injective n (hf.symm.trans (h.trans hg))

theorem blockReading_whole (D : AddBlockData (ArithVariety.whole n)) :
    D.BlockReading (wholePoint n) D.elt where
  ideal_eq := (mCoordIdeal_wholePoint n).symm
  ext_eq := by
    have h : D.plusCoord (wholePoint n) D.elt = D.extVal := by
      funext v
      rcases v with ⟨_ | k, i⟩ <;> rfl
    rw [h, mCoordIdeal_eq_ker]
    rfl
  reads j g h _ _ _ _ _ := by
    have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
    have hh := aeval_of_hom n (ArithVariety.whole n).mkF h
    exact ⟨fun e ↦ hg.symm.trans (e.trans (congrArg _ hh)),
      fun e ↦ hg.trans (e.trans (congrArg _ hh.symm))⟩

omit [Fintype ι] in

theorem reads_wholePoint (a : ι → ℤ) (t : (ArithVariety.whole n).FunField) :
    (ArithVariety.whole n).Reads (wholePoint n) a t t := by
  intro g h _ _ _ _ _
  have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
  have hh := aeval_of_hom n (ArithVariety.whole n).mkF h
  exact ⟨fun e ↦ hg.symm.trans (e.trans (congrArg _ hh)),
    fun e ↦ hg.trans (e.trans (congrArg _ hh.symm))⟩

theorem whole_isArithVar (N : ℕ) :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ N) (ArithVariety.whole fun _ : Unit ↦ N).ideal (N + 1) :=
  ⟨inferInstance, ArithVariety.isMultiProjPrime _, ArithVariety.isHorizontal _, whole_ringKrullDim N⟩

theorem wholePoint_isArithVar (N : ℕ) :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ N)
      (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ N) (wholePoint fun _ : Unit ↦ N)) (N + 1) := by
  rw [mCoordIdeal_wholePoint]
  exact whole_isArithVar N

def unitPoint : Coord (fun _ : Unit ↦ 0) → ℚ := fun _ ↦ 1

theorem mCoordIdeal_unitPoint :
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint = ⊥ := by
  rw [mCoordIdeal_eq_ker]
  have h : (eval₂Hom (Int.castRingHom (MvPolynomial Unit ℚ)) fun v : Coord (fun _ : Unit ↦ 0) ↦
      C (unitPoint v) * X v.1) =
      (map (Int.castRingHom ℚ)).comp (rename (Sigma.fst : Coord (fun _ : Unit ↦ 0) → Unit)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ by simp [unitPoint])
  rw [h]
  refine (RingHom.injective_iff_ker_eq_bot _).mp ?_
  refine (map_injective _ Int.cast_injective).comp (rename_injective _ ?_)
  rintro ⟨a, i⟩ ⟨b, j⟩ _
  cases a
  cases b
  have hij : i = j := Subsingleton.elim (α := Fin 1) i j
  rw [hij]

theorem unitPoint_isArithVar :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ 0)
      (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) := by
  rw [mCoordIdeal_unitPoint]
  exact whole_isArithVar 0

theorem unitPoint_birational : Geo.Birational (ι := blockIdx fun _ : Unit ↦ 0) unitPoint := by
  have hC : ∀ a : ℤ, Geo.IsMultiHomog (ι := blockIdx fun _ : Unit ↦ 0)
      (C a : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) 0 := by
    intro a m hm k
    have hm0 : m = 0 := by
      by_contra h0
      exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h0)])
    simp [hm0]
  intro s
  refine ⟨0, C s.num, C (s.den : ℤ), hC _, hC _, ?_, ?_⟩
  · simp
  · have hv : ∀ a : ℤ, aeval unitPoint (C a : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) = (a : ℚ) :=
      fun a ↦ by rw [aeval_C]; simp
    rw [hv, hv]
    push_cast
    exact (Rat.mul_den_eq_num s).symm

theorem form_eq_zero_of_unitPoint {f : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ} {δ : Unit → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ 0) f δ) (h : aeval unitPoint f = 0) : f = 0 := by
  have hm : ∀ m ∈ f.support, m = Finsupp.single ⟨(), 0⟩ (δ ()) := by
    intro m hm
    have h1 := (geoMultiHomog_iff f δ).mpr hf m hm ()
    ext ⟨u, i⟩
    cases u
    have hi : i = 0 := Subsingleton.elim (α := Fin 1) i 0
    subst hi
    have h2 : ∑ i : Fin 1, m ⟨(), i⟩ = m ⟨(), 0⟩ := Fin.sum_univ_one _
    rw [Finsupp.single_eq_same, ← h2]
    exact h1
  by_contra h0
  have hs : f.support = {Finsupp.single ⟨(), 0⟩ (δ ())} := by
    obtain ⟨m, hmem⟩ := Finset.nonempty_of_ne_empty (mt support_eq_empty.mp h0)
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, hm⟩
    rw [← hm m hmem]
    exact hmem
  have hc : coeff (Finsupp.single ⟨(), 0⟩ (δ ())) f ≠ 0 :=
    mem_support_iff.mp (by rw [hs]; exact Finset.mem_singleton_self _)
  rw [aeval_def, eval₂_eq, hs, Finset.sum_singleton] at h
  simp only [unitPoint, one_pow, Finset.prod_const_one, mul_one] at h
  have h3 : ((coeff (Finsupp.single ⟨(), 0⟩ (δ ())) f : ℤ) : ℚ) = 0 := by simpa using h
  exact hc (by exact_mod_cast h3)

theorem reads_unitPoint :
    (ArithVariety.whole fun _ : Unit ↦ 0).Reads unitPoint (fun _ ↦ 1) 1
      ((ArithVariety.whole fun _ : Unit ↦ 0).mkF (X ⟨(), 0⟩)) := by
  intro g h δg δh hg hh hd
  have hXh : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ 0)
      ((X ⟨(), 0⟩ : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) * h) δg := by
    have h1 := (isWeightedHomogeneous_X ℤ (coordDeg fun _ : Unit ↦ 0) ⟨(), 0⟩).mul hh
    have hδ : coordDeg (fun _ : Unit ↦ 0) ⟨(), 0⟩ + δh = δg := by
      funext u
      cases u
      have h2 : (δg () : ℤ) = δh () + 1 := hd ()
      simp only [coordDeg, Pi.add_apply, Pi.single_eq_same]
      change 1 + δh () = δg ()
      omega
    rwa [hδ] at h1
  have hsub := hg.sub hXh
  have hval : aeval unitPoint (X ⟨(), 0⟩ : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) = 1 := by
    simp [unitPoint]
  constructor
  · intro e
    have h0 : g - X ⟨(), 0⟩ * h = 0 := form_eq_zero_of_unitPoint hsub (by
      rw [map_sub, map_mul, hval, e, one_mul, sub_self])
    rw [sub_eq_zero.mp h0, map_mul]
  · intro e
    have h0 : g = X ⟨(), 0⟩ * h := ArithVariety.whole_mkF_injective _ (by rw [e, map_mul])
    rw [h0, map_mul, hval, one_mul]

theorem unitPoint_generates :
    (∀ j : Fin (0 + 1), (fun _ ↦ (1 : ℚ)) j ∈ Geo.chartLat (ι := blockIdx fun _ : Unit ↦ 0) unitPoint 0 1) ∧
      ArakelovGeometry.KH.GeneratesOn (ι := blockIdx fun _ : Unit ↦ 0) unitPoint 0 (fun _ : Fin (0 + 1) ↦ (1 : ℚ)) := by
  refine ⟨fun j c _ ↦ by simp [one_mem], fun c _ ↦ ⟨fun _ ↦ 1, fun _ ↦ one_mem _, by simp⟩⟩

omit [Fintype ι] [DecidableEq ι] in
theorem monomialValues_zero [Fintype ι] {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    monomialValues y 0 = {1} := by
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have h0 : ∀ p, μ p = 0 := fun p ↦ by
      have := hμ p.1
      rw [Pi.zero_apply, Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  · rintro rfl
    exact ⟨0, fun k ↦ by simp, by simp⟩

omit [Fintype ι] [DecidableEq ι] in

theorem span_monomialValues_zero [Fintype ι] {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    Submodule.span ℤ (Set.range fun _ : Fin (0 + 1) ↦ (1 : Ω)) =
      Submodule.span ℤ (monomialValues y 0) := by
  rw [monomialValues_zero, Set.range_const]

theorem whole_one_normal (L : HermLine n) :
    (ArithVariety.whole n).IsNormalSection (L.pow 0).deg 1 ∧
      (ArithVariety.whole n).IsSmallFor (L.pow 0) 1 := by
  have hd : (L.pow 0).deg = 0 := by
    funext k
    simp [HermLine.pow]
  refine ⟨⟨⟨1, 1, 0, 0, isWeightedHomogeneous_one ℤ (coordDeg n), isWeightedHomogeneous_one ℤ (coordDeg n),
    fun k ↦ by simp [hd], (Ideal.ne_top_iff_one _).mp (ArithVariety.whole n).isPrime.ne_top, by simp⟩,
    fun c _ ↦ ?_⟩, ?_⟩
  · rw [hd]
    simp only [ArithVariety.chartPow, Pi.zero_apply, zpow_zero, Finset.prod_const_one, div_one]
    exact one_mem _
  · intro p q _ _ _ _ _ h z _
    have hpq : p = q := ArithVariety.whole_mkF_injective n (by rw [h, one_mul])
    rw [hpq]
    change _ ≤ _ * L.metric z ^ 0
    simp

omit [Fintype ι] in

theorem blockLine_conjInvariant [Fintype ι] (k₀ : ι) : (blockLine n k₀).ConjInvariant :=
  fun z _ ↦ vectorL2Norm_conj (z k₀)

theorem blockLine_inducesMetric (k₀ : ι) :
    (blockAddData n k₀).InducesMetric (wholePoint n) (blockAddData n k₀).elt (blockLine n k₀).toGeo
      (blockLine (blockAddData n k₀).extSizes none).toGeo := by
  set D := blockAddData n k₀ with hD
  intro j g m dg dm _ _ _ hgm z hz
  have hz' := hz
  have hg : g = m * X ⟨k₀, j⟩ := by
    have h1 := aeval_of_hom n (ArithVariety.whole n).mkF g
    have h2 := aeval_of_hom n (ArithVariety.whole n).mkF m
    refine ArithVariety.whole_mkF_injective n ?_
    rw [map_mul, ← h1, ← h2]
    exact hgm
  have hcross : ∀ i, z ⟨none, j⟩ * z ⟨some k₀, i⟩ = z ⟨none, i⟩ * z ⟨some k₀, j⟩ := by
    intro i
    have hmem : (X (D.newCoord j) * X (D.oldCoord ⟨k₀, i⟩) - X (D.newCoord i) * X (D.oldCoord ⟨k₀, j⟩) :
        MvPolynomial (Coord D.extSizes) ℤ) ∈ Geo.mCoordIdeal (ι := blockIdx D.extSizes)
          (D.plusCoord (wholePoint n) D.elt) := by
      rw [mCoordIdeal_eq_ker, RingHom.mem_ker]
      simp only [map_sub, map_mul, eval₂Hom_X']
      have hi : D.plusCoord (wholePoint n) D.elt (D.newCoord i) =
          D.plusCoord (wholePoint n) D.elt (D.oldCoord ⟨k₀, i⟩) := rfl
      have hj : D.plusCoord (wholePoint n) D.elt (D.newCoord j) =
          D.plusCoord (wholePoint n) D.elt (D.oldCoord ⟨k₀, j⟩) := rfl
      rw [hi, hj]
      simp only [AddBlockData.newCoord, AddBlockData.oldCoord]
      ring
    have := hz.2 _ hmem
    simpa [AddBlockData.newCoord, AddBlockData.oldCoord, sub_eq_zero] using this
  have hold : BlockNonzero (unflatCone (D.oldFlat z)) := by
    refine (blockNonzero_unflatCone_iff _).mpr fun k ↦ ?_
    obtain ⟨i, hi⟩ := hz.1 (some k)
    exact ⟨i, hi⟩
  have hnew : BlockNonzero (unflatCone z) := (blockNonzero_unflatCone_iff _).mpr hz.1
  rw [HermLine.toGeo_h_of_blockNonzero _ hold, HermLine.toGeo_h_of_blockNonzero _ hnew, hg]
  change _ * _ * l2Norm (fun i ↦ z ⟨some k₀, i⟩) =
    _ * l2Norm (fun i ↦ z ⟨none, i⟩)
  have hev : eval (D.oldFlat z) (map (Int.castRingHom ℂ) (m * X ⟨k₀, j⟩)) =
      eval (D.oldFlat z) (map (Int.castRingHom ℂ) m) * z ⟨some k₀, j⟩ := by
    simp [AddBlockData.oldFlat]
  rw [hev, norm_mul]
  have key : ‖z ⟨none, j⟩‖ * l2Norm (fun i ↦ z ⟨some k₀, i⟩) =
      ‖z ⟨some k₀, j⟩‖ * l2Norm (fun i ↦ z ⟨none, i⟩) := by
    have hs : (‖z ⟨none, j⟩‖ * l2Norm (fun i ↦ z ⟨some k₀, i⟩)) ^ 2 =
        (‖z ⟨some k₀, j⟩‖ * l2Norm (fun i ↦ z ⟨none, i⟩)) ^ 2 := by
      simp only [mul_pow, l2Norm]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← mul_pow, ← mul_pow, ← norm_mul, ← norm_mul, hcross i, mul_comm]
    exact (pow_left_inj₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) two_ne_zero).mp hs
  linear_combination ‖eval (D.oldFlat z) (map (Int.castRingHom ℂ) m)‖ * key

theorem isSupSmallBlock_one {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    [CharZero Ω] (y : Coord n' → Ω) (k₀ : κ) (A : Geo.HermLine (blockIdx n')) :
    (1 : Ω) ∈ Geo.secM (ι := blockIdx n') y (Pi.single k₀ 0) ∧ IsSupSmallBlock y k₀ A 0 1 := by
  have hz : ∀ f : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι := blockIdx n') f (Pi.single k₀ 0) →
      f = C (coeff 0 f) := by
    intro f hf
    ext m
    rw [coeff_C]
    split_ifs with h0
    · rw [h0]
    · by_contra hc
      refine h0 (Finsupp.ext fun p ↦ ?_).symm
      have h := hf m (mem_support_iff.mpr hc) p.1
      rw [Pi.single_zero, Pi.zero_apply, Finset.sum_eq_zero_iff] at h
      exact h p.2 (Finset.mem_univ _)
  constructor
  · refine Submodule.subset_span ⟨1, fun m hm k ↦ ?_, map_one _⟩
    have hm0 : m = 0 := by
      by_contra h0
      exact (mem_support_iff.mp hm) (by rw [← C_1, coeff_C, if_neg (Ne.symm h0)])
    simp [hm0]
  · intro f hf hs z _
    rw [hz f hf] at hs ⊢
    have h1 : coeff 0 f = 1 := by
      rw [aeval_C] at hs
      exact_mod_cast (by simpa using hs : ((coeff 0 f : ℤ) : Ω) = 1)
    simp [h1]

omit [Fintype ι] in

theorem isSmallH_one_wholePoint [Fintype ι] (N : Geo.HermLine (blockIdx n)) :
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) (wholePoint n)) (wholePoint n) N 0 1 := by
  intro dg dh g h z _ _ _ hy _
  have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
  have hh := aeval_of_hom n (ArithVariety.whole n).mkF h
  have hgh : g = h := ArithVariety.whole_mkF_injective n (by
    rw [one_mul] at hy; exact hg.symm.trans (hy.trans hh))
  subst hgh
  simp

theorem whole_isOfDegree_one : (ArithVariety.whole n).IsOfDegree 0 1 := by
  simpa [HermLine.pow] using (whole_one_normal n (HermLine.standard n)).1.degree

theorem whole_isOfDegree_X : (ArithVariety.whole fun _ : Unit ↦ 0).IsOfDegree (fun _ ↦ 1)
    ((ArithVariety.whole fun _ : Unit ↦ 0).mkF (X ⟨(), 0⟩)) := by
  refine ⟨X ⟨(), 0⟩, 1, fun _ ↦ 1, 0, ?_, isWeightedHomogeneous_one ℤ _, fun k ↦ by simp, ?_, by simp⟩
  · have := isWeightedHomogeneous_X ℤ (coordDeg fun _ : Unit ↦ 0) ⟨(), 0⟩
    convert this using 1
    funext u
    cases u
    simp [coordDeg]
  · exact (Ideal.ne_top_iff_one _).mp (ArithVariety.whole _).isPrime.ne_top

theorem monomialsBounded_zero (Q : Ideal (MvPolynomial (Coord n) ℤ)) :
    Geo.MonomialsBounded (ι := blockIdx n) Q ((HermLine.standard n).pow 0).toGeo 0 := by
  intro z hz μ hμ
  have h0 : ∀ p, μ p = 0 := fun p ↦ by
    have := hμ p.1
    rw [Pi.zero_apply, Finset.sum_eq_zero_iff] at this
    exact this p.2 (Finset.mem_univ _)
  have hz' : BlockNonzero (unflatCone z) := (blockNonzero_unflatCone_iff z).mpr hz.1
  rw [HermLine.toGeo_h_of_blockNonzero _ hz']
  simp [h0, HermLine.pow]

end Examples

end

end GroundTheory.Heights₂.Heights
