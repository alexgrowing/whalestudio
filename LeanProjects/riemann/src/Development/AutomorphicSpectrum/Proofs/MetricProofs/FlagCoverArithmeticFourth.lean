import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogProdInt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsNormalise
import GroundTheory.HeightsAndTheta.Heights.Intersections.AevalNeZeroOfNotMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.POrbitCompNonvanish
import GroundTheory.HeightsAndTheta.Heights.Intersections.Imports
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPts
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartSpecCount
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartPrimElt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocAwaySpec
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordRatioDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MCoordIdealCompLeImageZ
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.BaseCount

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]

theorem mConeMap_rename {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hv.2.2.1 n]

theorem imageZ_mCoordIdeal {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) : imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v) := by
  ext f
  show mConeMap y (rename v f) = 0 ↔ mConeMap (y ∘ v) f = 0
  rw [mConeMap_rename hv]
  exact (rename_injective κ hv.1).eq_iff' (map_zero _)

theorem mCoordIdeal_map {Ω₁ : Type} [Field Ω₁] (φ : Ω →+* Ω₁) (x : (Σ k, ι k) → Ω) :
    mCoordIdeal (fun q => φ (x q)) = mCoordIdeal x := by
  have key : ∀ g : MRing ι, mConeMap (fun q => φ (x q)) g = MvPolynomial.map φ (mConeMap x g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp]
      congr 1
      simp [mConeMap]
  ext f
  show mConeMap _ f = 0 ↔ mConeMap x f = 0
  rw [key]
  exact (MvPolynomial.map_injective φ φ.injective).eq_iff' (map_zero _)

theorem exists_isArithVar [CharZero Ω] [Nonempty K] (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∃ n : ℕ, IsArithVar (mCoordIdeal y) (n + 1) := by
  choose c hc using hy
  have hd := HilbertSamuel.CoordArithOfFnField.dim_eq y c hc
  have hle : ringKrullDim (MRing ι ⧸ mCoordIdeal y) ≤ ringKrullDim (MRing ι) :=
    ringKrullDim_quotient_le _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField, hd] at hle
  generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = e at hd hle
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    have h1 : (1 : WithBot ℕ∞) + (Nat.card (Σ k, ι k) : WithBot ℕ∞) =
        (((1 + Nat.card (Σ k, ι k) : ℕ) : ℕ∞) : WithBot ℕ∞) := by push_cast; rfl
    rw [h1, WithBot.coe_le_coe] at hle
    simp only [top_add] at hle
    exact ENat.natCast_ne_top _ (top_le_iff.1 hle)
  | coe n =>
    refine ⟨n, inferInstance, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal y,
      CoordinateConeArithVar.relevant y c hc⟩, CoordinateConeArithVar.horizontal y, ?_⟩
    rw [hd]
    norm_cast
    omega

theorem blockFnField_comp_le {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) [CharZero Ω]
    (y : (Σ k, ι' k) → Ω) : blockFnField (y ∘ v) ≤ blockFnField y := by
  rw [blockFnField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨p, q, hpq, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨v p, v q, by rw [hv.2.2.1, hv.2.2.1, hpq], rfl⟩

theorem isAlgebraic_of_relfinrank_pos {F E : Type} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} (h : A ≤ B) (hpos : 0 < IntermediateField.relfinrank A B) :
    ∀ t ∈ B, IsAlgebraic A t := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le h] at hpos
  haveI := Module.finite_of_finrank_pos hpos
  intro t ht
  have h1 : IsAlgebraic A (⟨t, ht⟩ : IntermediateField.extendScalars h) :=
    Algebra.IsAlgebraic.isAlgebraic _
  exact (isAlgebraic_algebraMap_iff (A := E) (algebraMap (IntermediateField.extendScalars h) E).injective).2 h1

theorem count_of_nonempty (hGood : Inter.GenericPointsAvoidBadLocus.Statement) (hChart : Targets.GenFibreChartDeg.Statement)
    [CharZero Ω] [Nonempty K] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hpos : 0 < IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)) :
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ D ∉ mCoordIdeal (y ∘ v) ∧
      ∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (Inter.ptsOverPt (mCoordIdeal y) v z).ncard =
          IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) := by
  have hne : ∀ k, ∃ i, (y ∘ v) ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hy (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    have hk : p.1 = k := hv.1 ((hv.2.2.1 p).symm.trans (congrArg Sigma.fst hp))
    subst hk
    refine ⟨p.2, ?_⟩
    show y (v ⟨p.1, p.2⟩) ≠ 0
    rw [Sigma.eta, hp]
    exact hi
  obtain ⟨n, hA⟩ := exists_isArithVar (y ∘ v) hne
  have halg := isAlgebraic_of_relfinrank_pos (blockFnField_comp_le hv y) hpos
  have hP' : IsArithVar (mCoordIdeal y) (n + 1) :=
    Cmp.isArithVar_of_isAlgebraic_image K ι K' ι' κ v Ω y (n + 1) hv hy hA halg
  have hI := imageZ_mCoordIdeal hv y
  obtain ⟨G⟩ := Targets.genFibreExists K ι K' ι' κ v (mCoordIdeal y) (n + 1) hv hP'
  have hx' : ∀ q, y q ≠ 0 → G.x' q ≠ 0 := by
    intro q hq h0
    have h1 : (X q : MRing ι') ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ') := by
      rw [RingHom.mem_ker, aeval_X, h0]
    rw [G.genericFibre_ker_target, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X] at h1
    exact mul_ne_zero (by rw [Ne, C_eq_zero]; exact hq) (X_ne_zero _) h1
  haveI : CharZero G.Φ' := by
    refine charZero_of_inj_zero fun m hm => ?_
    have h1 : (C (m : ℤ) : MRing ι') ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ') := by
      rw [RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes]
      simpa using hm
    rw [G.genericFibre_ker_target] at h1
    have h2 : (m : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι') := h1
    rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι') = ⊥ from CoordinateConeArithVar.horizontal y] at h2
    exact_mod_cast (Ideal.mem_bot).1 h2
  choose ci hci using hy
  choose c hc using hne
  have hi : ∀ k : FibreBlock κ, G.x' ⟨k.1, ci k.1⟩ ≠ 0 := fun k => hx' _ (hci k.1)
  have hcx : ∀ k, G.x ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    refine hx' (v ⟨k, c k⟩) (hc k) ?_
    rw [G.compat, h0, map_zero]
  have hA' : IsArithVar (imageZ v (mCoordIdeal y)) (n + 1) := by rw [hI]; exact hA
  obtain ⟨D, a, hD, hDn, hcount⟩ := hGood K ι K' ι' κ v (mCoordIdeal y) n G (fun k => ci k.1) hv hP' hA' hi
  refine ⟨D, a, hD, by rwa [hI] at hDn, fun z hz hnz => ?_⟩
  rw [← hI] at hz
  rw [hcount z hz hnz]
  exact (hChart K ι K' ι' κ v (mCoordIdeal y) G c (fun k => ci k.1) hv
    (CoordinateConeArithVar.isMultiHomogIdeal y) hcx hi).trans
    (Targets.CoordRatioDeg.proof K ι K' ι' κ v Ω y G.Φ' G.x' hv G.genericFibre_ker_target)

section Dummy

abbrev SingletonBlock : Unit → Type := fun _ => Unit

def addOne {R : Type} [One R] (y : (Σ k, ι' k) → R) : (Σ k, Sum.elim ι' SingletonBlock k) → R
  | ⟨Sum.inl k, i⟩ => y ⟨k, i⟩
  | ⟨Sum.inr _, _⟩ => 1

theorem addOne_inlV {R : Type} [One R] (y : (Σ k, ι' k) → R) :
    addOne y ∘ (inlV (ι := ι') (ι₂ := SingletonBlock)) = y := funext fun _ => rfl

theorem addOne_inrV {R : Type} [One R] (y : (Σ k, ι' k) → R) :
    addOne y ∘ (inrV (ι := ι') (ι₂ := SingletonBlock)) = fun _ => 1 := funext fun _ => rfl

theorem blockFnField_addOne [CharZero Ω] (y : (Σ k, ι' k) → Ω) : blockFnField (addOne y) = blockFnField y := by
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | u, i⟩, ⟨k' | u', i'⟩, hpq, rfl⟩
    · obtain rfl : k = k' := Sum.inl_injective hpq
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · show (1 : Ω) / 1 ∈ blockFnField y
      rw [div_one]
      exact one_mem _
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, ⟨k', i'⟩, hpq, rfl⟩
    obtain rfl : k = k' := hpq
    exact IntermediateField.subset_adjoin _ _ ⟨⟨Sum.inl k, i⟩, ⟨Sum.inl k, i'⟩, rfl, rfl⟩

theorem blockFnField_one [CharZero Ω] :
    blockFnField (ι := SingletonBlock) (fun _ => (1 : Ω)) = ⊥ := by
  rw [eq_bot_iff, blockFnField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨p, q, -, rfl⟩
  show (1 : Ω) / 1 ∈ (⊥ : IntermediateField ℚ Ω)
  rw [div_one]
  exact one_mem _

theorem blockFnField_of_isEmpty [CharZero Ω] [IsEmpty K] (w : (Σ k, ι k) → Ω) : blockFnField w = ⊥ := by
  rw [eq_bot_iff, blockFnField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨p, -, -, -⟩
  exact isEmptyElim p.1

theorem comp_inlV_mem {y : (Σ k, ι' k) → Ω} {z : (Σ k, Sum.elim ι' SingletonBlock k) → ℂ}
    (h : z ∈ mcPts (mCoordIdeal (addOne y))) :
    z ∘ inlV (ι := ι') (ι₂ := SingletonBlock) ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => h.1 (Sum.inl k), fun f hf => ?_⟩
  have hI := imageZ_mCoordIdeal (isBlockMap_inl (ι := ι') (ι₂ := SingletonBlock)) (addOne y)
  rw [addOne_inlV] at hI
  rw [← hI] at hf
  have h1 := h.2 _ (show rename inlV f ∈ mCoordIdeal (addOne y) from hf)
  rwa [map_rename, eval_rename] at h1

theorem addOne_mem {y : (Σ k, ι' k) → Ω} {z : (Σ k, ι' k) → ℂ} (h : z ∈ mcPts (mCoordIdeal y)) :
    addOne z ∈ mcPts (mCoordIdeal (addOne y)) := by
  refine ⟨?_, fun f hf => ?_⟩
  · rintro (k | u)
    · exact h.1 k
    · exact ⟨(), one_ne_zero⟩
  · let ρ : MRing (Sum.elim ι' SingletonBlock) →ₐ[ℤ] MRing ι' := aeval (addOne fun q => (X q : MRing ι'))
    let τ : MvPolynomial (K' ⊕ Unit) Ω →+* MvPolynomial K' Ω :=
      (aeval (Sum.elim X fun _ => 1) : MvPolynomial (K' ⊕ Unit) Ω →ₐ[Ω] MvPolynomial K' Ω).toRingHom
    have key : ∀ g, mConeMap y (ρ g) = τ (mConeMap (addOne y) g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [mConeMap, ρ, τ]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p n hp =>
        simp only [map_mul, hp]
        congr 1
        obtain ⟨k | u, i⟩ := n
        · simp [mConeMap, ρ, τ, addOne]
        · simp [mConeMap, ρ, τ, addOne]
    have key2 : ∀ g : MRing (Sum.elim ι' SingletonBlock), eval (addOne z) (map (Int.castRingHom ℂ) g) =
        eval z (map (Int.castRingHom ℂ) (ρ g)) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [ρ]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p n hp =>
        simp only [map_mul, hp]
        congr 1
        obtain ⟨k | u, i⟩ := n
        · simp [ρ, addOne]
        · simp [ρ, addOne]
    rw [key2]
    refine h.2 _ ?_
    show mConeMap y (ρ f) = 0
    rw [key, show mConeMap (addOne y) f = 0 from hf, map_zero]

theorem sameOrbit_comp_inlV {z w : (Σ k, Sum.elim ι' SingletonBlock k) → ℂ} (h : SameOrbit z w) :
    SameOrbit (z ∘ inlV (ι := ι') (ι₂ := SingletonBlock)) (w ∘ inlV) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (Sum.inl k), fun k => hc _, rfl⟩

theorem image_orbit (z : (Σ k, Sum.elim ι' SingletonBlock k) → ℂ) :
    (fun w => w ∘ inlV (ι := ι') (ι₂ := SingletonBlock)) '' {w | SameOrbit w z} =
      {w | SameOrbit w (z ∘ inlV (ι := ι') (ι₂ := SingletonBlock))} := by
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact sameOrbit_comp_inlV hw'
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun p => Sum.elim c (fun _ => 1) p.1 * z p, ⟨Sum.elim c (fun _ => 1), ?_, rfl⟩, rfl⟩
    rintro (k | u)
    · exact hc k
    · exact one_ne_zero

theorem sameOrbit_of_comp_inlV {z w : (Σ k, Sum.elim ι' SingletonBlock k) → ℂ}
    (hz : ∀ u, ∃ i, z ⟨Sum.inr u, i⟩ ≠ 0) (hw : ∀ u, ∃ i, w ⟨Sum.inr u, i⟩ ≠ 0)
    (h : SameOrbit (z ∘ inlV (ι := ι') (ι₂ := SingletonBlock)) (w ∘ inlV)) : SameOrbit z w := by
  obtain ⟨c, hc, he⟩ := h
  have hz' : z ⟨Sum.inr (), ()⟩ ≠ 0 := by
    obtain ⟨⟨⟩, h⟩ := hz ()
    exact h
  have hw' : w ⟨Sum.inr (), ()⟩ ≠ 0 := by
    obtain ⟨⟨⟩, h⟩ := hw ()
    exact h
  refine ⟨Sum.elim c fun _ => z ⟨Sum.inr (), ()⟩ / w ⟨Sum.inr (), ()⟩, ?_, ?_⟩
  · rintro (k | u)
    · exact hc k
    · exact div_ne_zero hz' hw'
  · funext p
    obtain ⟨k | u, i⟩ := p
    · exact congrFun he ⟨k, i⟩
    · obtain ⟨⟩ := u
      obtain ⟨⟩ := i
      show z ⟨Sum.inr (), ()⟩ = z ⟨Sum.inr (), ()⟩ / w ⟨Sum.inr (), ()⟩ * w ⟨Sum.inr (), ()⟩
      rw [div_mul_cancel₀ _ hw']

theorem sameOrbit_of_isEmpty [IsEmpty K] (z w : (Σ k, ι k) → ℂ) : SameOrbit z w :=
  ⟨fun _ => 1, fun _ => one_ne_zero, funext fun p => isEmptyElim p.1⟩

theorem ncard_ptsOverPt_addOne [IsEmpty K] (v : (Σ k, ι k) → Σ k, ι' k) (y : (Σ k, ι' k) → Ω)
    (z : (Σ k, ι k) → ℂ) :
    (Inter.ptsOverPt (mCoordIdeal (addOne y)) (inrV (ι := ι') (ι₂ := SingletonBlock)) fun _ => 1).ncard =
      (Inter.ptsOverPt (mCoordIdeal y) v z).ncard := by
  refine Set.ncard_congr (fun O _ => (fun w => w ∘ inlV (ι := ι') (ι₂ := SingletonBlock)) '' O) ?_ ?_ ?_
  · rintro O ⟨z₁, hz₁, rfl, -⟩
    exact ⟨z₁ ∘ inlV, comp_inlV_mem hz₁, image_orbit z₁, sameOrbit_of_isEmpty _ _⟩
  · rintro _ _ ⟨z₁, hz₁, rfl, -⟩ ⟨z₂, hz₂, rfl, -⟩ h
    have h' : {w | SameOrbit w (z₁ ∘ inlV (ι := ι') (ι₂ := SingletonBlock))} =
        {w | SameOrbit w (z₂ ∘ inlV (ι := ι') (ι₂ := SingletonBlock))} := by
      rw [← image_orbit, ← image_orbit]
      exact h
    have h1 : SameOrbit (z₁ ∘ inlV (ι := ι') (ι₂ := SingletonBlock)) (z₂ ∘ inlV) := by
      have : z₁ ∘ inlV (ι := ι') (ι₂ := SingletonBlock) ∈ {w | SameOrbit w (z₁ ∘ inlV (ι := ι') (ι₂ := SingletonBlock))} :=
        Cj.sameOrbit_refl _
      rw [h'] at this
      exact this
    have h2 := sameOrbit_of_comp_inlV (fun u => hz₁.1 (Sum.inr u)) (fun u => hz₂.1 (Sum.inr u)) h1
    ext w
    exact ⟨fun hw => Cj.sameOrbit_trans hw h2, fun hw => Cj.sameOrbit_trans hw (Cj.sameOrbit_symm h2)⟩
  · rintro O ⟨z', hz', rfl, -⟩
    refine ⟨_, ⟨addOne z', addOne_mem hz', rfl, ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩⟩, ?_⟩
    · funext p
      simp [inrV, addOne]
    · show _ '' _ = _
      rw [image_orbit, addOne_inlV]

theorem aeval_one_eq {σ R : Type} [CommRing R] (f : MvPolynomial σ ℤ) :
    aeval (fun _ => (1 : R)) f = ((eval (fun _ => (1 : ℤ)) f : ℤ) : R) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

theorem one_mem_mcPts [CharZero Ω] :
    (fun _ => (1 : ℂ)) ∈ mcPts (mCoordIdeal (ι := SingletonBlock) (fun _ => (1 : Ω))) := by
  refine ⟨fun _ => ⟨(), one_ne_zero⟩, fun f hf => ?_⟩
  have hcone : ∀ g : MRing SingletonBlock, aeval (fun _ => (1 : Ω)) (mConeMap (ι := SingletonBlock) (fun _ => (1 : Ω)) g) =
      aeval (fun _ => (1 : Ω)) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp]
      simp [mConeMap]
  have h1 : aeval (fun _ => (1 : Ω)) f = 0 := by
    rw [← hcone, show mConeMap _ f = 0 from hf, map_zero]
  rw [aeval_one_eq] at h1
  have h2 : eval (fun _ => (1 : ℤ)) f = 0 := by exact_mod_cast h1
  have h3 : eval (fun _ => (1 : ℂ)) (map (Int.castRingHom ℂ) f) = aeval (fun _ => (1 : ℂ)) f := by
    rw [aeval_def, eval_map]
    rfl
  rw [h3, aeval_one_eq, h2]
  simp

theorem eval_one_ne_zero {D : MRing SingletonBlock} {a : Unit → ℕ} (hD : IsMultiHomog D a) (h0 : D ≠ 0) :
    eval (fun _ => (1 : ℂ)) (map (Int.castRingHom ℂ) D) ≠ 0 := by
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.support_nonempty.2 h0
  have huniq : ∀ m ∈ D.support, m = m₀ := by
    intro m hm
    have h1 := hD m hm ()
    have h2 := hD m₀ hm₀ ()
    simp only [Finset.univ_unique, Finset.sum_singleton] at h1 h2
    ext ⟨⟨⟩, ⟨⟩⟩
    exact h1.trans h2.symm
  have hD' : D = monomial m₀ (coeff m₀ D) := by
    ext m
    rw [coeff_monomial]
    split_ifs with e
    · rw [e]
    · by_contra hc
      exact e (huniq m (mem_support_iff.2 hc)).symm
  have hc : coeff m₀ D ≠ 0 := mem_support_iff.1 hm₀
  rw [hD', map_monomial, eval_monomial]
  simpa using hc

theorem count_of_isEmpty (hGood : Inter.GenericPointsAvoidBadLocus.Statement) (hChart : Targets.GenFibreChartDeg.Statement)
    [CharZero Ω] [IsEmpty K] {v : (Σ k, ι k) → Σ k, ι' k}
    (y : (Σ k, ι' k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hpos : 0 < IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)) :
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ D ∉ mCoordIdeal (y ∘ v) ∧
      ∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (Inter.ptsOverPt (mCoordIdeal y) v z).ncard =
          IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) := by
  have e1 : blockFnField (addOne y ∘ inrV (ι := ι') (ι₂ := SingletonBlock)) = blockFnField (y ∘ v) := by
    rw [addOne_inrV, blockFnField_one, blockFnField_of_isEmpty]
  have hy₁ : ∀ k, ∃ i, addOne y ⟨k, i⟩ ≠ 0 := by
    rintro (k | u)
    · exact hy k
    · exact ⟨(), one_ne_zero⟩
  obtain ⟨D, a, hD, hDn, hc⟩ := count_of_nonempty hGood hChart (K := Unit) (ι := SingletonBlock)
    (isBlockMap_inr (ι := ι') (ι₂ := SingletonBlock)) (addOne y) hy₁ (by rwa [e1, blockFnField_addOne])
  have hD0 : D ≠ 0 := fun h => hDn (h ▸ Ideal.zero_mem _)
  have h1 : (fun _ => (1 : ℂ)) ∈ mcPts (mCoordIdeal (addOne y ∘ inrV (ι := ι') (ι₂ := SingletonBlock))) := by
    rw [addOne_inrV]
    exact one_mem_mcPts
  have h2 := hc _ h1 (eval_one_ne_zero hD hD0)
  refine ⟨1, fun _ => 0, fun m _ k => isEmptyElim k, fun h => ?_, fun z _ _ => ?_⟩
  · have h3 : mConeMap (y ∘ v) (1 : MRing ι) = 0 := h
    rw [map_one] at h3
    exact one_ne_zero h3
  · rw [← ncard_ptsOverPt_addOne v y z, h2, e1, blockFnField_addOne]

end Dummy

theorem generic_points_good_for_intersection : Inter.GenericPointsAvoidBadLocus.Statement :=
  Inter.GenericPointsAvoidBadLocus.proof (Inter.GenericPointsInAffineChart.proof Inter.ArithmeticIntersectionChartFinite.proof
    (Inter.ChartNormCount.proof (Inter.ChartSpecCount.proof Inter.ChartPrimElt.proof Inter.LocAwaySpec.proof)
      Inter.ChartNormPts.proof) Inter.OrbitCompNonvanish.proof)

theorem genFibreChartDeg : Targets.GenFibreChartDeg.Statement :=
  Targets.GenFibreChartDeg.proof Inter.ChartScalingIndep.proof Inter.AdjoinIndepRelfinrank.proof

theorem base_count : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a ∧ D ∉ mCoordIdeal M.x ∧ ∀ zb ∈ mcPts (mCoordIdeal M.x), eval zb (map (Int.castRingHom ℂ) D) ≠ 0 → (GroundTheory.Heights₂.Heights.Inter.ptsOverPt (mCoordIdeal M'.x) Cv.v zb).ncard = Cv.deg := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _
  have hb : mCoordIdeal (M'.x ∘ Cv.v) = mCoordIdeal M.x := by
    have : M'.x ∘ Cv.v = fun q => Cv.φ (M.x q) := funext Cv.x_eq
    rw [this, mCoordIdeal_map]
  rw [← hb]
  rcases isEmpty_or_nonempty (NonPluckerBlocks M.blk) with h | h
  · exact count_of_isEmpty generic_points_good_for_intersection genFibreChartDeg M'.x M'.x_ne Cv.deg_pos
  · exact count_of_nonempty generic_points_good_for_intersection genFibreChartDeg Cv.block M'.x M'.x_ne
      Cv.deg_pos

end GlobalTheory.CompanionTheory.Ar.PB.BaseCount
