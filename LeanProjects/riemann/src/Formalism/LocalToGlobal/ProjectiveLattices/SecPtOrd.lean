import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

noncomputable section

open IsLocalRing Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace Formalism.L2.Pj

section VV

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

private theorem valV_unit_lemma (u : Vˣ) :
    IsDedekindDomain.HeightOneSpectrum.valuation F (IsDiscreteValuationRing.maximalIdeal V)
      (algebraMap V F (u : V)) = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hu : (u : V) ∉ (IsDiscreteValuationRing.maximalIdeal V).asIdeal := fun h =>
    (IsLocalRing.mem_maximalIdeal _).mp h u.isUnit
  first
  | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff _).mpr hu
  | exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hu
  | exact le_antisymm (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)
      (not_lt.mp fun h => hu ((IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mp h))
  | simpa using hu

private theorem valV_unif_lemma_2 {ϖ : V} (hϖ : Irreducible ϖ) :
    IsDedekindDomain.HeightOneSpectrum.valuation F (IsDiscreteValuationRing.maximalIdeal V)
      (algebraMap V F ϖ) = WithZero.exp (-1 : ℤ) := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hspan : (IsDiscreteValuationRing.maximalIdeal V).asIdeal = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  first
  | exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hspan
  | simpa using IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hspan

lemma vV_unit_alg (u : Vˣ) : vV V (algebraMap V F (u : V)) = 0 := by
  unfold vV valV
  rw [valV_unit_lemma]
  simp

lemma vV_unif_alg {ϖ : V} (hϖ : Irreducible ϖ) : vV V (algebraMap V F ϖ) = 1 := by
  unfold vV valV
  rw [valV_unif_lemma_2 hϖ]
  simp

lemma vV_pow_gen {x : F} (hx : x ≠ 0) (k : ℕ) : vV V (x ^ k) = k * vV V x := by
  unfold vV valV
  rw [map_pow]
  first
  | rw [WithZero.log_pow, nsmul_eq_mul]; ring
  | rw [WithZero.log_pow]; ring
  | simp [WithZero.log_pow]

lemma vV_alg_of_addVal {v : V} {k : ℕ} (hk : IsDiscreteValuationRing.addVal V v = k) :
    vV V (algebraMap V F v) = k := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hk
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hϖ
  have hn : n = k := by
    rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl] at hk
    exact_mod_cast hk
  subst hn
  unfold vV valV
  rw [map_mul, map_pow, map_mul, map_pow, valV_unit_lemma, valV_unif_lemma_2 hϖ, one_mul]
  simp

end VV

section Cover

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}

theorem isLocalization_unif (h : IsUnif A ϖ) :
    IsLocalization.Away (algebraMap O ↥(As O A) ϖ) A := by
  constructor
  constructor
  · first
    | (rintro ⟨_, n, rfl⟩; rw [map_pow]; exact h.isUnit.pow n)
    | (rintro _ ⟨n, rfl⟩; rw [map_pow]; exact h.isUnit.pow n)
  · intro x
    obtain ⟨n, hn⟩ := h.denom x
    refine ⟨⟨⟨ϖ ^ n • x, hn⟩, ⟨_, n, rfl⟩⟩, ?_⟩
    first
    | simp [Algebra.smul_def, mul_comm]
    | (show x * (algebraMap O A ϖ) ^ n = ϖ ^ n • x
       rw [Algebra.smul_def, map_pow, mul_comm])
  · intro a b hab
    refine ⟨1, ?_⟩
    rw [Subtype.ext hab]

variable (ζ : Pts O A) [IsDVRAt ζ]
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [Algebra V F]
  [IsFractionRing V F] (ι : Loc ζ →+* V)

def locMap : ↥(As O A) →+* F := (algebraMap V F).comp (ι.comp (algebraMap ↥(As O A) (Loc ζ)))

def AddValPres : Prop :=
  ∀ r : Loc ζ, IsDiscreteValuationRing.addVal V (ι r) = IsDiscreteValuationRing.addVal (Loc ζ) r

variable {ζ ι}

lemma vV_locMap (hι : AddValPres ζ ι) {a : ↥(As O A)} {k : ℕ} (hk : vL ζ a = k) :
    vV V (locMap ζ F ι a) = k := by
  show vV V (algebraMap V F (ι (algebraMap _ (Loc ζ) a))) = k
  exact vV_alg_of_addVal (by rw [hι, ← vL_eq_addVal, hk])

lemma locMap_ne_zero (hι : AddValPres ζ ι) {a : ↥(As O A)} (ha : vL ζ a ≠ ⊤) : locMap ζ F ι a ≠ 0 := by
  intro h0
  apply ha
  have h1 : ι (algebraMap _ (Loc ζ) a) = 0 := by
    have h0' : algebraMap V F (ι (algebraMap _ (Loc ζ) a)) = 0 := h0
    exact IsFractionRing.injective V F (by rw [h0', map_zero])
  rw [vL_eq_addVal, ← hι, h1, IsDiscreteValuationRing.addVal_zero]

lemma locMap_eq_zero {a : ↥(As O A)} (ha : vL ζ a = ⊤) : locMap ζ F ι a = 0 := by
  rw [vL_eq_addVal, IsDiscreteValuationRing.addVal_eq_top_iff] at ha
  show algebraMap V F (ι (algebraMap _ (Loc ζ) a)) = 0
  rw [ha, map_zero, map_zero]

lemma locMap_unif_ne (h : IsUnif A ϖ) (hι : AddValPres ζ ι) : locMap ζ F ι (algebraMap O ↥(As O A) ϖ) ≠ 0 := by
  apply locMap_ne_zero (F := F) hι
  rw [vL_eq_addVal]
  intro htop
  rw [IsDiscreteValuationRing.addVal_eq_top_iff] at htop
  obtain ⟨⟨s, hs⟩, hs0⟩ := (IsLocalization.map_eq_zero_iff ζ.asIdeal.primeCompl (Loc ζ) _).mp htop
  apply hs
  have hs0' : (s : A) * algebraMap O A ϖ = 0 := by
    have := congrArg Subtype.val hs0
    simpa using this
  have hs1 : s = 0 := Subtype.ext ((h.isUnit.mul_left_eq_zero).mp hs0')
  rw [hs1]
  exact Ideal.zero_mem _

variable (ζ ι)

def phiAt (h : IsUnif A ϖ) (hι : AddValPres ζ ι) : A →+* F :=
  letI := isLocalization_unif h
  IsLocalization.Away.lift (algebraMap O ↥(As O A) ϖ) (g := locMap ζ F ι) (IsUnit.mk0 _ (locMap_unif_ne (F := F) h hι))

variable {ζ ι}

theorem phiAt_coe (h : IsUnif A ϖ) (hι : AddValPres ζ ι) (a : ↥(As O A)) :
    phiAt ζ F ι h hι (a : A) = locMap ζ F ι a := by
  letI := isLocalization_unif h
  unfold phiAt
  first
  | exact IsLocalization.lift_eq _ a
  | exact IsLocalization.Away.lift_eq _ _ a
  | simp [IsLocalization.Away.lift]

private theorem vV_mul_lemma_4 {V₁ F₁ : Type} [CommRing V₁] [IsDomain V₁] [IsDiscreteValuationRing V₁]
    [Field F₁] [Algebra V₁ F₁] [IsFractionRing V₁ F₁] {x y : F₁} (hx : x ≠ 0) (hy : y ≠ 0) :
    vV V₁ (x * y) = vV V₁ x + vV V₁ y := by
  unfold vV valV
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
  ring

private theorem toE_ordAt_lemma_3 (h : IsUnif A ϖ) (hι : AddValPres ζ ι) (x : A) (m : ℕ) (a : ↥(As O A))
    (ha : (a : A) = ϖ ^ m • x) :
    toE (ordAt ϖ ζ m a) = nval V 1 (phiAt ζ F ι h hι x) := by
  have hu : locMap ζ F ι (algebraMap O ↥(As O A) ϖ) ≠ 0 := locMap_unif_ne (F := F) h hι
  have hkey : locMap ζ F ι (algebraMap O ↥(As O A) ϖ) ^ m * phiAt ζ F ι h hι x = locMap ζ F ι a := by
    rw [← phiAt_coe (F := F) h hι a, ha, Algebra.smul_def, map_mul]
    simp only [map_pow]
    rw [← phiAt_coe (F := F) h hι (algebraMap O ↥(As O A) ϖ)]
    rfl
  by_cases hT : vL ζ a = ⊤
  · have h0 : phiAt ζ F ι h hι x = 0 := by
      have h1 := hkey
      rw [locMap_eq_zero (F := F) hT] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hu)
    unfold nval
    rw [if_pos h0]
    unfold ordAt
    rw [hT]
    first
    | rfl
    | simp [toE]
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hT
    have hla : locMap ζ F ι a ≠ 0 := locMap_ne_zero (F := F) hι hT
    have hφ : phiAt ζ F ι h hι x ≠ 0 := by
      intro h0
      apply hla
      rw [← hkey, h0, mul_zero]
    have hϖT : vL ζ (algebraMap O ↥(As O A) ϖ) ≠ ⊤ := fun ht => hu (locMap_eq_zero (F := F) ht)
    have hvu : vV V (locMap ζ F ι (algebraMap O ↥(As O A) ϖ)) =
        ((vL ζ (algebraMap O ↥(As O A) ϖ)).toNat : ℤ) :=
      vV_locMap (F := F) hι (ENat.coe_toNat hϖT).symm
    have hva : vV V (locMap ζ F ι a) = k := vV_locMap (F := F) hι hk.symm
    have hv : (m : ℤ) * ((vL ζ (algebraMap O ↥(As O A) ϖ)).toNat : ℤ) + vV V (phiAt ζ F ι h hι x) = k := by
      rw [← hva, ← hkey, vV_mul_lemma_4 (V₁ := V) (pow_ne_zero _ hu) hφ, vV_pow_gen (V := V) hu, hvu]
    have hz : vV V (phiAt ζ F ι h hι x) = (k : ℤ) - m * (ep ϖ ζ : ℤ) := by
      unfold ep
      linarith
    have hord : ordAt ϖ ζ m a = (((k : ℤ) - m * (ep ϖ ζ : ℤ) : ℤ) : WithTop ℤ) := by
      unfold ordAt
      rw [← hk, sub_eq_add_neg, WithTop.coe_add]
      congr 1
    unfold nval
    rw [if_neg hφ, hord, hz]
    first
    | (show ((((k : ℤ) - m * (ep ϖ ζ : ℤ) : ℤ) : ℝ) : EReal) = _
       rw [Nat.cast_one, div_one])
    | simp [toE]
    | rfl

theorem toE_ord_eq (h : IsUnif A ϖ) (hι : AddValPres ζ ι) (x : A) :
    toE (ord ϖ ζ x) = nval V 1 (phiAt ζ F ι h hι x) := by
  have hex : ∃ n : ℕ, ϖ ^ n • x ∈ As O A := h.denom x
  unfold ord
  rw [dif_pos hex]
  exact toE_ordAt_lemma_3 (F := F) h hι x _ _ rfl

end Cover

end Formalism.L2.Pj
