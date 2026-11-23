import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.HasseKpAlgebraMapKl
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IsIntegralOfAll

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def PublishedIntClos : Prop :=
  ∀ (O K A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [CharZero K] [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A]
    [FiniteDimensional K A] [IsReduced A],
    Module.Finite O ↥(As O A) ∧ ∀ ζ : Pts O A, IsDVRAt ζ

private theorem inj_lemma (K A : Type) [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
    [IsReduced A] (x : A) (hx : ∀ M : MaximalSpectrum A, x ∈ M.asIdeal) : x = 0 := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have h : IsNilpotent x := by
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    haveI := hJ
    exact hx ⟨J, IsArtinianRing.isMaximal_of_isPrime J⟩
  exact h.eq_zero

private theorem idem_lemma_2 (K A : Type) [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
    (I : MaximalSpectrum A) : ∃ e : A, Ideal.Quotient.mk I.asIdeal e = 1 ∧
      ∀ J : MaximalSpectrum A, J ≠ I → Ideal.Quotient.mk J.asIdeal e = 0 := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hb : ∀ J : MaximalSpectrum A, J ≠ I →
      ∃ b : A, b ∈ J.asIdeal ∧ Ideal.Quotient.mk I.asIdeal b = 1 := by
    intro J hJ
    have hsup : I.asIdeal ⊔ J.asIdeal = ⊤ := by
      by_contra h
      have h1 : I.asIdeal = I.asIdeal ⊔ J.asIdeal := I.isMaximal.eq_of_le h le_sup_left
      have h2 : J.asIdeal ≤ I.asIdeal := le_sup_right.trans h1.ge
      exact hJ (MaximalSpectrum.ext (J.isMaximal.eq_of_le I.isMaximal.ne_top h2))
    have h1 : (1 : A) ∈ I.asIdeal ⊔ J.asIdeal := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    refine ⟨b, hb, ?_⟩
    have hb' : b = 1 - a := by rw [← hab]; ring
    rw [hb', map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr ha, sub_zero]
  choose! b hbJ hbI using hb
  refine ⟨∏ J ∈ Finset.univ.filter (fun J => J ≠ I), b J, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun J hJ => hbI J (Finset.mem_filter.mp hJ).2
  · intro J hJ
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hmem : J ∈ Finset.univ.filter (fun J => J ≠ I) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b hmem
    rw [hc]
    exact Ideal.mul_mem_right _ _ (hbJ J hJ)

private theorem fld_lemma_3 (O K A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CharZero K] [CommRing A] [Algebra K A] [Algebra O A]
    [IsScalarTower O K A] [FiniteDimensional K A] (M : Ideal A) [M.IsMaximal] :
    Module.Finite O ↥(integralClosure O (A ⧸ M)) ∧ IsDedekindDomain ↥(integralClosure O (A ⧸ M)) ∧
      ¬IsField ↥(integralClosure O (A ⧸ M)) := by
  letI : Field (A ⧸ M) := Ideal.Quotient.field M
  haveI : FiniteDimensional K (A ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  haveI : Algebra.IsSeparable K (A ⧸ M) := inferInstance
  refine ⟨IsIntegralClosure.finite O K (A ⧸ M) (integralClosure O (A ⧸ M)),
    IsIntegralClosure.isDedekindDomain O K (A ⧸ M) (integralClosure O (A ⧸ M)), ?_⟩
  intro h
  apply IsDiscreteValuationRing.not_isField O
  refine isField_of_isIntegral_of_isField ?_ h
  intro a b hab
  have hinj : Function.Injective (algebraMap O (A ⧸ M)) := by
    rw [IsScalarTower.algebraMap_eq O K (A ⧸ M)]
    exact (algebraMap K (A ⧸ M)).injective.comp (IsFractionRing.injective O K)
  exact hinj (congrArg Subtype.val hab)

set_option maxHeartbeats 800000 in

private theorem dvr_lemma_4 (Cr Dr : Type) [CommRing Cr] [CommRing Dr] [IsDomain Dr] [IsDedekindDomain Dr]
    (hD : ¬IsField Dr) (φ : Cr →+* Dr) (hφ : Function.Surjective φ) (e : Cr) (he1 : φ e = 1)
    (he0 : ∀ c, φ c = 0 → e * c = 0) (Pm : Ideal Cr) [Pm.IsMaximal] (heP : e ∉ Pm) :
    ∃ _ : IsDomain (Localization.AtPrime Pm), IsDiscreteValuationRing (Localization.AtPrime Pm) := by
  classical
  have hP : Pm.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  have hker : RingHom.ker φ ≤ Pm := by
    intro c hc
    have h0 : e * c ∈ Pm := by rw [he0 c (RingHom.mem_ker.mp hc)]; exact Pm.zero_mem
    exact (hP.mem_or_mem h0).resolve_left heP
  haveI hQ : (Pm.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hker
  have hcomap : (Pm.map φ).comap φ = Pm := by
    rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hker
  have hnotin : ∀ s : Cr, s ∉ Pm → φ s ∉ Pm.map φ := by
    intro s hs h
    apply hs
    rw [← hcomap]
    exact Ideal.mem_comap.mpr h
  have hQ0 : Pm.map φ ≠ ⊥ := by
    intro hQb
    apply hD
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {d} hd => ?_⟩
    obtain ⟨c, rfl⟩ := hφ d
    have hc : c ∉ Pm := by
      intro hcP
      apply hd
      have h1 : φ c ∈ Pm.map φ := Ideal.mem_map_of_mem φ hcP
      rw [hQb] at h1
      exact Ideal.mem_bot.mp h1
    obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv inferInstance hc
    refine ⟨φ y, ?_⟩
    have hφi : φ i = 0 := by
      have h1 : φ i ∈ Pm.map φ := Ideal.mem_map_of_mem φ hi
      rw [hQb] at h1
      exact Ideal.mem_bot.mp h1
    have h2 := congrArg φ hyi
    rw [map_add, map_mul, hφi, add_zero, map_one] at h2
    rw [mul_comm]
    exact h2
  let LQ := Localization.AtPrime (Pm.map φ)
  letI algC : Algebra Cr LQ := ((algebraMap Dr LQ).comp φ).toAlgebra
  haveI hloc : IsLocalization Pm.primeCompl LQ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs⟩
      exact IsLocalization.map_units LQ (⟨φ s, hnotin s hs⟩ : (Pm.map φ).primeCompl)
    · intro z
      obtain ⟨⟨d, t⟩, hz⟩ := IsLocalization.surj (Pm.map φ).primeCompl z
      obtain ⟨a, rfl⟩ := hφ d
      obtain ⟨s, hs⟩ := hφ (t : Dr)
      have hsP : s ∉ Pm := fun hsP => t.2 (by rw [← hs]; exact Ideal.mem_map_of_mem φ hsP)
      refine ⟨⟨a, ⟨s, hsP⟩⟩, ?_⟩
      show z * algebraMap Dr LQ (φ s) = algebraMap Dr LQ (φ a)
      rw [hs]
      exact hz
    · intro x y hxy
      have hxy' : algebraMap Dr LQ (φ x) = algebraMap Dr LQ (φ y) := hxy
      obtain ⟨⟨t, ht⟩, htxy⟩ := (IsLocalization.eq_iff_exists (Pm.map φ).primeCompl LQ).mp hxy'
      obtain ⟨s, rfl⟩ := hφ t
      have hsP : s ∉ Pm := fun h => ht (Ideal.mem_map_of_mem φ h)
      refine ⟨⟨e * s, fun h => (hP.mem_or_mem h).elim heP hsP⟩, ?_⟩
      have h1 : φ (s * x - s * y) = 0 := by
        rw [map_sub, map_mul, map_mul]
        exact sub_eq_zero.mpr htxy
      have h2 := he0 _ h1
      show e * s * x = e * s * y
      linear_combination h2
  haveI hLQd : IsDomain LQ :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (Pm.map φ))
  let f : Localization.AtPrime Pm ≃ₐ[Cr] LQ :=
    IsLocalization.algEquiv Pm.primeCompl (Localization.AtPrime Pm) LQ
  haveI hdom : IsDomain (Localization.AtPrime Pm) :=
    Function.Injective.isDomain f.toRingEquiv.toRingHom f.toRingEquiv.injective
  letI algD : Algebra Dr (Localization.AtPrime Pm) :=
    (f.symm.toRingEquiv.toRingHom.comp (algebraMap Dr LQ)).toAlgebra
  let g : LQ ≃ₐ[Dr] Localization.AtPrime Pm :=
    { f.symm.toRingEquiv with commutes' := fun _ => rfl }
  haveI : IsLocalization (Pm.map φ).primeCompl (Localization.AtPrime Pm) :=
    IsLocalization.isLocalization_of_algEquiv (M := (Pm.map φ).primeCompl) (S := LQ) g
  exact ⟨hdom, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain Dr hQ0
    (Localization.AtPrime Pm)⟩

private theorem fin_lemma_5 (O K A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CharZero K] [CommRing A] [Algebra K A] [Algebra O A]
    [IsScalarTower O K A] [FiniteDimensional K A] [IsReduced A] : Module.Finite O ↥(As O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : ∀ I : MaximalSpectrum A, Module.Finite O ↥(integralClosure O (A ⧸ I.asIdeal)) :=
    fun I => by haveI := I.isMaximal; exact (fld_lemma_3 O K A I.asIdeal).1
  let ψ : ↥(As O A) →ₗ[O] ((I : MaximalSpectrum A) → ↥(integralClosure O (A ⧸ I.asIdeal))) :=
    LinearMap.pi fun I => (((Ideal.Quotient.mkₐ O I.asIdeal).comp (As O A).val).codRestrict
      (integralClosure O (A ⧸ I.asIdeal)) fun x => id
        (IsIntegral.map (Ideal.Quotient.mkₐ O I.asIdeal) (x.2 : IsIntegral O (x : A)))).toLinearMap
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    rw [← sub_eq_zero]
    apply inj_lemma K A
    intro M
    rw [← Ideal.Quotient.eq]
    exact congrArg Subtype.val (congrFun hxy M)
  exact Module.Finite.of_injective ψ hψ

set_option maxHeartbeats 800000 in

private theorem pt_lemma_6 (O K A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CharZero K] [CommRing A] [Algebra K A] [Algebra O A]
    [IsScalarTower O K A] [FiniteDimensional K A] [IsReduced A] (ζ : Pts O A) : IsDVRAt ζ := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  choose E hE1 hE0 using idem_lemma_2 K A
  have hmk : ∀ (M I : MaximalSpectrum A) (a : A),
      Ideal.Quotient.mk M.asIdeal (E I * a) = if M = I then Ideal.Quotient.mk M.asIdeal a else 0 := by
    intro M I a
    rw [map_mul]
    split_ifs with h
    · rw [h, hE1, one_mul]
    · rw [hE0 I M h, zero_mul]
  have hev : ∀ (M : MaximalSpectrum A) (x : A) (q : Polynomial O),
      Ideal.Quotient.mk M.asIdeal (Polynomial.aeval x q) =
        Polynomial.aeval (Ideal.Quotient.mk M.asIdeal x) q := by
    intro M x q
    rw [← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]
  have hint : ∀ (I : MaximalSpectrum A) (y : A ⧸ I.asIdeal), IsIntegral O y → ∀ a : A,
      Ideal.Quotient.mk I.asIdeal a = y → E I * a ∈ As O A := by
    intro I y hy a ha
    obtain ⟨p, hp, hpy⟩ := hy
    refine (show IsIntegral O (E I * a) from ⟨Polynomial.X * p, Polynomial.monic_X.mul hp, ?_⟩)
    rw [← Polynomial.aeval_def, map_mul, Polynomial.aeval_X]
    apply inj_lemma K A
    intro M
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hev, hmk M I a]
    split_ifs with h
    · rw [h, ha, Polynomial.aeval_def, hpy, mul_zero]
    · rw [zero_mul]
  have hEi : ∀ I, E I ∈ As O A := fun I => by
    simpa using hint I 1 isIntegral_one 1 (map_one _)
  have hsum : ∑ I, E I = 1 := by
    rw [← sub_eq_zero]
    apply inj_lemma K A
    intro M
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, map_one, Finset.sum_eq_single M]
    · rw [hE1, sub_self]
    · intro J _ hJ
      exact hE0 J M (Ne.symm hJ)
    · intro h
      exact absurd (Finset.mem_univ M) h
  obtain ⟨I, hI⟩ : ∃ I, (⟨E I, hEi I⟩ : ↥(As O A)) ∉ ζ.asIdeal := by
    by_contra hall
    push_neg at hall
    apply ζ.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (∑ I, (⟨E I, hEi I⟩ : ↥(As O A))) ∈ ζ.asIdeal :=
      ζ.asIdeal.sum_mem fun I _ => hall I
    have h2 : (∑ I, (⟨E I, hEi I⟩ : ↥(As O A))) = 1 := by
      apply Subtype.ext
      simp [hsum]
    rw [h2] at h1
    exact h1
  haveI := I.isMaximal
  haveI := ζ.isMaximal
  obtain ⟨_, hDed, hNF⟩ := fld_lemma_3 O K A I.asIdeal
  haveI := hDed
  let φ : ↥(As O A) →+* ↥(integralClosure O (A ⧸ I.asIdeal)) :=
    (((Ideal.Quotient.mkₐ O I.asIdeal).comp (As O A).val).codRestrict
      (integralClosure O (A ⧸ I.asIdeal)) fun x => id
        (IsIntegral.map (Ideal.Quotient.mkₐ O I.asIdeal) (x.2 : IsIntegral O (x : A)))).toRingHom
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y : A ⧸ I.asIdeal)
    refine ⟨⟨E I * a, hint I y (y.2 : IsIntegral O (y : A ⧸ I.asIdeal)) a ha⟩, ?_⟩
    apply Subtype.ext
    show Ideal.Quotient.mk I.asIdeal (E I * a) = y
    rw [hmk, if_pos rfl, ha]
  have hone : φ ⟨E I, hEi I⟩ = 1 := Subtype.ext (hE1 I)
  have hzero : ∀ c, φ c = 0 → (⟨E I, hEi I⟩ : ↥(As O A)) * c = 0 := by
    intro c hc
    apply Subtype.ext
    show E I * (c : A) = 0
    apply inj_lemma K A
    intro M
    rw [← Ideal.Quotient.eq_zero_iff_mem, hmk]
    split_ifs with h
    · rw [h]
      exact congrArg Subtype.val hc
    · rfl
  obtain ⟨h1, h2⟩ := dvr_lemma_4 _ _ hNF φ hsurj _ hone hzero ζ.asIdeal hI
  exact ⟨h1, h2⟩

theorem integralClosure_dvr' : PublishedIntClos := by
  intro O K A _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ⟨fin_lemma_5 O K A, fun ζ => pt_lemma_6 O K A ζ⟩

def unif (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) : X.Ol la :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible (X.Ol la))

def unifO (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Op X la N :=
  algebraMap (X.Ol la) (Op X la N) (unif X la)

def toE : WithTop ℤ → EReal
  | ⊤ => ⊤
  | (n : ℤ) => ((n : ℝ) : EReal)

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

abbrev PtsG (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) := Pts (Op X la G.N) (OsK X la G.w)

def resF (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (F : B.Cusp j wF) : SectionSheafQuotient X la G.w wF :=
  rho0 X la G.w wF ⟨emb X la G.N (X.inc wF F), emb_mem_Vw X la G.N wF F⟩

def tL (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (i : Fin G.del) : SectionSheafQuotient X la G.w wF := resF G la (G.th' i)

def InBasis (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  LinearIndependent (Kp X la G.N) (tL G la) ∧ Submodule.span (Kp X la G.N) (Set.range (tL G la)) = ⊤

def zK (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : Fin G.rz) : Rp X la G.N :=
  secPow X la G.w (G.alz k) * emb X la G.N (X.inc _ (G.th0 k))

def InContain (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) : Prop :=
  Submodule.span (Kp X la G.N)
      {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
          θ ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ v = secPow X la G.w al * emb X la G.N (X.inc _ θ)} ≤
    Submodule.span (Kp X la G.N) (Set.range (zK G la)) ∧
  Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc ka F)) '' (WeightFamilies.MggK B CRm T c j ka : Set (B.Cusp j ka))) ≤
    Submodule.span (Kp X la G.N)
      ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       Set.range (zK G la))

structure LocalPointData (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) where
  y : PtsG G la → X.Pt la
  g0 : B.Cusp j wF
  c : PtsG G la → ℤ

namespace LocalPointData

variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la)

def e : SectionSheafQuotient X la G.w wF := resF G la Q.g0

def ordA (ζ : PtsG G la) (a : SectionSheafQuotient X la G.w wF) : WithTop ℤ := ordV (unifO X la G.N) ζ Q.e Q.c a

def A0 : Submodule (Op X la G.N) (SectionSheafQuotient X la G.w wF) := ballO (unifO X la G.N) Q.e Q.c

def Ila : ℕ∞ :=
  Module.length (Op X la G.N) (↥Q.A0 ⧸ (Submodule.span (Op X la G.N) (Set.range (tL G la))).comap Q.A0.subtype)

def nu (S : Scal B) (ζ : PtsG G la) : ℝ := (X.depth S.sW wL la (Q.y ζ)).toReal

def Net : ℝ :=
  ∑ᶠ ζ, (ep (unifO X la G.N) ζ : ℝ) * fdeg ζ * (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal

def AAp (T : ℕ) (m : PtsG G la → ℕ) : Submodule (Op X la G.N) (WK X la G.w wF (a0 D j T)) :=
  Submodule.span (Op X la G.N) ((toWK X la G.w wF (a0 D j T)) '' {x : ↥(HK X la G.w wF) |
    ∃ hx : ∀ β : Idx D j G.N →₀ ℕ, β.sum (fun _ n => n) ≤ a0 D j T - 1 →
        hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF,
      ∀ β hβ ζ, ((-(m ζ : ℤ) : ℤ) : WithTop ℤ) ≤ Q.ordA ζ (toA0K X la G.w wF ⟨hasse X la G.w β (x : Lw X la G.w), hx β hβ⟩)})

def mm (S : Scal B) (T e : ℕ) (ζ : PtsG G la) : ℕ :=
  (max 0 ⌈(ep (unifO X la G.N) ζ : ℝ) * ((T : ℝ) * Q.nu S ζ - (e : ℝ))⌉).toNat

def AA (T : ℕ) := Q.AAp T (fun _ => 0)

def InCurve : Prop :=
  FiniteDimensional (Kp X la G.N) (OsK X la G.w) ∧ IsReduced (OsK X la G.w) ∧ IsGen (OsK X la G.w) Q.e

def InTie (S : Scal B) : Prop :=
  ∀ ζ : PtsG G la,
    X.depth S.sW wL la (Q.y ζ) ≠ ⊤ ∧ X.depth S.sW wL la (Q.y ζ) ≠ ⊥ ∧
    (j < D.R.m → X.vAt la (Q.y ζ) (X.inc _ G.et) ≠ ⊤) ∧
    (∃ n : ℤ, (ep (unifO X la G.N) ζ : ℝ) * Q.nu S ζ = n) ∧
    (((Q.c ζ : ℝ) : EReal) = (ep (unifO X la G.N) ζ : EReal) * X.vAt la (Q.y ζ) (X.inc wF Q.g0)) ∧
    (∀ (k : ℕ) (g : B.Cusp j (addL (wt0 D j) wL k)),
      toE (ord (unifO X la G.N) ζ (toOsK X la G.w
        (fr0 X la G.w k ⟨emb X la G.N (X.inc _ g), emb_mem_Vw X la G.N _ g⟩))) =
      (ep (unifO X la G.N) ζ : EReal) *
        (X.vAt la (Q.y ζ) (X.inc _ g) - (k : EReal) * X.depth S.sW wL la (Q.y ζ))) ∧
    (∀ (k : ℕ) (g : B.Cusp j (addL wF wL k)),
      toE (Q.ordA ζ (toA0K X la G.w wF (toHK X la G.w wF k ⟨emb X la G.N (X.inc _ g), emb_mem_Vw X la G.N _ g⟩))) =
      (ep (unifO X la G.N) ζ : EReal) *
        (X.vAt la (Q.y ζ) (X.inc _ g) - (k : EReal) * X.depth S.sW wL la (Q.y ζ)))

def Ok (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) : Prop :=
  InBasis G la ∧ Q.InCurve ∧ Q.InTie S ∧ InContain G la S CRm T c

end LocalPointData

def rLa {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (CRm : ℝ) (T : ℕ) (c : ℝ) : ℝ :=
  (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) *
      ((Q.Ila.toNat : ℝ) + (if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0)) +
    (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) +
    ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin G.rq => (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ)

def Heights {G : GlobalFamilyData X ka wL wF} (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) : Prop :=
  (∀ la, (Qf la).Ila ≠ ⊤) ∧ Summable (fun la => ((Qf la).Ila.toNat : ℝ) * X.lN la) ∧
  2 * (∑' la, ((Qf la).Ila.toNat : ℝ) * X.lN la) ≤
    (G.del : ℝ) * Real.log G.del + 2 * ∑ i, WeightFamilies.meanLogSup B (G.th' i) +
      8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
      2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size ∧
  (j < D.R.m → Summable (fun la => (Qf la).Net * X.lN la) ∧
    (∑' la, (Qf la).Net * X.lN la) / (G.iet : ℝ) ≤
      g0 D * (((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size +
        4 / 3 * (WeightFamilies.dimY D j : ℝ) * G.del * Prw * wL.size) + G.del * Pet)

def Conclusion1Of2 : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    AdmW large₂ X K H Ch Ah Cq Aq → WeightFamilies.TransferenceTheoremCond →
    (∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
        (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
      Hyp large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
      ∃ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
        G.Tied large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Gc Prw Ch Ah K.Cf K.Af ∧
        DeepIn (X j h1 h2) ka large₂ K.CG K.AG Pd ∧
        Shares D wL G.del G.rz G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) T K.CRm (cc D large₂ C2 A2 CR wL) ∧
        PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ∧
        ∃ Qf : ∀ la, LocalPointData G la,
          (∀ la, (Qf la).Ok S K.CRm T (cc D large₂ C2 A2 CR wL)) ∧ Heights Qf Gc PH Prw Pet) →
    Conclusion1 large₂ X H C2 A2 CR CT

end Formalism.MainNotions.Gaps.EtaleWeightGaps
