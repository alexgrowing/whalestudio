import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare GlobalTheory.Mem.Chr GlobalTheory.Mem.LocTriv
open scoped nonZeroDivisors

namespace GlobalTheory.RayFromArtin

section Galois

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : Type) [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]

theorem valuation_int_le_one {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω] (A : ValuationSubring Ω) (x : 𝓞 L) :
    A.valuation (algebraMap L Ω (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom))

theorem unramIn_of_ine {v : HeightOneSpectrum (𝓞 K)}
    (h : ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := K) A, AlgEquiv.restrictNormalHom L σ = 1) :
    GlobalTheory.NT.UnramIn L v := by
  rintro τ ⟨P, hP, hPo, hτ⟩
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  have hAv : IsPlaceOver A v := fun x => by
    have := hA (algebraMap (𝓞 K) (𝓞 L) x)
    rw [hPo.over, Ideal.mem_under, IsScalarTower.algebraMap_apply K L Ω]
    exact this
  have hu : ∀ s : 𝓞 L, s ∉ P → A.valuation (algebraMap L Ω (s : L)) = 1 := fun s hs =>
    le_antisymm (valuation_int_le_one A s) (not_lt.1 ((hA s).not.2 hs))
  obtain ⟨σ, hσ, e⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A L τ (fun x hx => by
    obtain ⟨s, t, hs, e⟩ : ∃ s t : 𝓞 L, s ∉ P ∧ x * (s : L) = t := by
      obtain ⟨n, d, e | e⟩ := w.exists_primeCompl_mul_eq_or_mul_eq x
      · exact ⟨d, n, d.2, e⟩
      · refine ⟨n, d, fun hn => ?_, e⟩
        have h1 := hu d d.2
        have e' : x * (n : L) = ((d : 𝓞 L) : L) := e
        rw [← e', map_mul, map_mul] at h1
        exact ((mul_le_of_le_one_left' hx).trans_lt ((hA n).2 hn)).ne h1
    have hs' : τ • s ∉ P := fun hs' => hs (by simpa using P.sub_mem hs' (hτ s))
    have e2 : τ x * τ (s : L) = τ (t : L) := by rw [← map_mul, e]
    have key : τ (s : L) * (τ x - x) = (τ (t : L) - t) - x * (τ (s : L) - s) := by
      rw [← e2, ← e]; ring
    have h1 : A.valuation (algebraMap L Ω (τ (s : L))) = 1 := hu _ hs'
    have h2 : A.valuation (algebraMap L Ω (τ (t : L) - t)) < 1 := (hA _).2 (hτ t)
    have h3 : A.valuation (algebraMap L Ω (τ (s : L) - s)) < 1 := (hA _).2 (hτ s)
    have h4 : A.valuation (algebraMap L Ω (τ (s : L) * (τ x - x))) < 1 := by
      rw [key, map_sub (algebraMap L Ω) _ (x * _), map_mul]
      refine Valuation.map_sub_lt _ h2 ?_
      rw [map_mul]
      exact (mul_le_of_le_one_left' hx).trans_lt h3
    rwa [map_mul, map_mul, h1, one_mul, map_sub] at h4)
  rw [← h A hAv σ hσ]
  ext x
  apply (algebraMap L Ω).injective
  rw [← e]
  exact (σ.restrictNormal_commutes L x).symm

omit [IsAlgClosure K Ω] [NumberField L] in

theorem isFrob_restrict {v : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G K Ω}
    (hσ : IsFrob (F := K) A (normV v) σ) : GlobalTheory.NT.IsFrob L v (AlgEquiv.restrictNormalHom L σ) := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A fun x =>
    (A.valuation_le_one_iff _).1 (valuation_int_le_one A x)
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap L Ω (x : L)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  refine ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, ⟨?_⟩, fun x => ?_⟩
  · ext x
    rw [Ideal.mem_under, hf, ← hA x, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  · rw [hf]
    have := hσ.2 _ (valuation_int_le_one A x)
    rw [← σ.restrictNormal_commutes L, ← map_pow, ← map_sub] at this
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact this

theorem exists_field {B : Type} [CommGroup B] (φ : G K Ω →* B) (ho : IsOpen (φ.ker : Set (G K Ω))) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
      ∀ σ : G K Ω, AlgEquiv.restrictNormalHom L σ = 1 ↔ φ σ = 1 := by
  have : IsGalois K Ω := {}
  let N : ClosedSubgroup (G K Ω) := ⟨φ.ker, φ.ker.isClosed_of_isOpen ho⟩
  let L := IntermediateField.fixedField φ.ker
  have hN : L.fixingSubgroup = φ.ker := InfiniteGalois.fixingSubgroup_fixedField N
  have h1 : FiniteDimensional K L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hN]; exact ho)
  have h2 : IsGalois K L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hN]; infer_instance)
  have h3 : ∀ σ : G K Ω, AlgEquiv.restrictNormalHom L σ = 1 ↔ φ σ = 1 := fun σ => by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hN, MonoidHom.mem_ker]
  have h4 : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω a
    obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω b
    rw [← mul_inv_eq_one, ← map_mul, ← map_mul, ← map_inv, ← map_mul, h3, map_mul, map_inv, map_mul, map_mul,
      mul_comm (φ a), mul_inv_cancel]⟩⟩
  exact ⟨L, h1, {}, h3⟩

end Galois

section Idelic

variable {K : Type} [Field K] [NumberField K]

def rad (𝔪 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : WithZero (Multiplicative ℤ) :=
  WithZero.exp (-FractionalIdeal.count K v (𝔪 : FractionalIdeal (𝓞 K)⁰ K))

theorem rad_lt_one {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪) :
    rad 𝔪 v < 1 := by
  have := FractionalIdeal.count_mono K v (FractionalIdeal.coeIdeal_ne_zero.2 hm)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 (Ideal.le_of_dvd hv))
  rw [FractionalIdeal.count_self] at this
  rw [rad, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem rad_eq_one {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪) :
    rad 𝔪 v = 1 := by
  classical
  have : (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors = 0 := by
    by_contra hne
    exact hv ((Associates.count_ne_zero_iff_dvd hm v.irreducible).1 hne)
  rw [rad, FractionalIdeal.count_coe K v hm]
  simp [this]

theorem mem_iff_rad {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) (a : 𝓞 K) :
    a ∈ 𝔪 ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (a : K) ≤ rad 𝔪 v :=
  Iff.trans ⟨FractionalIdeal.mem_coeIdeal_of_mem _, fun h => by
      obtain ⟨b, hb, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 h
      rwa [← RingOfIntegers.ext e]⟩
    (GlobalTheory.Idele.mem_iff_valuation_le (FractionalIdeal.coeIdeal_ne_zero.2 hm) _)

theorem mem_rayUnits_iff {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) (k : Kˣ) : k ∈ rayUnits 𝔪 ↔
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 → v.valuation K ((k : K) - 1) ≤ rad 𝔪 v) ∧
      ∀ φ : K →+* ℝ, 0 < φ (k : K) := by
  constructor
  · rintro ⟨a, b, ⟨ha, hb, -, hb', hab, hp⟩, e⟩
    refine ⟨fun v hv => ?_, fun φ => ?_⟩
    · have h1 : v.valuation K (b : K) = 1 := by
        refine le_antisymm (v.valuation_le_one b) (not_lt.1 fun h => ?_)
        exact v.prime.not_isUnit (hb'.isUnit_of_dvd'
          (Ideal.dvd_span_singleton.2 ((v.valuation_lt_one_iff_mem b).1 h)) hv)
      have h2 := (mem_iff_rad hm _).1 hab v
      have e2 : ((a - b : 𝓞 K) : K) = ((k : K) - 1) * b := by
        rw [sub_mul, e, one_mul]; rfl
      rwa [e2, map_mul, h1, mul_one] at h2
    · have := hp φ
      rw [← e, map_mul, mul_assoc] at this
      exact pos_of_mul_pos_left this (mul_self_nonneg _)
  · rintro ⟨h, hp⟩
    let D : Ideal (𝓞 K) :=
      { carrier := {b | ∃ a : 𝓞 K, (k : K) * (b : K) = a}
        zero_mem' := ⟨0, by simp⟩
        add_mem' := by
          rintro b c ⟨a, ha⟩ ⟨d, hd⟩
          exact ⟨a + d, by push_cast; rw [mul_add, ha, hd]⟩
        smul_mem' := by
          rintro c b ⟨a, ha⟩
          refine ⟨c * a, ?_⟩
          show (k : K) * ((c : K) * b) = c * a
          rw [← ha]; ring }
    have hD : D ⊔ 𝔪 = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      let v : HeightOneSpectrum (𝓞 K) :=
        ⟨M, hM.isPrime, fun h0 => hm (le_bot_iff.1 (h0 ▸ le_sup_right.trans hle))⟩
      have hv : v.asIdeal ∣ 𝔪 := Ideal.dvd_iff_le.2 (le_sup_right.trans hle)
      have h1 : v.valuation K (k : K) ≤ 1 := by
        have := Valuation.map_add_le (v.valuation K) ((h v hv).trans (rad_lt_one hm hv).le) (map_one _).le
        rwa [sub_add_cancel] at this
      obtain ⟨n, d, e⟩ := v.exists_primeCompl_mul_eq_of_integer _ h1
      exact d.2 (hle (le_sup_left (a := D) ⟨n, e⟩))
    obtain ⟨b, hb, hb0, hb1⟩ : ∃ b ∈ D, b ≠ 0 ∧ 1 - b ∈ 𝔪 := by
      obtain ⟨b, hb, c, hc, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hD)
      have hc' : 1 - b ∈ 𝔪 := by rwa [← e, add_sub_cancel_left]
      by_cases hb0 : b = 0
      · obtain ⟨n, d, hd, e⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (k : K)
        have hd0 := nonZeroDivisors.ne_zero hd
        refine ⟨d, ⟨n, ?_⟩, hd0, ?_⟩
        · rw [← e]
          exact div_mul_cancel₀ _ (by simpa using hd0)
        · rw [hb0, sub_zero] at hc'
          simpa using 𝔪.mul_mem_left (1 - d) hc'
      · exact ⟨b, hb, hb0, hc'⟩
    obtain ⟨a, e⟩ := hb
    have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
    have hab : a - b ∈ 𝔪 := (mem_iff_rad hm _).2 fun v => by
      by_cases hv : v.asIdeal ∣ 𝔪
      · have e2 : ((a - b : 𝓞 K) : K) = ((k : K) - 1) * b := by
          rw [sub_mul, e, one_mul]; rfl
        rw [e2, map_mul]
        exact (mul_le_of_le_one_right' (v.valuation_le_one b)).trans (h v hv)
      · rw [rad_eq_one hm hv]
        exact v.valuation_le_one _
    refine ⟨a, b, ⟨?_, hb0, ?_, ?_, hab, fun φ => ?_⟩, e⟩
    · rintro rfl
      exact mul_ne_zero k.ne_zero hbK e
    · exact Ideal.isCoprime_iff_exists.2 ⟨a, Ideal.mem_span_singleton_self a, _, 𝔪.sub_mem hb1 hab, by ring⟩
    · exact Ideal.isCoprime_iff_exists.2 ⟨b, Ideal.mem_span_singleton_self b, _, hb1, by ring⟩
    · rw [← e, map_mul, mul_assoc]
      exact mul_pos (hp φ) (mul_self_pos.2 ((map_ne_zero φ).2 hbK))

theorem mem_connectedComponentOfOne_of_pos (k : Kˣ) (hk : ∀ φ : K →+* ℝ, 0 < φ (k : K)) :
    (Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom k : (InfiniteAdeleRing K)ˣ) ∈
      Subgroup.connectedComponentOfOne (InfiniteAdeleRing K)ˣ := by
  have h : ∀ w : InfinitePlace K, ∃ S : Set w.Completion, IsPreconnected S ∧ 0 ∉ S ∧ 1 ∈ S ∧
      algebraMap K w.Completion (k : K) ∈ S := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      have he : e (algebraMap K w.Completion (k : K)) = InfinitePlace.embedding_of_isReal hw (k : K) :=
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm (k : K))
      refine ⟨e ⁻¹' Set.Ioi 0, (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isPreconnected_preimage.2
        isPreconnected_Ioi, by simp, by simp, ?_⟩
      rw [Set.mem_preimage, he]
      exact hk _
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      exact ⟨e ⁻¹' {0}ᶜ, (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isPreconnected_preimage.2
        (isConnected_compl_singleton_of_one_lt_rank (by simp) 0).isPreconnected, by simp, by simp,
        (map_ne_zero e).2 ((map_ne_zero _).2 k.ne_zero)⟩
  choose S hS h0 h1 h2 using h
  let T : Set (InfiniteAdeleRing K) := Set.univ.pi S
  have hp : IsPreconnected ((Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T) := by
    rw [← (isOpenEmbedding_val_inf K).isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset]
    · exact isPreconnected_univ_pi hS
    · intro y hy
      have : IsUnit y := Pi.isUnit_iff.2 fun w => IsUnit.mk0 _ fun h => h0 w (h ▸ hy w trivial)
      exact this
  exact hp.subset_connectedComponent (fun w _ => h1 w) (fun w _ => h2 w)

def infPart : Ideles K →* (InfiniteAdeleRing K)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

def rayIdl (𝔪 : Ideal (𝓞 K)) : Subgroup (Ideles K) where
  carrier := {a | a ∈ unitIdl K ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
    Valued.v (ev v (a : AdeleRing (𝓞 K) K) - 1) ≤ rad 𝔪 v) ∧
    infPart a ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing K)ˣ}
  one_mem' := ⟨one_mem _, fun v _ => by simp, by rw [map_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha', ha''⟩ ⟨hb, hb', hb''⟩
    refine ⟨mul_mem ha hb, fun v hv => ?_, by rw [map_mul]; exact mul_mem ha'' hb''⟩
    have h1 : Valued.v (ev v (a : AdeleRing (𝓞 K) K)) = 1 := ha v
    rw [Units.val_mul, map_mul, show ∀ x y : v.adicCompletion K, x * y - 1 = x * (y - 1) + (x - 1) from
      fun x y => by ring]
    refine Valuation.map_add_le _ ?_ (ha' v hv)
    rw [map_mul, h1, one_mul]
    exact hb' v hv
  inv_mem' := by
    rintro a ⟨ha, ha', ha''⟩
    refine ⟨inv_mem ha, fun v hv => ?_, by rw [map_inv]; exact inv_mem ha''⟩
    have h1 : Valued.v (ev v (a : AdeleRing (𝓞 K) K)) = 1 := ha v
    have h2 : ev v (a : AdeleRing (𝓞 K) K) * (ev v ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K) - 1) =
        1 - ev v (a : AdeleRing (𝓞 K) K) := by
      rw [mul_sub, ← map_mul, Units.mul_inv, map_one, mul_one]
    have h3 := ha' v hv
    rwa [Valuation.map_sub_swap, ← h2, map_mul, h1, one_mul] at h3

theorem isOpen_rayIdl {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) : IsOpen (rayIdl 𝔪 : Set (Ideles K)) := by
  have h : IsOpen (⋂ v ∈ {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔪},
      {a : Ideles K | Valued.v (ev v (a : AdeleRing (𝓞 K) K) - 1) ≤ rad 𝔪 v}) :=
    (Ideal.finite_factors hm).isOpen_biInter fun v _ => (GlobalTheory.Mem.UnitOpen.isOpen_val_le v _).preimage
      ((GlobalTheory.Mem.UnitOpen.continuous_comp v).sub continuous_const)
  have hp : Continuous (infPart (K := K)) := Continuous.units_map _ continuous_fst
  convert GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (h.inter ((isOpen_connectedComponentOfOne_inf K).preimage hp)) using 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  rfl

theorem infConn_le_rayIdl (𝔪 : Ideal (𝓞 K)) : infConn K ≤ rayIdl 𝔪 := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨fun v => map_one (Valued.v : Valuation (v.adicCompletion K) _), fun v _ => ?_, ?_⟩
  · show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    simp
  · have e : infPart (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) y) = y :=
      Units.ext rfl
    exact e.symm ▸ hy

theorem localIdele_mem_rayIdl {𝔪 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪)
    {x : (v.adicCompletion K)ˣ} (hx : IsUnitAt v x) : localIdele K v x ∈ rayIdl 𝔪 := by
  refine ⟨fun w => ?_, fun w hw => ?_, ?_⟩
  · show Valued.v (ev w (localIdele K v x : AdeleRing (𝓞 K) K)) = 1
    by_cases h : w = v
    · subst h
      rw [ev_local_self]
      exact hx
    · rw [ev_local_ne h, map_one]
  · rw [ev_local_ne (by rintro rfl; exact hv hw)]
    simp
  · rw [show infPart (localIdele K v x) = 1 from Units.ext rfl]
    exact one_mem _

def unif (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ := atFin v (exists_unif v).choose

theorem isUnifAt_unif (v : HeightOneSpectrum (𝓞 K)) : IsUnifAt v (unif v) := (exists_unif v).choose_spec

def unifIdl (𝔪 : Ideal (𝓞 K)) : idealsPrimeTo 𝔪 →* Ideles K := extend 𝔪 fun v => localIdele K v (unif v)

theorem infPart_unifIdl (𝔪 : Ideal (𝓞 K)) (J : idealsPrimeTo 𝔪) : infPart (unifIdl 𝔪 J) = 1 := by
  refine (MonoidHom.map_finprod infPart (finite_support_zpow (fun v => localIdele K v (unif v)) _)).trans ?_
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [map_zpow, show infPart (localIdele K v (unif v)) = 1 from Units.ext rfl, one_zpow]

theorem ev_unifIdl (𝔪 : Ideal (𝓞 K)) (J : idealsPrimeTo 𝔪) (v : HeightOneSpectrum (𝓞 K)) :
    ev v (unifIdl 𝔪 J : AdeleRing (𝓞 K) K) =
      (unif v : v.adicCompletion K) ^ FractionalIdeal.count K v (J.1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have := MonoidHom.map_finprod (Units.map (ev v)) (finite_support_zpow (fun v => localIdele K v (unif v))
    (J.1 : FractionalIdeal (𝓞 K)⁰ K))
  rw [finprod_eq_single (fun w => Units.map (ev v) _) v fun w hw => by
    rw [map_zpow, show Units.map (ev v) (localIdele K w (unif w)) = 1 from Units.ext (ev_local_ne hw.symm _), one_zpow],
    map_zpow, show Units.map (ev v) (localIdele K v (unif v)) = unif v from Units.ext (ev_local_self v _)] at this
  rw [← Units.val_zpow_eq_zpow_val, ← this]
  rfl

theorem valued_unifIdl (𝔪 : Ideal (𝓞 K)) (J : idealsPrimeTo 𝔪) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (ev v (unifIdl 𝔪 J : AdeleRing (𝓞 K) K)) =
      WithZero.exp (-FractionalIdeal.count K v (J.1 : FractionalIdeal (𝓞 K)⁰ K)) := by
  have h : Valued.v (unif v : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := isUnifAt_unif v
  rw [ev_unifIdl, map_zpow₀, h, ← WithZero.exp_zsmul]
  simp

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem ev_diagUnits (v : HeightOneSpectrum (𝓞 K)) (k : Kˣ) :
    ev v (diagUnits K k : AdeleRing (𝓞 K) K) = algebraMap K (v.adicCompletion K) k := rfl

theorem div_mem_rayIdl_iff {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) (J : idealsPrimeTo 𝔪) (k : Kˣ) :
    diagUnits K k * (unifIdl 𝔪 J)⁻¹ ∈ rayIdl 𝔪 ↔ k ∈ rayUnits 𝔪 ∧ toPrincipalIdeal (𝓞 K) K k = J.1 := by
  have e0 : ∀ v, ev v ((diagUnits K k * (unifIdl 𝔪 J)⁻¹ : Ideles K) : AdeleRing (𝓞 K) K) =
      algebraMap K (v.adicCompletion K) k * (ev v (unifIdl 𝔪 J : AdeleRing (𝓞 K) K))⁻¹ := fun v => by
    rw [Units.val_mul, map_mul, ev_diagUnits, map_units_inv]
  have e1 : diagUnits K k * (unifIdl 𝔪 J)⁻¹ ∈ unitIdl K ↔ toPrincipalIdeal (𝓞 K) K k = J.1 := by
    have : ∀ v, Valued.v (ev v ((diagUnits K k * (unifIdl 𝔪 J)⁻¹ : Ideles K) : AdeleRing (𝓞 K) K)) = 1 ↔
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K)) =
          FractionalIdeal.count K v (J.1 : FractionalIdeal (𝓞 K)⁰ K) := fun v => by
      rw [e0, map_mul, map_inv₀, valued_unifIdl, valued_algebraMap, mul_inv_eq_one₀ WithZero.exp_ne_zero,
        GlobalTheory.Idele.valuation_eq_exp_neg_count v k.ne_zero, WithZero.exp_inj, neg_inj]
    rw [Units.ext_iff, coe_toPrincipalIdeal]
    exact ⟨fun h => GlobalTheory.Idele.eq_of_count_eq (FractionalIdeal.spanSingleton_ne_zero_iff.2 k.ne_zero) J.1.ne_zero
      fun v => (this v).1 (h v), fun h v => (this v).2 (by rw [h])⟩
  have e2 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
      Valued.v (ev v ((diagUnits K k * (unifIdl 𝔪 J)⁻¹ : Ideles K) : AdeleRing (𝓞 K) K) - 1) =
        v.valuation K ((k : K) - 1) := fun v hv => by
    rw [e0, ev_unifIdl, J.2 v hv, zpow_zero, inv_one, mul_one, ← valued_algebraMap, map_sub (algebraMap K _), map_one]
  have e3 : infPart (diagUnits K k * (unifIdl 𝔪 J)⁻¹) =
      Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom k := by
    rw [map_mul, map_inv, infPart_unifIdl, inv_one, mul_one]
    exact Units.ext rfl
  rw [mem_rayUnits_iff hm]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨fun v hv => e2 v hv ▸ h2 v hv, pos_of_mem_connectedComponentOfOne K k (e3 ▸ h3)⟩, e1.1 h1⟩
  · rintro ⟨⟨h2, h3⟩, h1⟩
    exact ⟨e1.2 h1, fun v hv => (e2 v hv).symm ▸ h2 v hv, e3 ▸ mem_connectedComponentOfOne_of_pos k h3⟩

def rayGrp (𝔪 : Ideal (𝓞 K)) : Subgroup (Ideles K) := (diagUnits K).range ⊔ rayIdl 𝔪

theorem unifIdl_mem_rayGrp_iff {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) (J : idealsPrimeTo 𝔪) :
    unifIdl 𝔪 J ∈ rayGrp 𝔪 ↔ J ∈ (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪) := by
  rw [Subgroup.mem_subgroupOf, rayGrp, Subgroup.mem_sup]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, u, hu, e⟩
    refine ⟨k, (div_mem_rayIdl_iff hm J k).1 ?_⟩
    rw [← e, mul_inv, mul_inv_cancel_left]
    exact inv_mem hu
  · rintro ⟨k, hk⟩
    exact ⟨_, ⟨k, rfl⟩, _, inv_mem ((div_mem_rayIdl_iff hm J k).2 hk), by
      rw [mul_inv, inv_inv, mul_inv_cancel_left]⟩

end Idelic

end GlobalTheory.RayFromArtin

namespace GlobalTheory.Published

open GlobalTheory.RayFromArtin

theorem GlobalArtinReciprocity.rayClassFieldSt : GlobalArtinReciprocity → RayClassFieldSt := by
  intro H
  rw [rayClassFieldSt_iff_artinIso]
  intro K _ _ 𝔪 hm
  obtain ⟨art, ha⟩ := H K (AlgebraicClosure K)
  have hU : IsOpen (rayGrp 𝔪 : Set (Ideles K)) := Subgroup.isOpen_mono le_sup_right (isOpen_rayIdl hm)
  let θ : Ideles K →* Ideles K ⧸ rayGrp 𝔪 := QuotientGroup.mk' _
  have hθ : θ.ker = rayGrp 𝔪 := QuotientGroup.ker_mk' _
  have hker : art.ker ≤ θ.ker := by
    rw [ha.ker, hθ]
    exact Subgroup.topologicalClosure_minimal _ (sup_le_sup_left (infConn_le_rayIdl 𝔪) _)
      (Subgroup.isClosed_of_isOpen _ hU)
  let ρ := art.liftOfSurjective ha.quot.surjective ⟨θ, hker⟩
  have hρ : ∀ x, ρ (art x) = θ x := fun x => art.liftOfRightInverse_comp_apply _ _ ⟨θ, hker⟩ x
  have hρo : IsOpen (ρ.ker : Set (Gab K (AlgebraicClosure K))) := by
    rw [← ha.quot.isQuotientMap.isOpen_preimage]
    convert hU using 1
    ext x
    rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, MonoidHom.mem_ker, hρ, ← MonoidHom.mem_ker, hθ]
  let φ := ρ.comp (GlobalTheory.HeckeGal.toAb K (AlgebraicClosure K))
  have hφ : Function.Surjective φ := fun b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ b
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    exact ⟨σ, by rw [MonoidHom.comp_apply, hσ, hρ]⟩
  obtain ⟨L, _, _, hL⟩ := exists_field φ (hρo.preimage QuotientGroup.continuous_mk)
  have : NumberField L := NumberField.of_module_finite K L
  have hk2 : φ.ker ≤ (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) L).ker := fun σ => (hL σ).2
  let e := φ.liftOfSurjective hφ ⟨_, hk2⟩
  have he : ∀ σ, e (φ σ) = AlgEquiv.restrictNormalHom L σ := fun σ =>
    φ.liftOfRightInverse_comp_apply _ _ ⟨_, hk2⟩ σ
  have he1 : ∀ b, e b = 1 ↔ b = 1 := fun b => by
    obtain ⟨σ, rfl⟩ := hφ b
    rw [he, hL]
  let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := e.comp (θ.comp (unifIdl 𝔪))⁻¹
  have hψ : ∀ 𝔭 h, GlobalTheory.NT.UnramIn L 𝔭 ∧ GlobalTheory.NT.IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h)) := fun v hv => by
    refine ⟨unramIn_of_ine (Ω := AlgebraicClosure K) L fun A hA σ hσ => ?_, ?_⟩
    · obtain ⟨x, hx, e⟩ := (ha.ine v A hA _).2 ⟨σ, hσ, rfl⟩
      rw [hL, MonoidHom.comp_apply, ← e, hρ, ← MonoidHom.mem_ker, hθ]
      exact Subgroup.mem_sup_right (localIdele_mem_rayIdl hv hx)
    · obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure K) v
      obtain ⟨σ, hσ, e'⟩ := (ha.frob v A hA _).1 ⟨_, isUnifAt_unif v, rfl⟩
      have : ψ (primeElt 𝔪 v hv) = AlgEquiv.restrictNormalHom L σ := by
        rw [← he, MonoidHom.comp_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, unifIdl, extend_primeElt, ← hρ,
          ← e', map_inv (GlobalTheory.HeckeGal.toAb K _), map_inv ρ, inv_inv]
        rfl
      rw [this]
      exact isFrob_restrict L hA hσ
  have hkψ : ψ.ker = (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪) := by
    ext J
    rw [← unifIdl_mem_rayGrp_iff hm, ← hθ, MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, he1,
      MonoidHom.inv_apply, inv_eq_one, MonoidHom.comp_apply]
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← GlobalTheory.RayMaximal.closure_isFrob_eq_top L hm, Subgroup.closure_le]
    rintro σ ⟨𝔭, h, hσ⟩
    exact ⟨primeElt 𝔪 𝔭 h, isFrob_unique L (hψ 𝔭 h).1 (hψ 𝔭 h).2 hσ⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    (QuotientGroup.quotientMulEquivOfEq hkψ.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), hψ⟩

end GlobalTheory.Published

end
