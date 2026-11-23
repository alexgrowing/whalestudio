import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdUnifMulUnitIdl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfTameLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfRoot

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Chr.IdlFact

namespace GlobalTheory.Mem.EtaExt

def freeHom {X G : Type} [CommGroup G] (g : X → G) : Multiplicative (X →₀ ℤ) →* G where
  toFun m := (Multiplicative.toAdd m).prod fun v z => g v ^ z
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul]
    exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

theorem freeHom_apply {X G : Type} [CommGroup G] (g : X → G) (m : X →₀ ℤ) :
    freeHom g (Multiplicative.ofAdd m) = ∏ v ∈ m.support, g v ^ m v := rfl

theorem freeHom_single {X G : Type} [CommGroup G] (g : X → G) (v : X) (z : ℤ) :
    freeHom g (Multiplicative.ofAdd (Finsupp.single v z)) = g v ^ z :=
  Finsupp.prod_single_index (h := fun v z => g v ^ z) (zpow_zero _)

theorem freeHom_eq_finprod {X G : Type} [CommGroup G] (g : X → G) (m : X →₀ ℤ) :
    freeHom g (Multiplicative.ofAdd m) = ∏ᶠ v, g v ^ m v := by
  rw [freeHom_apply, finprod_eq_prod_of_mulSupport_subset]
  intro v hv
  by_contra h
  have : m v = 0 := by simpa using h
  exact hv (by simp [this])

variable {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

theorem valuation_eq_exp (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    P.valuation L (k : L) = WithZero.exp (-ordF P k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (by simp)]

theorem ordF_mul (P : HeightOneSpectrum (𝓞 L)) (k k' : Lˣ) : ordF P (k * k') = ordF P k + ordF P k' := by
  have h := valuation_eq_exp P (k * k')
  rw [Units.val_mul, map_mul, valuation_eq_exp, valuation_eq_exp, ← WithZero.exp_add, WithZero.exp_inj] at h
  omega

theorem valAt_diag (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    valAt P (diagUnits L k) = WithZero.exp (-ordF P k) := by
  rw [← valuation_eq_exp]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _

theorem mem_aboveF (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 L)) :
    Q ∈ aboveF (L := L) F v ↔ Q.under (𝓞 F) = v := by
  unfold aboveF; rw [Set.Finite.mem_toFinset]; rfl

open Classical in
theorem valAt_locF (hord : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (P : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    valAt P (locF F v k) = WithZero.exp (-(if P.under (𝓞 F) = v then ordF v k else 0)) := by
  unfold locF
  rw [map_prod]
  split_ifs with hw
  · rw [Finset.prod_eq_single P (fun Q _ hQ => valAt_localIdele_ne hQ.symm _)
      (fun h => absurd ((mem_aboveF v P).2 hw) h), valAt_localIdele_self, ← hw, ← hord, ← valuation_eq_exp]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  · rw [neg_zero, WithZero.exp_zero]
    refine Finset.prod_eq_one fun Q hQ => valAt_localIdele_ne ?_ _
    rintro rfl
    exact hw ((mem_aboveF _ _).1 hQ)

theorem valAt_free (hord : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (P : HeightOneSpectrum (𝓞 L)) (m : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    valAt P (freeHom (fun v => locF (L := L) F v (unif v)) (Multiplicative.ofAdd m)) =
      WithZero.exp (-m (P.under (𝓞 F))) := by
  classical
  rw [freeHom_apply, map_prod, Finset.prod_eq_single (P.under (𝓞 F))]
  · rw [map_zpow, valAt_locF hord, if_pos rfl, ordF_unif_self, ← WithZero.exp_zsmul]
    simp
  · intro v _ hv
    rw [map_zpow, valAt_locF hord, if_neg hv.symm]
    simp
  · intro h
    have : m (P.under (𝓞 F)) = 0 := by simpa using h
    rw [this, zpow_zero, map_one]

theorem exists_under (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 L), P.under (𝓞 F) = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, HeightOneSpectrum.ext hl.over.symm⟩
  exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q

theorem comap_bijective {c : L ≃ₐ[F] L} {I : Type} {φ : I → L →+* ℂ} (h : CMData F c φ) :
    Function.Bijective fun w : InfinitePlace L => w.comap (algebraMap F L) := by
  have := h.real
  have := h.cplx
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨InfinitePlace.comap_surjective (k := F) (K := L), ?_⟩
  have h1 := IsTotallyComplex.finrank L
  have h2 := IsTotallyReal.finrank F
  have h3 := Module.finrank_mul_finrank ℚ F L
  rw [h.rank] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, IsTotallyReal.nrComplexPlaces_eq_zero F]
  omega

theorem sign_zpow_odd {x : ℝ} (hx : x ≠ 0) {n : ℤ} (hn : Odd n) :
    ((x : ℂ) / ((‖(x : ℂ)‖ : ℝ) : ℂ)) ^ n = if x < 0 then -1 else 1 := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_neg h]
    push_cast
    rw [div_neg, div_self hx', hn.neg_one_zpow]
  · rw [abs_of_nonneg (not_lt.1 h), div_self hx', one_zpow]

theorem etaInf_eq [IsTotallyReal F] (ψ : L →+* ℂ) {n : ℤ} (hn : Odd n) (k : Fˣ) :
    ((etaInf F ((InfinitePlace.mk ψ).comap (algebraMap F L)) k : ℂˣ) : ℂ) =
      (ψ (upF F k : Lˣ) / ((‖ψ (upF F k : Lˣ)‖ : ℝ) : ℂ)) ^ n := by
  have hr : ComplexEmbedding.IsReal (ψ.comp (algebraMap F L)) :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  have e : ψ (upF F k : Lˣ) = ((hr.embedding (k : F) : ℝ) : ℂ) := (hr.coe_embedding_apply (k : F)).symm
  unfold etaInf
  rw [InfinitePlace.comap_mk, InfinitePlace.embedding_mk_eq_of_isReal hr, e, sign_zpow_odd (by simp) hn,
    ← hr.coe_embedding_apply, Complex.ofReal_re]
  split_ifs <;> simp

theorem prod_etaInf {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ) {n : I → ℤ}
    (hn : ∀ i, Odd (n i)) (k : Fˣ) :
    ((∏ w : InfinitePlace F, etaInf F w k : ℂˣ) : ℂ) =
      ∏ i, (φ i (upF F k : Lˣ) / ((‖φ i (upF F k : Lˣ)‖ : ℝ) : ℂ)) ^ n i := by
  have := h.real
  rw [Units.coe_prod]
  symm
  refine Fintype.prod_bijective _ ((comap_bijective h).comp h.bij) _ _ fun i => ?_
  exact (etaInf_eq (φ i) (hn i) k).symm

theorem conj_conj {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ) (x : L) :
    c (c x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
  apply w.embedding.injective
  rw [h.embedding_conj, h.embedding_conj, Complex.conj_conj]

theorem exists_upF {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ) (k : Lˣ)
    (hk : c (k : L) = k) : ∃ a : Fˣ, upF F a = k := by
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := h.rank }
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h.rank]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (k : L)).2 fun σ => by
    by_cases e : σ = 1
    · rw [e]; rfl
    · rw [(hy σ e).trans (hy c h.ne).symm, hk]
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← ha, map_zero])
  exact ⟨Units.mk0 a ha0, Units.ext ha⟩

theorem div_conj_isRoot {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ) (k : Lˣ)
    (m : HeightOneSpectrum (𝓞 F) → ℤ) (hk : ∀ P : HeightOneSpectrum (𝓞 L), ordF P k = m (P.under (𝓞 F))) :
    ∃ r : ℕ, 0 < r ∧ ((k : L) / c k) ^ r = 1 := by
  have hk0 : (k : L) ≠ 0 := k.ne_zero
  have hc0 : c (k : L) ≠ 0 := by simp
  have h1 := normOne_unit_isRoot F L c I φ h (Units.mk0 (k / c k) (div_ne_zero hk0 hc0)) (by
    rw [Units.val_mk0, map_div₀, conj_conj h]; field_simp) (fun P => by
    obtain ⟨P', hP, -⟩ := existsUnique_conjPl c.toRingEquiv P
    have hu := (under_eq_iff_conjPl c h.rank h.ne P P').2 (Or.inr hP)
    have h2 : P'.valuation L (c (c k)) = P.valuation L (c k) := hP (c k)
    rw [conj_conj h] at h2
    rw [Units.val_mk0, map_div₀, ← h2, valuation_eq_exp, valuation_eq_exp, hk, hk, hu]
    exact div_self WithZero.exp_ne_zero)
  rwa [Units.val_mk0] at h1

theorem etaFin_unif_zpow (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    etaFin (L := L) F v (unif v) ^ ordF v k = etaFin (L := L) F v k := by
  unfold etaFin
  split_ifs
  · rw [ordF_unif_self, zpow_one]
  · rw [one_zpow]

theorem cmHeckeChar_ideleCompat_finprod {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ)
    (hord : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (hprod : ∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) *
      ∏ w : InfinitePlace F, etaInf F w a = 1)
    {n : I → ℤ} (hn : ∀ i, Odd (n i)) (δ : Lˣ)
    (hδ : ∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ))
    (hδ' : ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) (a : Fˣ)
    (m : HeightOneSpectrum (𝓞 F) → ℤ)
    (hk : ∀ P : HeightOneSpectrum (𝓞 L), ordF P (δ * upF F a) = -m (P.under (𝓞 F))) :
    ((∏ᶠ v, etaFin (L := L) F v (unif v) ^ m v : ℂˣ) : ℂ) =
      ∏ i, (φ i (δ * upF F a : Lˣ) / ((‖φ i (δ * upF F a : Lˣ)‖ : ℝ) : ℂ)) ^ n i := by
  have e1 : ∀ v, etaFin (L := L) F v (unif v) ^ m v = (etaFin (L := L) F v a)⁻¹ := fun v => by
    obtain ⟨P, rfl⟩ := exists_under (L := L) v
    have h1 := hk P
    rw [ordF_mul, hord] at h1
    unfold etaFin
    split_ifs with hc
    · obtain ⟨r, hr⟩ := hδ P hc
      have : m (P.under (𝓞 F)) = 2 * (-r) + -ordF (P.under (𝓞 F)) a := by omega
      rw [ordF_unif_self, zpow_one, this, zpow_add, zpow_neg, zpow_mul]
      simp [zpow_ofNat]
    · simp
  simp only [e1]
  rw [finprod_inv_distrib, inv_eq_of_mul_eq_one_right (hprod a), prod_etaInf h hn, ← one_mul (∏ i, _), ← hδ',
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← mul_zpow, Units.val_mul, map_mul, norm_mul]
  push_cast
  rw [mul_div_mul_comm]

theorem compat {c : L ≃ₐ[F] L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} (h : CMData F c φ)
    (hord : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (hprod : ∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) *
      ∏ w : InfinitePlace F, etaInf F w a = 1)
    {n : I → ℤ} (hn : ∀ i, Odd (n i))
    (hroot : ∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧
      (∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ)) ∧
      ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) (k : Lˣ)
    (m : HeightOneSpectrum (𝓞 F) → ℤ)
    (hk : ∀ P : HeightOneSpectrum (𝓞 L), ordF P k = -m (P.under (𝓞 F))) :
    ((∏ᶠ v, etaFin (L := L) F v (unif v) ^ m v : ℂˣ) : ℂ) =
      ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i := by
  obtain ⟨δ, hδe, hδ, hδ'⟩ := hroot _ (div_conj_isRoot h k (fun v => -m v) hk)
  have hk0 : (k : L) ≠ 0 := k.ne_zero
  have hck : c (k : L) ≠ 0 := by simp
  have hδ0 : (δ : L) ≠ 0 := δ.ne_zero
  have hcδ : c (δ : L) ≠ 0 := by simp
  have e : (δ : L) * c (k : L) = k * c (δ : L) := by
    calc (δ : L) * c (k : L) = (k / c k * c δ) * c (k : L) := by rw [← hδe]
      _ = k * c (δ : L) := by field_simp
  obtain ⟨a, ha⟩ := exists_upF h (δ⁻¹ * k) (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    field_simp
    linear_combination e)
  obtain rfl : k = δ * upF F a := by rw [ha, mul_inv_cancel_left]
  exact cmHeckeChar_ideleCompat_finprod h hord hprod hn δ hδ hδ' a m hk

theorem infIdele_mem (w : InfinitePlace L) (y : (w.Completion)ˣ) : infIdele L w y ∈ unitIdl L := fun v => by
  show Valued.v (1 : v.adicCompletion L) = 1
  exact map_one _

theorem infDiag_eq (k : Lˣ) : infDiag k = ∏ w, infIdele L w (atInf w k) := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply]; rfl

open Classical in

theorem exists_unramified_resEta : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → (∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k) → (∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) * ∏ w : InfinitePlace F, etaInf F w a = 1) → ∀ (n : I → ℤ), (∀ i, Odd (n i)) → (∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧ (∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ)) ∧ ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ (∀ v, χ.UnrAt v) ∧ χ.ResEta F ∧ χ.HasInf φ n := by
  intro F L _ _ _ _ _ c I _ φ h hord hprod n hn hroot
  have := h.real
  obtain ⟨ψ, hψc, hψu, hψi, -, hψl, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar L I φ h.bij n ∅ (fun _ => 1) (by simp)
  have hψl' : ∀ v x, ψ (localIdele L v x) = 1 := fun v x => hψl v (by simp) x
  have hψF : ∀ v k, ψ (locF F v k) = 1 := fun v k => by
    unfold locF
    rw [map_prod]
    exact Finset.prod_eq_one fun Q _ => hψl' _ _
  have hψinf : ∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i := fun k => by
    rw [infDiag_eq, map_prod, Units.coe_prod]
    symm
    exact Fintype.prod_bijective _ h.bij _ _ fun i => (hψi i k).symm
  let β := freeHom fun v => locF (L := L) F v (unif v)
  let b := freeHom fun v => etaFin (L := L) F v (unif v)
  have hψβ : ∀ m, ψ (β m) = 1 := fun m => by
    show ψ (freeHom _ (Multiplicative.ofAdd (Multiplicative.toAdd m))) = 1
    rw [freeHom_apply, map_prod]
    exact Finset.prod_eq_one fun v _ => by rw [map_zpow, hψF, one_zpow]
  obtain ⟨χ, hχc, hχu, hχU, hχA⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles L)
    (Lˣ × Multiplicative (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (unitIdl L)
    (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open L).1 ((diagUnits L).coprod β) (MonoidHom.coprod 1 b) ψ hψc hψu
    (fun y => by
      show ‖((1 * freeHom _ (Multiplicative.ofAdd (Multiplicative.toAdd y.2)) : ℂˣ) : ℂ)‖ = 1
      rw [one_mul, freeHom_apply, Units.coe_prod, norm_prod]
      refine Finset.prod_eq_one fun v _ => ?_
      unfold etaFin
      split_ifs <;> simp)
    (fun y hy => by
      obtain ⟨k, m⟩ := y
      show 1 * freeHom _ (Multiplicative.ofAdd (Multiplicative.toAdd m)) = ψ (diagUnits L k * β m)
      rw [one_mul, map_mul, hψβ, mul_one, hψd, Finset.prod_empty, mul_one, freeHom_eq_finprod]
      apply Units.ext
      rw [hψinf]
      refine compat h hord hprod hn hroot k _ fun P => ?_
      have h1 : valAt P (diagUnits L k * freeHom _ (Multiplicative.ofAdd (Multiplicative.toAdd m))) = 1 := hy P
      rw [map_mul, valAt_diag, valAt_free hord, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h1
      omega)
  have hχd : ∀ k : Lˣ, χ (diagUnits L k) = 1 := fun k => by simpa using hχA (k, 1)
  have hχβ : ∀ m, χ (β m) = b m := fun m => by simpa using hχA (1, m)
  refine ⟨⟨χ, hχc, hχd⟩, hχu, fun v x hx => ?_, ⟨fun v k => ?_, fun w k => ?_⟩, fun k => ?_⟩
  · show χ (localIdele L v x) = 1
    rw [hχU _ fun w => ?_, hψl']
    show valAt w _ = 1
    by_cases e : w = v
    · subst e; rw [valAt_localIdele_self]; exact hx
    · exact valAt_localIdele_ne e x
  · have e : HChar.resFin ⟨χ, hχc, hχd⟩ v k = χ (locF F v k) := by
      rw [HChar.resFin_apply]
      unfold locF
      rw [map_prod]
      rfl
    have h1 := hχβ (Multiplicative.ofAdd (Finsupp.single v (ordF v k)))
    have h2 := hχU (locF F v k * (β (Multiplicative.ofAdd (Finsupp.single v (ordF v k))))⁻¹) fun P => by
      show valAt P _ = 1
      rw [map_mul, map_inv, valAt_locF hord, valAt_free hord, Finsupp.single_apply]
      simp only [eq_comm (a := v)]
      exact mul_inv_cancel₀ WithZero.exp_ne_zero
    rw [map_mul, map_mul, map_inv, map_inv, hψF, hψβ, inv_one, mul_one, mul_inv_eq_one, h1] at h2
    rw [e, h2, freeHom_single, etaFin_unif_zpow]
  · obtain ⟨i, rfl⟩ := ((comap_bijective h).comp h.bij).2 w
    have e : aboveInf (L := L) F ((InfinitePlace.mk (φ i)).comap (algebraMap F L)) = {InfinitePlace.mk (φ i)} := by
      ext w'
      simp only [aboveInf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact (comap_bijective h).1.eq_iff
    show HChar.resInf _ ((InfinitePlace.mk (φ i)).comap (algebraMap F L)) k =
      etaInf F ((InfinitePlace.mk (φ i)).comap (algebraMap F L)) k
    rw [HChar.resInf_apply, e, Finset.prod_singleton]
    apply Units.ext
    rw [etaInf_eq (φ i) (hn i), ← hψi, ← hχU _ (infIdele_mem _ _)]
    rfl
  · rw [← hψinf, ← hχU _ (by rw [infDiag_eq]; exact prod_mem fun w _ => infIdele_mem _ _)]
    rfl

end GlobalTheory.Mem.EtaExt
