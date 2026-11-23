import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.Places

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

abbrev Tau (R : Ranks) : Type := R.Psi

instance tauFintype (R : Ranks) : Fintype (Tau R) := Fintype.ofFinite _

theorem card_Tau {R : Ranks} (H : Host R) : Fintype.card (Tau R) = R.f := by
  rw [← Nat.card_eq_fintype_card]
  exact (factCardPsi R H).1

section Cond

variable {R : Ranks} (H : Host R) {p : ℕ}

theorem mod_eq_one_of_cond (h : p % (H.QS * H.q * H.d) = 1) {m : ℕ} (hm : 1 < m)
    (hdv : m ∣ H.QS * H.q * H.d) : p % m = 1 := by
  rw [← Nat.mod_mod_of_dvd p hdv, h, Nat.mod_eq_of_lt hm]

theorem four_dvd_QS : 4 ∣ H.QS := (pow_dvd_pow 2 (Nat.le_add_left 2 R.e)).trans H.tower_dvd

theorem cls_eq_splitK_of_cond (h : p % (H.QS * H.q * H.d) = 1) : H.cls p = .splitK := by
  have hq1 := H.hyp.1.one_lt
  have hd1 := H.hyp.2.1.one_lt
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have h4 : p % 4 = 1 := mod_eq_one_of_cond H h (by norm_num) (((four_dvd_QS H).mul_right _).mul_right _)
  have hq : p % H.q = 1 := mod_eq_one_of_cond H h hq1 ⟨H.QS * H.d, by ring⟩
  have hd : p % H.d = 1 := mod_eq_one_of_cond H h hd1 ⟨H.QS * H.q, by ring⟩
  have h2 : p ∉ H.small := by
    intro hp
    have hp' : p ∈ H.QS.primeFactors := hp
    have := mod_eq_one_of_cond H h (Nat.prime_of_mem_primeFactors hp').one_lt
      (((Nat.dvd_of_mem_primeFactors hp').mul_right _).mul_right _)
    simp at this
  have hq' : p ≠ H.q := by rintro rfl; simp at hq
  have hd' : p ≠ H.d := by rintro rfl; simp at hd
  have hj : jacobiSym (-(H.d : ℤ)) p = 1 := by
    rw [jacobiSym.neg _ (Nat.odd_iff.2 (by omega)), ZMod.χ₄_nat_one_mod_four h4, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.2 (by omega)) h4, jacobiSym.mod_left,
      ← Int.natCast_mod, hd, Nat.cast_one, jacobiSym.one_left]
  exact (primeClass_eq_splitK_iff H.toHostRaw).2 ⟨h2, hq', hd', hj⟩

end Cond

def HasHyperbolicAuxiliaryFrame {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (S : Spaces R F E) (j : ℕ) : Prop :=
  ∃ e f : Fin ((R.m - 1 - j) / 2) → (S.Y j).V,
    (∀ i i', (S.Y j).hT (e i) (e i') = 0) ∧ (∀ i i', (S.Y j).hT (f i) (f i') = 0) ∧
    (∀ i i', (S.Y j).hT (e i) (f i') = if i = i' then 1 else 0) ∧
    (∀ i x, (S.Y j).hT (S.iXY j x) (e i) = 0 ∧ (S.Y j).hT (S.iXY j x) (f i) = 0) ∧
    (Even j → ∃ z : (S.Y j).V, (S.Y j).hT z z = -(S.T : E) ∧ (∀ x, (S.Y j).hT (S.iXY j x) z = 0) ∧
      ∀ i, (S.Y j).hT z (e i) = 0 ∧ (S.Y j).hT z (f i) = 0)

theorem auxiliary_frame_zero {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (S : Spaces R F E) : HasHyperbolicAuxiliaryFrame S 0 := by
  have h : (R.m - 1 - 0) / 2 = R.rS := by
    obtain ⟨a, ha⟩ := R.m_even
    unfold Ranks.rS
    omega
  refine ⟨fun i => S.hypE (i.cast h), fun i => S.hypF (i.cast h), fun _ _ => S.hyp_ee _ _, fun _ _ => S.hyp_ff _ _,
    fun i i' => ?_, fun _ x => S.hyp_orthX _ x, fun _ => ⟨S.zm, S.zm_norm, S.zm_orth, fun _ => S.hyp_orthz _⟩⟩
  rw [S.hyp_ef]
  simp [Fin.ext_iff]

structure Pre where

  R : Ranks

  host : Host R

  ccK_top : host.ccK = ⊤

  level_cond : ∀ p ∈ host.levelPrimes, p.Prime ∧ p % (host.QS * host.q * host.d) = 1

  BB_disj : Disjoint (Formalism.CyclotomicNorms.BB R.r (host.g 0)) (Formalism.CyclotomicNorms.BB R.r (host.g 1))

  sp : @Spaces R host.F host.E _ _ _ _ host.cmStar _

  Y_sigval : letI := host.cmStar; ∀ j, j ≤ R.m → ∀ τ : host.E →+* ℂ, (sp.Y j).sig τ = sigYD R j

  auxiliaryFrame : letI := host.cmStar; ∀ j, 0 < j → j < R.m → HasHyperbolicAuxiliaryFrame sp j

  V_pos : letI := host.cmStar; ∀ j, 1 ≤ j → j ≤ R.m → sp.Vneg j = false

  z_norm : letI := host.cmStar; (sp.X R.m).hT sp.z sp.z = (sp.T : host.E)

  Word : Type
  [wordFin : Fintype Word]

  u₀ : Word

  hc : Tau R → HCParam R

  hcW : Word → Tau R → HCParam R
  hcW_base : hcW u₀ = hc
  hcW_v : ∀ u τ, (hcW u τ).v = (hc τ).v
  hcW_b : ∀ u τ, (hcW u τ).b = (hc τ).b
  hcW_e : ∀ u τ, (hcW u τ).e = (hc τ).e
  hcW_first : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hc τ).u ⟨0, h⟩
  hcW_last : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hc τ).u ⟨R.k - 1, by omega⟩

  T : Word → ℕ
  T_level : ∀ u, T u ∈ host.levelPrimes

  T_norm : ∀ u, ∃ π : 𝓞 host.E, (π : host.E) ∈ host.K ∧
    (π : host.E) * host.conj (π : host.E) = (T u : host.E) ∧
    (π - 1) ∈ Ideal.span {((host.QS * host.q * host.d * (host.g 0 * host.g 1) ^ 2 : ℕ) : 𝓞 host.E)}

  sp_T : letI := host.cmStar; sp.T = T u₀

  cOf : Word → host.E
  cOf_ne : ∀ u, cOf u ≠ 0
  cOf_eq : ∀ u, cOf u * host.conj (cOf u) * (T u : host.E) = (T u₀ : host.E)
  T_ne_pde : ∀ u, T u ≠ host.pde ∧ T u ≠ host.pde'

  duStar : Word → ℕ
  duStar_pos : ∀ u, 0 < duStar u

  Dstar : ℝ
  Dstar_pos : 0 < Dstar

  GamP : ℝ
  one_lt_gammaP : 1 < GamP

  T_win : ∀ u, (Dstar / duStar u) ^ ((1 : ℝ) / (R.f * R.k)) * GamP ^ (-(2 : ℝ) / (R.f * R.k)) ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) *
      ((Dstar / duStar u) ^ ((1 : ℝ) / (R.f * R.k)) * GamP ^ (-(2 : ℝ) / (R.f * R.k)))

attribute [instance] Pre.wordFin

namespace Pre

variable (B : Pre)

theorem level_prime : ∀ p ∈ B.host.levelPrimes, p.Prime := fun p hp => (B.level_cond p hp).1

theorem level_split : ∀ p ∈ B.host.levelPrimes, B.host.cls p = .splitK :=
  fun p hp => cls_eq_splitK_of_cond B.host (B.level_cond p hp).2

theorem level_mod_four : ∀ p ∈ B.host.levelPrimes, p % 4 = 1 := fun p hp =>
  mod_eq_one_of_cond B.host (B.level_cond p hp).2 (by norm_num)
    (((four_dvd_QS B.host).mul_right _).mul_right _)

theorem g_cond : ∀ k, B.host.g k % (B.host.QS * B.host.q * B.host.d) = 1 :=
  fun k => (B.level_cond _ (B.host.g_level k)).2

theorem pde_cond : B.host.pde % (B.host.QS * B.host.q * B.host.d) = 1 ∧
    B.host.pde' % (B.host.QS * B.host.q * B.host.d) = 1 :=
  ⟨(B.level_cond _ B.host.pde_level.1).2, (B.level_cond _ B.host.pde_level.2).2⟩

theorem T_prime : ∀ u, (B.T u).Prime := fun u => B.level_prime _ (B.T_level u)

theorem T_cond : ∀ u, B.T u % (B.host.QS * B.host.q * B.host.d) = 1 :=
  fun u => (B.level_cond _ (B.T_level u)).2

theorem auxiliary_frame_exists : letI := B.host.cmStar; ∀ j, j < B.R.m → HasHyperbolicAuxiliaryFrame B.sp j := by
  letI := B.host.cmStar
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | h
  · exact auxiliary_frame_zero _
  · exact B.auxiliaryFrame j h hj

theorem V_posDef : letI := B.host.cmStar; ∀ j, 1 ≤ j → j ≤ B.R.m → (B.sp.V j).IsPosDef := by
  letI := B.host.cmStar
  intro j h1 h2 τ
  rw [factVSig B.R B.host.F B.sp j h1 h2 τ, B.V_pos j h1 h2, B.sp.V_rank j h1 h2]
  rfl

theorem X_posDef : letI := B.host.cmStar; ∀ j, j ≤ B.R.m → (B.sp.X j).IsPosDef := by
  letI := B.host.cmStar
  intro j hj τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := B.sp.cm.cmUnram.2.1 τ
  have hk := B.R.m_add_three_le_k
  rcases B.sp.X_def j hj τ with h | h
  · exact h
  exfalso
  have hsX := B.sp.X_sig j τ
  rw [h] at hsX
  rcases hj.lt_or_eq with hlt | rfl
  · have hw : (Matrix.of fun a b => (B.sp.Y j).hT (B.sp.iXY j ((B.sp.X j).frame a))
        (B.sp.iXY j ((B.sp.X j).frame b))) = (B.sp.X j).gram := by
      refine Matrix.ext fun a b => ?_
      exact B.sp.iXY_isom j hlt _ _
    rw [← hw] at hsX
    have hsY := B.sp.Y_sig j τ
    have hsum := sig_sum _ (B.sp.Y_sig j) τ
    rw [B.Y_sigval j hj τ] at hsY hsum
    have key := (sig_family (B.sp.Y j) τ hτ _ hsX hsY).2
    rw [B.sp.X_rank j hj] at key
    simp only [sigYD, Ranks.N] at key hsum
    omega
  · have hsY := B.sp.Y_sig B.R.m τ
    rw [B.Y_sigval _ hj τ] at hsY
    have hw : (Matrix.of fun a b => (B.sp.X B.R.m).hT (B.sp.iX' (B.sp.eYm.symm ((B.sp.Y B.R.m).frame a)))
        (B.sp.iX' (B.sp.eYm.symm ((B.sp.Y B.R.m).frame b)))) = (B.sp.Y B.R.m).gram := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.of_apply, B.sp.iX'_isom, ← B.sp.eYm_isom]
      simp [HSpace.gram]
    rw [← hw] at hsY
    have key := (sig_family (B.sp.X B.R.m) τ hτ _ hsY hsX).1
    simp only [sigYD, Ranks.rankY, Ranks.r] at key
    omega

def conjF : B.host.E →ₐ[B.host.F] B.host.E := letI := B.host.cmStar; B.sp.cm.sig

theorem conjF_eq (x : B.host.E) : B.conjF x = B.host.conj x := bridge_star_holds B.R B.host x

def zOf (u : B.Word) : letI := B.host.cmStar; (B.sp.X B.R.m).V :=
  letI := B.host.cmStar; (B.cOf u)⁻¹ • B.sp.z

theorem zOf_norm (u : B.Word) :
    letI := B.host.cmStar; (B.sp.X B.R.m).hT (B.zOf u) (B.zOf u) = (B.T u : B.host.E) := by
  letI := B.host.cmStar
  have hs : ∀ x : B.host.E, star x = B.host.conj x := bridge_star_holds B.R B.host
  have h0 := B.cOf_ne u
  have h1 : B.host.conj (B.cOf u) ≠ 0 := by simpa using h0
  unfold zOf
  rw [map_smulₛₗ, map_smulₛₗ, LinearMap.smul_apply, B.z_norm, B.sp_T, ← B.cOf_eq u, starRingEnd_apply, star_inv₀,
    hs, RingHom.id_apply, smul_eq_mul, smul_eq_mul]
  field_simp

def restRowsFiniteGroupCard : ℕ := ∏ k : Fin 2, (Nat.card (GL (Fin B.R.r) (ZMod (B.host.g k)))) ^ B.R.f

theorem restRowsFiniteGroupCard_pos : 0 < B.restRowsFiniteGroupCard := by
  refine Finset.prod_pos fun k _ => pow_pos ?_ _
  have : NeZero (B.host.g k) := ⟨(B.host.g_prime k).ne_zero⟩
  exact Nat.card_pos

def ramOrder : ℕ := 8 * (∏ l ∈ B.host.small, l) * B.host.q

theorem ramOrder_pos : 0 < B.ramOrder := by
  unfold ramOrder
  refine Nat.mul_pos (Nat.mul_pos (by norm_num) (Finset.prod_pos fun l hl => ?_)) B.host.hyp.1.pos
  exact (Nat.prime_of_mem_primeFactors hl).pos

theorem eight_mul_q_dvd_ramOrder : 8 * B.host.q ∣ B.ramOrder :=
  Nat.mul_dvd_mul (Dvd.intro _ rfl) dvd_rfl

theorem eight_mul_dvd_ramOrder {l : ℕ} (hl : l ∈ B.host.small) : 8 * l ∣ B.ramOrder :=
  (Nat.mul_dvd_mul_left 8 (Finset.dvd_prod_of_mem (fun l => l) hl)).mul_right _

example : 0 ∉ B.host.levelPrimes ∧ 1 ∉ B.host.levelPrimes ∧ 2 ∉ B.host.levelPrimes ∧ 4 ∉ B.host.levelPrimes :=
  ⟨fun h => Nat.not_prime_zero (B.level_prime _ h), fun h => Nat.not_prime_one (B.level_prime _ h),
    fun h => by simpa using B.level_mod_four _ h, fun h => by simpa using B.level_mod_four _ h⟩

example : letI := B.host.cmStar;
    (B.sp.X B.R.m).hT B.sp.z B.sp.z + (B.sp.Y 0).hT B.sp.zm B.sp.zm = 0 := by
  letI := B.host.cmStar
  rw [B.z_norm, B.sp.zm_norm, add_neg_cancel]

end Pre

structure Base extends Pre where

  LL : Type
  [instLL : Field LL]
  [nfLL : NumberField LL]
  [starLL : StarRing LL]
  [galLL : IsGalois ℚ LL]

  embLL : LL →+* ℂ

  starLL_cx : ∀ x : LL, embLL (star x) = starRingEnd ℂ (embLL x)

  embE : host.E →+* LL
  embE_φ₀ : embLL.comp embE = host.φ₀

  LL0 : IntermediateField ℚ LL
  coeffGaloisSubfield_isGalois : IsGalois ℚ LL0

  Ks : IntermediateField ℚ LL
  Ks_le : Ks ≤ LL0
  E_le_Ks : ∀ x : host.E, embE x ∈ Ks

  roots_Ks : ∀ N ∈ [toPre.restRowsFiniteGroupCard, host.g 0 * (host.g 0 - 1), host.g 1 * (host.g 1 - 1), 3 ^ 4, 5 ^ 4],
    ∃ z ∈ Ks, embLL z = Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))

  roots_Ks' : ∀ N ∈ [host.pde, host.pde', classNumber host.E],
    ∃ z ∈ Ks, embLL z = Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))

  capit : ∀ 𝔞 : Ideal (𝓞 host.E), ∃ β : Ks,
    Submodule.span (𝓞 Ks) {β} = Submodule.span (𝓞 Ks) {x : Ks | ∃ a ∈ 𝔞, (x : LL) = embE (a : host.E)}

  kPsi : ∀ j, 1 ≤ j → j ≤ R.m → ∀ 𝔞 : Ideal (𝓞 host.E), 𝔞 ≠ ⊥ → ∃ β : Ks, β ≠ 0 ∧
    Submodule.span (𝓞 Ks) {β} =
      ∏ g : Tau R,
        (Submodule.span (𝓞 Ks) {x : Ks | ∃ a ∈ 𝔞, (x : LL) = embE (host.sigmaOf g (a : host.E))} ^ (R.sigW j).1 *
          Submodule.span (𝓞 Ks) {x : Ks | ∃ a ∈ 𝔞, (x : LL) = embE (host.sigmaOf g (host.conj (a : host.E)))} ^
            (R.sigW j).2) ∧
    ∀ σ : Ks →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((R.sigW j).1 + (R.sigW j).2)

  rootOfUnity_eightQ_mem_coeffGaloisSubfield : ∃ z ∈ LL0, embLL z = Complex.exp (2 * Real.pi * Complex.I / (toPre.ramOrder : ℕ))

  roots_LL : ∀ u, ∃ z : LL, embLL z = Complex.exp (2 * Real.pi * Complex.I / (T u : ℕ))

attribute [instance] Base.instLL Base.nfLL Base.starLL Base.galLL

namespace Base

variable (B : Base)

instance tcLL : NumberField.IsTotallyComplex B.LL := by
  have := B.host.isCMField_hostE
  letI : Algebra B.host.E B.LL := B.embE.toAlgebra
  exact NumberField.isTotallyComplex_of_algebra B.host.E B.LL

abbrev places : Rows.Places B.LL := Formalism.BasicNotions.Examples₂.placesOf B.LL

abbrev O : Type := 𝓞 B.Ks

def OtoLL : B.O →+* B.LL := (B.Ks.val : B.Ks →+* B.LL).comp (algebraMap (𝓞 B.Ks) B.Ks)

theorem OtoLL_injective : Function.Injective B.OtoLL :=
  Subtype.val_injective.comp (RingOfIntegers.coe_injective (K := B.Ks))

theorem O_int (y : B.O) : IsIntegral ℤ (B.OtoLL y) :=
  (RingOfIntegers.isIntegral_coe y).map (B.Ks.val : B.Ks →+* B.LL).toIntAlgHom

theorem O_full (x : B.LL) (hx : x ∈ B.Ks) (hi : IsIntegral ℤ x) : ∃ y : B.O, B.OtoLL y = x :=
  ⟨⟨⟨x, hx⟩, (isIntegral_algHom_iff (B.Ks.val : B.Ks →+* B.LL).toIntAlgHom Subtype.val_injective).1 hi⟩, rfl⟩

theorem O_contains (x : 𝓞 B.host.E) : ∃ y : B.O, B.OtoLL y = B.embE (x : B.host.E) :=
  B.O_full _ (B.E_le_Ks _) ((RingOfIntegers.isIntegral_coe x).map B.embE.toIntAlgHom)

theorem hostField_le_fixedField (x : B.host.E) : B.embE x ∈ B.LL0 := B.Ks_le (B.E_le_Ks x)

theorem embE_conj (x : B.host.E) : B.embE (B.host.conj x) = star (B.embE x) := by
  apply B.embLL.injective
  rw [B.starLL_cx]
  have h : ∀ y, B.embLL (B.embE y) = B.host.φ₀ y := fun y => RingHom.congr_fun B.embE_φ₀ y
  rw [h, h]
  exact B.host.conjE_apply _ _

theorem roots_of_unity_in_fixed_field {N : ℕ} (hN : N ∣ B.ramOrder) :
    ∃ z ∈ B.LL0, B.embLL z = Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) := by
  obtain ⟨z, hz, h⟩ := B.rootOfUnity_eightQ_mem_coeffGaloisSubfield
  obtain ⟨k, hk⟩ := hN
  have h0 := B.ramOrder_pos
  rw [hk] at h0 h
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; simp at h0)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; simp at h0)
  refine ⟨z ^ k, pow_mem hz k, ?_⟩
  rw [map_pow, h, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

def embKs : B.host.E →+* B.Ks := B.embE.codRestrict B.Ks B.E_le_Ks

def intE : 𝓞 B.host.E →+* B.O := RingOfIntegers.mapRingHom B.embKs

theorem OtoLL_intE (x : 𝓞 B.host.E) : B.OtoLL (B.intE x) = B.embE (x : B.host.E) := rfl

theorem isPrincipal_map_intE (𝔞 : Ideal (𝓞 B.host.E)) : (𝔞.map B.intE).IsPrincipal := by
  obtain ⟨β, hβ⟩ := B.capit 𝔞
  have hinj : Function.Injective (Algebra.linearMap (𝓞 B.Ks) B.Ks) := RingOfIntegers.coe_injective
  have hmap : Submodule.map (Algebra.linearMap (𝓞 B.Ks) B.Ks) (𝔞.map B.intE) = Submodule.span (𝓞 B.Ks) {β} := by
    rw [hβ, Ideal.map, Ideal.span, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, hx⟩
      exact ⟨_, ⟨a, ha, rfl⟩, Subtype.ext hx.symm⟩
  obtain ⟨b, -, hb⟩ : β ∈ Submodule.map (Algebra.linearMap (𝓞 B.Ks) B.Ks) (𝔞.map B.intE) :=
    hmap ▸ Submodule.mem_span_singleton_self β
  refine ⟨b, Submodule.map_injective_of_injective hinj ?_⟩
  rw [hmap, Submodule.map_span, Set.image_singleton, hb]

example : ∃ z ∈ B.Ks, IsPrimitiveRoot z 3 := by
  obtain ⟨z, hz, h⟩ := B.roots_Ks (3 ^ 4) (by simp)
  have h1 : IsPrimitiveRoot (B.embLL z) (3 ^ 4) := h ▸ Complex.isPrimitiveRoot_exp _ (by norm_num)
  exact ⟨z ^ 27, pow_mem hz _, (h1.of_map_of_injective B.embLL.injective).pow (by norm_num) (by norm_num)⟩

end Base

end GlobalTheory.Mem

end
