import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.CoboundaryCommutesHomomorphism
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversal
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffVecConsPairEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog)

namespace BrC

section Alg

variable {K : Type} [Field K]

private theorem lgF_zero_lemma (l : ℕ) : PowerSeries.constantCoeff (lgF K l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF, PowerSeries.coeff_mk]
  simp

private theorem lgF_one_lemma_2 {l : ℕ} (hl : 2 ≤ l) : PowerSeries.coeff 1 (lgF K l) = 1 := by
  have h1 : l ^ 2 ≠ 1 := by nlinarith
  rw [lgF, PowerSeries.coeff_mk]
  simp [Finset.sum_range_succ, h1, h1.symm]

theorem logPair {l : ℕ} (hl : 2 ≤ l) : C.IsLogPair (lgF K l) (expF K l) := by
  have h0 := lgF_zero_lemma (K := K) l
  have h1 := lgF_one_lemma_2 (K := K) hl
  have hu : IsUnit (PowerSeries.coeff 1 (lgF K l)) := by rw [h1]; exact isUnit_one
  have he : expF K l = (lgF K l).substInvOfIsUnit hu := by rw [expF, dif_pos hu]
  refine ⟨h0, h1, ?_, ?_, ?_⟩
  · rw [he]; exact PowerSeries.constantCoeff_substInvOfIsUnit _ _
  · rw [he]; exact PowerSeries.subst_substInvOfIsUnit_left _ h0 hu
  · rw [he]; exact PowerSeries.subst_substInvOfIsUnit_right _ h0 hu

end Alg

section Cont

variable {K : Type} [Field K]

theorem coeff_mul_pow_zero {τ : Type} {x y : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    {e : τ →₀ ℕ} {i j : ℕ} (h : e.degree < i ∨ e.degree < j) :
    MvPowerSeries.coeff e (x ^ i * y ^ j) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  have hi := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero i hx
  have hj := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero j hy
  have hm := MvPowerSeries.le_order_mul (f := x ^ i) (g := y ^ j)
  rcases h with h | h
  · calc (e.degree : ℕ∞) < i := by exact_mod_cast h
      _ ≤ (x ^ i).order := hi
      _ ≤ (x ^ i).order + (y ^ j).order := le_self_add
      _ ≤ _ := hm
  · calc (e.degree : ℕ∞) < j := by exact_mod_cast h
      _ ≤ (y ^ j).order := hj
      _ ≤ (x ^ i).order + (y ^ j).order := le_add_self
      _ ≤ _ := hm

theorem coeffCont_subst2 [TopologicalSpace K] [IsTopologicalRing K] {T : Type} [TopologicalSpace T]
    {τ : Type} {a b : T → MvPowerSeries τ K} (ha : C.Clo.CoeffCont a) (hb : C.Clo.CoeffCont b)
    (ha0 : ∀ t, MvPowerSeries.constantCoeff (a t) = 0)
    (hb0 : ∀ t, MvPowerSeries.constantCoeff (b t) = 0) (f : MvPowerSeries (Fin 2) K) :
    C.Clo.CoeffCont fun t => MvPowerSeries.subst ![a t, b t] f := by
  intro n
  have key : ∀ t, MvPowerSeries.coeff n (MvPowerSeries.subst ![a t, b t] f) =
      ∑ d ∈ (Finset.range (n.degree + 1) ×ˢ Finset.range (n.degree + 1)).image
          (fun p : ℕ × ℕ => Finsupp.equivFunOnFinite.symm ![p.1, p.2]),
        MvPowerSeries.coeff d f • MvPowerSeries.coeff n (a t ^ d 0 * b t ^ d 1) := by
    intro t
    have hS : MvPowerSeries.HasSubst ![a t, b t] :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [ha0, hb0])
    rw [MvPowerSeries.coeff_subst hS]
    have hp : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![a t, b t] s) ^ e) = a t ^ d 0 * b t ^ d 1 := by
      intro d; rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]; rfl
    simp only [hp]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe]
    by_contra hne
    apply hd
    have hlt : n.degree < d 0 ∨ n.degree < d 1 := by
      by_contra h'
      push_neg at h'
      exact hne (Finset.mem_image.2 ⟨(d 0, d 1), Finset.mem_product.2
        ⟨Finset.mem_range.2 (Nat.lt_succ_of_le h'.1), Finset.mem_range.2 (Nat.lt_succ_of_le h'.2)⟩,
        by ext i; fin_cases i <;> rfl⟩)
    rw [coeff_mul_pow_zero (ha0 t) (hb0 t) hlt, smul_zero]
  rw [show (fun t => MvPowerSeries.coeff n (MvPowerSeries.subst ![a t, b t] f)) = _ from funext key]
  refine continuous_finset_sum _ fun d _ => ?_
  exact (((ha.pow (d 0)).mul (hb.pow (d 1))) n).const_smul (MvPowerSeries.coeff d f)

end Cont

section Normed

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def Osub (σ : K →+* K) : Subring K :=
  Formalism.G.unitBall K ⊓ (σ.comp σ).eqLocus (RingHom.id K)

theorem mem_Osub {σ : K →+* K} {a : K} : a ∈ Osub σ ↔ ‖a‖ ≤ 1 ∧ σ (σ a) = a := by
  simp only [Osub, Subring.mem_inf, RingHom.mem_eqLocus, RingHom.comp_apply, RingHom.id_apply]
  exact Iff.rfl

@[reducible] def starO {σ : K →+* K} (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) : StarRing (Osub σ) where
  star a := ⟨σ a.1, mem_Osub.2 ⟨hσ _ a.2.1, congrArg σ a.2.2⟩⟩
  star_involutive a := Subtype.ext a.2.2
  star_mul a b := Subtype.ext (by
    show σ (a.1 * b.1) = σ b.1 * σ a.1
    rw [map_mul, mul_comm])
  star_add a b := Subtype.ext (map_add σ a.1 b.1)

theorem ne_zero_of_norm {a : K} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h
  rw [h, norm_zero] at ha
  exact zero_ne_one ha

theorem norm_sub_le (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

def unitO {σ : K →+* K} {a : K} (ha : ‖a‖ = 1) (hs : σ (σ a) = a) : (Osub σ)ˣ where
  val := ⟨a, mem_Osub.2 ⟨ha.le, hs⟩⟩
  inv := ⟨a⁻¹, mem_Osub.2 ⟨by rw [norm_inv, ha, inv_one], by rw [map_inv₀, map_inv₀, hs]⟩⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (ne_zero_of_norm ha))
  inv_val := Subtype.ext (inv_mul_cancel₀ (ne_zero_of_norm ha))

theorem norm_unitO {σ : K →+* K} (u : (Osub σ)ˣ) : ‖((u : Osub σ) : K)‖ = 1 := by
  have h1 : ‖((u : Osub σ) : K)‖ ≤ 1 := (mem_Osub.1 (u : Osub σ).2).1
  have h2 : ‖(((u⁻¹ : (Osub σ)ˣ) : Osub σ) : K)‖ ≤ 1 := (mem_Osub.1 ((u⁻¹ : (Osub σ)ˣ) : Osub σ).2).1
  have h3 : ((u : Osub σ) : K) * (((u⁻¹ : (Osub σ)ˣ) : Osub σ) : K) = 1 := by
    exact congrArg Subtype.val u.mul_inv
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  have h5 := mul_le_mul_of_nonneg_left h2 (norm_nonneg ((u : Osub σ) : K))
  rw [h4, mul_one] at h5
  exact le_antisymm h1 h5

variable [CharZero K]

theorem norm_two {l : ℕ} {σ : K →+* K} (hU : UnrOK K l σ) : ‖(2 : K)‖ = 1 := by
  obtain ⟨hp, h2p, hpn, -, -⟩ := hU
  have hle : ‖(2 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2
  obtain ⟨m, hm⟩ : Odd l := hp.odd_of_ne_two (by omega)
  have h1 : (1 : K) = (l : K) - 2 * (m : K) := by rw [hm]; push_cast; ring
  have h3 : (1 : ℝ) ≤ max ‖(l : K)‖ ‖2 * (m : K)‖ := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(l : K) - 2 * (m : K)‖ := by rw [← h1]
      _ ≤ _ := BrC.norm_sub_le _ _
  rw [hpn, norm_mul] at h3
  have hm1 : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  have hl : ((l : ℕ) : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < l))
  have h4 := mul_le_of_le_one_right (norm_nonneg (2 : K)) hm1
  rcases le_max_iff.1 h3 with h | h
  · linarith
  · linarith

theorem mem_closure_nat {l : ℕ} {σ : K →+* K} (hU : UnrOK K l σ) {x : K} (hx : ‖x‖ ≤ 1)
    (hs : σ x = x) : x ∈ closure (Set.range fun n : ℕ => (n : K)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have h1 : (1 : ℝ) < l := by exact_mod_cast (by have := hU.2.1; omega : 1 < l)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ h1)
  obtain ⟨n, hn⟩ := fixed_is_limit K l σ hU x hx hs k
  refine ⟨n, ⟨n, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  rw [inv_pow] at hk
  exact lt_of_le_of_lt hn hk

theorem of_closed_nat {l : ℕ} {σ : K →+* K} (hU : UnrOK K l σ) {P : K → Prop}
    (hc : IsClosed {z : K | P z}) (hi : ∀ n : ℕ, P (n : K)) {x : K} (hx : ‖x‖ ≤ 1)
    (hs : σ x = x) : P x := by
  exact closure_minimal (Set.range_subset_iff.2 hi) hc (mem_closure_nat hU hx hs)

theorem of_closed_int {l : ℕ} {σ : K →+* K} (hU : UnrOK K l σ) {P : K → Prop}
    (hc : IsClosed {z : K | P z}) (hi : ∀ n : ℤ, P (n : K)) {x : K} (hx : ‖x‖ ≤ 1)
    (hs : σ x = x) : P x := by
  exact of_closed_nat hU hc (fun n => by simpa using hi n) hx hs

theorem lawLog {l : ℕ} (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K} (hF : IsLawOfLog l F) :
    Formalism.L2.Th1.B.LawLog F (lgF K l) := by
  exact ⟨hF.1, hF.2.1, lgF_zero_lemma l, lgF_one_lemma_2 hl, hF.2.2⟩

theorem endInt {l : ℕ} {σ : K →+* K} (hU : UnrOK K l σ) {α : K} (hα : ‖α‖ ≤ 1)
    (hs : σ (σ α) = α) : C.EndInt (Formalism.G.unitBall K) (lgF K l) (expF K l) α := by
  have hl : 2 ≤ l := by have := hU.2.1; omega
  obtain ⟨hLP0, -, hLP2, -, hLP4⟩ := logPair (K := K) hl
  have hgc : MvPowerSeries.constantCoeff (PowerSeries.C α * lgF K l) = 0 := by
    change PowerSeries.constantCoeff _ = 0
    simp [hLP0]
  have hg : PowerSeries.HasSubst (PowerSeries.C α * lgF K l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hgc
  have he : PowerSeries.HasSubst (expF K l) := PowerSeries.HasSubst.of_constantCoeff_zero' hLP2
  have hmul : IsMul l α (mulS K l α) := by
    refine ⟨?_, ?_⟩
    · change MvPowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C α * lgF K l) (expF K l)) = 0
      rw [PowerSeries.constantCoeff_subst hg]
      apply finsum_eq_zero_of_forall_eq_zero
      intro d
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [hLP2]
      · simp [map_pow, hgc, hd.ne']
    · rw [mulS, ← PowerSeries.subst_comp_subst_apply he hg, hLP4, PowerSeries.subst_X hg]
  intro n
  exact (mulSpec K l σ hU α).2.2 hα hs _ hmul n

theorem phNorm_iff {l : ℕ} {σ : K →+* K} (ph : PowerSeries K) (α : K) :
    C.PhNormAt (Formalism.G.unitBall K) (lgF K l) (expF K l) ph α (σ α) ↔ NormRel l σ ph α := by
  unfold C.PhNormAt NormRel
  rw [Formalism.L2.Th1.C.simeq_iff_congruence K Unit, PowerSeries.smul_eq_C_mul]
  rfl

theorem two_units {l : ℕ} {σ : K →+* K} (hU : UnrOK K l σ) (α : Osub σ) :
    ∃ u v : (Osub σ)ˣ, α = u + v := by
  have hα := mem_Osub.1 α.2
  have h2 := norm_two hU
  rcases lt_or_eq_of_le hα.1 with h | h
  · have hn : ‖(α : K) + 1‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne), norm_one]
      exact max_eq_right h.le
    refine ⟨unitO hn (by simp [hα.2]), unitO (a := -1) (by simp) (by simp), ?_⟩
    apply Subtype.ext
    show (α : K) = ((α : K) + 1) + -1
    ring
  · refine ⟨unitO (a := 2 * (α : K)) (by rw [norm_mul, h2, h, one_mul]) (by simp [hα.2, map_ofNat]),
      unitO (a := -(α : K)) (by rw [norm_neg, h]) (by simp [hα.2]), ?_⟩
    apply Subtype.ext
    show (α : K) = 2 * (α : K) + -(α : K)
    ring

theorem all {l : ℕ} {σ : K →+* K} (hU : UnrOK K l σ) {F : MvPowerSeries (Fin 2) K}
    (hF : IsLawOfLog l F) {ph : PowerSeries K} (hph : PowerSeries.constantCoeff ph = 0)
    (hF1 : F1 F (cob F ph))
    (hN : ∀ α : K, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ ph α) :
    C.Frame (Formalism.G.unitBall K) (lgF K l) (expF K l) ph ∧
    C.F1 (Formalism.G.unitBall K) (lgF K l) (expF K l) ph ∧
    F = C.fadd (lgF K l) (expF K l) (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∧
    ∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α →
      C.PhNormAt (Formalism.G.unitBall K) (lgF K l) (expF K l) ph α (σ α) ∧
      C.AdjAt (Formalism.G.unitBall K) (lgF K l) (expF K l) ph α (σ α) := by
  have hl : 2 ≤ l := by have := hU.2.1; omega
  have hLP := logPair (K := K) hl
  have hLL := lawLog hl hF
  obtain ⟨hFeq, hFG, hF1C⟩ := Formalism.L2.Th1.C.first_level_from_universal_holds K F (lgF K l) (expF K l) ph hLP hLL hph hF1.2.1
  have hFrame : C.Frame (Formalism.G.unitBall K) (lgF K l) (expF K l) ph := ⟨hLP, hFG, hph⟩
  refine ⟨hFrame, hF1C, hFeq, ?_⟩
  have hiso := sigma_isometry K l σ hU
  have hσ1 : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := fun a ha => by rw [hiso a]; exact ha
  letI : StarRing (Osub σ) := starO hσ1
  have hσc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hiso).continuous
  have hcs : Continuous (star : Osub σ → Osub σ) :=
    (hσc.comp continuous_subtype_val).subtype_mk _
  have hfix : ∀ z : Osub σ, star z = z →
      (Osub σ).subtype z ∈ closure (Set.range (fun n : ℤ => (n : K))) := fun z hz => by
    have h1 : σ (z : K) = z := congrArg Subtype.val hz
    refine closure_mono (fun y hy => ?_) (mem_closure_nat hU (mem_Osub.1 z.2).1 h1)
    obtain ⟨n, rfl⟩ := hy
    exact ⟨n, by simp⟩
  have hinv2 : (2 : K)⁻¹ ∈ Formalism.G.unitBall K := by
    show ‖(2 : K)⁻¹‖ ≤ 1
    rw [norm_inv, norm_two hU, inv_one]
  have hu2 : IsUnit (2 : Osub σ) :=
    ⟨unitO (a := 2) (norm_two hU) (by simp [map_ofNat]), Subtype.ext (by show (2 : K) = _; first | rfl | norm_num | push_cast; rfl)⟩
  have hDn : ∀ a ∈ Set.range (fun u : (Osub σ)ˣ => (u : Osub σ)),
      C.EndInt (Formalism.G.unitBall K) (lgF K l) (expF K l) ((Osub σ).subtype a) ∧
      C.PhNormAt (Formalism.G.unitBall K) (lgF K l) (expF K l) ph ((Osub σ).subtype a) ((Osub σ).subtype (star a)) := by
    rintro a ⟨u, rfl⟩
    have hn := norm_unitO u
    have hs := (mem_Osub.1 (u : Osub σ).2).2
    exact ⟨endInt hU hn.le hs, (phNorm_iff (l := l) (σ := σ) ph _).2 (hN _ hn hs)⟩
  have key := Formalism.L2.Th1.C.endoAll K (Formalism.G.unitBall K) (Formalism.L2.Th1.C.unit_ball_closed K)
    (lgF K l) (expF K l) ph hFrame hF1C (Osub σ) (Osub σ).subtype continuous_subtype_val hcs hfix
    hinv2 hu2 (two_units hU) (Set.range (fun u : (Osub σ)ˣ => (u : Osub σ)))
    (fun u => subset_closure ⟨u, rfl⟩) hDn
  intro α hα hs
  obtain ⟨-, h2, h3⟩ := key ⟨α, mem_Osub.2 ⟨hα, hs⟩⟩
  exact ⟨h2, h3⟩

end Normed

end BrC

open BrC in
theorem second_level_of_norm_holds : SecondLevelOfNorm := by
  intro K _ _ _ l σ hU F hF ph hph hF1 hN
  have hl : 2 ≤ l := hU.1.two_le
  have hP := logPair (K := K) hl
  have hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (frobSq K l σ hU).2
  obtain ⟨hFr, hC1, hFe, hall⟩ := all hU hF hph hF1 hN
  refine ⟨?_, fun α hα hs => (phNorm_iff ph α).1 (hall α hα hs).1, ?_⟩
  · intro α hα hs e e' he he'
    have e1 : e = mulS K l α := (mulSpec K l σ hU α).2.1 _ _ he (Pair.isMul_mulF expSpec hl α)
    have e2 : e' = mulS K l (σ α) :=
      (mulSpec K l σ hU (σ α)).2.1 _ _ he' (Pair.isMul_mulF expSpec hl (σ α))
    rw [e1, e2]
    exact C.adjoint_universal_form K F _ _ ph α (σ α) hP (lawLog hl hF) hph (endInt hU hα hs)
      (endInt hU (hσ _ hα) (congrArg σ hs)) (hall α hα hs).2
  · have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
      PowerSeries.constantCoeff_X
    have h2 := (hall 2 (norm_two hU).le (by rw [map_ofNat, map_ofNat])).1
    have ev : (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) =
        ![(PowerSeries.X : MvPowerSeries Unit K), PowerSeries.X] := by
      funext i
      fin_cases i <;> rfl
    have e3 : C.fadd (lgF K l) (expF K l) (PowerSeries.X : MvPowerSeries Unit K) PowerSeries.X =
        C.mulBy (lgF K l) (expF K l) 2 := by
      rw [C.Pts.mulBy_eq_fmul, ← one_add_one_eq_two, C.Pts.fmul_add hP 1 1 hX, C.Pts.fmul_one hP hX]
    rw [ev, hFe, C.Dict.subst_cob hP ph hX hX, C.be0, e3, PowerSeries.X_subst]
    have hsym := InverseCommuting.sim_symm ((phNorm_iff ph 2).1 h2)
    unfold Simeq at hsym ⊢
    rw [map_ofNat] at hsym
    have e4 : MvPowerSeries.C (2 : K) * ph -
        (PowerSeries.subst (C.mulBy (lgF K l) (expF K l) 2) ph - ph - ph) =
        MvPowerSeries.C ((2 : K) * 2) * ph - PowerSeries.subst (mulS K l 2) ph := by
      rw [map_mul]
      show _ = MvPowerSeries.C (2 : K) * MvPowerSeries.C (2 : K) * ph -
        PowerSeries.subst (C.mulBy (lgF K l) (expF K l) 2) ph
      rw [map_ofNat]
      ring
    rw [e4]
    exact hsym

open BrC in
theorem split_phi : SplitPh := by
  intro K _ _ _ l σ hU F hF ph hph hF1 hN κ E _ _ _ c hc hG
  have hl : 2 ≤ l := hU.1.two_le
  have hP := logPair (K := K) hl
  have hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (frobSq K l σ hU).2
  obtain ⟨hFr, hC1, hFe, hall⟩ := all hU hF hph hF1 hN
  have hcl := C.unit_ball_closed K
  let _ : StarRing (Osub σ) := starO hσ
  have gram : ∀ x x' : Bool × E,
      ∑ i, star (⟨c i x, mem_Osub.2 (hc i x)⟩ : Osub σ) * (⟨c i x', mem_Osub.2 (hc i x')⟩ : Osub σ) =
        if x'.1 ≠ x.1 ∧ x'.2 = x.2 then 1 else 0 := by
    intro x x'
    apply Subtype.ext
    have e : ((if x'.1 ≠ x.1 ∧ x'.2 = x.2 then 1 else 0 : Osub σ) : K) =
        if x'.1 ≠ x.1 ∧ x'.2 = x.2 then 1 else 0 := by
      split_ifs <;> rfl
    rw [e, ← hG x' x, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have key := C.hyperbolicSum K (Formalism.G.unitBall K) _ _ ph hFr (Osub σ) (Osub σ).subtype
    (fun α => endInt hU α.2.1 α.2.2)
    (fun z hz => of_closed_int hU (C.binomClosed K _ hcl) (C.intBinomScalar K _) z.2.1
      (congrArg Subtype.val hz))
    hC1 (fun α => (hall α.1 α.2.1 α.2.2).1) (fun α => (hall α.1 α.2.1 α.2.2).2)
    κ E (fun e i => ⟨c i (false, e), mem_Osub.2 (hc i _)⟩)
    (fun e i => ⟨c i (true, e), mem_Osub.2 (hc i _)⟩)
    (fun e e' => by rw [gram]; simp)
    (fun e e' => by rw [gram]; simp)
    (fun e e' => by rw [gram]; simp [eq_comm])
    (Bool × E) (fun e => MvPowerSeries.X (false, e)) (fun e => MvPowerSeries.X (true, e))
    (fun e => ⟨MvPowerSeries.constantCoeff_X _, C.Pts.intMv_X _⟩)
    (fun e => ⟨MvPowerSeries.constantCoeff_X _, C.Pts.intMv_X _⟩)
  have e1 : ∀ k, combS l (c k) = C.flin (lgF K l) (expF K l)
      (Sum.elim (fun e => (Osub σ).subtype ⟨c k (false, e), mem_Osub.2 (hc k _)⟩)
        (fun e => (Osub σ).subtype ⟨c k (true, e), mem_Osub.2 (hc k _)⟩))
      (Sum.elim (fun e => (MvPowerSeries.X (false, e) : MvPowerSeries (Bool × E) K))
        (fun e => MvPowerSeries.X (true, e))) := by
    intro k
    unfold combS C.flin
    congr 1
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    rfl
  have e2 : ∀ e : E, MvPowerSeries.subst
      (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
        MvPowerSeries (Bool × E) K)) (cob F ph) =
      C.be0 (lgF K l) (expF K l) ph (MvPowerSeries.X (false, e)) (MvPowerSeries.X (true, e)) := by
    intro e
    have ev : (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
        MvPowerSeries (Bool × E) K)) = ![MvPowerSeries.X (false, e), MvPowerSeries.X (true, e)] := by
      funext i
      fin_cases i <;> rfl
    rw [ev, hFe, C.Dict.subst_cob hP ph (MvPowerSeries.constantCoeff_X _)
      (MvPowerSeries.constantCoeff_X _)]
  simp only [e1, e2]
  exact key

open BrC in
theorem norm_units_alt : NormUnits := by
  intro K _ _ _ l σ hU ph hph S hS α hα
  have hl : 2 ≤ l := by have := hU.2.1; omega
  obtain ⟨hL0, -, hE0, -, -⟩ := BrC.logPair (K := K) hl
  have hσc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ (sigma_isometry K l σ hU)).continuous
  have hC := Formalism.L2.Th1.C.phNormClosed K (Formalism.G.unitBall K) (Formalism.L2.Th1.C.unit_ball_closed K)
    (lgF K l) (expF K l) ph hL0 hE0 hph
  have hC' : IsClosed {a : K | NormRel l σ ph a} := by
    have h2 := hC.preimage (continuous_id.prodMk hσc)
    convert h2 using 1
    ext a
    exact (BrC.phNorm_iff (l := l) (σ := σ) ph a).symm
  apply closure_minimal (fun a ha => hS a ha) hC'
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, ha, h⟩ := hα ε hε
  exact ⟨a, ha, by rw [dist_eq_norm, norm_sub_rev]; exact h⟩

open BrC in
theorem fixed_linear : FixedLinear := by
  intro K _ _ _ l σ hU F hF be0 hF1 n hn hs
  have hl : 2 ≤ l := hU.1.two_le
  have hP := logPair (K := K) hl
  have hFe := C.Dict.law_eq hP hF.1 hF.2.2
  have hFG : C.FGInt (Formalism.G.unitBall K) (lgF K l) (expF K l) := by
    rw [C.FGInt, ← hFe]
    exact hF.2.1
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have permutedRowProductSplitSum : C.IsPt (Formalism.G.unitBall K) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    ⟨hX1, C.Pts.intMv_X 1⟩
  have hbe : MvPowerSeries.constantCoeff be0 = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hF1.1 0 (Or.inl rfl)

  have hadd : ∀ y y' : MvPowerSeries (Fin 2) K, C.IsPt (Formalism.G.unitBall K) y →
      C.IsPt (Formalism.G.unitBall K) y' →
      Simeq (MvPowerSeries.subst ![MvPowerSeries.X 0, C.fadd (lgF K l) (expF K l) y y'] be0)
        (MvPowerSeries.subst ![MvPowerSeries.X 0, y] be0 +
          MvPowerSeries.subst ![MvPowerSeries.X 0, y'] be0) := by
    intro y y' hy hy'
    have h := TraceNormBounds.sim_subst0 (φ := ![y, y', MvPowerSeries.X 0]) (C.Dict.constantCoeff_vec_three_eq_zero hy.1 hy'.1 hX0)
      (by
        intro i
        fin_cases i
        · exact hy.2
        · exact hy'.2
        · exact C.Pts.intMv_X (R := Formalism.G.unitBall K) 0) hF1.2.2
    have hc : MvPowerSeries.constantCoeff (MvPowerSeries.subst ![y, y'] F) = 0 := by
      rw [hFe, ← C.Pts.fadd_eq_substMv hP hy.1 hy'.1]
      exact C.Pts.constantCoeff_fadd hP hy.1 hy'.1
    rw [Pair.subst_first_coboundary_three hF.1 hy.1 hy'.1 hX0, Pair.subst_swap2 hc hX0, Pair.subst_swap2 hy.1 hX0,
      Pair.subst_swap2 hy'.1 hX0] at h
    rw [C.Pts.fadd_eq_substMv hP hy.1 hy'.1, ← hFe]
    exact Pair.simeq_of_sub h
  have hid : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1]
      be0 = be0 := by
    have ev : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] =
        MvPowerSeries.X := by
      funext i
      fin_cases i <;> rfl
    rw [ev, MvPowerSeries.subst_self]
    rfl

  have hnat : ∀ m : ℕ, Simeq (MvPowerSeries.subst ![MvPowerSeries.X 0,
      C.fmul (lgF K l) (expF K l) (m : K) (MvPowerSeries.X 1)] be0)
      (MvPowerSeries.C (m : K) * be0) := by
    intro m
    induction m with
    | zero =>
      have p0 : C.IsPt (Formalism.G.unitBall K) (0 : MvPowerSeries (Fin 2) K) :=
        ⟨map_zero _, fun _ => by rw [map_zero]; exact Subring.zero_mem _⟩
      have h := hadd 0 0 p0 p0
      rw [C.Pts.fadd_zero hP (map_zero _)] at h
      rw [Nat.cast_zero, C.Pts.fmul_zero_left hP, map_zero, zero_mul]
      refine InverseCommuting.sim_symm ?_
      unfold Simeq at h ⊢
      rwa [sub_add_cancel_left, ← zero_sub] at h
    | succ m ih =>
      have pm : C.IsPt (Formalism.G.unitBall K)
          (C.fmul (lgF K l) (expF K l) (m : K) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) :=
        C.Pts.isPt_fmul hP (C.Clo.endInt_natCast hP hFG m) permutedRowProductSplitSum
      have h := hadd _ _ pm permutedRowProductSplitSum
      rw [hid] at h
      rw [Nat.cast_succ, C.Pts.fmul_add hP _ _ hX1, C.Pts.fmul_one hP hX1, map_add, map_one, add_mul,
        one_mul]
      exact InverseCommuting.sim_trans h (InverseCommuting.sim_add ih (InverseCommuting.sim_refl _))

  have hcc : ∀ z : K, MvPowerSeries.constantCoeff
      (C.fmul (lgF K l) (expF K l) z (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = 0 :=
    fun z => C.Pts.constantCoeff_fmul hP z hX1
  have hclosed : IsClosed {z : K | Simeq (MvPowerSeries.subst ![MvPowerSeries.X 0,
      C.fmul (lgF K l) (expF K l) z (MvPowerSeries.X 1)] be0) (MvPowerSeries.C z * be0)} := by
    refine C.Clo.isClosed_LG (C.unit_ball_closed K)
      (f := fun z : K => MvPowerSeries.subst ![MvPowerSeries.X 0,
        C.fmul (lgF K l) (expF K l) z (MvPowerSeries.X 1)] be0 - MvPowerSeries.C z * be0)
      ((coeffCont_subst2 (C.Clo.CoeffCont.const _)
        (C.Clo.coeffCont_fmul hP.1 _ continuous_id hX1) (fun _ => hX0) hcc be0).sub
        (C.Clo.CoeffCont.C_mul continuous_id (C.Clo.CoeffCont.const _))) ?_
    intro z
    rw [map_sub, map_mul, hbe, mul_zero, sub_zero]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (Pair.hs2 hX0 (hcc z))
      (C.Dict.constantCoeff_vecCons_pair_eq_zero hX0 (hcc z)) hbe
  have hfin := of_closed_nat hU hclosed hnat hn hs
  rw [C.Pts.fmul_eq_subst_mulBy hP n hX1] at hfin
  exact hfin

end Formalism.L2.Th1.D
