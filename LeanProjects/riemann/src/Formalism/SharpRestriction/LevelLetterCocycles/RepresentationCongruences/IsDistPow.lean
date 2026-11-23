import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

section Core

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable {l : ℕ} [Fact l.Prime] (P : PhiData O l)

theorem ArcLengthThreeDescent.isDist_pow {g : O⟦X⟧} (hg : IsDist g) (k : ℕ) : IsDist (g ^ k) := by
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.IsDist at hg ⊢
  rw [map_pow]
  exact pow_ne_zero k hg

theorem ArcLengthThreeDescent.cancel {ϖ : O} (hϖ : Irreducible ϖ) {G : O⟦X⟧} (hG : IsDist G) (a m : ℕ) {H : O⟦X⟧}
    (h : C ϖ ^ a * H ∈ Ideal.span {C ϖ ^ (a + m), G}) : H ∈ Ideal.span {C ϖ ^ m, G} := by
  have hϖ0 : (C ϖ : O⟦X⟧) ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    have h1 := congrArg PowerSeries.constantCoeff h0
    simpa using h1
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)
  have step : ∀ (m : ℕ) (H : O⟦X⟧), C ϖ * H ∈ Ideal.span {C ϖ ^ (m + 1), G} →
      H ∈ Ideal.span {C ϖ ^ m, G} := by
    intro m H h
    rw [Ideal.mem_span_pair] at h ⊢
    obtain ⟨A, B, hAB⟩ := h
    have h1 := congrArg (PowerSeries.map (IsLocalRing.residue O)) hAB
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, hres, map_zero,
      zero_pow (by omega : m + 1 ≠ 0), mul_zero, zero_mul, zero_add] at h1
    have hB : B.map (IsLocalRing.residue O) = 0 := (mul_eq_zero.1 h1).resolve_right hG
    have hcoef : ∀ k, ∃ b : O, PowerSeries.coeff k B = ϖ * b := by
      intro k
      have h2 := congrArg (PowerSeries.coeff k) hB
      rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff,
        (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at h2
      obtain ⟨b, hb⟩ := h2
      exact ⟨b, by rw [← hb, mul_comm]⟩
    choose b hb using hcoef
    have hBeq : B = C ϖ * PowerSeries.mk b := by
      ext k
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]
    refine ⟨A, PowerSeries.mk b, ?_⟩
    apply mul_left_cancel₀ hϖ0
    rw [← hAB, hBeq, pow_succ]
    ring
  induction a generalizing H m with
  | zero => simpa using h
  | succ a ih =>
    apply step m H
    apply ih (m := m + 1) (H := C ϖ * H)
    rw [← mul_assoc, ← pow_succ]
    rwa [show a + (m + 1) = a + 1 + m by omega]

theorem ArcLengthThreeDescent.const_int {ϖ : O} (hϖ : Irreducible ϖ) (b₁ y κ K : ℕ) (x : O) (α β : O⟦X⟧)
    (h : C ((l : O) ^ κ) * α - C x * P.p 1 ^ b₁ = P.p 2 ^ y * β)
    (hK : cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ b₁) ≤ ((eO (O := O) l * K : ℕ) : ℕ∞)) :
    ∃ X₂ : O, (l : O) ^ κ * X₂ = (l : O) ^ K * x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨a, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨v, hv⟩ := l_eq_unit_mul_pow hϖ P.hl0
  set E := eO (O := O) l with hE
  by_cases hle : E * κ ≤ E * K + a
  · refine ⟨(v : O) ^ K * ((v⁻¹ : Oˣ) : O) ^ κ * ϖ ^ (E * K + a - E * κ) * w, ?_⟩
    have key : ϖ ^ (E * κ) * ϖ ^ (E * K + a - E * κ) = ϖ ^ (E * K) * ϖ ^ a := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have hvv : (v : O) ^ κ * ((v⁻¹ : Oˣ) : O) ^ κ = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    rw [hw, hv, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    linear_combination ((v : O) ^ K * (w : O) * ϖ ^ (E * κ) * ϖ ^ (E * K + a - E * κ)) * hvv +
      ((v : O) ^ K * (w : O)) * key
  · exfalso
    push Not at hle
    have hlk : (C ((l : O) ^ κ) : O⟦X⟧) = C ((v : O) ^ κ) * C ϖ ^ (E * κ) := by
      rw [hv, mul_pow, ← pow_mul]
      simp only [map_mul, map_pow]
    have hmem : C ϖ ^ a * (C (w : O) * P.p 1 ^ b₁) ∈
        Ideal.span {C ϖ ^ (a + (E * κ - a)), P.p 2 ^ y} := by
      have e1 : C ϖ ^ a * (C (w : O) * P.p 1 ^ b₁) = C x * P.p 1 ^ b₁ := by
        rw [hw, map_mul, map_pow]; ring
      have e2 : a + (E * κ - a) = E * κ := by omega
      rw [e1, e2, Ideal.mem_span_pair]
      exact ⟨C ((v : O) ^ κ) * α, -β, by linear_combination h - α * hlk⟩
    have hmem2 := ArcLengthThreeDescent.cancel hϖ (ArcLengthThreeDescent.isDist_pow (P.isDist_p 2) y) a (E * κ - a) hmem
    have hmem3 : P.p 1 ^ b₁ ∈ Ideal.span {C ϖ ^ (E * κ - a), P.p 2 ^ y} := by
      have := Ideal.mul_mem_left _ (C ((w⁻¹ : Oˣ) : O)) hmem2
      rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at this
    rw [ContD.mem_iff_le] at hmem3
    have hdesc : cont ϖ (P.p 2 ^ y) (P.p 1 ^ b₁) = cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ b₁) := by
      have := P.cont_phi_phi_eq hϖ (ArcLengthThreeDescent.isDist_pow (P.isDist_p 1) y) ((X : O⟦X⟧) ^ b₁)
      have e1 : P.φ (P.p 1) = P.p 2 := (P.p_succ 1).symm
      have e0 : P.φ X = P.p 1 := rfl
      rwa [map_pow, map_pow, e1, e0] at this
    rw [hdesc] at hmem3
    have h3 := hmem3.trans hK
    have h4 : E * κ - a ≤ E * K := by exact_mod_cast h3
    omega

theorem ArcLengthThreeDescent.cont_le {ϖ : O} (hϖ : Irreducible ϖ) (b₁ y : ℕ) (hy : 1 ≤ y) (hge : l * y ≤ b₁) :
    cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ b₁) ≤
      ((eO (O := O) l * ((b₁ + l - 1) / l - (y - 1) +
        padicValNat l (((b₁ + l - 1) / l).choose (y - 1))) : ℕ) : ℕ∞) := by
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  have hdm := Nat.div_add_mod (b₁ + l - 1) l
  have hr := Nat.mod_lt (b₁ + l - 1) hl0
  have hla : b₁ ≤ l * ((b₁ + l - 1) / l) := by
    generalize l * ((b₁ + l - 1) / l) = P at hdm ⊢
    omega
  have hya : y ≤ (b₁ + l - 1) / l := Nat.le_of_mul_le_mul_left (hge.trans hla) hl0
  have hmono : cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ b₁) ≤
      cont ϖ (P.p 1 ^ y) ((X : O⟦X⟧) ^ (l * ((b₁ + l - 1) / l))) := by
    unfold cont
    refine iSup₂_le fun k hk => le_iSup₂_of_le k ?_ le_rfl
    rw [← Nat.sub_add_cancel hla, pow_add]
    exact Ideal.mul_mem_left _ _ hk
  refine hmono.trans ?_
  rw [P.E1 hϖ _ y hy]
  exact iInf₂_le (y - 1) (Finset.mem_range.2 (by omega))

end Core

def ArcLengthThreeDescent.Kc (l b₁ y : ℕ) : ℕ :=
  if b₁ < l * y then 0 else (b₁ + l - 1) / l - (y - 1) + padicValNat l (((b₁ + l - 1) / l).choose (y - 1))

theorem ArcLengthThreeDescent.Kc_le (l b₁ y η : ℕ) [hl : Fact l.Prime] (hy : 1 ≤ y) (hge : l * y ≤ b₁)
    (hlt : b₁ < l * (y + η)) : (ArcLengthThreeDescent.Kc l b₁ y : ℝ) ≤ η + 1 + Real.logb l b₁ := by
  have hl2 : 2 ≤ l := hl.out.two_le
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 1 < l)
  have hl0 : 0 < l := by omega
  unfold ArcLengthThreeDescent.Kc
  rw [if_neg (not_lt.2 hge)]
  set a := (b₁ + l - 1) / l with ha
  have ha_le : a ≤ y + η := by
    have h2 : a < y + η + 1 := by
      rw [ha, Nat.div_lt_iff_lt_mul hl0]
      have : (y + η + 1) * l = l * (y + η) + l := by ring
      omega
    omega
  have hly : l ≤ l * y := by nlinarith
  have ha_pos : 1 ≤ a := by
    rw [ha, Nat.le_div_iff_mul_le hl0]
    omega
  have ha_b : a ≤ b₁ := by
    have h3 : a * l ≤ b₁ + l - 1 := Nat.div_mul_le_self _ _
    have h4 : 2 * a ≤ a * l := by nlinarith
    omega
  have hv : padicValNat l (a.choose (y - 1)) ≤ Nat.log l a := by
    rw [← Nat.factorization_def _ hl.out]
    exact Nat.factorization_choose_le_log
  have hlog1 : (Nat.log l a : ℝ) ≤ Real.logb l a := by
    have h1 : ((l ^ Nat.log l a : ℕ) : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self l (by omega : a ≠ 0)
    push_cast at h1
    have h2 := Real.logb_le_logb_of_le hl1 (by positivity) h1
    rwa [Real.logb_pow, Real.logb_self_eq_one hl1, mul_one] at h2
  have hlog2 : Real.logb l a ≤ Real.logb l b₁ :=
    Real.logb_le_logb_of_le hl1 (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast ha_b)
  have hcast : ((a - (y - 1) + padicValNat l (a.choose (y - 1)) : ℕ) : ℝ) ≤ (η : ℝ) + 1 + (Nat.log l a : ℝ) := by
    have h5 : a - (y - 1) + padicValNat l (a.choose (y - 1)) ≤ η + 1 + Nat.log l a := by omega
    exact_mod_cast h5
  linarith

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem ArcLengthThreeDescent.letE_idem (c : ZMod n) : (letE (O := O) c : LetA O n) * letE c = letE c := by
  funext i
  simp only [Formalism.BasicNotions.letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

theorem ArcLengthThreeDescent.letE_mem (W : LocWach PD LL O v n) (c : ZMod n) : (letE (O := O) c : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (letE c) = letE c
  intro δ _
  funext i
  show (W.γ₀ δ) ((letE c : LetA O n) i) = (letE c : LetA O n) i
  by_cases h : i = c
  · subst h
    simp [Formalism.BasicNotions.letE]
  · simp [Formalism.BasicNotions.letE, Pi.single_apply, h]

theorem ArcLengthThreeDescent.split [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (hinj : Function.Injective (algebraMap O LL)) (c : ZMod n) (b₁ y y₀ : ℕ) (hy : 1 ≤ y) (hb : 1 ≤ b₁)
    (f : W.EE) (hf1 : InFr W c 1 (ps W 1 ^ b₁) f)
    (hf2 : ∃ (κ : ℕ) (x : O), InFr W c (ps W 2 ^ y) (ps W 1 ^ b₁)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x))
    (hf0 : ∃ (κ : ℕ) (x : O), InFr W c (ps W 0 ^ y₀) (ps W 1 ^ b₁)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ (X₂ : O) (f₂ : W.EE),
      lE W (ArcLengthThreeDescent.Kc PD.p b₁ y) * f = algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂ + f₂ ∧
      InFr W c (ps W 2 ^ y) (ps W 1 ^ b₁) f₂ ∧
      ∃ (κ : ℕ) (X₀ : O), InFr W c (ps W 0 ^ y₀) (ps W 1 ^ b₁)
        (lE W κ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀) := by
  have : Fact PD.p.Prime := Fact.mk PD.hp
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T hT hO hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨κ, x, hx⟩ := hf2
  set K := ArcLengthThreeDescent.Kc PD.p b₁ y with hKdef

  have hf1' : InFr W c (Br.cst 1) (Br.cst (Br.P.p 1 ^ b₁)) f := by
    rw [Br.cst_one, Br.cst_pow, ← Br.ps_eq]; exact hf1
  have hx' : InFr W c (Br.cst (Br.P.p 2 ^ y)) (Br.cst (Br.P.p 1 ^ b₁))
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) := by
    rw [Br.cst_pow, Br.cst_pow, ← Br.ps_eq, ← Br.ps_eq]; exact hx
  obtain ⟨U₁, U₂, hU⟩ := Br.inFr_const c hf1' hx'
  have hrel : C (((PD.p : ℕ) : O) ^ κ) * U₁ - C x * Br.P.p 1 ^ b₁ = Br.P.p 2 ^ y * U₂ := by
    rw [map_pow]; linear_combination -hU
  have hK : cont ϖ (Br.P.p 1 ^ y) ((X : O⟦X⟧) ^ b₁) ≤ ((eO (O := O) PD.p * K : ℕ) : ℕ∞) := by
    rw [hKdef]; unfold ArcLengthThreeDescent.Kc
    split_ifs with hlt
    · rw [Br.P.cont_pow_X_pow_eq_zero_of_lt hϖ y b₁ hy hb hlt]; simp
    · exact ArcLengthThreeDescent.cont_le Br.P hϖ b₁ y hy (by omega)
  obtain ⟨X₂, hX₂⟩ := ArcLengthThreeDescent.const_int Br.P hϖ b₁ y κ K x U₁ U₂ hrel hK

  have hLA : ∀ k : ℕ, algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k := by
    intro k; simp [lA, lE, map_pow, map_natCast]
  have hOE : ∀ z : O, algebraMap O W.EE z = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) z) :=
    fun z => IsScalarTower.algebraMap_apply O (LetA O n) W.EE z
  have hX₂E : lE W κ * algebraMap O W.EE X₂ = lE W K * algebraMap O W.EE x := by
    have := congrArg (algebraMap O W.EE) hX₂
    simpa [lE, map_mul, map_pow, map_natCast] using this
  have he := ArcLengthThreeDescent.letE_idem (O := O) (n := n) c
  have heM := ArcLengthThreeDescent.letE_mem W c
  have hpsM : ∀ s : ℕ, ps W s ∈ W.AΔ := fun s => by rw [Br.ps_eq]; exact Br.cst_mem _
  have hlM : lA W ∈ W.AΔ := by rw [Br.lA_eq]; exact Br.cst_mem _
  obtain ⟨u₀, hu₀, hf1e⟩ := hf1
  obtain ⟨u₂, hu₂, hxe⟩ := hx
  refine ⟨X₂, lE W K * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂, by ring, ?_, ?_⟩
  ·
    set H : LetA O n := lA W ^ K * (letE c * 1 * u₀) - letE c * algebraMap O (LetA O n) X₂ * ps W 1 ^ b₁
      with hHdef
    have hH : algebraMap (LetA O n) W.EE H = algebraMap (LetA O n) W.EE (ps W 1 ^ b₁) *
        (lE W K * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂) := by
      rw [hHdef, map_sub, map_mul (algebraMap (LetA O n) W.EE) (lA W ^ K), hLA, ← hf1e, hOE X₂]
      simp only [map_mul]
      ring
    have hHm : H ∈ W.AΔ := by
      rw [hHdef]
      exact sub_mem (mul_mem (pow_mem hlM _) (mul_mem (mul_mem heM (one_mem _)) hu₀))
        (mul_mem (mul_mem heM (Subalgebra.algebraMap_mem _ X₂)) (pow_mem (hpsM 1) _))
    have hk : lA W ^ κ * (1 * H) = ps W 2 ^ y * (lA W ^ K * (letE c * u₂)) := by
      apply W.EE_inj
      rw [one_mul, map_mul, map_mul, map_mul, map_mul, hLA, hLA, hH]
      rw [map_mul, map_mul] at hxe
      linear_combination (lE W K) * hxe -
        (algebraMap (LetA O n) W.EE (ps W 1 ^ b₁) * algebraMap (LetA O n) W.EE (letE c)) * hX₂E
    have hN₂ : ps W 2 ^ y ∈ PiPs W :=
      Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self 2))) y
    obtain ⟨yy, hyy, hyyeq⟩ := saturation_fraction_ring W hcase hP9 hinj (ps W 2 ^ y) 1 1 hN₂ (one_mem _) (one_mem _) H
      (by rw [one_mul]; exact hHm)
      ⟨κ, lA W ^ K * (letE c * u₂), mul_mem (pow_mem hlM _) (mul_mem heM hu₂), hk⟩
    refine ⟨yy, hyy, ?_⟩
    have hHe : letE c * H = H := by
      rw [hHdef]
      linear_combination (lA W ^ K * u₀ - algebraMap O (LetA O n) X₂ * ps W 1 ^ b₁) * he
    rw [← hH, ← hHe, ← one_mul H, hyyeq, mul_assoc]
  ·
    obtain ⟨κ₀, x₀, u₃, hu₃, h0e⟩ := hf0
    refine ⟨κ₀, ((PD.p : ℕ) : O) ^ K * x₀ - ((PD.p : ℕ) : O) ^ κ₀ * X₂, lA W ^ K * u₃,
      mul_mem (pow_mem hlM _) hu₃, ?_⟩
    have hX₀ : algebraMap O W.EE (((PD.p : ℕ) : O) ^ K * x₀ - ((PD.p : ℕ) : O) ^ κ₀ * X₂) =
        lE W K * algebraMap O W.EE x₀ - lE W κ₀ * algebraMap O W.EE X₂ := by
      simp [lE, map_sub, map_mul, map_pow, map_natCast]
    rw [hX₀, map_mul, map_mul, map_mul, hLA]
    rw [map_mul, map_mul] at h0e
    linear_combination (lE W K) * h0e

end Formalism.MainNotions.N.FrobeniusPowerSeries
