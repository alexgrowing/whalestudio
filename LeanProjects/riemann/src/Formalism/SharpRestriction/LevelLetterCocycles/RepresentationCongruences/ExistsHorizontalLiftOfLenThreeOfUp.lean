import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AcoordSumVecMul
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthFourCostBound

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

open scoped TensorProduct

namespace ArcLengthFourSecond

open PowerSeries in

theorem mem_span_of_coeff {R : Type*} [CommRing R] (F : PowerSeries R) (t : R) (B' : ℕ)
    (h : ∀ j < B', t ∣ coeff j F) : F ∈ Ideal.span {C t, (X : PowerSeries R) ^ B'} := by
  classical
  rw [Ideal.mem_span_pair]
  refine ⟨PowerSeries.mk fun j => if hj : j < B' then (h j hj).choose else 0,
    PowerSeries.mk fun j => coeff (j + B') F, ?_⟩
  ext m
  rw [map_add, coeff_mul_C, coeff_mul_X_pow', coeff_mk]
  by_cases hm : m < B'
  · rw [dif_pos hm, if_neg (by omega), add_zero, mul_comm]
    exact ((h m hm).choose_spec).symm
  · rw [dif_neg hm, zero_mul, zero_add, if_pos (by omega), coeff_mk, Nat.sub_add_cancel (by omega)]

section Dv
variable (W : LocWach PD LL O v n)

theorem dvO_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
  simp only [dvO, dv, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.smul_sum]
  simp

theorem dv_shift (T : LocLat G Qp LL O) (e k : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T (e + k) b c₀ = ((φVB PD (LL := LL) (V := T.V)) ^ k) (dv W T e b c₀) := by
  unfold dv
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pow_add, pow_mul_comm, Module.End.mul_apply]

theorem dvO_shift (T : LocLat G Qp LL O) (e k : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + k) b c₀ = ((φVB PD (LL := LL) (V := T.V)) ^ k) (dvO W T e b c₀) := by
  exact dv_shift W T e k b _

theorem dvO_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  unfold dvO
  congr 1
  funext m
  by_cases hm : m = k
  · subst hm; simp
  · simp [Pi.single_apply, hm]

theorem filV_mono (T : LocLat G Qp LL O) {u u' : ℤ} (h : u ≤ u') :
    FilV PD (LL := LL) (V := T.V) u' ≤ FilV PD (LL := LL) (V := T.V) u := by
  have hF : PD.Fil u' ≤ PD.Fil u := antitone_int_of_succ_le PD.Fil_anti h
  have hF' : (PD.Fil u').restrictScalars Qp ≤ (PD.Fil u).restrictScalars Qp := hF
  unfold FilV
  calc _ = LinearMap.range ((TensorProduct.AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[LL] T.V)
        ((PD.Fil u).restrictScalars Qp).subtype).comp
        (TensorProduct.AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[LL] T.V) (Submodule.inclusion hF'))) := by
        rw [← TensorProduct.AlgebraTensorModule.map_comp, LinearMap.id_comp, Submodule.subtype_comp_inclusion]
    _ ≤ _ := LinearMap.range_comp_le_range _ _

theorem filS_mono (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ} (h : u ≤ u') :
    FilS W T a s u' ≤ FilS W T a s u := by
  unfold FilS FilCris
  exact Submodule.map_mono (inf_le_inf_right _ (inf_le_inf_left _ (Submodule.comap_mono (filV_mono T h))))

theorem pow_inj (T : LocLat G Qp LL O) (e : ℕ) :
    Function.Injective ((φVB PD (LL := LL) (V := T.V)) ^ e) := by
  rw [Module.End.coe_pow]
  exact (Formalism.MainNotions.UnusedSlot80.ArcF.φVB_inj (PD := PD) T).iterate e

theorem filS_shift (T : LocLat G Qp LL O) {a c : ZMod n} (s : ℕ) (h : a = c - (s : ZMod n)) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : x ∈ FilS W T a 0 u) : ((φVB PD (LL := LL) (V := T.V)) ^ s) x ∈ FilS W T c s u := by
  subst h
  rw [FilS, Submodule.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, by simpa using hy, ?_⟩
  simp

theorem filS_unshift (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) {u : ℤ} {x : T.V ⊗[Qp] B}
    (hx : ((φVB PD (LL := LL) (V := T.V)) ^ s) x ∈ FilS W T c s u) : x ∈ FilS W T (c - (s : ZMod n)) 0 u := by
  rw [FilS, Submodule.mem_map] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  obtain rfl := pow_inj T s hyx
  exact ⟨y, by simpa using hy, by simp⟩

theorem repVV_smulA {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} {x : W.DD T} {f : Fin d → W.EE}
    (a : LetA O n) (ha : a ∈ W.AΔ) (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a • x) (fun k => algebraMap (LetA O n) W.EE a * f k) := by
  obtain ⟨κ, κ', Hh, a', hH, ha', hF⟩ := h
  refine ⟨κ, κ', Hh, fun k => a * a' k, hH, fun k => ⟨W.AΔ.mul_mem ha (ha' k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (ha' k).2, mul_left_comm]
  · have := Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul (W := W) T c' e (W.π₀ * Λ ^ 2) ha hF
    convert this using 1
    simp only [smul_sub, Finset.smul_sum, smul_smul]
    congr 1
    · congr 1; ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      congr 1; ring

end Dv

end ArcLengthFourSecond

namespace ArcLengthFourSecond
variable [IsDomain O] [IsDiscreteValuationRing O] {W : LocWach PD LL O v n}

theorem cst_sub (Br : PhiBridge W) (F G : PowerSeries O) : Br.cst (F - G) = Br.cst F - Br.cst G := by
  funext i
  exact map_sub Br.ι F G
theorem cst_zero (Br : PhiBridge W) : Br.cst 0 = 0 := by
  funext i
  exact map_zero Br.ι
theorem cst_sum (Br : PhiBridge W) {ι : Type*} (s : Finset ι) (F : ι → PowerSeries O) :
    Br.cst (∑ i ∈ s, F i) = ∑ i ∈ s, Br.cst (F i) := by
  funext i
  rw [Finset.sum_apply]
  exact map_sum Br.ι F s
theorem cst_letter (Br : PhiBridge W) (a : ZMod n) (F : PowerSeries O) :
    ((letE a : LetA O n) * Br.cst F) a = Br.ι F := by
  simp [PhiBridge.cst, Formalism.BasicNotions.letE]
theorem cst_letter_inj (Br : PhiBridge W) (a : ZMod n) {F F' : PowerSeries O}
    (h : (letE a : LetA O n) * Br.cst F = letE a * Br.cst F') : F = F' := by
  apply Br.inj
  rw [← cst_letter Br a F, ← cst_letter Br a F', h]
theorem letter_rep (Br : PhiBridge W) (a : ZMod n) (u : LetA O n) (hu : u ∈ W.AΔ) :
    ∃ G : PowerSeries O, (letE a : LetA O n) * u = letE a * Br.cst G := by
  obtain ⟨G, hG⟩ := Br.range u hu a
  refine ⟨G, ?_⟩
  funext i
  by_cases hi : i = a
  · subst hi
    simp [Pi.mul_apply, PhiBridge.cst, hG]
  · simp [Formalism.BasicNotions.letE, hi, Pi.mul_apply]

end ArcLengthFourSecond

theorem exists_horizontal_lift_of_len_three_of_up [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂)
    (hArc : ArcCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL)) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hSec : ArcSecMapCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (halt : Alt b η up size)
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true)
    (hOK : (arcOf b w S η up size).OK)
    (hth : Formalism.MainNotions.LiftingTheory.AI W F (c - 2) + η + 2 * (arcOf b w S η up size).σ PD.p + 2 ≤ size (c - 2)) :
    ∃ (d₁ : ℕ) (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL) (c₁ : Fin d₁ → O),
      IsHor W T₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) b₁ sol₁ ∧
      dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁ ∈ FilS W T₁ c 2 (size (c - 2)) ∧
      Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁) =
        ((PD.p : LL) ^ (2 * (arcOf b w S η up size).σ PD.p + 1)) •
          dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) := by
  classical
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have hp11 : 11 ≤ PD.p := hB.1
  have hl5 : 5 ≤ PD.p := by omega
  have hSet := hB.2.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hSet.2.1
  have hJL : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi := hSet.2.2.2.2.2.2
  have hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w := hSet.2.2.2.2.2.1
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hW₁.1 hO hinj
  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  have hqu : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := GS.isUnit_qA hR
  have hqmem : qA W ∈ W.AΔ := GS.qA_mem W
  have hπmem : W.π₀ ∈ W.AΔ := GS.π₀_mem W
  have h1len : 1 ≤ (arcOf b w S η up size).len c := by rw [hlen]; norm_num

  have hac : c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((1 : ℕ) : ZMod n) = c - 2 := by
    rw [hlen]; push_cast; ring
  have hty2 : (arcOf b w S η up size).ty (c - ((2 : ℕ) : ZMod n)) = .up (size (c - 2)) := by
    simp [arcOf, hU]
  have htya : (arcOf b w S η up size).ty
      (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((1 : ℕ) : ZMod n) - ((0 : ℕ) : ZMod n)) =
        .up (size (c - 2)) := by
    rw [hac]; simp [arcOf, hU]
  have hnt2 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
    have h3 : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3 := hlen
    have hne : Set.Nonempty {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      rcases Set.eq_empty_or_nonempty {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} with h | h
      · rw [h, Nat.sInf_empty] at h3; exact absurd h3 (by norm_num)
      · exact h
    have hm := Nat.sInf_mem hne
    rw [h3] at hm
    have hm' : 1 ≤ 3 ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - ((3 : ℕ) : ZMod n) + 1) := hm
    have e : c - ((3 : ℕ) : ZMod n) + 1 = c - 2 := by push_cast; ring
    rw [e] at hm'
    exact hm'.2
  have hwaG : size (c - 2) ≤ w + S := by have := hnt (c - 2) hnt2; omega
  have hΛ : abelian₂ W (arcOf b w S η up size) (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((1 : ℕ) : ZMod n)) 1 =
      qA W ^ (w + S) := by
    simp [abelian₂, ArcP.Hs, ps, arcOf]

  obtain ⟨hJJ, hAT⟩ := hArc hcase hl5 _ hOK c hc 1 (le_refl _) h1len
  obtain ⟨-, C2₁, -, hD₁⟩ := hAT T₁ hW₁
  obtain ⟨-, -, -, hD₂⟩ := hAT T₂ hW₂
  obtain ⟨d₁, b₁, sol₁, hb₁⟩ := hHF hcase hl5 _ hOK T₁ hW₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))
  obtain ⟨-, -, -, D4₁, -, -, -⟩ := hD₁ d₁ b₁ sol₁ hb₁
  obtain ⟨-, -, -, -, D5₂, -, -⟩ := hD₂ d bb sol hbb
  obtain ⟨-, μ, hμcris, hμrep⟩ := hSec hcase hl5 _ hOK c hc 1 (le_refl _) h1len T₁ T₂ F hW₁ hW₂ d₁ b₁ sol₁ hb₁ d bb sol hbb
  rw [hΛ] at C2₁ D4₁ D5₂ hμrep
  rw [hac] at C2₁ D4₁ D5₂ hμrep

  have hk2 := hk₀ 2 (by rw [hlen]; norm_num) (size (c - 2)) hty2
  rw [show (arcOf b w S η up size).len c = 1 + 2 from hlen, ArcLengthFourSecond.dv_shift] at hk2
  have hdesc := ArcLengthFourSecond.filS_unshift W T₂ c 2 hk2
  rw [show c - ((2 : ℕ) : ZMod n) = c - 2 by push_cast; rfl] at hdesc
  set G₀ := w + S with hG₀
  set wa := size (c - 2) with hwa
  set σ := (arcOf b w S η up size).σ PD.p with hσ
  set AI := Formalism.MainNotions.LiftingTheory.AI W F (c - 2) with hAI
  set c' := c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) with hc'
  set M := (arcOf b w S η up size).M PD.p with hM

  set qi : W.EE := ((hqu.unit⁻¹ : W.EEˣ) : W.EE) with hqi
  have hqq : algebraMap (LetA O n) W.EE (qA W) * qi = 1 := IsUnit.mul_val_inv hqu
  set g₂ : W.EE := qi ^ wa * algebraMap (LetA O n) W.EE (letE (c - 2)) with hg₂
  have hpow : algebraMap (LetA O n) W.EE (qA W) ^ G₀ * qi ^ wa =
      algebraMap (LetA O n) W.EE (qA W) ^ (G₀ - wa) := by
    conv_lhs => rw [show G₀ = (G₀ - wa) + wa by omega, pow_add, mul_assoc, ← mul_pow, hqq, one_pow, mul_one]
  have hg₂Λ : algebraMap (LetA O n) W.EE (qA W ^ G₀) * g₂ =
      algebraMap (LetA O n) W.EE (letE (c - 2) * 1 * qA W ^ (G₀ - wa)) := by
    rw [hg₂, map_pow, ← mul_assoc, hpow, map_mul, map_mul, map_one, map_pow]; ring
  have hg₂q : algebraMap (LetA O n) W.EE (qA W ^ wa) * g₂ =
      algebraMap (LetA O n) W.EE (letE (c - 2) * qA W ^ 0 * 1) := by
    rw [hg₂, map_pow, ← mul_assoc, ← mul_pow, hqq, one_pow, one_mul, pow_zero, mul_one, mul_one]
  set f₂ : Fin d → W.EE := fun k => if k = k₀ then g₂ else 0 with hf₂
  have hf₂fr : ∀ k, InFr W (c - 2) 1 (qA W ^ G₀) (f₂ k) := by
    intro k
    by_cases hk : k = k₀
    · simp only [hf₂, if_pos hk]; exact ⟨_, W.AΔ.pow_mem hqmem _, hg₂Λ⟩
    · simp only [hf₂, if_neg hk]; exact ⟨0, W.AΔ.zero_mem, by simp⟩
  have hf₂NL : InNL W T₂ (c - 2) 1 (qA W ^ G₀) bb f₂ := by
    refine ⟨hf₂fr, 0, 1, fun _ => g₂, fun _ => Pi.single k₀ 1, fun _ _ => -(wa : ℤ), fun _ => ⟨?_, ?_⟩, ?_⟩
    · show InFr W (c - 2) (∏ s ∈ Finset.range 1, ps W s ^ (-(wa : ℤ)).toNat)
        (∏ s ∈ Finset.range 1, ps W s ^ (-(-(wa : ℤ))).toNat) g₂
      simp only [Finset.prod_range_one, neg_neg, Int.toNat_natCast]
      rw [Int.toNat_of_nonpos (by omega), show ps W 0 = qA W by simp [ps]]
      exact ⟨1, W.AΔ.one_mem, hg₂q⟩
    · intro s hs
      interval_cases s
      rw [neg_neg, ArcLengthFourSecond.dvO_single]
      exact hdesc
    · intro k
      simp only [Fin.sum_univ_one]
      by_cases hk : k = k₀
      · subst hk; simp [hf₂, lE]
      · simp [hf₂, hk, lE, Pi.single_apply]
  obtain ⟨x₂, hx₂N, hx₂R⟩ := D5₂ f₂ hf₂NL

  have hK : Formalism.MainNotions.LiftingTheory.KillsΔ W F (c - 2) (W.π₀ ^ AI) := (hWR hcase T₁ T₂ F Mi hi hsur hJL (c - 2)).2.1
  obtain ⟨y, hyN, hyl, rfl⟩ := hx₂N
  have hyN' := (lemGB_memNΔ W).1 hyN
  have hyNl : y ∈ W.Nl T₂ (c - 2) := Submodule.mem_map.2 ⟨y, hyN'.1, by simpa using hyl⟩
  have hΔ := (lemG_units W hcase hP9 hW₁.1 hO hOv hinj).2.2
  have hπA : W.π₀ ^ AI ∈ W.AΔ := W.AΔ.pow_mem hπmem _
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ (W.π₀ ^ AI • y) = W.π₀ ^ AI • y := fun δ hδ => by
    rw [GS.γD_smulA W T₂ δ, hπA δ hδ, hyN'.2 δ hδ]
  obtain ⟨n₁, hn₁, hFn₁⟩ := inImg_of_Nimg W hΔ F (c - 2) (hK y hyNl hyN'.2) hzΔ
  have hidem : (letE (c - 2) : LetA O n) * letE (c - 2) = letE (c - 2) := by
    unfold letE; rw [← Pi.single_mul, one_mul]
  have hn₁F : InFNc W T₁ (c - 2) 1 n₁ := by
    obtain ⟨hN, hNl⟩ := (lemGB_inNΔi_iff W).1 hn₁
    obtain ⟨z, -, hz⟩ := Submodule.mem_map.1 hNl
    refine ⟨n₁, hN, ?_, (one_smul _ _).symm⟩
    rw [← hz]
    simp [smul_smul, hidem]
  obtain ⟨g₁, hg₁NL, hg₁R⟩ := D4₁ n₁ hn₁F

  have hP₁ : InFP W T₁ c' 1 1 (qA W ^ G₀ • (lA W ^ σ • n₁)) := by
    rw [smul_comm]; exact TypesA.inMultiple_smul W (TypesA.lA_pow_mem W σ) (C2₁ n₁ hn₁F)
  have hRa := hμrep (lA W ^ σ • n₁) g₁ hP₁ hg₁NL.1 hg₁R
  have hmemσA : lA W ^ σ * W.π₀ ^ AI ∈ W.AΔ := W.AΔ.mul_mem (TypesA.lA_pow_mem W σ) hπA
  have hRb : RepVV W T₂ c' 1 M (qA W ^ G₀) bb sol (W.map F (lA W ^ σ • n₁))
      (fun k => algebraMap (LetA O n) W.EE (lA W ^ σ * W.π₀ ^ AI) * (lE W σ * f₂ k)) := by
    have e : W.map F (lA W ^ σ • n₁) = (lA W ^ σ * W.π₀ ^ AI) • ((1 : LetA O n) • y) := by
      rw [TypesA.map_smulA, hFn₁, one_smul, smul_smul]
    rw [e]; exact ArcLengthFourSecond.repVV_smulA W _ hmemσA hx₂R
  have hR0 := TypesA.RepVV_add W hRa (TypesA.RepVV_neg W hRb)
  rw [add_neg_cancel] at hR0
  have hMpos : 1 ≤ M := by rw [hM]; unfold ArcP.M; exact Nat.le_add_left 1 _
  have hφπ : W.φA W.π₀ = Br.cst Br.P.u * W.π₀ * qA W ^ (PD.p - 1) := by
    rw [Br.π₀_eq, Br.φA_cst, Br.P.hφ0, Br.cst_mul, Br.cst_mul, Br.cst_pow, ← Br.π₀_eq, ← Br.qA_eq]
  have hN : ∃ N : ℕ, ∃ w' ∈ W.AΔ, ((W.φA ^ 1) W.π₀) ^ N = W.π₀ * (qA W ^ G₀) ^ 2 * w' := by
    have h1 : 2 * G₀ + 1 ≤ (PD.p - 1) * (2 * G₀ + 1) := Nat.le_mul_of_pos_left _ (by omega)
    obtain ⟨r, hr⟩ : ∃ r, (PD.p - 1) * (2 * G₀ + 1) = 2 * G₀ + r :=
      ⟨_, (Nat.add_sub_cancel' (le_trans (Nat.le_succ _) h1)).symm⟩
    refine ⟨2 * G₀ + 1, Br.cst Br.P.u ^ (2 * G₀ + 1) * W.π₀ ^ (2 * G₀) * qA W ^ r,
      W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (Br.cst_mem _) _) (W.AΔ.pow_mem hπmem _)) (W.AΔ.pow_mem hqmem _), ?_⟩
    rw [pow_one, hφπ, mul_pow, mul_pow, ← pow_mul, hr]
    ring
  obtain ⟨Kc, hKc⟩ := repVV_zero_coord W hcase hP9 hinj T₂ hW₂.1 c' 1 M hMpos (qA W ^ G₀)
    (W.AΔ.pow_mem hqmem _) (by rw [map_pow]; exact hqu.pow _) hN bb sol hbb _ hR0
  rw [hac] at hKc

  set E : LetA O n := letE (c - 2) with hE
  have hEE : algebraMap (LetA O n) W.EE E * algebraMap (LetA O n) W.EE E = algebraMap (LetA O n) W.EE E := by
    rw [← map_mul, hidem]
  choose u₁ hu₁ hu₁eq using fun m => hg₁NL.1 m
  choose G₁ hG₁ using fun m => ArcLengthFourSecond.letter_rep Br (c - 2) (u₁ m) (hu₁ m)
  choose u₂ hu₂ hu₂eq using hKc
  choose G₂ hG₂ using fun k => ArcLengthFourSecond.letter_rep Br (c - 2) (u₂ k) (hu₂ k)
  set Φ : PowerSeries O := (PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) ^ AI * PowerSeries.X ^ (G₀ - wa) with hΦ
  have hΦc : Br.cst Φ = W.π₀ ^ AI * qA W ^ (G₀ - wa) := by
    rw [hΦ, Br.cst_mul, Br.cst_pow, Br.cst_pow, ← Br.π₀_eq, ← Br.qA_eq]

  have hPk : ∀ k, PowerSeries.C ((PD.p : ℕ) : O) ^ Kc *
      (∑ m, G₁ m * PowerSeries.C (μ m k) - if k = k₀ then PowerSeries.C ((PD.p : ℕ) : O) ^ (2 * σ) * Φ else 0) =
      PowerSeries.X ^ (2 * G₀) * ((PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) * G₂ k) := by
    intro k
    apply ArcLengthFourSecond.cst_letter_inj Br (c - 2)
    apply W.EE_inj
    have hm : ∀ m, algebraMap (LetA O n) W.EE (qA W ^ G₀) * (algebraMap (LetA O n) W.EE E * (g₁ m * algebraMap O W.EE (μ m k))) =
        algebraMap (LetA O n) W.EE (E * Br.cst (G₁ m) * algebraMap O (LetA O n) (μ m k)) := by
      intro m
      rw [show algebraMap (LetA O n) W.EE (qA W ^ G₀) * (algebraMap (LetA O n) W.EE E * (g₁ m * algebraMap O W.EE (μ m k))) =
          algebraMap (LetA O n) W.EE E * (algebraMap (LetA O n) W.EE (qA W ^ G₀) * g₁ m) * algebraMap O W.EE (μ m k) by ring,
        hu₁eq m, mul_one, hG₁ m, IsScalarTower.algebraMap_apply O (LetA O n) W.EE (μ m k), ← map_mul, ← map_mul, ← mul_assoc,
        hidem]
    have h2 : algebraMap (LetA O n) W.EE (qA W ^ G₀) * f₂ k =
        if k = k₀ then algebraMap (LetA O n) W.EE (E * 1 * qA W ^ (G₀ - wa)) else 0 := by
      by_cases hk : k = k₀
      · simp only [hf₂, if_pos hk]; exact hg₂Λ
      · simp [hf₂, hk]
    have h3 := hu₂eq k
    rw [show E * (W.π₀ * qA W ^ G₀) * u₂ k = (E * u₂ k) * (W.π₀ * qA W ^ G₀) by ring, hG₂ k] at h3
    have hsum : algebraMap (LetA O n) W.EE (qA W) ^ G₀ *
        (algebraMap (LetA O n) W.EE E * ∑ m, g₁ m * algebraMap O W.EE (μ m k)) =
        algebraMap (LetA O n) W.EE E * ∑ m, algebraMap (LetA O n) W.EE (Br.cst (G₁ m)) *
          algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) (μ m k)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have := hm m
      rw [map_pow] at this
      rw [this, map_mul, map_mul]
      ring
    have hq : algebraMap (LetA O n) W.EE (qA W) = algebraMap (LetA O n) W.EE W.π₀ + ((PD.p : ℕ) : W.EE) := by
      simp only [qA, lA, map_add, map_natCast]
    simp only [Br.cst_mul, Br.cst_pow, ArcLengthFourSecond.cst_sub, ArcLengthFourSecond.cst_sum, apply_ite Br.cst, ArcLengthFourSecond.cst_zero]
    rw [← Br.lA_eq, ← Br.qA_eq, hΦc]
    simp only [Br.cst_C]
    by_cases hk : k = k₀
    · rw [if_pos hk] at h2 ⊢
      simp only [map_mul, map_sub, map_sum, map_pow, map_natCast, map_one, map_neg, lA, lE, mul_one] at h3 h2 ⊢
      linear_combination (algebraMap (LetA O n) W.EE (qA W)) ^ G₀ * h3 - ((PD.p : ℕ) : W.EE) ^ Kc * hsum +
        (algebraMap (LetA O n) W.EE E * ((PD.p : ℕ) : W.EE) ^ Kc * ((PD.p : ℕ) : W.EE) ^ σ *
          (algebraMap (LetA O n) W.EE W.π₀) ^ AI * ((PD.p : ℕ) : W.EE) ^ σ) * h2 +
        (((PD.p : ℕ) : W.EE) ^ Kc * ((PD.p : ℕ) : W.EE) ^ (2 * σ) * (algebraMap (LetA O n) W.EE W.π₀) ^ AI *
          (algebraMap (LetA O n) W.EE (qA W)) ^ (G₀ - wa)) * hEE -
        (algebraMap (LetA O n) W.EE E * algebraMap (LetA O n) W.EE (Br.cst (G₂ k)) *
          (algebraMap (LetA O n) W.EE (qA W)) ^ (2 * G₀)) * hq
    · rw [if_neg hk] at h2 ⊢
      simp only [map_mul, map_sub, map_sum, map_pow, map_natCast, map_one, map_neg, map_zero, lA, lE, mul_one,
        sub_zero] at h3 h2 ⊢
      linear_combination (algebraMap (LetA O n) W.EE (qA W)) ^ G₀ * h3 - ((PD.p : ℕ) : W.EE) ^ Kc * hsum +
        (algebraMap (LetA O n) W.EE E * ((PD.p : ℕ) : W.EE) ^ Kc * ((PD.p : ℕ) : W.EE) ^ σ *
          (algebraMap (LetA O n) W.EE W.π₀) ^ AI * ((PD.p : ℕ) : W.EE) ^ σ) * h2 -
        (algebraMap (LetA O n) W.EE E * algebraMap (LetA O n) W.EE (Br.cst (G₂ k)) *
          (algebraMap (LetA O n) W.EE (qA W)) ^ (2 * G₀)) * hq
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := GS.p_ne_zero W

  have hcoef : ∀ j < 2 * G₀, ∀ k, ∑ m, PowerSeries.coeff j (G₁ m) * μ m k =
      if k = k₀ then ((PD.p : ℕ) : O) ^ (2 * σ) * PowerSeries.coeff j Φ else 0 := by
    intro j hj k
    have h := congrArg (PowerSeries.coeff j) (hPk k)
    rw [show (PowerSeries.C ((PD.p : ℕ) : O)) ^ Kc = PowerSeries.C (((PD.p : ℕ) : O) ^ Kc) from (map_pow _ _ _).symm,
      show (PowerSeries.C ((PD.p : ℕ) : O)) ^ (2 * σ) = PowerSeries.C (((PD.p : ℕ) : O) ^ (2 * σ)) from
        (map_pow _ _ _).symm] at h
    simp only [PowerSeries.coeff_X_pow_mul', if_neg (show ¬ 2 * G₀ ≤ j by omega), PowerSeries.coeff_C_mul, map_sub,
      map_sum, PowerSeries.coeff_mul_C, apply_ite (PowerSeries.coeff j), map_zero] at h
    rcases mul_eq_zero.1 h with h0 | h0
    · exact absurd h0 (pow_ne_zero _ hp0)
    · exact sub_eq_zero.1 h0

  have hgap : ∀ c₀ : Fin d₁ → O, dvO W T₁ 1 b₁ c₀ ∈ FilS W T₁ (c - 2) 0 ((η : ℤ) + 1) →
      dvO W T₁ 1 b₁ c₀ ∈ FilS W T₁ (c - 2) 0 (wa : ℤ) := by
    intro c₀ h
    have := (hFL hcase hl5 _ hOK c hc 1 (le_refl _) h1len T₁ hW₁ d₁ b₁ sol₁ hb₁ c₀ 0 (by norm_num)).2 wa htya
    rw [hac] at this
    exact this h
  have hdvO_smul : ∀ (r : O) (x : Fin d₁ → O), dvO W T₁ 1 b₁ (fun m => r * x m) = algebraMap O LL r • dvO W T₁ 1 b₁ x := by
    intro r x
    rw [ArcLengthFourSecond.dvO_eq_sum, ArcLengthFourSecond.dvO_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, mul_smul]
  obtain ⟨κ, I, gg, c₀, α, hI, hsumI⟩ := hg₁NL.2
  have hId : ∀ i, ∃ v ∈ W.AΔ, algebraMap (LetA O n) W.EE (qA W ^ (-(α i 0)).toNat) * gg i =
      algebraMap (LetA O n) W.EE (E * qA W ^ (α i 0).toNat * v) := by
    intro i
    have := (hI i).1
    simp only [InId, Finset.prod_range_one] at this
    rw [show ps W 0 = qA W by simp [ps]] at this
    exact this
  choose v hv hveq using hId
  choose V hV using fun i => ArcLengthFourSecond.letter_rep Br (c - 2) (v i) (hv i)
  set N' : ℕ := G₀ + ∑ i, (-(α i 0)).toNat with hN'
  have hnle : ∀ i, (-(α i 0)).toNat ≤ ∑ i, (-(α i 0)).toNat := fun i =>
    Finset.single_le_sum (f := fun i => (-(α i 0)).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hX : ∀ m, PowerSeries.X ^ (N' - G₀) * (PowerSeries.C (((PD.p : ℕ) : O) ^ κ) * G₁ m) =
      ∑ i, PowerSeries.X ^ (N' - (-(α i 0)).toNat + (α i 0).toNat) * (V i * PowerSeries.C (c₀ i m)) := by
    intro m
    apply ArcLengthFourSecond.cst_letter_inj Br (c - 2)
    apply W.EE_inj
    have hL : algebraMap (LetA O n) W.EE (qA W) ^ N' * (lE W κ * g₁ m) =
        algebraMap (LetA O n) W.EE (E * Br.cst (PowerSeries.X ^ (N' - G₀) *
          (PowerSeries.C (((PD.p : ℕ) : O) ^ κ) * G₁ m))) := by
      have e1 := hu₁eq m
      rw [mul_one, hG₁ m] at e1
      rw [Br.cst_mul, Br.cst_pow, Br.cst_mul, Br.cst_C, ← Br.qA_eq]
      have e2 : algebraMap (LetA O n) W.EE (qA W) ^ N' * (lE W κ * g₁ m) =
          algebraMap (LetA O n) W.EE (qA W) ^ (N' - G₀) * lE W κ * (algebraMap (LetA O n) W.EE (qA W ^ G₀) * g₁ m) := by
        have hNG : N' - G₀ + G₀ = N' := Nat.sub_add_cancel (by omega)
        rw [map_pow]
        conv_lhs => rw [← hNG, pow_add]
        ring
      rw [e2, e1]
      simp only [map_mul, map_pow, lE, map_natCast]
      ring
    have hR : ∀ i, algebraMap (LetA O n) W.EE (qA W) ^ N' * (gg i * algebraMap O W.EE (c₀ i m)) =
        algebraMap (LetA O n) W.EE (E * Br.cst (PowerSeries.X ^ (N' - (-(α i 0)).toNat + (α i 0).toNat) *
          (V i * PowerSeries.C (c₀ i m)))) := by
      intro i
      have e1 := hveq i
      rw [show E * qA W ^ (α i 0).toNat * v i = qA W ^ (α i 0).toNat * (E * v i) by ring, hV i] at e1
      rw [Br.cst_mul, Br.cst_pow, Br.cst_mul, Br.cst_C, ← Br.qA_eq]
      have e2 : algebraMap (LetA O n) W.EE (qA W) ^ N' * (gg i * algebraMap O W.EE (c₀ i m)) =
          algebraMap (LetA O n) W.EE (qA W) ^ (N' - (-(α i 0)).toNat) *
            (algebraMap (LetA O n) W.EE (qA W ^ (-(α i 0)).toNat) * gg i) * algebraMap O W.EE (c₀ i m) := by
        have hNG : N' - (-(α i 0)).toNat + (-(α i 0)).toNat = N' := Nat.sub_add_cancel (by have := hnle i; omega)
        rw [map_pow]
        conv_lhs => rw [← hNG, pow_add]
        ring
      rw [e2, e1, IsScalarTower.algebraMap_apply O (LetA O n) W.EE (c₀ i m)]
      simp only [map_mul, map_pow, pow_add]
      ring
    have hs := hsumI m
    beta_reduce at hs
    rw [← hL, hs, Finset.mul_sum, ArcLengthFourSecond.cst_sum, Finset.mul_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => hR i
  have hFil : ∀ j < G₀ - η, dvO W T₁ 1 b₁ (fun m => PowerSeries.coeff j (G₁ m)) ∈ FilS W T₁ (c - 2) 0 (wa : ℤ) := by
    intro j hj
    set r : Fin I → O := fun i => if N' - (-(α i 0)).toNat + (α i 0).toNat ≤ N' - G₀ + j then
      PowerSeries.coeff (N' - G₀ + j - (N' - (-(α i 0)).toNat + (α i 0).toNat)) (V i) else 0 with hr
    have hvec : ∀ m, ((PD.p : ℕ) : O) ^ κ * PowerSeries.coeff j (G₁ m) = ∑ i, r i * c₀ i m := by
      intro m
      have h := congrArg (PowerSeries.coeff (N' - G₀ + j)) (hX m)
      rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left, PowerSeries.coeff_C_mul, map_sum] at h
      rw [h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PowerSeries.coeff_X_pow_mul']
      simp only [hr]
      split_ifs
      · rw [PowerSeries.coeff_mul_C]
      · rw [zero_mul]
    have hsumFil : dvO W T₁ 1 b₁ (fun m => ((PD.p : ℕ) : O) ^ κ * PowerSeries.coeff j (G₁ m)) ∈
        FilS W T₁ (c - 2) 0 (wa : ℤ) := by
      have e : dvO W T₁ 1 b₁ (fun m => ((PD.p : ℕ) : O) ^ κ * PowerSeries.coeff j (G₁ m)) =
          ∑ i, algebraMap O LL (r i) • dvO W T₁ 1 b₁ (c₀ i) := by
        simp_rw [hvec, ArcLengthFourSecond.dvO_eq_sum, Finset.smul_sum, map_sum, Finset.sum_smul, map_mul, mul_smul]
        exact Finset.sum_comm
      rw [e]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hi : N' - (-(α i 0)).toNat + (α i 0).toNat ≤ N' - G₀ + j
      · refine Submodule.smul_mem _ _ (hgap _ ?_)
        have hc := (hI i).2 0 (by norm_num)
        refine ArcLengthFourSecond.filS_mono W T₁ (c - 2) 0 ?_ hc
        have := hnle i
        omega
      · simp only [hr, if_neg hi, map_zero, zero_smul]
        exact Submodule.zero_mem _
    rw [hdvO_smul] at hsumFil
    have hne : algebraMap O LL (((PD.p : ℕ) : O) ^ κ) ≠ 0 := by
      rw [map_pow, map_natCast]; exact pow_ne_zero _ (Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W)
    exact (Submodule.smul_mem_iff _ hne).1 hsumFil

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨uu, huu⟩ := l_eq_unit_mul_pow (l := PD.p) hϖ hp0
  have heO : 1 ≤ eO (O := O) PD.p := by
    by_contra h0
    have h00 : eO (O := O) PD.p = 0 := by omega
    rw [h00, pow_zero, mul_one] at huu
    exact ((IsLocalRing.mem_maximalIdeal _).1 Br.P.hl) (huu ▸ uu.isUnit)
  have hnot : ¬ (PowerSeries.C (((PD.p : ℕ) : O) ^ (2 * σ)) * 1 *
      (PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) ^ AI * PowerSeries.X ^ (G₀ - wa) ∈
        Ideal.span {PowerSeries.C (ϖ ^ (eO (O := O) PD.p * (2 * σ + 1))), (PowerSeries.X : PowerSeries O) ^ (G₀ - η)}) := by
    intro hmem
    have h1 : ϖ ^ (eO (O := O) PD.p * 0) ∣ PowerSeries.constantCoeff (1 : PowerSeries O) := by simp
    have h2 : ¬ ϖ ^ (eO (O := O) PD.p * 0 + 1) ∣ PowerSeries.constantCoeff (1 : PowerSeries O) := by
      rw [mul_zero, zero_add, pow_one, map_one, ← isUnit_iff_dvd_one]; exact hϖ.not_isUnit
    have := hR2 O ϖ hϖ PD.p PD.hp _ uu heO huu 1 (2 * σ) AI (G₀ - wa) (G₀ - η) 0 _ h1 h2 (by omega) hmem
    have heO' : ((eO (O := O) PD.p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show eO (O := O) PD.p ≠ 0 by omega)
    rw [Nat.cast_mul, mul_div_cancel_left₀ _ heO'] at this
    push_cast at this
    linarith
  obtain ⟨j, hj, hjnd⟩ : ∃ j < G₀ - η, ¬ ϖ ^ (eO (O := O) PD.p * (2 * σ + 1)) ∣
      PowerSeries.coeff j (PowerSeries.C (((PD.p : ℕ) : O) ^ (2 * σ)) * 1 *
        (PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) ^ AI * PowerSeries.X ^ (G₀ - wa)) := by
    by_contra hall
    push_neg at hall
    exact hnot (ArcLengthFourSecond.mem_span_of_coeff _ _ _ hall)
  rw [mul_one, mul_assoc, ← hΦ, PowerSeries.coeff_C_mul] at hjnd
  set t := PowerSeries.coeff j Φ with ht

  have hpt : ¬ ((PD.p : ℕ) : O) ∣ t := by
    intro hd
    apply hjnd
    obtain ⟨t', ht'⟩ := hd
    refine ⟨(uu : O) ^ (2 * σ + 1) * t', ?_⟩
    rw [ht', ← mul_assoc, ← pow_succ, huu, mul_pow, ← pow_mul]
    ring
  obtain ⟨rq, hrq⟩ : t ∣ ((PD.p : ℕ) : O) := by
    have ht0 : t ≠ 0 := fun h0 => hpt (h0 ▸ dvd_zero _)
    obtain ⟨r₀, ut, hut⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hϖ
    by_cases hr : eO (O := O) PD.p ≤ r₀
    · have hpow : ϖ ^ r₀ = ϖ ^ eO (O := O) PD.p * ϖ ^ (r₀ - eO (O := O) PD.p) := by
        rw [← pow_add, Nat.add_sub_cancel' hr]
      have hu1 : (uu : O) * ((uu⁻¹ : Oˣ) : O) = 1 := uu.mul_inv
      exact absurd ⟨(ut : O) * ((uu⁻¹ : Oˣ) : O) * ϖ ^ (r₀ - eO (O := O) PD.p), by
        rw [hut, huu]
        linear_combination (ut : O) * hpow - ((ut : O) * ϖ ^ eO (O := O) PD.p * ϖ ^ (r₀ - eO (O := O) PD.p)) * hu1⟩ hpt
    · have hpow : ϖ ^ eO (O := O) PD.p = ϖ ^ r₀ * ϖ ^ (eO (O := O) PD.p - r₀) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      have hu2 : (ut : O) * ((ut⁻¹ : Oˣ) : O) = 1 := ut.mul_inv
      refine ⟨(uu : O) * ((ut⁻¹ : Oˣ) : O) * ϖ ^ (eO (O := O) PD.p - r₀), ?_⟩
      rw [hut, huu]
      linear_combination (uu : O) * hpow - ((uu : O) * ϖ ^ r₀ * ϖ ^ (eO (O := O) PD.p - r₀)) * hu2

  set c₁ : Fin d₁ → O := fun m => rq * PowerSeries.coeff j (G₁ m) with hc₁
  have hFil1 : dvO W T₁ 1 b₁ c₁ ∈ FilS W T₁ (c - 2) 0 (wa : ℤ) := by
    rw [hc₁, hdvO_smul]
    exact Submodule.smul_mem _ _ (hFil j (by omega))
  have hμc : ∀ k, ∑ m, c₁ m * μ m k = if k = k₀ then ((PD.p : ℕ) : O) ^ (2 * σ + 1) else 0 := by
    intro k
    simp only [hc₁, mul_assoc, ← Finset.mul_sum]
    rw [hcoef j (by omega) k]
    split_ifs
    · rw [← ht, pow_succ, hrq]; ring
    · rw [mul_zero]
  have hcris1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ 1 b₁ c₁) =
      ((PD.p : LL) ^ (2 * σ + 1)) • dv W T₂ 1 bb (Pi.single k₀ 1) := by
    rw [ArcLengthFourSecond.dvO_eq_sum, map_sum]
    simp_rw [map_smul, hμcris, ArcLengthFourSecond.dvO_eq_sum, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← map_mul, ← map_sum, hμc]
    rw [Finset.sum_eq_single k₀]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨d₁, b₁, sol₁, c₁, hb₁, ?_, ?_⟩
  · rw [show (arcOf b w S η up size).len c = 1 + 2 from hlen, ArcLengthFourSecond.dvO_shift]
    exact ArcLengthFourSecond.filS_shift W T₁ 2 (by push_cast; rfl) hFil1
  · rw [show (arcOf b w S η up size).len c = 1 + 2 from hlen, ArcLengthFourSecond.dvO_shift, ArcLengthFourSecond.dv_shift,
      Formalism.MainNotions.UnusedSlot80.ArcC.crisMap_φVB_pow, hcris1, map_smul]

end Formalism.MainNotions.N.FrobeniusPowerSeries
