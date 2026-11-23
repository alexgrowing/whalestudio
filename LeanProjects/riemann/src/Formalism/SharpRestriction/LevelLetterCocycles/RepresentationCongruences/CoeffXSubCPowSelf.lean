import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RepVVSmulA

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
open PowerSeries

namespace ArcLengthTwo

section Letter

variable {W : LocWach PD LL O v n} [IsDomain O] [IsDiscreteValuationRing O] (Br : PhiBridge W) (a : ZMod n)

def EL (F : PowerSeries O) : W.EE := algebraMap (LetA O n) W.EE (letE a * Br.cst F)

theorem cst_add' (F G : PowerSeries O) : Br.cst (F + G) = Br.cst F + Br.cst G := by
  funext i
  simp [PhiBridge.cst]

theorem cst_mul' (F G : PowerSeries O) : Br.cst (F * G) = Br.cst F * Br.cst G := by
  funext i
  simp [PhiBridge.cst]

theorem cst_sum' {I : Type} (s : Finset I) (F : I → PowerSeries O) :
    Br.cst (∑ i ∈ s, F i) = ∑ i ∈ s, Br.cst (F i) := by
  funext j
  simp [PhiBridge.cst, Finset.sum_apply]

theorem cst_C' (x : O) : Br.cst (C x) = algebraMap O (LetA O n) x := by
  funext i
  have h : Br.ι (C x) = C x := Br.ι.commutes x
  simp [PhiBridge.cst, h]

theorem EL_add (F G : PowerSeries O) : EL Br a (F + G) = EL Br a F + EL Br a G := by
  simp only [EL, cst_add' Br, mul_add, map_add]

theorem EL_sum {I : Type} (s : Finset I) (F : I → PowerSeries O) :
    EL Br a (∑ i ∈ s, F i) = ∑ i ∈ s, EL Br a (F i) := by
  simp only [EL, cst_sum' Br, Finset.mul_sum, map_sum]

theorem EL_zero : EL Br a 0 = 0 := by
  have h : Br.cst 0 = 0 := by
    funext i
    simp [PhiBridge.cst]
  simp [EL, h]

theorem EL_mulA (u : LetA O n) (F G : PowerSeries O) (h : Br.cst F = u) :
    algebraMap (LetA O n) W.EE u * EL Br a G = EL Br a (F * G) := by
  subst h
  simp only [EL, cst_mul' Br]
  rw [← map_mul]
  congr 1
  ring

theorem EL_C (x : O) (F : PowerSeries O) :
    algebraMap O W.EE x * EL Br a F = EL Br a (C x * F) := by
  rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  exact EL_mulA Br a _ (C x) F (cst_C' Br x)

theorem EL_lE (K : ℕ) (F : PowerSeries O) :
    lE W K * EL Br a F = EL Br a (C (((PD.p : ℕ) : O) ^ K) * F) := by
  unfold lE
  rw [← EL_C Br a _ F, map_pow, map_natCast]

theorem EL_letE (F : PowerSeries O) :
    algebraMap (LetA O n) W.EE (letE a) * EL Br a F = EL Br a F := by
  simp only [EL]
  rw [← map_mul, ← mul_assoc, letE_mul_self]

theorem EL_inj {F G : PowerSeries O} (h : EL Br a F = EL Br a G) : F = G := by
  have h1 : letE a * Br.cst F = letE a * Br.cst G := W.EE_inj (by simpa only [EL] using h)
  have h2 := congrFun h1 a
  simp only [Pi.mul_apply, PhiBridge.cst] at h2
  unfold letE at h2
  simp only [Pi.single_eq_same, one_mul] at h2
  exact Br.inj h2

theorem EL_of_mem {u : LetA O n} (hu : u ∈ W.AΔ) :
    ∃ F, algebraMap (LetA O n) W.EE (letE a * u) = EL Br a F := by
  obtain ⟨F, hF⟩ := Br.range u hu a
  refine ⟨F, ?_⟩
  simp only [EL]
  congr 1
  funext i
  simp only [Pi.mul_apply, PhiBridge.cst]
  by_cases hi : i = a
  · subst hi
    rw [hF]
  · unfold letE
    rw [Pi.single_eq_of_ne hi, zero_mul, zero_mul]

end Letter

theorem coeff_X_sub_C_pow_self {R : Type} [CommRing R] [Nontrivial R] (x : R) (k : ℕ) :
    PowerSeries.coeff k ((X - C x : PowerSeries R) ^ k) = 1 := by
  have hm : ((Polynomial.X - Polynomial.C x) ^ k).Monic := (Polynomial.monic_X_sub_C x).pow k
  have hd : ((Polynomial.X - Polynomial.C x) ^ k).natDegree = k := by
    rw [(Polynomial.monic_X_sub_C x).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hc : ((X - C x : PowerSeries R) ^ k) =
      (((Polynomial.X - Polynomial.C x) ^ k : Polynomial R) : PowerSeries R) := by
    simp only [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]
  have h1 := hm.coeff_natDegree
  rw [hd] at h1
  rw [hc, Polynomial.coeff_coe, h1]

theorem cst_pow' {W : LocWach PD LL O v n} [IsDomain O] [IsDiscreteValuationRing O] (Br : PhiBridge W)
    (F : PowerSeries O) (k : ℕ) : Br.cst (F ^ k) = Br.cst F ^ k := by
  funext i
  simp [PhiBridge.cst]

end ArcLengthTwo

namespace ArcLengthTwo

theorem crisMap_coords (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (e : ℕ)
    {d₁ d : ℕ} (b₁ : Fin d₁ → W.DD T₁) (bb : Fin d → W.DD T₂) (μ : Fin d₁ → Fin d → O)
    (hμ : ∀ m, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ e b₁ (Pi.single m 1)) = dvO W T₂ e bb (μ m))
    (c₁ : Fin d₁ → O) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ e b₁ c₁) = dvO W T₂ e bb (fun k => ∑ m, c₁ m * μ m k) := by
  have hX : ∀ m, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (((φVB PD (LL := LL) (V := T₁.V)) ^ e) (cmpD W T₁ (b₁ m))) =
      ∑ k, algebraMap O LL (μ m k) • ((φVB PD (LL := LL) (V := T₂.V)) ^ e) (cmpD W T₂ (bb k)) := by
    intro m
    have hm := hμ m
    simp only [dvO, dv, map_sum, map_smul] at hm
    simpa [Pi.single_apply] using hm
  simp only [dvO, dv, map_sum, map_smul, hX, Finset.smul_sum, smul_smul, map_mul, Finset.sum_smul]
  exact Finset.sum_comm

set_option maxHeartbeats 1000000 in

theorem lift2a [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂)
    (hArc : ArcCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hSec : ArcSecMapCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK)
    (hup : up c = false) (h2a : Formalism.MainNotions.LiftingTheory.AI W F (c - 1) + η + 1 ≤ size (c - 1)) :
    ∃ (d₁ : ℕ) (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL),
      IsHor W T₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) b₁ sol₁ ∧
      ∃ c₁ : Fin d₁ → O,
        dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁ ∈ FilS W T₁ c 1 (size (c - 1)) ∧
        Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁) =
          ((PD.p : LL) ^ (2 * (arcOf b w S η up size).σ PD.p)) •
            dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) := by
  classical
  have hOKc := hOK
  set A := arcOf b w S η up size with hA
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  set a : ZMod n := c' + ((1 : ℕ) : ZMod n) with ha
  set w' := size (c - 1) with hw'
  set σ := A.σ PD.p with hσdef
  set M := A.M PD.p with hM
  set AA := Formalism.MainNotions.LiftingTheory.AI W F (c - 1) with hAA
  have hac : a = c - 1 := by rw [ha, hc', hlen]; push_cast; ring
  have hca : c - ((1 : ℕ) : ZMod n) = a := by rw [hac]; simp
  have ha0 : a - ((0 : ℕ) : ZMod n) = c - 1 := by rw [hac]; simp
  have hup1 : up (c - 1) = true := by
    cases h : up (c - 1) <;> simp_all
  have hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up w' := by rw [hA, arc_letter_type_eq_ite, hup1]; rfl
  have htya : A.ty (a - ((0 : ℕ) : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up w' := by rw [ha0, hty1]
  have hl5 : 5 ≤ PD.p := by have := hB.1; omega
  have hcase : Formalism.MainNotions.LiftingTheory.CaseA W := hB.2.1.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hB.2.1.2.1
  have hJL : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi := hB.2.1.2.2.2.2.2.2
  have hj : A.j = 1 := rfl
  obtain ⟨-, -, hcuts, -, hok, -, -, -, halt⟩ := hOK
  have hc'cut : c' ∈ A.cuts := (hcuts c hc).2.2.1
  have hc'1 : c' + 1 = c - 1 := by rw [← hac, ha]; simp
  have hwG : w' + S ≤ w + S := by
    rcases halt with h | ⟨-, -, h⟩
    · have := h c' hc'cut 1 le_rfl (by simp [hj])
      rw [Nat.cast_one, hc'1, hty1] at this
      cases this
    · have := h c' hc'cut
      rw [hc'1, hty1] at this
      exact this
  have hηw : η < w' := by
    have := hok (c - 1)
    rw [hty1] at this
    exact this
  have hT₁ : IsCrys PD T₁.ρ := hW₁.1
  have hT₂ : IsCrys PD T₂.ρ := hW₂.1
  obtain ⟨-, hqu, hΔu⟩ := lemG_units W hcase hP9 hT₁ hO hOv hinj
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hT₁ hO hinj
  have hqA : qA W ∈ W.AΔ := by
    have := TypesA.ps_mem W 0
    simpa [ps] using this
  have hΛ : abelian₂ W A a 1 = qA W ^ (w + S) := by
    unfold abelian₂
    rw [Finset.prod_range_one]
    unfold ArcP.Hs
    rw [if_pos (Or.inr (by simp [hj]))]
    show ps W 0 ^ (w + S) = qA W ^ (w + S)
    simp [ps]
  have hl0 : ((PD.p : ℕ) : O) ≠ 0 := Br.P.hl0
  have hdv2 : ∀ (T : LocLat G Qp LL O) {d' : ℕ} (b' : Fin d' → W.DD T) (c₀ : Fin d' → LL),
      dv W T 2 b' c₀ = φVB PD (LL := LL) (V := T.V) (dv W T 1 b' c₀) := fun T _ b' c₀ => dv_succ W T 1 b' c₀
  have hdvO2 : ∀ (T : LocLat G Qp LL O) {d' : ℕ} (b' : Fin d' → W.DD T) (c₀ : Fin d' → O),
      dvO W T 2 b' c₀ = φVB PD (LL := LL) (V := T.V) (dvO W T 1 b' c₀) := fun T _ b' c₀ => dvO_succ W T 1 b' c₀

  have HA := hArc hcase hl5 A hOKc c hc 1 (by simp [hj]) (by omega)
  dsimp only at HA
  obtain ⟨hJJ, HT⟩ := HA
  obtain ⟨-, hNP₂, -, hfr₂⟩ := HT T₂ hW₂
  obtain ⟨-, -, -, -, hnl2, -, -⟩ := hfr₂ d bb sol hbb

  have hlamFil : dvO W T₂ 1 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 0 w' := by
    have h := hk₀ 1 (by omega) w' (by rw [Nat.cast_one]; exact hty1)
    rw [hlen, hdv2] at h
    rw [dvO_single]
    exact filS_φ_inv W T₂ hca h

  set qu : W.EEˣ := hqu.unit with hqudef
  have hqq : algebraMap (LetA O n) W.EE (qA W) ^ w' * ((qu⁻¹ ^ w' : W.EEˣ) : W.EE) = 1 := by
    rw [← hqu.unit_spec, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
      Units.val_one]
  set g₂ : W.EE := algebraMap (LetA O n) W.EE (letE a) * ((qu⁻¹ ^ w' : W.EEˣ) : W.EE) with hg₂
  set f₂ : Fin d → W.EE := fun k => if k = k₀ then g₂ else 0 with hf₂
  have hf₂Fr : ∀ k, InFr W a 1 (abelian₂ W A a 1) (f₂ k) := by
    intro k
    by_cases hk : k = k₀
    · refine ⟨qA W ^ (w + S - w'), pow_mem hqA _, ?_⟩
      simp only [hf₂, if_pos hk, hΛ, hg₂, mul_one]
      have e : w + S = (w + S - w') + w' := by omega
      rw [e, pow_add, map_mul, map_mul, map_pow, map_pow, map_pow, Nat.add_sub_cancel]
      linear_combination (algebraMap (LetA O n) W.EE (letE a) *
        algebraMap (LetA O n) W.EE (qA W) ^ (w + S - w')) * hqq
    · refine ⟨0, zero_mem _, ?_⟩
      simp [hf₂, hk]
  have hId : InId W a 1 (fun _ => -(w' : ℤ)) g₂ := by
    show InFr W a (∏ s ∈ Finset.range 1, ps W s ^ (-(w' : ℤ)).toNat)
      (∏ s ∈ Finset.range 1, ps W s ^ (-(-(w' : ℤ))).toNat) g₂
    have h0 : (-(w' : ℤ)).toNat = 0 := by omega
    have h1 : (-(-(w' : ℤ))).toNat = w' := by omega
    rw [h0, h1]
    refine ⟨1, one_mem _, ?_⟩
    simp only [Finset.prod_range_one, pow_zero, mul_one, hg₂]
    have hps : ps W 0 = qA W := by simp [ps]
    rw [hps, map_pow]
    linear_combination (algebraMap (LetA O n) W.EE (letE a)) * hqq
  have hcond : condNN W T₂ a 1 bb (fun _ => -(w' : ℤ)) (Pi.single k₀ 1) := by
    intro s hs
    obtain rfl : s = 0 := by omega
    show dvO W T₂ 1 bb (Pi.single k₀ 1) ∈ FilS W T₂ a 0 (-(-(w' : ℤ)))
    rw [neg_neg]
    exact hlamFil
  have hSec₂ : SecIn W a 1 (condNN W T₂ a 1 bb) (fun k => lE W 0 * f₂ k) := by
    refine ⟨1, fun _ => g₂, fun _ => Pi.single k₀ 1, fun _ _ => -(w' : ℤ), fun _ => ⟨hId, hcond⟩, fun k => ?_⟩
    simp only [lE, pow_zero, one_mul, Fin.sum_univ_one, hf₂]
    by_cases hk : k = k₀
    · simp [hk]
    · simp [hk, Pi.single_apply]
  obtain ⟨n₂, hn₂N, hn₂R⟩ := hnl2 f₂ ⟨hf₂Fr, 0, hSec₂⟩

  obtain ⟨y, hyΔ, hylet, hn₂y⟩ := hn₂N
  have hy' : y ∈ W.N T₂ ∧ ∀ δ ∈ W.DelF, W.γD T₂ δ y = y := hyΔ
  have hyNl : y ∈ W.Nl T₂ a := by
    refine ⟨y, hy'.1, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact hylet
  have hK : Formalism.MainNotions.LiftingTheory.KillsΔ W F a (W.π₀ ^ AA) := by
    rw [hac]
    exact (hWR hcase T₁ T₂ F Mi hi hsur hJL (c - 1)).2.1
  obtain ⟨z, hzNl, hzmap⟩ := hK y hyNl hy'.2
  obtain ⟨z₀, hz₀, rfl⟩ := hzNl
  simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply] at hzmap
  have hzN : (letE a : LetA O n) • z₀ ∈ W.N T₁ := (W.N T₁).smul_mem _ hz₀
  have hzlet : (letE a : LetA O n) • ((letE a : LetA O n) • z₀) = (letE a : LetA O n) • z₀ := by
    rw [smul_smul, letE_mul_self]
  set zb : W.DD T₁ := ∑ δ ∈ W.DelF, W.γD T₁ δ ((letE a : LetA O n) • z₀) with hzb
  obtain ⟨hzbΔ, hzblet⟩ := avg_props W a hzN hzlet
  have hmapzb : W.map F zb = (W.DelF.card : ℕ) • (W.π₀ ^ AA • y) := by
    rw [hzb, map_sum]
    have : ∀ δ ∈ W.DelF, W.map F (W.γD T₁ δ ((letE a : LetA O n) • z₀)) = W.π₀ ^ AA • y := by
      intro δ hδ
      rw [W.map_γ, hzmap, γD_smulA, hy'.2 δ hδ,
        (show ∀ δ ∈ W.DelF, W.γA δ (W.π₀ ^ AA) = W.π₀ ^ AA from pow_mem (TypesA.pi0_mem_ADelta W) AA) δ hδ]
    rw [Finset.sum_congr rfl this, Finset.sum_const]

  obtain ⟨d₁, b₁, sol₁, hb₁⟩ := hHF hcase hl5 A hOKc T₁ hW₁ c'
  obtain ⟨-, hNP₁, -, hfr₁⟩ := HT T₁ hW₁
  obtain ⟨⟨hlin₁, -⟩, -, -, hnl1₁, -, -, -⟩ := hfr₁ d₁ b₁ sol₁ hb₁
  have hn₁Nc : InFNc W T₁ a 1 zb := ⟨zb, hzbΔ, hzblet, (one_smul _ _).symm⟩
  obtain ⟨f₁, hf₁NL, hf₁R⟩ := hnl1₁ zb hn₁Nc

  obtain ⟨-, μ, hμ, hRep⟩ := hSec hcase hl5 A hOKc c hc 1 (by simp [hj]) (by omega) T₁ T₂ F hW₁ hW₂
    d₁ b₁ sol₁ hb₁ d bb sol hbb
  have hxP : InFP W T₁ c' 1 1 (abelian₂ W A a 1 • (lA W ^ σ • zb)) :=
    hNP₁ _ (TypesA.InFNc_smul W (TypesA.lA_pow_mem W σ) hn₁Nc)
  have hR₂ := hRep (lA W ^ σ • zb) f₁ hxP hf₁NL.1 hf₁R
  obtain ⟨aa, haadef⟩ : ∃ aa : LetA O n, aa = ((W.DelF.card : ℕ) : LetA O n) * lA W ^ σ * W.π₀ ^ AA := ⟨_, rfl⟩
  have haa : aa ∈ W.AΔ := by
    rw [haadef]
    exact mul_mem (mul_mem (natCast_mem _ _) (TypesA.lA_pow_mem W σ)) (pow_mem (TypesA.pi0_mem_ADelta W) _)
  have hR₃ := RepVV_smulA W haa hn₂R
  have hxeq : W.map F (lA W ^ σ • zb) = aa • n₂ := by
    rw [TypesA.map_smulA, hmapzb, hn₂y, one_smul, haadef, mul_smul, mul_smul,
      ← Nat.cast_smul_eq_nsmul (LetA O n), smul_comm (lA W ^ σ)]
  have hR₀ : RepVV W T₂ c' 1 M (abelian₂ W A a 1) bb sol 0 (fun k => (∑ m, f₁ m * algebraMap O W.EE (μ m k)) -
      algebraMap (LetA O n) W.EE aa * (lE W σ * f₂ k)) :=
    TypesA.RepVV_congr W (TypesA.RepVV_add W hR₂ (TypesA.RepVV_neg W hR₃))
    (by rw [hxeq, add_neg_cancel]) (fun k => (sub_eq_add_neg _ _).symm)
  have hΛmem : abelian₂ W A a 1 ∈ W.AΔ := by rw [hΛ]; exact pow_mem hqA _
  have hΛu : IsUnit (algebraMap (LetA O n) W.EE (abelian₂ W A a 1)) := by rw [hΛ, map_pow]; exact hqu.pow _
  have hM1 : 1 ≤ M := by rw [hM]; unfold ArcP.M; exact Nat.le_add_left 1 _
  have hN : ∃ N : ℕ, ∃ wv ∈ W.AΔ, ((W.φA ^ 1) W.π₀) ^ N = W.π₀ * abelian₂ W A a 1 ^ 2 * wv := by
    obtain ⟨K', hK'⟩ : ∃ K' : ℕ, K' = (PD.p - 1) * (2 * (w + S) + 1) - 2 * (w + S) := ⟨_, rfl⟩
    have hle : 2 * (w + S) ≤ (PD.p - 1) * (2 * (w + S) + 1) := by
      have hp1 : 1 ≤ PD.p - 1 := by omega
      nlinarith
    have e1 : (PD.p - 1) * (2 * (w + S) + 1) = K' + 2 * (w + S) := by omega
    refine ⟨2 * (w + S) + 1, Br.cst (Br.P.u ^ (2 * (w + S) + 1) * (X - C ((PD.p : ℕ) : O)) ^ (2 * (w + S)) *
      X ^ K'), Br.cst_mem _, ?_⟩
    rw [pow_one, Br.π₀_eq, Br.φA_cst, Br.P.hφ0, hΛ, Br.qA_eq]
    simp only [← cst_pow', ← cst_mul']
    congr 1
    rw [mul_pow, mul_pow, ← pow_mul, e1, pow_add]
    ring
  obtain ⟨K, hKk⟩ := repVV_zero_coord W hcase hP9 hinj T₂ hT₂ c' 1 M hM1 (abelian₂ W A a 1) hΛmem hΛu hN bb sol hbb _ hR₀

  have hps : ps W 0 = qA W := by simp [ps]
  have hAS : A.S = S := rfl
  have hAη : A.η = η := rfl
  have hqcst : ∀ k : ℕ, Br.cst (X ^ k) = qA W ^ k := fun k => by rw [Br.cst_pow, Br.qA_eq]
  have hπcst : ∀ k : ℕ, Br.cst ((X - C ((PD.p : ℕ) : O)) ^ k) = W.π₀ ^ k := fun k => by rw [Br.cst_pow, Br.π₀_eq]
  choose U hUm hUeq using hf₁NL.1
  choose Φ hΦ using fun m => EL_of_mem Br a (hUm m)
  have hΦe : ∀ m, algebraMap (LetA O n) W.EE (qA W ^ (w + S)) * f₁ m = EL Br a (Φ m) := by
    intro m
    rw [← hΦ m, ← hΛ, hUeq m, mul_one]
  obtain ⟨κ, I, g, c₀, α, hgi, hsum⟩ := hf₁NL.2
  set Nn : Fin I → ℕ := fun i => (-(α i 0)).toNat with hNn
  set Pn : Fin I → ℕ := fun i => (α i 0).toNat with hPn
  have hgI : ∀ i, ∃ V ∈ W.AΔ, algebraMap (LetA O n) W.EE (qA W ^ Nn i) * g i =
      algebraMap (LetA O n) W.EE (letE a * qA W ^ Pn i * V) := by
    intro i
    obtain ⟨V, hV, e⟩ := (hgi i).1
    refine ⟨V, hV, ?_⟩
    show algebraMap (LetA O n) W.EE (qA W ^ (-(α i 0)).toNat) * g i =
      algebraMap (LetA O n) W.EE (letE a * qA W ^ (α i 0).toNat * V)
    simp only [Finset.prod_range_one, hps] at e
    exact e
  choose V hVm hVeq using hgI
  choose Ψ hΨ using fun i => EL_of_mem Br a (hVm i)
  have hgE : ∀ i, algebraMap (LetA O n) W.EE (qA W ^ Nn i) * g i = EL Br a (X ^ Pn i * Ψ i) := by
    intro i
    rw [hVeq i, ← EL_mulA Br a (qA W ^ Pn i) _ _ (hqcst _), ← hΨ i, ← map_mul]
    ring_nf

  have hbad : ∀ i, w' + S < Nn i → c₀ i = 0 := by
    intro i hi
    have hF := (hgi i).2 0 (by norm_num)
    have htop : FilS W T₁ a 0 (-(α i 0)) = ⊥ := by
      refine filS_top W hcase A T₁ hW₁ a 0 _ ?_
      intro x hx
      rw [htya, hAS, hAη] at hx
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hx
      have hi' : w' + S < (-(α i 0)).toNat := hi
      omega
    rw [htop] at hF
    have h0 : dvO W T₁ 1 b₁ (c₀ i) = 0 := (Submodule.mem_bot _).1 hF
    funext m
    rw [dvO, dv_eq_sum] at h0
    have := Fintype.linearIndependent_iff.mp hlin₁ _ h0 m
    exact hinj (by simpa using this)

  set Tm : Fin I → Fin d₁ → PowerSeries O := fun i m =>
    if Nn i ≤ w' + S then X ^ (w + S - Nn i + Pn i) * Ψ i * C (c₀ i m) else 0 with hTm
  have hterm : ∀ i m, algebraMap (LetA O n) W.EE (qA W ^ (w + S)) * (g i * algebraMap O W.EE (c₀ i m)) =
      EL Br a (Tm i m) := by
    intro i m
    by_cases h : Nn i ≤ w' + S
    · simp only [hTm, if_pos h]
      have hsplit : algebraMap (LetA O n) W.EE (qA W ^ (w + S)) =
          algebraMap (LetA O n) W.EE (qA W ^ (w + S - Nn i)) * algebraMap (LetA O n) W.EE (qA W ^ Nn i) := by
        rw [← map_mul, ← pow_add, Nat.sub_add_cancel (by omega)]
      calc algebraMap (LetA O n) W.EE (qA W ^ (w + S)) * (g i * algebraMap O W.EE (c₀ i m))
          = algebraMap O W.EE (c₀ i m) * (algebraMap (LetA O n) W.EE (qA W ^ (w + S - Nn i)) *
              (algebraMap (LetA O n) W.EE (qA W ^ Nn i) * g i)) := by rw [hsplit]; ring
        _ = algebraMap O W.EE (c₀ i m) * (algebraMap (LetA O n) W.EE (qA W ^ (w + S - Nn i)) *
              EL Br a (X ^ Pn i * Ψ i)) := by rw [hgE i]
        _ = algebraMap O W.EE (c₀ i m) * EL Br a (X ^ (w + S - Nn i) * (X ^ Pn i * Ψ i)) := by
              rw [EL_mulA Br a _ _ _ (hqcst _)]
        _ = EL Br a (C (c₀ i m) * (X ^ (w + S - Nn i) * (X ^ Pn i * Ψ i))) := by rw [EL_C]
        _ = EL Br a (X ^ (w + S - Nn i + Pn i) * Ψ i * C (c₀ i m)) := by congr 1; rw [pow_add]; ring
    · simp only [hTm, if_neg h, hbad i (by omega), Pi.zero_apply, map_zero, mul_zero, EL_zero]
  have hstar : ∀ m, C (((PD.p : ℕ) : O) ^ κ) * Φ m = ∑ i, Tm i m := by
    intro m
    apply EL_inj Br a
    have hs := hsum m
    simp only at hs
    rw [← EL_lE, EL_sum, ← hΦe m, mul_left_comm, hs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i m

  set J : ℕ := AA + (w + S) - w' with hJ
  set Cc : Fin d₁ → O := fun m => PowerSeries.coeff J (Φ m) with hCc
  set coef : Fin I → O := fun i => if Nn i ≤ w' + S then PowerSeries.coeff J (X ^ (w + S - Nn i + Pn i) * Ψ i) else 0
    with hcoef
  have hlC : ∀ m, ((PD.p : ℕ) : O) ^ κ * Cc m = ∑ i, coef i * c₀ i m := by
    intro m
    have := congrArg (PowerSeries.coeff J) (hstar m)
    rw [PowerSeries.coeff_C_mul, map_sum] at this
    show _ * PowerSeries.coeff J (Φ m) = _
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hTm, hcoef]
    split_ifs <;> simp [PowerSeries.coeff_mul_C]
  have hp0 : algebraMap O LL (((PD.p : ℕ) : O) ^ κ) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O LL)]
    exact fun h => pow_ne_zero κ hl0 (hinj h)
  have hCfil : dvO W T₁ 1 b₁ Cc ∈ FilS W T₁ a 0 ((A.η : ℤ) + 1) := by
    have h1 : dvO W T₁ 1 b₁ (fun m => ((PD.p : ℕ) : O) ^ κ * Cc m) ∈ FilS W T₁ a 0 ((A.η : ℤ) + 1) := by
      rw [show (fun m => ((PD.p : ℕ) : O) ^ κ * Cc m) = fun m => ∑ i ∈ Finset.univ, coef i * c₀ i m from
        funext hlC, dvO_lin]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hz : coef i = 0
      · rw [hz, map_zero, zero_smul]; exact zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have hgood : Nn i ≤ w' + S := by
          by_contra h
          exact hz (by simp [hcoef, h])
        have hE : w + S - Nn i + Pn i ≤ J := by
          by_contra h
          apply hz
          simp only [hcoef, if_pos hgood]
          rw [PowerSeries.coeff_X_pow_mul', if_neg h]
        have hN' : Nn i = (-(α i 0)).toNat := rfl
        have hP' : Pn i = (α i 0).toNat := rfl
        have hα : (A.η : ℤ) + 1 ≤ -(α i 0) := by
          rw [hAη]
          omega
        exact filS_anti W T₁ a 0 hα ((hgi i).2 0 (by norm_num))
    rw [dvO_smul] at h1
    have := Submodule.smul_mem _ (algebraMap O LL (((PD.p : ℕ) : O) ^ κ))⁻¹ h1
    rwa [inv_smul_smul₀ hp0] at this
  have hCw : dvO W T₁ 1 b₁ Cc ∈ FilS W T₁ a 0 w' :=
    (hFL hcase hl5 A hOKc c hc 1 (by rw [hj]) (by omega) T₁ hW₁ d₁ b₁ sol₁ hb₁ Cc 0 (by norm_num)).2 w'
      htya hCfil

  have hAAw : AA < w' := by omega
  have hJlt : J < 2 * (w + S) := by omega
  have hJsub : J - (w + S - w') = AA := by omega
  set R₀ : PowerSeries O := C (((W.DelF.card : ℕ) : O) * ((PD.p : ℕ) : O) ^ (2 * σ)) *
    (X - C ((PD.p : ℕ) : O)) ^ AA * X ^ (w + S - w') with hR₀def
  have hR₀E : algebraMap (LetA O n) W.EE (qA W ^ (w + S)) * (algebraMap (LetA O n) W.EE aa * (lE W σ * g₂)) =
      EL Br a R₀ := by
    have hcR : Br.cst R₀ = ((W.DelF.card : ℕ) : LetA O n) * lA W ^ (2 * σ) * W.π₀ ^ AA * qA W ^ (w + S - w') := by
      rw [hR₀def, cst_mul', cst_mul', cst_C', hπcst, hqcst, map_mul, map_pow, map_natCast, map_natCast]
      rfl
    have e : w + S = (w + S - w') + w' := by omega
    rw [EL, hcR, haadef, hg₂, e, pow_add, Nat.add_sub_cancel]
    simp only [map_mul, map_pow, map_natCast, lE, lA]
    linear_combination (algebraMap (LetA O n) W.EE (letE a) * ((W.DelF.card : ℕ) : W.EE) *
      ((PD.p : ℕ) : W.EE) ^ (2 * σ) * algebraMap (LetA O n) W.EE W.π₀ ^ AA *
      algebraMap (LetA O n) W.EE (qA W) ^ (w + S - w')) * hqq
  have hsumμ : ∀ k, ∑ m, Cc m * μ m k = if k = k₀ then ((W.DelF.card : ℕ) : O) * ((PD.p : ℕ) : O) ^ (2 * σ) else 0 := by
    intro k
    obtain ⟨u, hu, hue⟩ := hKk k
    obtain ⟨Uu, hUu⟩ := EL_of_mem Br a hu
    set δk : PowerSeries O := if k = k₀ then R₀ else 0 with hδk
    have hδE : algebraMap (LetA O n) W.EE (qA W ^ (w + S)) * (algebraMap (LetA O n) W.EE aa * (lE W σ * f₂ k)) =
        EL Br a δk := by
      by_cases hk : k = k₀
      · simp only [hf₂, hδk, if_pos hk]; exact hR₀E
      · simp [hf₂, hδk, if_neg hk, EL_zero]
    have hser : C (((PD.p : ℕ) : O) ^ K) * ((∑ m, Φ m * C (μ m k)) - δk) =
        X ^ (2 * (w + S)) * ((X - C ((PD.p : ℕ) : O)) * Uu) := by
      apply EL_inj Br a
      have h1 := congrArg (fun t => algebraMap (LetA O n) W.EE (qA W ^ (w + S)) * t) hue
      have hL : algebraMap (LetA O n) W.EE (qA W ^ (w + S)) *
          (algebraMap (LetA O n) W.EE (letE a) *
            (lE W K * ((∑ m, f₁ m * algebraMap O W.EE (μ m k)) - algebraMap (LetA O n) W.EE aa * (lE W σ * f₂ k)))) =
          EL Br a (C (((PD.p : ℕ) : O) ^ K) * ((∑ m, Φ m * C (μ m k)) - δk)) := by
        have hs : algebraMap (LetA O n) W.EE (qA W ^ (w + S)) * (∑ m, f₁ m * algebraMap O W.EE (μ m k)) =
            EL Br a (∑ m, Φ m * C (μ m k)) := by
          rw [Finset.mul_sum, EL_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← mul_assoc, hΦe m, mul_comm, EL_C]
          congr 1
          ring
        have hsub : EL Br a ((∑ m, Φ m * C (μ m k)) - δk) =
            EL Br a (∑ m, Φ m * C (μ m k)) - EL Br a δk := by
          have := EL_add Br a ((∑ m, Φ m * C (μ m k)) - δk) δk
          rw [sub_add_cancel] at this
          rw [this, add_sub_cancel_right]
        rw [← EL_lE, ← EL_letE Br a, hsub, ← hs, ← hδE]
        ring
      have hR : algebraMap (LetA O n) W.EE (qA W ^ (w + S)) *
          algebraMap (LetA O n) W.EE (letE a * (W.π₀ * abelian₂ W A a 1) * u) =
          EL Br a (X ^ (2 * (w + S)) * ((X - C ((PD.p : ℕ) : O)) * Uu)) := by
        have hc2 : Br.cst (X ^ (2 * (w + S)) * (X - C ((PD.p : ℕ) : O))) = qA W ^ (w + S) * (W.π₀ * abelian₂ W A a 1) := by
          rw [cst_mul', hqcst, Br.π₀_eq, hΛ]
          ring
        have e : algebraMap (LetA O n) W.EE (letE a * (W.π₀ * abelian₂ W A a 1) * u) =
            algebraMap (LetA O n) W.EE (W.π₀ * abelian₂ W A a 1) * algebraMap (LetA O n) W.EE (letE a * u) := by
          rw [← map_mul]; ring_nf
        rw [e, hUu, ← mul_assoc, ← map_mul, EL_mulA Br a _ _ _ hc2, mul_assoc]
      exact hL.symm.trans (h1.trans hR)
    have hco := congrArg (PowerSeries.coeff J) hser
    rw [PowerSeries.coeff_C_mul, map_sub, map_sum, PowerSeries.coeff_X_pow_mul', if_neg (by omega)] at hco
    have hδc : PowerSeries.coeff J δk = if k = k₀ then ((W.DelF.card : ℕ) : O) * ((PD.p : ℕ) : O) ^ (2 * σ) else 0 := by
      by_cases hk : k = k₀
      · simp only [hδk, if_pos hk, hR₀def]
        rw [PowerSeries.coeff_mul_X_pow', if_pos (by omega), hJsub, PowerSeries.coeff_C_mul,
          coeff_X_sub_C_pow_self, mul_one]
      · simp [hδk, if_neg hk]
    rw [hδc] at hco
    have hco' : ∑ m, PowerSeries.coeff J (Φ m * C (μ m k)) = ∑ m, Cc m * μ m k :=
      Finset.sum_congr rfl fun m _ => by rw [PowerSeries.coeff_mul_C]
    rw [hco'] at hco
    have := (mul_eq_zero.mp hco).resolve_left (pow_ne_zero K hl0)
    exact sub_eq_zero.mp this

  set u₀ : Oˣ := hΔu.unit with hu₀
  refine ⟨d₁, b₁, sol₁, hb₁, fun m => ((u₀⁻¹ : Oˣ) : O) * Cc m, ?_, ?_⟩
  · rw [hlen, hdvO2, dvO_smul]
    exact filS_φ W T₁ hca (Submodule.smul_mem _ _ hCw)
  · have hf : (fun k => ∑ m, ((u₀⁻¹ : Oˣ) : O) * Cc m * μ m k) =
        fun k => ((PD.p : ℕ) : O) ^ (2 * σ) * (Pi.single k₀ (1 : O) : Fin d → O) k := by
      funext k
      have e1 : ∑ m, ((u₀⁻¹ : Oˣ) : O) * Cc m * μ m k = ((u₀⁻¹ : Oˣ) : O) * ∑ m, Cc m * μ m k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
      rw [e1, hsumμ k]
      have hu : ((u₀⁻¹ : Oˣ) : O) * ((W.DelF.card : ℕ) : O) = 1 := by
        have := hΔu.unit.inv_mul
        rw [hΔu.unit_spec] at this
        rw [hu₀]
        exact this
      by_cases hk : k = k₀
      · rw [if_pos hk, hk, Pi.single_eq_same, ← mul_assoc, hu, one_mul, mul_one]
      · rw [if_neg hk, Pi.single_eq_of_ne hk, mul_zero, mul_zero]
    have h1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ 1 b₁ fun m => ((u₀⁻¹ : Oˣ) : O) * Cc m) =
        ((PD.p : LL) ^ (2 * σ)) • dv W T₂ 1 bb (Pi.single k₀ 1) := by
      rw [crisMap_coords W F 1 b₁ bb μ hμ, hf, dvO_smul, dvO_single, map_pow, map_natCast]
    rw [hlen, hdvO2, crisMap_φ, h1, map_smul, ← hdv2]

end ArcLengthTwo

end Formalism.MainNotions.N.FrobeniusPowerSeries
