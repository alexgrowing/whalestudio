import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PhiSqPi0PowEqPi0LambdaSq
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FilVSep
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoeffRelation

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

theorem arc_length_one_or_two_case_b [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = true) (h1b : PD.p * (size (c - 1) + S + η) + η < size c) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 12 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  set A := arcOf b w S η up size with hA
  have hl5 : 5 ≤ PD.p := by have := hB.1; omega
  set L := A.len c with hL
  have hcc : c - ((L : ℕ) : ZMod n) + ((L : ℕ) : ZMod n) = c := sub_add_cancel _ _
  set b₀ := size c with hb₀
  set w' := size (c - 1) with hw'
  have hdn : up (c - 1) = false := by
    cases h : up (c - 1)
    · rfl
    · exact absurd (h.trans hup.symm) hdiff
  have hty0 : A.ty (c - ((0 : ℕ) : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up b₀ := by simp [hA, arcOf, hup, hb₀]
  have hty1 : A.ty (c - ((1 : ℕ) : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down w' := by simp [hA, arcOf, hdn, hw']
  have htyc : A.ty c = Formalism.MainNotions.LocalTheoryWindows.LT.up b₀ := by simpa using hty0
  have hAS : A.S = S := rfl
  have hAη : A.η = η := rfl
  have hAG : A.G₀ = w + S := rfl
  have hAj : A.j = 1 := rfl
  have hη0 : η < b₀ := by
    have := hOK.2.2.2.2.1 c
    rw [htyc] at this
    exact this
  have hh : b₀ + S ≤ A.h := by
    have := hOK.2.2.2.2.2.2.2.1 c
    rw [htyc] at this
    exact this rfl
  set y := w' + S + η with hy
  set k₀' := S + PD.p * y with hk₀'
  have hk₀b : k₀' + η + 1 ≤ b₀ + S := by omega
  have hk₀h : k₀' < A.h := by omega
  have hj : A.j ≤ L := by rw [hlen, hAj]; norm_num
  have hT₁ := hW₁.1
  have hT₂ := hW₂.1

  obtain ⟨d₁, b₁, sol₁, hb₁⟩ := hHF hcase hl5 A hOK T₁ hW₁ (c - ((L : ℕ) : ZMod n))
  have hAC := hArc hcase hl5 A hOK c hc L hj le_rfl
  dsimp only at hAC
  rw [hcc] at hAC
  obtain ⟨hJJ, hACT⟩ := hAC
  obtain ⟨-, hNP₁, -, hfr₁⟩ := hACT T₁ hW₁
  obtain ⟨hlin₁, -, -, hNcoord₁, -, -, -⟩ := hfr₁ d₁ b₁ sol₁ hb₁
  obtain ⟨-, -, -, hfr₂⟩ := hACT T₂ hW₂
  obtain ⟨-, -, -, -, hNLx₂, -, -⟩ := hfr₂ d bb sol hbb
  obtain ⟨-, μ, hμ, hμR⟩ := hSec hcase hl5 A hOK c hc L hj le_rfl T₁ T₂ F hW₁ hW₂ d₁ b₁ sol₁ hb₁ d bb sol hbb
  rw [hcc] at hμR
  set Λ := abelian₂ W A c L with hΛdef
  have hpsu : ∀ s, IsUnit (algebraMap (LetA O n) W.EE (ps W s)) := ArcLengthTwoLifting.isUnit_ps W hcase hP9 T₁ hT₁
  have hHs0 : A.Hs c 2 0 = A.h := by
    unfold ArcP.Hs
    rw [if_neg]
    rintro (h | h)
    · rw [hty0] at h; exact Formalism.MainNotions.LocalTheoryWindows.LT.noConfusion h
    · rw [hAj] at h; omega
  have hHs1 : A.Hs c 2 1 = A.G₀ := by
    unfold ArcP.Hs
    rw [if_pos]
    right; rw [hAj]
  have hΛ_eq : Λ = ps W 0 ^ A.h * ps W 1 ^ (w + S) := by
    rw [hΛdef, abelian₂, hlen, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
      hHs0, hHs1, hAG]
  have hΛA : Λ ∈ W.AΔ := by
    rw [hΛ_eq]
    exact W.AΔ.mul_mem (W.AΔ.pow_mem (TypesA.ps_mem W 0) _) (W.AΔ.pow_mem (TypesA.ps_mem W 1) _)
  have hΛu : IsUnit (algebraMap (LetA O n) W.EE Λ) := by
    rw [hΛ_eq, map_mul, map_pow, map_pow]
    exact ((hpsu 0).pow _).mul ((hpsu 1).pow _)
  have hπu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := (lemG_units W hcase hP9 hT₁ hO hOv hinj).1

  have hnnNum : nnNum W A c = ps W 1 ^ (w' + S) := by
    simp only [nnNum, prodTy]
    rw [show A.len c = 2 from hlen, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, hty0, hty1]
    simp [hAS]
  have hnnDen : nnDen W A c = ps W 0 ^ b₀ := by
    simp only [nnDen, prodTy]
    rw [show A.len c = 2 from hlen, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, hty0, hty1]
    simp
  have hD : IsUnit (algebraMap (LetA O n) W.EE (nnDen W A c)) := by
    rw [hnnDen, map_pow]; exact (hpsu 0).pow _
  set g₂ : W.EE := ↑(hD.unit⁻¹) * algebraMap (LetA O n) W.EE (letE c * nnNum W A c) with hg₂
  have hg₂F : InFr W c (nnNum W A c) (nnDen W A c) g₂ :=
    ⟨1, W.AΔ.one_mem, by rw [hg₂, ← mul_assoc, IsUnit.mul_val_inv, one_mul, mul_one]⟩
  have hc₀ : ∀ s < L, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₂ L bb (Pi.single k₀ 1) ∈ FilS W T₂ c s bs := by
    intro s hs bs hbs
    rw [hlen] at hs
    interval_cases s
    · rw [hty0] at hbs
      obtain rfl := Formalism.MainNotions.LocalTheoryWindows.LT.up.inj hbs
      rw [ArcLengthTwoLifting.dvO_single]
      exact hk₀ 0 (by omega) b₀ hty0
    · rw [hty1] at hbs
      exact Formalism.MainNotions.LocalTheoryWindows.LT.noConfusion hbs
  have hNL₂ := hNN hcase hl5 A hOK c hc T₂ hW₂ d bb sol hbb (Pi.single k₀ 1) hc₀ g₂ hg₂F
  obtain ⟨n₂, hn₂N, hn₂R⟩ := hNLx₂ _ hNL₂

  obtain ⟨n₁, hn₁N, hn₁F⟩ := ArcLengthTwoLifting.liftΔ W hcase hP9 hO hOv hinj hT₁ F c rr (hkill c hc) n₂ hn₂N
  obtain ⟨f₁, hf₁NL, hf₁R⟩ := hNcoord₁ n₁ hn₁N
  have hPn₁ : InFP W T₁ (c - ((L : ℕ) : ZMod n)) L 1 (Λ • (lA W ^ A.σ PD.p • n₁)) := by
    rw [smul_comm]
    exact TypesA.inMultiple_smul W (TypesA.lA_pow_mem W _) (hNP₁ n₁ hn₁N)
  have R1 := hμR _ f₁ hPn₁ hf₁NL.1 hf₁R
  rw [TypesA.map_smulA, hn₁F] at R1
  have R2 := TypesA.RepVV_nat W (PD.p ^ (A.σ PD.p + rr)) hn₂R
  have Rd := TypesA.RepVV_congr W (TypesA.RepVV_add W R1 (TypesA.RepVV_neg W R2)) (x' := 0)
    (by rw [smul_smul, ← pow_add, lA, ← Nat.cast_pow, add_neg_cancel]) (fun k => rfl)
  have hM : 1 ≤ A.M PD.p := by simp [ArcP.M]
  have hN : ∃ N : ℕ, ∃ w ∈ W.AΔ, ((W.φA ^ L) W.π₀) ^ N = W.π₀ * Λ ^ 2 * w := by
    obtain ⟨u, hu, hu'⟩ := hJJ
    have hLj : L - A.j = 1 := by rw [hlen, hAj]
    rw [hLj, pow_one, hAj] at hu'
    rw [hlen]
    exact ArcLengthTwoLifting.phi_sq_pi0_pow_eq_pi0_lambda_sq W (GS.ringData_of_caseA_of_p9 W hcase hP9) Λ hΛA
      (by rw [map_mul, map_pow]; exact hπu.mul (hΛu.pow 2)) _ _ u hu hu'
  obtain ⟨K, hK⟩ := repVV_zero_coord W hcase hP9 hinj T₂ hT₂ (c - ((L : ℕ) : ZMod n)) L (A.M PD.p) hM Λ hΛA hΛu
    hN bb sol hbb _ Rd
  rw [hcc] at hK

  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hT₁ hO hinj
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  set Φ : LetA O n := ps W 1 ^ η * ps W 0 ^ (b₀ + S) with hΦ
  have hpsPi : ∀ s, ps W s ∈ PiPs W := fun s => Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨s, rfl⟩)
  have hΦPi : Φ ∈ PiPs W :=
    (PiPs W).mul_mem ((PiPs W).pow_mem (hpsPi 1) _) ((PiPs W).pow_mem (hpsPi 0) _)
  have hΛPi : Λ ∈ PiPs W := by
    rw [hΛ_eq]; exact (PiPs W).mul_mem ((PiPs W).pow_mem (hpsPi 0) _) ((PiPs W).pow_mem (hpsPi 1) _)
  have hletc : (letE c : LetA O n) ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c

  obtain ⟨κ, I, gi, c₀, α, hgi, hsum⟩ := hf₁NL.2
  have hdvO0 : ∀ c' : Fin d₁ → O, dvO W T₁ L b₁ c' = 0 → c' = 0 := by
    intro c' h
    have h2 : ∑ m, algebraMap O LL (c' m) • dv W T₁ L b₁ (Pi.single m 1) = 0 := by
      rw [← ArcLengthTwoLifting.dv_eq_sum_single]; exact h
    have := Fintype.linearIndependent_iff.1 hlin₁.1 _ h2
    funext m; exact hinj (by rw [this m]; simp)
  have hL0 : 0 < L := by rw [hlen]; norm_num
  have hL1 : 1 < L := by rw [hlen]; norm_num
  have htop : ∀ i, c₀ i ≠ 0 → -(α i 0) ≤ ((b₀ + S : ℕ) : ℤ) ∧ -(α i 1) ≤ (η : ℤ) := by
    intro i hi
    have hc := (hgi i).2
    constructor
    · by_contra hlt
      push_neg at hlt
      have hm := hc 0 hL0
      rw [filS_top W hcase A T₁ hW₁ c 0 _ ?_, Submodule.mem_bot] at hm
      · exact hi (hdvO0 _ hm)
      · intro x hx
        rw [hty0] at hx
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, hAS, hAη, Set.mem_union, Set.mem_Icc] at hx
        push_cast at hlt
        omega
    · by_contra hlt
      push_neg at hlt
      have hm := hc 1 hL1
      rw [filS_top W hcase A T₁ hW₁ c 1 _ ?_, Submodule.mem_bot] at hm
      · exact hi (hdvO0 _ hm)
      · intro x hx
        rw [hty1] at hx
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, hAS, hAη, Set.mem_union, Set.mem_Icc] at hx
        omega
  have hprod : ∀ t : ℕ → ℕ, ∏ s ∈ Finset.range L, ps W s ^ t s = ps W 0 ^ t 0 * ps W 1 ^ t 1 := by
    intro t
    rw [hlen, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  choose vv hvvΔ hvvE using fun i => (hgi i).1

  set t : Fin I → LetA O n := fun i => if c₀ i = 0 then 0 else
    letE c * (ps W 0 ^ (α i 0).toNat * ps W 1 ^ (α i 1).toNat) * vv i *
      ps W 1 ^ (η - (-(α i 1)).toNat) * ps W 0 ^ (b₀ + S - (-(α i 0)).toNat) with ht
  have htΔ : ∀ i, t i ∈ W.AΔ := by
    intro i
    simp only [ht]
    split_ifs
    · exact W.AΔ.zero_mem
    · refine W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hletc ?_) (hvvΔ i)) ?_) ?_
      · exact W.AΔ.mul_mem (W.AΔ.pow_mem (TypesA.ps_mem W 0) _) (W.AΔ.pow_mem (TypesA.ps_mem W 1) _)
      · exact W.AΔ.pow_mem (TypesA.ps_mem W 1) _
      · exact W.AΔ.pow_mem (TypesA.ps_mem W 0) _
  have htg : ∀ i k, algebraMap (LetA O n) W.EE Φ * (gi i * algebraMap O W.EE (c₀ i k)) =
      algebraMap (LetA O n) W.EE (t i * algebraMap O (LetA O n) (c₀ i k)) := by
    intro i k
    by_cases hci : c₀ i = 0
    · simp [ht, hci]
    · have hd := htop i hci
      have hd0 : (-(α i 0)).toNat ≤ b₀ + S := by have := Int.toNat_eq_max (-(α i 0)); push_cast at hd; omega
      have hd1 : (-(α i 1)).toNat ≤ η := by have := Int.toNat_eq_max (-(α i 1)); omega
      have hE := hvvE i
      rw [hprod, hprod] at hE
      have hΦs : Φ = ps W 1 ^ (η - (-(α i 1)).toNat) * ps W 0 ^ (b₀ + S - (-(α i 0)).toNat) *
          (ps W 0 ^ (-(α i 0)).toNat * ps W 1 ^ (-(α i 1)).toNat) := by
        rw [hΦ]
        conv_lhs => rw [← Nat.sub_add_cancel hd1, ← Nat.sub_add_cancel hd0]
        ring
      simp only [ht, if_neg hci]
      rw [hΦs, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      have hE' := hE
      simp only [map_mul] at hE'
      simp only [map_mul]
      linear_combination (algebraMap (LetA O n) W.EE (ps W 1 ^ (η - (-(α i 1)).toNat)) *
        algebraMap (LetA O n) W.EE (ps W 0 ^ (b₀ + S - (-(α i 0)).toNat)) *
        algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) (c₀ i k))) * hE'
  set Y : Fin d₁ → LetA O n := fun m => ∑ i, t i * algebraMap O (LetA O n) (c₀ i m) with hYdef
  have hYΔ : ∀ m, Y m ∈ W.AΔ := fun m =>
    W.AΔ.sum_mem fun i _ => W.AΔ.mul_mem (htΔ i) (W.AΔ.algebraMap_mem _)
  have hY : ∀ m, algebraMap (LetA O n) W.EE (Y m) = algebraMap (LetA O n) W.EE Φ * (lE W κ * f₁ m) := by
    intro m
    rw [show lE W κ * f₁ m = ∑ i, gi i * algebraMap O W.EE (c₀ i m) from hsum m, Finset.mul_sum, hYdef, map_sum]
    exact Finset.sum_congr rfl fun i _ => (htg i m).symm

  choose uu huuΔ huuE using hf₁NL.1
  have hG : ∀ m, ∃ yy ∈ W.AΔ, algebraMap (LetA O n) W.EE Φ * f₁ m = algebraMap (LetA O n) W.EE yy ∧
      lA W ^ κ * yy = Y m := by
    intro m
    have hx : (1 : LetA O n) * (letE c * 1 * uu m) ∈ W.AΔ := by
      rw [one_mul]; exact W.AΔ.mul_mem (W.AΔ.mul_mem hletc W.AΔ.one_mem) (huuΔ m)
    obtain ⟨yy, hyy, hyyE⟩ := saturation_fraction_ring (W := W) hcase hP9 hinj Λ Φ 1 hΛPi hΦPi (PiPs W).one_mem _ hx
      ⟨κ, Y m, hYΔ m, by
        apply W.EE_inj
        have h1 := huuE m
        have h2 := hY m
        simp only [map_mul, map_pow, lA, lE, map_natCast, map_one, mul_one] at h1 h2 ⊢
        linear_combination (-(((PD.p : ℕ) : W.EE) ^ κ * algebraMap (LetA O n) W.EE Φ)) * h1 -
          algebraMap (LetA O n) W.EE Λ * h2⟩
    have h1 : algebraMap (LetA O n) W.EE Φ * f₁ m = algebraMap (LetA O n) W.EE yy := by
      apply hΛu.mul_left_cancel
      have e := congrArg (algebraMap (LetA O n) W.EE) hyyE
      have h1 := huuE m
      simp only [map_mul, map_one, mul_one] at e h1 ⊢
      linear_combination (algebraMap (LetA O n) W.EE Φ) * h1 + e
    refine ⟨yy, hyy, h1, W.EE_inj ?_⟩
    have h2 := hY m
    simp only [map_mul, map_pow, lA, lE, map_natCast] at h2 ⊢
    rw [h2]
    linear_combination (-(((PD.p : ℕ) : W.EE) ^ κ)) * h1
  choose Gy hGyΔ hGyE hGyY using hG

  have hpsc : ∀ s, ps W s c = Br.ι (Br.P.p s) := fun s => by rw [Br.ps_eq]; rfl
  have hπc : W.π₀ c = Br.ι (PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) := by rw [Br.π₀_eq]; rfl
  have hP0 : Br.P.p 0 = PowerSeries.X := rfl
  have hletcc : (letE c : LetA O n) c = 1 := by simp [letE]
  have hCa : ∀ x : O, algebraMap O (PowerSeries O) x = PowerSeries.C x := fun x => by
    rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hιC : ∀ x : O, Br.ι (PowerSeries.C x) = PowerSeries.C x := fun x => by
    rw [← hCa, AlgHom.commutes]
  choose Fq hFq using fun m => Br.range (Gy m) (hGyΔ m) c
  choose Tt hTt using fun i => Br.range (t i) (htΔ i) c
  choose Vv hVv using fun i => Br.range (vv i) (hvvΔ i) c
  have hFeq : ∀ m, PowerSeries.C (((PD.p : ℕ) : O) ^ κ) * Fq m =
      ∑ i, Tt i * PowerSeries.C (c₀ i m) := by
    intro m
    apply Br.inj
    have h := congrFun (hGyY m) c
    simp only [hYdef, lA, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Pi.algebraMap_apply,
      hFq, hTt, hCa] at h
    simp only [map_mul, map_sum, map_pow, hιC, map_natCast]
    rw [← h]
  have hTshape : ∀ i, c₀ i ≠ 0 → Tt i = PowerSeries.X ^ ((α i 0).toNat + (b₀ + S - (-(α i 0)).toNat)) *
      (Br.P.p 1 ^ ((α i 1).toNat + (η - (-(α i 1)).toNat)) * Vv i) := by
    intro i hci
    apply Br.inj
    rw [← hTt i]
    simp only [ht, if_neg hci, Pi.mul_apply, Pi.pow_apply, hletcc, hpsc, hVv, hP0, one_mul, map_mul, map_pow]
    ring
  have hT0 : ∀ i, c₀ i = 0 → Tt i = 0 := by
    intro i hci
    apply Br.inj
    rw [← hTt i, map_zero]
    simp [ht, hci]
  have hcoefF : ∀ m, ((PD.p : ℕ) : O) ^ κ * PowerSeries.coeff k₀' (Fq m) =
      ∑ i, PowerSeries.coeff k₀' (Tt i) * c₀ i m := by
    intro m
    have := congrArg (PowerSeries.coeff k₀') (hFeq m)
    simpa only [PowerSeries.coeff_C_mul, map_sum, PowerSeries.coeff_mul_C] using this
  have hFil : ∀ i, PowerSeries.coeff k₀' (Tt i) ≠ 0 →
      dvO W T₁ L b₁ (c₀ i) ∈ FilS W T₁ c 0 ((η : ℤ) + 1) := by
    intro i hne
    have hci : c₀ i ≠ 0 := fun h => hne (by rw [hT0 i h, map_zero])
    have htp := htop i hci
    rw [hTshape i hci, PowerSeries.coeff_X_pow_mul'] at hne
    split_ifs at hne with hle
    · have h1 := Int.toNat_eq_max (α i 0)
      have h2 := Int.toNat_eq_max (-(α i 0))
      have hα0 : (η : ℤ) + 1 ≤ -(α i 0) := by omega
      exact ArcLengthTwoLifting.filS_anti W T₁ c 0 hα0 ((hgi i).2 0 hL0)
    · exact absurd rfl hne

  set th : O := PowerSeries.coeff (PD.p * y) (Br.P.p 1 ^ y) with hth
  have hthu : IsUnit th := ArcLengthTwoLifting.coeff_p1_pow_top_isUnit Br.P y
  set c₁ : Fin d₁ → O := fun m => ↑(hthu.unit⁻¹) * PowerSeries.coeff k₀' (Fq m) with hc₁
  have hpLL : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have := W.v_l
    rw [h0, AddValuation.map_zero] at this
    exact absurd this (by simp)
  have hvecFil : dvO W T₁ L b₁ c₁ ∈ FilS W T₁ c 0 ((η : ℤ) + 1) := by
    set a : O := ((PD.p : ℕ) : O) ^ κ * th with ha
    have hsc : dvO W T₁ L b₁ (fun m => a * c₁ m) = algebraMap O LL a • dvO W T₁ L b₁ c₁ := by
      unfold dvO
      simp only [map_mul]
      exact ArcLengthTwoLifting.dv_smul W T₁ L b₁ _ _
    have hfun : (fun m => a * c₁ m) = fun m => ∑ i, PowerSeries.coeff k₀' (Tt i) * c₀ i m := by
      funext m
      rw [← hcoefF m, hc₁, ha]
      have := hthu.mul_val_inv
      linear_combination (((PD.p : ℕ) : O) ^ κ * PowerSeries.coeff k₀' (Fq m)) * this
    have hsum' : dvO W T₁ L b₁ (fun m => a * c₁ m) ∈ FilS W T₁ c 0 ((η : ℤ) + 1) := by
      rw [hfun]
      unfold dvO
      simp only [map_sum, map_mul]
      rw [ArcLengthTwoLifting.dv_sum W T₁ L b₁ Finset.univ (fun i => algebraMap O LL (PowerSeries.coeff k₀' (Tt i)))
        (fun i m => algebraMap O LL (c₀ i m))]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hz : PowerSeries.coeff k₀' (Tt i) = 0
      · rw [hz, map_zero, zero_smul]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (hFil i hz)
    have hne : algebraMap O LL a ≠ 0 := by
      rw [ha, map_mul, map_pow, map_natCast]
      exact mul_ne_zero (pow_ne_zero _ hpLL) (hthu.map _).ne_zero
    have := Submodule.smul_mem _ (algebraMap O LL a)⁻¹ hsum'
    rwa [hsc, inv_smul_smul₀ hne] at this
  have hgapC := (hFL hcase hl5 A hOK c hc L hj le_rfl T₁ hW₁ d₁ b₁ sol₁ hb₁ c₁ 0 hL0).2
  rw [hcc] at hgapC
  have hlt0 : dvO W T₁ L b₁ c₁ ∈ FilS W T₁ c 0 b₀ := hgapC b₀ hty0 hvecFil

  set Qc : LetA O n := letE c * ps W 0 ^ S * ps W 1 ^ y with hQc
  have hDinv : algebraMap (LetA O n) W.EE (ps W 0 ^ b₀) * ↑(hD.unit⁻¹) = 1 := by
    have e : algebraMap (LetA O n) W.EE (nnDen W A c) = algebraMap (LetA O n) W.EE (ps W 0 ^ b₀) := by
      rw [hnnDen]
    rw [← e]
    exact hD.mul_val_inv
  have hΦg₂ : algebraMap (LetA O n) W.EE Φ * g₂ = algebraMap (LetA O n) W.EE Qc := by
    rw [hg₂, hnnNum, hΦ, hQc, hy]
    simp only [map_mul, map_pow, pow_add] at hDinv ⊢
    linear_combination (algebraMap (LetA O n) W.EE (ps W 1) ^ η * algebraMap (LetA O n) W.EE (ps W 0) ^ S *
      algebraMap (LetA O n) W.EE (letE c) * (algebraMap (LetA O n) W.EE (ps W 1) ^ w' *
        algebraMap (LetA O n) W.EE (ps W 1) ^ S)) * hDinv
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := Br.P.hl0
  have hrel : ∀ j : Fin d, ∃ R : PowerSeries O, PowerSeries.C ((PD.p : ℕ) : O) ^ K *
      (∑ m, Fq m * PowerSeries.C (μ m j) - (if j = k₀ then PowerSeries.C ((PD.p : ℕ) : O) ^
        (A.σ PD.p + rr + A.σ PD.p) * PowerSeries.X ^ S * Br.P.p 1 ^ y else 0)) = PowerSeries.X ^ A.h * R := by
    intro j
    obtain ⟨uk, hukΔ, hukE⟩ := hK j
    obtain ⟨Uk, hUk⟩ := Br.range uk hukΔ c
    refine ⟨(PowerSeries.X - PowerSeries.C ((PD.p : ℕ) : O)) * Br.P.p 1 ^ (w + S) * Uk *
      (Br.P.p 1 ^ η * PowerSeries.X ^ (b₀ + S)), ?_⟩
    set Z : LetA O n := ∑ m, Gy m * algebraMap O (LetA O n) (μ m j) +
      -(((PD.p ^ (A.σ PD.p + rr) : ℕ) : LetA O n) * lA W ^ A.σ PD.p * Qc *
        algebraMap O (LetA O n) ((Pi.single k₀ (1 : O) : Fin d → O) j)) with hZ
    have e2 : algebraMap (LetA O n) W.EE Φ * (∑ m, f₁ m * algebraMap O W.EE (μ m j) +
        -(((PD.p ^ (A.σ PD.p + rr) : ℕ) : W.EE) * (lE W (A.σ PD.p) * (g₂ * algebraMap O W.EE ((Pi.single k₀ (1 : O) : Fin d → O) j))))) =
        algebraMap (LetA O n) W.EE Z := by
      rw [hZ, map_add, map_neg, map_sum, mul_add, Finset.mul_sum, mul_neg]
      congr 1
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [← mul_assoc, hGyE m, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      · congr 1
        have h := hΦg₂
        simp only [map_mul, map_pow, lE, lA, map_natCast, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
        linear_combination (((PD.p ^ (A.σ PD.p + rr) : ℕ) : W.EE) * ((PD.p : ℕ) : W.EE) ^ A.σ PD.p *
          algebraMap O W.EE ((Pi.single k₀ (1 : O) : Fin d → O) j)) * h
    have e3 : letE c * (lA W ^ K * Z) = letE c * (W.π₀ * Λ) * uk * Φ := by
      apply W.EE_inj
      have h := hukE
      have e2' := e2
      simp only [lA, lE, map_natCast, map_mul, map_pow] at h e2' ⊢
      linear_combination (-(algebraMap (LetA O n) W.EE (letE c) * ((PD.p : ℕ) : W.EE) ^ K)) * e2' +
        (algebraMap (LetA O n) W.EE Φ) * h
    rw [hΛ_eq, hZ, hΦ, hQc] at e3
    have e4 := congrFun e3 c
    simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, Finset.sum_apply, Pi.natCast_apply,
      Pi.algebraMap_apply, hletcc, one_mul, hFq, hUk, hpsc, hπc, hP0, lA, hCa, map_sub, map_mul, map_pow, hιC,
      map_natCast, Nat.cast_pow] at e4
    apply Br.inj
    simp only [map_mul, map_sub, map_sum, map_pow, hιC, map_natCast, Nat.cast_pow]
    by_cases hjk : j = k₀
    · subst hjk
      simp only [if_pos rfl, if_true, ite_true, Pi.single_eq_same, map_one, mul_one, map_mul, map_pow, hιC,
        map_natCast, Nat.cast_pow] at e4 ⊢
      linear_combination e4
    · simp only [if_neg hjk, Pi.single_eq_of_ne hjk, map_zero, mul_zero, neg_zero, add_zero, sub_zero, if_false,
        ite_false] at e4 ⊢
      linear_combination e4
  have hcr := ArcLengthTwo.coeff_relation ((PD.p : ℕ) : O) hp0 Fq μ k₀ K (A.σ PD.p + rr + A.σ PD.p) S A.h k₀'
    (Br.P.p 1 ^ y) hk₀h (by omega) hrel
  have hkS : k₀' - S = PD.p * y := by omega
  have hSc₁ := ArcLengthTwoLifting.sum_unit_inv th hthu (fun m => PowerSeries.coeff k₀' (Fq m)) μ k₀
    (((PD.p : ℕ) : O) ^ (A.σ PD.p + rr + A.σ PD.p)) (by intro j; rw [hcr j, hkS, ← hth])
  have hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ L b₁ c₁) =
      ((PD.p : LL) ^ (A.σ PD.p + rr + A.σ PD.p)) • dv W T₂ L bb (Pi.single k₀ 1) := by
    rw [ArcLengthTwoLifting.crisMap_dvO W F L b₁ bb μ hμ c₁ k₀ _ hSc₁, map_pow, map_natCast]

  have hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick := by
    intro s _
    simp only [hA, arcOf]
    split_ifs <;> rfl
  have hSi : ∀ s ∈ ({0} : Finset ℕ), s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs := by
    intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    exact ⟨hL0, b₀, hty0⟩
  refine ⟨A.σ PD.p + rr + A.σ PD.p + A.σ PD.p, ?_, ?_⟩
  · push_cast
    linarith
  · refine liftsAt_thin_letter_type W A F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hW₁ hW₂ hbb {0} hSi b₁ sol₁ hb₁ c₁ _ ?_ hpr f ?_ ?_ ?_
    · intro s hs bs hbs
      rw [Finset.mem_singleton] at hs
      subst hs
      rw [hty0] at hbs
      obtain rfl := Formalism.MainNotions.LocalTheoryWindows.LT.up.inj hbs
      exact hlt0
    · rw [Finset.prod_singleton, hty0]
      have := hf.1
      rw [hnnDen] at this
      exact this
    · intro s hs bs hbs
      obtain ⟨κ', x, hx⟩ := hf.2 s hs bs hbs
      refine ⟨κ', x, ?_⟩
      rw [Finset.prod_singleton, hty0]
      rw [hnnDen] at hx
      exact hx
    · intro s hs hs0 bs hbs
      rw [Finset.mem_singleton] at hs0
      have hs2 : s < 2 := by have : s < L := hs; omega
      interval_cases s
      · exact absurd rfl hs0
      · rw [hty1] at hbs
        exact Formalism.MainNotions.LocalTheoryWindows.LT.noConfusion hbs

end Formalism.MainNotions.N.FrobeniusPowerSeries
