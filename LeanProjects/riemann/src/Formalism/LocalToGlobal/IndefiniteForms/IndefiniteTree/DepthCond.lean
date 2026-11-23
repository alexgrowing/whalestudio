import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalToGlobal.Divisibility.Numbers

open Module NumberField IsDedekindDomain

namespace Formalism.L2.Indef.Tree.DepthCond

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.DIV Formalism.BasicNotions

def RoundCore : Prop :=
  ∀ (e₁ e₂ : ℕ) (x : ℝ) (E : ℕ), 1 ≤ e₁ → 1 ≤ e₂ → (E : ℤ) ≤ (e₁ : ℤ) * ⌈(e₂ : ℝ) * x⌉ →
    (E : ℝ) / ((e₁ : ℝ) * (e₂ : ℝ)) < x + 1 / (e₂ : ℝ)

def NuLevelCore : Prop :=
  ∀ (g T ν D D' : ℝ), 3 ≤ g → 0 ≤ T → ν ≤ D / (g - 1) → T * D ≤ D' → D' < (g - 2) / 2 → T * ν < 1 / 2

def LevelCore : Prop :=
  ∀ (e T ν s n X : ℝ), 2 ≤ e → 1 ≤ T → T * ν < 1 / 2 → 0 ≤ s → X < T * (ν + 1) + 1 / e → X - (n + s) ≤ 2 * T - n

def RamCore : Prop :=
  ∀ (l T ν s s' D D' C k B X : ℝ), 1 < l → 0 ≤ T → ν ≤ D / (l - 1) → 0 ≤ s' → T * D ≤ D' → D' ≤ C * k * B →
    C * k ≤ l - 1 → 0 ≤ B → X < T * (ν + s + 1) + 1 → X - (T * s + s') ≤ B + T + 1

def FjPCore : Prop :=
  ∀ (Nd : NumDatum) (j p : ℕ),
    ((p = Nd.g 0 ∨ p = Nd.g 1) → Nd.FjP j p = Nd.FTypeG j) ∧
    (p ≠ Nd.g 0 → p ≠ Nd.g 1 → (p ∈ Nd.H.small ∨ p = Nd.q) → Nd.FjP j p = 0) ∧
    (p ≠ Nd.g 0 → p ≠ Nd.g 1 → p ≠ 2 → p ≠ Nd.q → p = Nd.d → Nd.FjP j p = Nd.FRamD j)

def FRamDCore : Prop :=
  ∀ (Nd : NumDatum) (j : ℕ) (b : ℝ), 1 ≤ Nd.R.k →
    (∀ t : Nd.R.A, 0 ≤ Nd.w j (false, t) ∧ 0 ≤ Nd.w j (true, t) ∧ min (Nd.w j (false, t)) (Nd.w j (true, t)) ≤ 2 * b) →
    -((Nd.R.n : ℝ) * (((Nd.R.k : ℝ) - 1) * b)) ≤ Nd.FRamD j ∧ Nd.FRamD j ≤ 0

section Record

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

def TieT (O : OnObj S P c) (TO : ℕ) : Prop := O.T = (TO : ℝ)

def TieE (O : OnObj S P c) (e₁ e₂ : HeightOneSpectrum (𝓞 K) → ℕ) (ν : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) : Prop :=
  AtPair S fun v => 1 ≤ e₁ v ∧ 1 ≤ e₂ v ∧ ramw v = (e₁ v : ℤ) * (e₂ v : ℤ) ∧
    ∀ j, (O.E v j : ℤ) ≤ (e₁ v : ℤ) * ⌈(e₂ v : ℝ) * O.T * (ν v j + if plc v ∈ O.Bad then 1 else 0)⌉

def ContentEqualsDatumContent (N : IndefNum Bs) (Nd : NumDatum) (ι : Bs.J → ℕ) : Prop := ∀ w j, N.F0 w j = Nd.Fj (ι j) w

def TiePrimes (O : OnObj S P c) (Nd : NumDatum) : Prop := O.g1 = Nd.g 0 ∧ O.g2 = Nd.g 1 ∧ O.q1 = Nd.q ∧ O.dd = Nd.d ∧ O.sm = Nd.H.small

def TieFK (O : OnObj S P c) (Nd : NumDatum) : Prop := O.f = 2 * (Nd.R.n : ℝ) ∧ O.k = (Nd.R.k : ℝ)

def NuLevel (O : OnObj S P c) (ν : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (DL : Bs.J → ℝ) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.g1 ∨ plc w = O.g2) → ∀ j,
    ν w j ≤ DL j / ((plc w : ℝ) - 1) ∧ ν (conjPl w) j ≤ DL j / ((plc w : ℝ) - 1)

def DegScale (O : OnObj S P c) (DL Dk : Bs.J → ℝ) : Prop := ∀ j, O.T * DL j ≤ Dk j

def DegLevelPage (O : OnObj S P c) (Dk : Bs.J → ℝ) : Prop :=
  ∀ j, Dk j < ((O.g1 : ℝ) - 2) / 2 ∧ Dk j < ((O.g2 : ℝ) - 2) / 2

def RamLevel (O : OnObj S P c) (e₂ : HeightOneSpectrum (𝓞 K) → ℕ) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.g1 ∨ plc w = O.g2) → (plc w : ℝ) - 1 ≤ e₂ w ∧ (plc w : ℝ) - 1 ≤ e₂ (conjPl w)

def SigmaLevel (O : OnObj S P c) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.g1 ∨ plc w = O.g2) → ∀ j,
    (∃ s : ℝ, 0 ≤ s ∧ (vw w (O.σ w j) : ℝ) / (ramw w : ℝ) = O.nn w j + s) ∧
    (∃ s : ℝ, 0 ≤ s ∧ (vw (conjPl w) (O.σ (conjPl w) j) : ℝ) / (ramw (conjPl w) : ℝ) = O.nn (conjPl w) j + s)

def NnLevel (O : OnObj S P c) (Nd : NumDatum) (ι : Bs.J → ℕ) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.g1 ∨ plc w = O.g2) → ∀ j,
    O.nn w j + O.nn (conjPl w) j = ((Nd.Dplus (ι j) + Nd.Dminus (ι j) : ℚ) : ℝ)

def TieScale (S : IndefData Df) (ν νW sW : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) : Prop :=
  AtPair S fun v => ∀ j, ν v j = νW v j + sW v j

def TieSigma (O : OnObj S P c) (sW s1 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) : Prop :=
  AtPair S fun v => ∀ j, (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) = O.T * sW v j + s1 v j

def CrudeRam (O : OnObj S P c) (νW : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (DL : Bs.J → ℝ) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.q1 ∨ plc w = O.dd) → ∀ j,
    νW w j ≤ DL j / ((plc w : ℝ) - 1) ∧ νW (conjPl w) j ≤ DL j / ((plc w : ℝ) - 1)

def SprimeRam (O : OnObj S P c) (s1 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.q1 ∨ plc w = O.dd) → ∀ j, 0 ≤ s1 w j ∧ 0 ≤ s1 (conjPl w) j

def DegWeight (O : OnObj S P c) (Dk : Bs.J → ℝ) (C₀ : ℝ) : Prop := ∀ j, Dk j ≤ C₀ * O.k * O.sB j

def PageRam (O : OnObj S P c) (C₀ : ℝ) : Prop := C₀ * O.k ≤ (O.q1 : ℝ) - 1 ∧ C₀ * O.k ≤ (O.dd : ℝ) - 1

def WtRam (O : OnObj S P c) (Nd : NumDatum) (ι : Bs.J → ℕ) : Prop :=
  ∀ j (t : Nd.R.A), 0 ≤ Nd.w (ι j) (false, t) ∧ 0 ≤ Nd.w (ι j) (true, t) ∧
    min (Nd.w (ι j) (false, t)) (Nd.w (ι j) (true, t)) ≤ 2 * O.bp

private lemma two_mem_small_nd (Nd : NumDatum) : 2 ∈ Nd.H.small := by
  show 2 ∈ Nd.H.QS.primeFactors
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
    dvd_trans (dvd_pow_self 2 (by omega)) Nd.H.tower_dvd, Nd.H.QS_pos.ne'⟩

private lemma level_at (O : OnObj S P c) (TO : ℕ) (e₁ e₂ : HeightOneSpectrum (𝓞 K) → ℕ)
    (ν : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (cR : RoundCore) (cL : LevelCore) (tT : TieT O TO) (hT : 1 ≤ TO)
    (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) (he1 : 1 ≤ e₁ v) (he2 : 1 ≤ e₂ v) (hram : ramw v = (e₁ v : ℤ) * (e₂ v : ℤ))
    (hE : (O.E v j : ℤ) ≤ (e₁ v : ℤ) * ⌈(e₂ v : ℝ) * O.T * (ν v j + 1)⌉)
    (h2 : (2 : ℝ) ≤ e₂ v) (hTν : O.T * ν v j < 1 / 2)
    (hσ : ∃ s : ℝ, 0 ≤ s ∧ (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) = O.nn v j + s) :
    O.e0 v j ≤ 2 * O.T - O.nn v j := by
  obtain ⟨s, hs0, hs⟩ := hσ
  have hT1 : (1 : ℝ) ≤ O.T := by rw [tT]; exact_mod_cast hT
  have hr : ((ramw v : ℤ) : ℝ) = (e₁ v : ℝ) * (e₂ v : ℝ) := by rw [hram]; push_cast; ring
  have hround := cR (e₁ v) (e₂ v) (O.T * (ν v j + 1)) (O.E v j) he1 he2 (by rw [← mul_assoc]; exact hE)
  have hlev := cL (e₂ v) O.T (ν v j) s (O.nn v j) ((O.E v j : ℝ) / ((e₁ v : ℝ) * (e₂ v : ℝ)))
    h2 hT1 hTν hs0 hround
  have he0 : O.e0 v j = (O.E v j : ℝ) / ((e₁ v : ℝ) * (e₂ v : ℝ)) - (O.nn v j + s) := by
    rw [← hs, ← hr]
    simp only [OnObj.e0, sub_div]
  rw [he0]
  exact hlev

private lemma ram_at (O : OnObj S P c) (e₁ e₂ : HeightOneSpectrum (𝓞 K) → ℕ)
    (ν νW sW s1 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (cR : RoundCore) (cM : RamCore)
    (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) (l D D' C₀ : ℝ)
    (he1 : 1 ≤ e₁ v) (he2 : 1 ≤ e₂ v) (hram : ramw v = (e₁ v : ℤ) * (e₂ v : ℤ))
    (hE : (O.E v j : ℤ) ≤ (e₁ v : ℤ) * ⌈(e₂ v : ℝ) * O.T * (ν v j + 1)⌉)
    (hS : ν v j = νW v j + sW v j) (hσ : (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) = O.T * sW v j + s1 v j)
    (hl : 1 < l) (hT0 : 0 ≤ O.T) (hν : νW v j ≤ D / (l - 1)) (hs1 : 0 ≤ s1 v j) (hD : O.T * D ≤ D')
    (hW : D' ≤ C₀ * O.k * O.sB j) (hP : C₀ * O.k ≤ l - 1) (hB : 0 ≤ O.sB j) :
    O.e0 v j ≤ O.sB j + O.T + 1 := by
  have hr : ((ramw v : ℤ) : ℝ) = (e₁ v : ℝ) * (e₂ v : ℝ) := by rw [hram]; push_cast; ring
  have hround := cR (e₁ v) (e₂ v) (O.T * (ν v j + 1)) (O.E v j) he1 he2 (by rw [← mul_assoc]; exact hE)
  have he2' : (1 : ℝ) ≤ e₂ v := by exact_mod_cast he2
  have hinv : 1 / (e₂ v : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact he2'
  have hX : (O.E v j : ℝ) / ((e₁ v : ℝ) * (e₂ v : ℝ)) < O.T * (νW v j + sW v j + 1) + 1 := by
    rw [← hS]; linarith
  have hm := cM l O.T (νW v j) (sW v j) (s1 v j) D D' C₀ O.k (O.sB j) _ hl hT0 hν hs1 hD hW hP hB hX
  have he0 : O.e0 v j = (O.E v j : ℝ) / ((e₁ v : ℝ) * (e₂ v : ℝ)) - (O.T * sW v j + s1 v j) := by
    rw [← hσ, ← hr]
    simp only [OnObj.e0, sub_div]
  rw [he0]
  exact hm

theorem leafDepthLevel_of (N : IndefNum Bs) (O : OnObj S P c) (Nd : NumDatum) (ι : Bs.J → ℕ) (TO : ℕ)
    (e₁ e₂ : HeightOneSpectrum (𝓞 K) → ℕ) (ν : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (DL Dk : Bs.J → ℝ)
    (cR : RoundCore) (cN : NuLevelCore) (cL : LevelCore) (cF : FjPCore)
    (hPg : LeafPage O) (tT : TieT O TO) (hT : 1 ≤ TO) (tE : TieE O e₁ e₂ ν) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd)
    (iν : NuLevel O ν DL) (iD : DegScale O DL Dk) (iP : DegLevelPage O Dk) (iR : RamLevel O e₂) (iS : SigmaLevel O)
    (iN : NnLevel O Nd ι) :
    LeafDepthLevel N O := by
  obtain ⟨hC, hk, hm, hf, hT0, hSc, heta, hbp, hvd, hNc, hg1p, hg2p, hq1p, hddp, hg12, hqd, hqg1, hqg2,
    hdg1, hdg2, hg1s, hg2s, hq1s, hdds, hx⟩ := hPg
  obtain ⟨tg1, tg2, tq, td, tsm⟩ := tP
  have h2s : 2 ∈ O.sm := by rw [tsm]; exact two_mem_small_nd Nd
  intro w hw hpl j
  have hpr : (plc w).Prime := by rcases hpl with h | h <;> rw [h] <;> assumption
  have hne : plc w ≠ 2 := fun h2 => by
    rcases hpl with h | h
    · exact hg1s (by rw [← h, h2]; exact h2s)
    · exact hg2s (by rw [← h, h2]; exact h2s)
  have hp3 : (3 : ℝ) ≤ (plc w : ℝ) := by
    have := hpr.two_le
    have h3 : 3 ≤ plc w := by omega
    exact_mod_cast h3
  have hbad : plc w ∈ O.Bad := by
    unfold OnObj.Bad
    rcases hpl with h | h <;> simp [h]
  have key : ∀ v, plc v = plc w → (2 : ℝ) ≤ e₂ v →
      (∃ s : ℝ, 0 ≤ s ∧ (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) = O.nn v j + s) →
      ν v j ≤ DL j / ((plc w : ℝ) - 1) →
      (1 ≤ e₁ v ∧ 1 ≤ e₂ v ∧ ramw v = (e₁ v : ℤ) * (e₂ v : ℤ) ∧ ∀ j, (O.E v j : ℤ) ≤
        (e₁ v : ℤ) * ⌈(e₂ v : ℝ) * O.T * (ν v j + if plc v ∈ O.Bad then 1 else 0)⌉) →
      O.e0 v j ≤ 2 * O.T - O.nn v j := by
    intro v hv he2 hσ hν hq
    obtain ⟨he1, he2', hram, hE⟩ := hq
    have hE' := hE j
    rw [if_pos (by rw [hv]; exact hbad)] at hE'
    have hTν : O.T * ν v j < 1 / 2 := by
      have hDk := iP j
      rcases hpl with h | h
      · exact cN (plc w) O.T (ν v j) (DL j) (Dk j) hp3 hT0 hν (iD j) (by rw [h]; exact hDk.1)
      · exact cN (plc w) O.T (ν v j) (DL j) (Dk j) hp3 hT0 hν (iD j) (by rw [h]; exact hDk.2)
    exact level_at O TO e₁ e₂ ν cR cL tT hT v j he1 he2' hram hE' he2 hTν hσ
  have hr := iR w hw hpl
  have hν := iν w hw hpl j
  have hs := iS w hw hpl j
  have htE := tE w hw
  refine ⟨key w rfl (by linarith [hr.1]) hs.1 hν.1 htE.1,
    key (conjPl w) (plc_conjPl w) (by linarith [hr.2]) hs.2 hν.2 htE.2, ?_⟩
  rw [iN w hw hpl j, tF w j]
  have hFj : Nd.Fj (ι j) w = Nd.FTypeG (ι j) := by
    show Nd.FjP (ι j) (plc w) = _
    refine (cF Nd (ι j) (plc w)).1 ?_
    rcases hpl with h | h
    · left; rw [h, tg1]
    · right; rw [h, tg2]
  rw [hFj]
  simp only [NumDatum.FTypeG]
  ring

theorem leafDepthRam_of (N : IndefNum Bs) (O : OnObj S P c) (Nd : NumDatum) (ι : Bs.J → ℕ)
    (e₁ e₂ : HeightOneSpectrum (𝓞 K) → ℕ) (ν νW sW s1 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (DL Dk : Bs.J → ℝ) (C₀ : ℝ)
    (cR : RoundCore) (cM : RamCore) (cF : FjPCore) (cD : FRamDCore)
    (hPg : LeafPage O) (hSz : LeafSizes O) (tE : TieE O e₁ e₂ ν) (tF : ContentEqualsDatumContent N Nd ι)
    (tP : TiePrimes O Nd) (tK : TieFK O Nd)
    (tS : TieScale S ν νW sW) (tσ : TieSigma O sW s1) (iν : CrudeRam O νW DL) (iS : SprimeRam O s1) (iD : DegScale O DL Dk) (iW : DegWeight O Dk C₀) (iP : PageRam O C₀) (iB : WtRam O Nd ι) :
    LeafDepthRam N O := by
  obtain ⟨hC, hk, hm, hf, hT0, hSc, heta, hbp, hvd, hNc, hg1p, hg2p, hq1p, hddp, hg12, hqd, hqg1, hqg2,
    hdg1, hdg2, hg1s, hg2s, hq1s, hdds, hx⟩ := hPg
  obtain ⟨tg1, tg2, tq, td, tsm⟩ := tP
  have h2s : 2 ∈ O.sm := by rw [tsm]; exact two_mem_small_nd Nd
  obtain ⟨tf, tk⟩ := tK
  obtain ⟨hwt, -⟩ := hSz
  intro w hw hpl j
  have hbad : plc w ∈ O.Bad := by
    unfold OnObj.Bad
    rcases hpl with h | h <;> simp [h]
  have hl1 : (1 : ℝ) < (plc w : ℝ) := by
    have hpr : (plc w).Prime := by rcases hpl with h | h <;> rw [h] <;> assumption
    exact_mod_cast hpr.one_lt
  have hB : 0 ≤ O.sB j := by
    unfold OnObj.sB OnObj.Se
    exact add_nonneg (hwt j).1 (mul_nonneg (by linarith) (add_nonneg hSc heta))
  have hPl : C₀ * O.k ≤ (plc w : ℝ) - 1 := by
    rcases hpl with h | h <;> rw [h]
    exacts [iP.1, iP.2]
  have key : ∀ v, plc v = plc w → νW v j ≤ DL j / ((plc w : ℝ) - 1) → 0 ≤ s1 v j →
      ν v j = νW v j + sW v j →
      (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) = O.T * sW v j + s1 v j →
      (1 ≤ e₁ v ∧ 1 ≤ e₂ v ∧ ramw v = (e₁ v : ℤ) * (e₂ v : ℤ) ∧ ∀ j, (O.E v j : ℤ) ≤
        (e₁ v : ℤ) * ⌈(e₂ v : ℝ) * O.T * (ν v j + if plc v ∈ O.Bad then 1 else 0)⌉) →
      O.e0 v j ≤ O.sB j + O.T + 1 := by
    intro v hv hν hs1 hS hσ hq
    obtain ⟨he1, he2, hram, hE⟩ := hq
    have hE' := hE j
    rw [if_pos (by rw [hv]; exact hbad)] at hE'
    exact ram_at O e₁ e₂ ν νW sW s1 cR cM v j (plc w) (DL j) (Dk j) C₀ he1 he2 hram hE' hS hσ hl1 hT0
      hν hs1 (iD j) (iW j) hPl hB
  have hν := iν w hw hpl j
  have hs := iS w hw hpl j
  have htE := tE w hw
  have htS := tS w hw
  have htσ := tσ w hw
  refine ⟨key w rfl hν.1 hs.1 (htS.1 j) (htσ.1 j) htE.1,
    key (conjPl w) (plc_conjPl w) hν.2 hs.2 (htS.2 j) (htσ.2 j) htE.2, ?_, ?_⟩
  · intro hq
    rw [tF w j]
    show Nd.FjP (ι j) (plc w) = 0
    refine (cF Nd (ι j) (plc w)).2.1 ?_ ?_ (Or.inr ?_)
    · rw [hq, ← tg1]; exact hqg1
    · rw [hq, ← tg2]; exact hqg2
    · rw [hq, tq]
  · intro hd
    rw [tF w j]
    show -(2 * (O.f * O.k * O.bp)) ≤ Nd.FjP (ι j) (plc w) ∧ Nd.FjP (ι j) (plc w) ≤ 0
    have hdne2 : O.dd ≠ 2 := fun h => hdds (by rw [h]; exact h2s)
    have hF : Nd.FjP (ι j) (plc w) = Nd.FRamD (ι j) :=
      (cF Nd (ι j) (plc w)).2.2 (by rw [hd, ← tg1]; exact hdg1) (by rw [hd, ← tg2]; exact hdg2)
        (by rw [hd]; exact hdne2) (by rw [hd, ← tq]; exact fun h => hqd h.symm) (by rw [hd, td])
    have hk1 : 1 ≤ Nd.R.k := by
      have h1 : (1 : ℝ) ≤ (Nd.R.k : ℝ) := by rw [← tk]; exact hk
      exact_mod_cast h1
    obtain ⟨h1, h2⟩ := cD Nd (ι j) O.bp hk1 (iB j)
    rw [hF]
    refine ⟨le_trans ?_ h1, h2⟩
    rw [tf, tk]
    have hn : (0 : ℝ) ≤ Nd.R.n := Nat.cast_nonneg _
    have hk' : (1 : ℝ) ≤ Nd.R.k := by exact_mod_cast hk1
    nlinarith [mul_nonneg (mul_nonneg hn hbp) (by linarith : (0 : ℝ) ≤ 3 * (Nd.R.k : ℝ) + 1)]

end Record

end Formalism.L2.Indef.Tree.DepthCond
