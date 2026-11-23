import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStepCharIdealValueEqBaseMulRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceStepFactorInverseAwayUnitStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal)

theorem stepFac_ratio_core {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (W : G.Weil) (S : GridChoice W Set.univ) (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ)
    (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (h0 : stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0) :
    GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
      (stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  classical
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨hc1, -, hcmul, hcinv, -⟩ := GlobalTheory.Square.isAwayUnit_closure D.what₂.LL (Qn G t) hQn
  have hone : GlobalTheory.Square.IsAwayUnit (Qn G t) (1 : D.what₂.LL) := GlobalTheory.Square.IsAwayUnit.one _
  have hzpow : ∀ (x : D.what₂.LL) (n : ℕ), 0 < n → x ^ n = 1 → ∀ e : ℤ, GlobalTheory.Square.IsAwayUnit (Qn G t) (x ^ e) := by
    intro x n hn hx e
    refine hc1 _ n hn ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hprod : ∀ (s : Finset Bs.P) (f : Bs.P → D.what₂.LL), (∀ v ∈ s, GlobalTheory.Square.IsAwayUnit (Qn G t) (f v)) →
      GlobalTheory.Square.IsAwayUnit (Qn G t) (∏ v ∈ s, f v) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact hcmul _ _ (hf a (Finset.mem_insert_self _ _)) (ih fun v hv => hf v (Finset.mem_insert_of_mem hv))
  set σ := D.what₂.embLL with hσ
  set X₀ := GlobalTheory.SqStep.chs G i j μ₀ with hX₀
  set X := GlobalTheory.SqStep.chs G i j t with hX
  set Sz := G.pl.S0 with hS0
  set f : Chars D.host.F D.host.E → Bs.P → ℂ := fun Y v =>
    (chrW Y.ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW Y.ν (Bs.τ v)) z with hf
  have hS0T : Sz ⊆ X.T := Finset.subset_union_left
  have hT0 : X₀.T = Sz := GlobalTheory.SqStepArith.chs_T_base G hL i j
  have hst : ∀ Y : Chars D.host.F D.host.E, stepFac Bs Y e₁ e₂ s 𝔟 𝔠 z =
      ((idealVal Y.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) * ((idealVal Y.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Y.T), f Y v := by
    intro Y
    simp only [stepFac, Units.val_mul, Units.val_zpow_eq_zpow_val, hf]

  have hsplit : ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T), f X v =
      (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T)) (fun v : Bs.P => v.1 ∈ Sz),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    · ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hS0T h, h⟩⟩
  have hne : ∀ v : Bs.P, v.1 ∈ Sz → f X v ≠ 0 := by
    intro v hv
    rw [hst, hsplit] at h0
    have h1 := left_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using hv)
  have hS := fun (v : Bs.P) (hv : v.1 ∈ Sz) => GlobalTheory.T.base_place_character_factor G hL W S hN i j t Bs hB v hv s z (hne v hv)
  choose bS gS gS' hbS hgS hgS' heS using hS
  have hneT : ∀ v : Bs.P, v.1 ∈ X.T → v.1 ∉ Sz → f X v ≠ 0 := by
    intro v hv hv'
    rw [hst, hsplit] at h0
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using And.intro hv hv')
  have hTw := fun (v : Bs.P) (hv : v.1 ∈ X.T) (hv' : v.1 ∉ Sz) => GlobalTheory.T.twistPlace_stepFactor_inverse_awayUnit G hL W S hN i j t Bs hB v hv hv' s z (hneT v hv hv')
  choose bT hbT heT using hTw
  obtain ⟨b1, ⟨n1, hn1, hb1⟩, e1⟩ := GlobalTheory.T.squareStepChar_idealValue_eq_base_mul_rootOfUnity G hL W S hN i j t 𝔟
  obtain ⟨b2, ⟨n2, hn2, hb2⟩, e2⟩ := GlobalTheory.T.squareStepChar_idealValue_eq_base_mul_rootOfUnity G hL W S hN i j t 𝔠
  let bS₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ Sz then bS v h else 1
  let bT₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ X.T ∧ v.1 ∉ Sz then bT v h.1 h.2 else 1
  let g : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS ⟨v, h.1⟩ h.2 else 1
  let g' : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS' ⟨v, h.1⟩ h.2 else 1
  have hSP : ∀ v ∈ Sz, v ∈ Bs.P := fun v hv => hB.2.1 (hS0T hv)

  have hmap : ∀ F' : HeightOneSpectrum (𝓞 D.host.F) → D.what₂.LL,
      ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1 = ∏ v ∈ Sz, F' v := by
    intro F'
    rw [show (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1) =
        ∏ v ∈ (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)).map (Function.Embedding.subtype _), F' v from
      (Finset.prod_map (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)) (Function.Embedding.subtype _) F').symm]
    congr 1
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    exact ⟨fun ⟨w, hw, e⟩ => e ▸ hw, fun hv => ⟨⟨v, hSP v hv⟩, hv, rfl⟩⟩
  refine ⟨b1 ^ (e₁ : ℤ) * b2 ^ (e₂ : ℤ) * (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
    (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v), g, g', ?_, ?_, ?_⟩
  · refine hcmul _ _ (hcmul _ _ (hcmul _ _ (hzpow b1 n1 hn1 hb1 _) (hzpow b2 n2 hn2 hb2 _)) ?_) ?_
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ Sz := by simpa using hv
      simp only [bS₁, dif_pos hv']
      exact hbS v hv'
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      exact hbT v hv'.1 hv'.2
  · intro v hv
    have h : v ∈ Bs.P ∧ v ∈ Sz := ⟨hSP v hv, hv⟩
    simp only [g, g', dif_pos h]
    exact ⟨hgS _ h.2, hgS' _ h.2⟩
  · have hA : ∀ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz),
        f X₀ v = σ (bS₁ v * ((g v.1 : D.what₂.LL) / (g' v.1 : D.what₂.LL))) * f X v := by
      intro v hv
      have hv' : v.1 ∈ Sz := by simpa using hv
      have h2 : v.1 ∈ Bs.P ∧ v.1 ∈ Sz := ⟨v.2, hv'⟩
      simp only [bS₁, g, g', dif_pos hv', dif_pos h2]
      exact heS v hv'
    have hTw : (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v) *
        σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v) = 1 := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      rw [mul_comm]
      exact heT v hv'.1 hv'.2
    rw [hst X₀, hst X, hsplit, hT0, Finset.prod_congr rfl hA, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_mul_distrib, hmap (fun v => (g v : D.what₂.LL) / (g' v : D.what₂.LL)), e1, e2, mul_zpow, mul_zpow]
    simp only [map_mul, map_zpow₀]
    linear_combination (-((σ b1) ^ (e₁ : ℤ) * (σ b2) ^ (e₂ : ℤ) *
      σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
      σ (∏ v ∈ Sz, (g v : D.what₂.LL) / (g' v : D.what₂.LL)) * ((idealVal X.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) *
      ((idealVal X.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) * ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v)) * hTw

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

theorem stepFac_ratio : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S _ hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0
  exact stepFac_ratio_core G hL W S hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0

end GlobalTheory.SqStepArith
