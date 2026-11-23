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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGaussSumIntegerDvdResidueCardPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqStepArith

theorem chrW_chs_eq_mul {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    chrW (GlobalTheory.SqStep.chs G i j t).ν τ = chrW (GlobalTheory.SqStep.chs G i j μ₀).ν τ *
      ((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime τ)).comp
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom) := by
  have e : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]
    exact (div_mul_eq_mul_div _ _ _).symm
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.mul_apply, chrW_chs G hL, chrW_chs G hL, MonoidHom.comp_apply, e]
  rfl

theorem chrW_chs_continuous {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    Continuous (fun x : (Fv D.host.F v)ˣ => (chrW (GlobalTheory.SqStep.chs G i j t).ν τ x : ℂ)) := by
  refine GlobalTheory.StepFacNe.chrW_continuous _ ?_ τ
  have e : (GlobalTheory.SqStep.chs G i j t).ν = G.nu t i (j + 1) := by
    show (Lc.mu t (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  rw [e]
  exact (chrEq_nu G t i j hL).1.1

theorem chrW_chs_norm {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (x : (Fv D.host.F v)ˣ) : ‖(chrW (GlobalTheory.SqStep.chs G i j t).ν τ x : ℂ)‖ = 1 :=
  Circle.norm_coe _

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

open Formalism.L2.Host in
theorem levelLe_mul {L : Type} [Field L] [NumberField L] {a b : HChar L} {w : HeightOneSpectrum (𝓞 L)} {n : ℕ}
    (ha : a.LevelLe w n) (hb : b.LevelLe w n) : (a * b).LevelLe w n := fun x hx h => by
  rw [HChar.loc_mul, ha x hx h, hb x hx h, one_mul]

open Formalism.L2.Host in
theorem levelLe_inv {L : Type} [Field L] [NumberField L] {a : HChar L} {w : HeightOneSpectrum (𝓞 L)} {n : ℕ}
    (ha : a.LevelLe w n) : (a⁻¹).LevelLe w n := fun x hx h => by
  rw [HChar.loc_inv, ha x hx h, inv_one]

open Formalism.L2.Host in
theorem levelLe_mono {L : Type} [Field L] [NumberField L] {a : HChar L} {w : HeightOneSpectrum (𝓞 L)} {m n : ℕ}
    (ha : a.LevelLe w m) (hmn : m ≤ n) : a.LevelLe w n := fun x hx h =>
  ha x hx (h.trans (WithZero.exp_le_exp.2 (by omega)))

theorem nuH_levelLe_two {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) (PP : HeightOneSpectrum (𝓞 D.host.E)) (hPP : PP.under (𝓞 D.host.F) ∈ S1 D) :
    (nuH G t i j).LevelLe PP 2 ∧ ¬ (nuH G t i j).LevelLe PP 1 := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hchi := G.ch.lev1 _ hm.1 hm.2 PP hPP
  have hmu : (Lc.C.mu0 j).LevelLe PP 1 := (Lc.C.isMu0 j).tame PP
  have hxi : (Lc.xiH t).LevelLe PP 1 := hL.xi_tame t PP
  refine ⟨?_, fun h => hchi.2 ?_⟩
  · rw [nuH, div_eq_mul_inv]
    exact levelLe_mul (levelLe_mul (levelLe_mono hmu (by omega)) (levelLe_mono hxi (by omega))) (levelLe_inv hchi.1)
  · have e : G.ch.chiH (D.R.m - i) = Lc.C.mu0 j * Lc.xiH t / nuH G t i j := by
      rw [nuH, div_div_cancel]
    rw [e, div_eq_mul_inv]
    exact levelLe_mul (levelLe_mul hmu hxi) (levelLe_inv h)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem condExp_comp_eq_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (χ : HChar E)
    (h2 : χ.LevelLe (GlobalTheory.AdelicU.splitPrime τ) 2) (h1 : ¬ χ.LevelLe (GlobalTheory.AdelicU.splitPrime τ) 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ((χ.loc (GlobalTheory.AdelicU.splitPrime τ)).comp
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) = 2 := by
  have key : ∀ n, GlobalTheory.SplitFlip.CondLE (unifAt v) n ((χ.loc (GlobalTheory.AdelicU.splitPrime τ)).comp
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) ↔ χ.LevelLe (GlobalTheory.AdelicU.splitPrime τ) n :=
    fun n => GlobalTheory.CondLESplit.condLE_iff τ _ n
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
  refine le_antisymm (Nat.sInf_le ((key 2).2 h2)) (le_csInf ⟨2, (key 2).2 h2⟩ fun c hc => ?_)
  by_contra hlt
  exact h1 (levelLe_mono ((key c).1 hc) (by omega))

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem factor_unr {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ)
    (hξ : ∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ξ x = 1)
    (s : (Fv F v)ˣ) (z : ℤ) (h0 : (((ν₀ * ξ) s : ℂˣ) : ℂ) * eps ψ (ν₀ * ξ) z ≠ 0) :
    ∃ u : (Fv F v)ˣ, ((ν₀ s : ℂˣ) : ℂ) * eps ψ ν₀ z = ((ξ u : ℂˣ) : ℂ) * ((((ν₀ * ξ) s : ℂˣ) : ℂ) * eps ψ (ν₀ * ξ) z) := by
  obtain ⟨hc, y, hg⟩ := GlobalTheory.GaussUnr.gauss_mul_unram ψ ν₀ ξ hξ
  have he := eps_mul_of_condExp ψ ν₀ ξ s z hc
  have hG1 : gauss ψ (ν₀ * ξ) ≠ 0 := by
    intro h; apply h0; unfold eps; rw [h]; ring
  have hG0 : gauss ψ ν₀ ≠ 0 := by
    intro h; apply hG1; rw [hg, h, mul_zero]
  refine ⟨y * (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀)⁻¹, ?_⟩
  rw [hg] at he
  simp only [Units.val_inv_eq_inv_val] at he
  have hy : ((ξ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hb : ((ξ (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  refine mul_right_cancel₀ (mul_ne_zero (inv_ne_zero hy) hG0) ?_
  rw [he]
  field_simp

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem factor_ram {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)} (ν₀ ξ : (Fv F v)ˣ →* ℂˣ) (s : (Fv F v)ˣ) (z : ℤ) (c : ℕ)
    (hc0 : condExp ν₀ = c) (hc1 : condExp (ν₀ * ξ) = c) (h1 : 1 ≤ c) (hψ : PsiUnr ψ v)
    (hcont0 : Continuous (fun x : (Fv F v)ˣ => (ν₀ x : ℂ))) (hcont1 : Continuous (fun x : (Fv F v)ˣ => ((ν₀ * ξ) x : ℂ)))
    (hun0 : ∀ x, ‖(ν₀ x : ℂ)‖ = 1) (hun1 : ∀ x, ‖((ν₀ * ξ) x : ℂ)‖ = 1)
    (hr0 : ∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → (ν₀ x : ℂ) ∈ Set.range σ)
    (hr1 : ∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ((ν₀ * ξ) x : ℂ) ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ c) = 1 → ζ ∈ Set.range σ)
    (h0 : (((ν₀ * ξ) s : ℂˣ) : ℂ) * eps ψ (ν₀ * ξ) z ≠ 0) :
    ∃ g g' : 𝓞 K, g ∣ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ c ∧ g' ∣ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ c ∧
      ((ν₀ s : ℂˣ) : ℂ) * eps ψ ν₀ z =
        (((ξ (s * unifAt v ^ c))⁻¹ : ℂˣ) : ℂ) * (σ (g : K) / σ (g' : K)) * ((((ν₀ * ξ) s : ℂˣ) : ℂ) * eps ψ (ν₀ * ξ) z) := by
  obtain ⟨g, g₁, hg, hgg⟩ := GlobalTheory.GaussDiv.gauss_dvd_pow σ ψ v ν₀ hψ hcont0 hun0 (hc0 ▸ h1) hr0 (hc0 ▸ hζ)
  obtain ⟨g', g₁', hg', hgg'⟩ := GlobalTheory.GaussDiv.gauss_dvd_pow σ ψ v (ν₀ * ξ) hψ hcont1 hun1 (hc1 ▸ h1) hr1 (hc1 ▸ hζ)
  have he := eps_mul_of_condExp ψ ν₀ ξ s z (hc1.trans hc0.symm)
  have hG1 : gauss ψ (ν₀ * ξ) ≠ 0 := by
    intro h; apply h0; unfold eps; rw [h]; ring
  refine ⟨g, g', ⟨g₁, by rw [hgg, hc0]⟩, ⟨g₁', by rw [hgg', hc1]⟩, ?_⟩
  rw [hg, hg', ← hc0]
  calc _ = ((ν₀ s : ℂˣ) : ℂ) * eps ψ ν₀ z * gauss ψ (ν₀ * ξ) / gauss ψ (ν₀ * ξ) := (mul_div_cancel_right₀ _ hG1).symm
    _ = _ := by rw [he]; ring

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

open Formalism.L2.Host in

theorem nuH_loc_mem {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} {G : GridData Lc sc} {μ₀ : T} {W : G.Weil}
    {S : GridChoice W Set.univ} (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (y : (w.adicCompletion D.host.E)ˣ) :
    (((nuH G t i j).loc w y : ℂˣ) : ℂ) ∈ Set.range D.what₂.embLL := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have h1 : _ ∈ D.what₂.embLL.fieldRange := RingHom.mem_fieldRange.2 (hN.chars.mu0 j w y)
  have h2 : _ ∈ D.what₂.embLL.fieldRange := RingHom.mem_fieldRange.2 (hN.chars.xi t w y)
  have h3 : _ ∈ D.what₂.embLL.fieldRange := RingHom.mem_fieldRange.2 (hN.chars.chi _ hm.1 hm.2 w y)
  refine RingHom.mem_fieldRange.1 ?_
  rw [nuH, div_eq_mul_inv, HChar.loc_mul, HChar.loc_mul, HChar.loc_inv, Units.val_mul, Units.val_mul,
    Units.val_inv_eq_inv_val]
  exact mul_mem (mul_mem h1 h2) (inv_mem h3)

open Formalism.L2.Host in

theorem isUnitAt_complMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) (h1 : (x : Fv F v) ∈ v.adicCompletionIntegers F)
    (h2 : ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F) :
    IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) := by
  unfold IsUnitAt
  rw [Units.coe_map]
  show Valued.v (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ) (x : Fv F v)) = 1
  rw [GlobalTheory.LFun.SplitTie.valued_complMap τ (GlobalTheory.AdelicU.splitPrime_under τ)]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
  have hne : Valued.v (x : Fv F v) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
open Formalism.L2.Host in

theorem base_place_factor_zero : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ),
    ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 →
    ∃ (b : D.what₂.LL) (g g' : 𝓞 D.what₂.LL), GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      g ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      g' ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      ((chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v)) z) =
        D.what₂.embLL (b * ((g : D.what₂.LL) / (g' : D.what₂.LL))) * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) := by
  intro D T Lc sc G μ₀ hL W S hN i j t Bs hB v hv s z h0
  classical
  have hwu : (GlobalTheory.AdelicU.splitPrime (Bs.τ v)).under (𝓞 D.host.F) = v.1 := GlobalTheory.AdelicU.splitPrime_under (Bs.τ v)
  have hν := chrW_chs_eq_mul G hL i j t (Bs.τ v)
  rw [hν] at h0 ⊢
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨hc1, -, -, -, -⟩ := GlobalTheory.Square.isAwayUnit_closure D.what₂.LL (Qn G t) hQn
  have hval : ∀ y, ∃ b : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      D.what₂.embLL b = (((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v)) y : ℂˣ) : ℂ) := by
    intro y
    obtain ⟨b, hb⟩ := hN.chars.xi t _ y
    obtain ⟨n, hn, hord⟩ := hL.xi_fin t
    refine ⟨b, hc1 b n hn ?_, hb⟩
    apply D.what₂.embLL.injective
    rw [map_pow, hb, map_one]
    have e := congrArg (fun χ : HChar D.host.E => ((χ.loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v)) y : ℂˣ) : ℂ)) hord
    exact e
  by_cases hu : ∀ x : (Fv D.host.F v.1)ˣ, (x : Fv D.host.F v.1) ∈ v.1.adicCompletionIntegers D.host.F →
      ((x⁻¹ : (Fv D.host.F v.1)ˣ) : Fv D.host.F v.1) ∈ v.1.adicCompletionIntegers D.host.F →
      (((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v))).comp
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom)) x = 1
  · obtain ⟨u, hu'⟩ := factor_unr Bs.ψ _ _ hu _ z h0
    obtain ⟨b, hb, hbe⟩ := hval (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom u)
    refine ⟨b, 1, 1, hb, one_dvd _, one_dvd _, ?_⟩
    rw [hu', div_self (by simp), mul_one, hbe]
    rfl
  · have hy0 : ∃ y0 : (Fv D.host.F v.1)ˣ, y0 = Units.map (Int.castRingHom (Fv D.host.F v.1)).toMonoidHom s := ⟨_, rfl⟩
    obtain ⟨y0, hy0⟩ := hy0
    have hy1 : ∃ y1 : (Fv D.host.F v.1)ˣ, y1 = (y0 * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v.1 ^ 2)⁻¹ := ⟨_, rfl⟩
    obtain ⟨y1, hy1⟩ := hy1
    obtain ⟨b, hb, hbe⟩ := hval (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom y1)
    have hram : ¬ (Lc.xiH t).UnrAt (GlobalTheory.AdelicU.splitPrime (Bs.τ v)) := fun h =>
      hu fun x h1 h2 => h _ (isUnitAt_complMap (Bs.τ v) x h1 h2)
    have hv0 : v.1 ≠ G.pl.v0 := by
      intro e
      rcases (hL.Q_ram t _).1 hram with h | ⟨PP', h, hc'⟩
      · exact G.pl.levelPlace_ne_basePlace t _ h (hwu.trans e)
      · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans (hwu.trans e))
    have hv1 : v.1 ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left hv0
    have hce : condExp G.pl v.1 = 2 := if_neg hv0
    have hloc : GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G t := hB.2.2.2 v (Finset.mem_union_left _ hv)
    have hw : GlobalTheory.AdelicU.splitPrime (Bs.τ v) = G.pl.w v.1 := by
      rcases Finset.mem_union.1 hloc with h | h
      · obtain ⟨v', hv', e⟩ := Finset.mem_image.1 h
        have e' : v' = v.1 := by rw [← G.pl.under_w hv', e, hwu]
        rw [← e, e']
      · have := G.pl.w_Q t _ h (hwu.symm ▸ hv1)
        rwa [hwu] at this
    have hdep : depthAt G (GlobalTheory.AdelicU.splitPrime (Bs.τ v)) = 2 := by
      rw [hw, (depthAt_w G hv).2]
      exact if_neg hv0
    have hroots := hN.roots t _ hloc
    rw [hdep, GlobalTheory.LFun.SplitChart.absNorm_splitPrime] at hroots
    have hchr : ∀ t', chrW (GlobalTheory.SqStep.chs G i j t').ν (Bs.τ v) = ((nuH G t' i j).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v))).comp
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom) := fun t' =>
      MonoidHom.ext fun x => chrW_chs G hL i j t' (Bs.τ v) x
    have hexp : ∀ t', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t').ν (Bs.τ v)) = 2 := fun t' => by
      obtain ⟨h2, h1⟩ := nuH_levelLe_two G hL i j t' _ (hwu.symm ▸ hv1)
      rw [hchr]
      exact condExp_comp_eq_two (Bs.τ v) _ h2 h1
    have hrange : ∀ t' x, (chrW (GlobalTheory.SqStep.chs G i j t').ν (Bs.τ v) x : ℂ) ∈ Set.range D.what₂.embLL := fun t' x => by
      rw [hchr]
      exact nuH_loc_mem hN i j t' _ _
    have e1 := hexp t
    have c1 := chrW_chs_continuous G hL i j t (Bs.τ v)
    have n1 := chrW_chs_norm G i j t (Bs.τ v)
    have r1 := hrange t
    rw [hν] at e1 c1 n1 r1
    have key := factor_ram D.what₂.embLL Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v))
      (((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v))).comp
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom))
      (Units.map (Int.castRingHom (Fv D.host.F v.1)).toMonoidHom s) z 2 (hexp μ₀) e1 (by norm_num)
    specialize key (hB.2.2.1 v.1 v.2)
    specialize key (chrW_chs_continuous G hL i j μ₀ (Bs.τ v))
    specialize key c1
    specialize key (chrW_chs_norm G i j μ₀ (Bs.τ v))
    specialize key n1
    specialize key (fun x _ _ => hrange μ₀ x)
    specialize key (fun x _ _ => r1 x)
    specialize key hroots
    have k2 := key h0
    rcases k2 with ⟨g, k3⟩
    rcases k3 with ⟨g', k4⟩
    have hg := k4.1
    have hg' := k4.2.1
    have he := k4.2.2
    refine ⟨b, g, g', hb, hce ▸ hg, hce ▸ hg', ?_⟩
    have hξ : ((((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v)))
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom y1) : ℂˣ) : ℂ) =
        ((((((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v))).comp
          (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom))
          (Units.map (Int.castRingHom (Fv D.host.F v.1)).toMonoidHom s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v.1 ^ 2))⁻¹ : ℂˣ) : ℂ) := by
      rw [hy1, hy0, map_inv, map_inv]
      rfl
    rw [he]
    rw [map_mul D.what₂.embLL]
    rw [map_div₀]
    rw [hbe, hξ]

end GlobalTheory.SqStepArith
