import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchrodingerIntertwinerIntegralMatrices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleDescentOfParity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVacuumTransverseLagrangianLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatVectorIrreducibleTranslationsCharaStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.StoneVN

section Char

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_int {ψ0 : AddChar k ℂ} (hc : ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k])
    {y : k} (hy : y ∈ 𝒪[k]) : ψ0 y = 1 := by
  simpa using (hc 1).2 (one_mem _) y hy

theorem norm_eq_one {ψ0 : AddChar k ℂ} (hc : ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k])
    (x : k) : ‖ψ0 x‖ = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm, h⟩ := GlobalTheory.SBUnif.exists_nat_mem_mul_integer x⁻¹ (inv_ne_zero hx)
  rw [inv_inv] at h
  have h1 : ψ0 x ^ m = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
    exact triv_int hc h
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h2

def toCirc (ψ0 : AddChar k ℂ) (hc : ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) :
    AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (norm_eq_one hc x)⟩
  map_zero_eq_one' := by ext; simp
  map_add_eq_mul' a b := by ext; exact AddChar.map_add_eq_mul ψ0 a b

theorem toCirc_apply {ψ0 : AddChar k ℂ} (hc : ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k])
    (x : k) : (toCirc ψ0 hc x : ℂ) = ψ0 x := rfl

theorem toCirc_cont {ψ0 : AddChar k ℂ} (hc : ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k])
    (h : Continuous ψ0) : Continuous (toCirc ψ0 hc) :=
  Continuous.subtype_mk h _

theorem toCirc_ne_one {ψ0 : AddChar k ℂ} (hc : ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) :
    toCirc ψ0 hc ≠ 1 := by
  intro h
  obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hnot : w⁻¹ ∉ 𝒪[k] := by
    intro hm
    have h3 : valuation k w⁻¹ ≤ 1 := hm
    have h4 : valuation k (w * w⁻¹) = 1 := by rw [mul_inv_cancel₀ hw0, map_one]
    rw [map_mul] at h4
    have h5 : valuation k w * valuation k w⁻¹ ≤ valuation k w * 1 := by gcongr
    rw [h4, mul_one] at h5
    exact absurd (lt_of_le_of_lt h5 hw1) (lt_irrefl _)
  apply hnot
  rw [← hc]
  intro y _
  have := congrArg (fun χ : AddChar k Circle => (χ (w⁻¹ * y) : ℂ)) h
  simpa [toCirc_apply] using this

theorem irr_mat [CharZero k] {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (ψ0 : AddChar k ℂ) (hcont : Continuous ψ0) (hc : ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k])
    (W : Submodule ℂ (Matrix Y Y' k → ℂ)) (hW : W ≤ GlobalTheory.WeilM.SB (Matrix Y Y' k))
    (hT : ∀ Φ ∈ W, ∀ x, (fun t => Φ (t + x)) ∈ W)
    (hM : ∀ Φ ∈ W, ∀ z : Matrix Y Y' k, (fun t => ψ0 (∑ i, ∑ j, t i j * z i j) * Φ t) ∈ W)
    (Φ₀ : Matrix Y Y' k → ℂ) (h0 : Φ₀ ∈ W) (hne : Φ₀ ≠ 0) : W = GlobalTheory.WeilM.SB (Matrix Y Y' k) :=
  GlobalTheory.IrredSB.sb_irreducible k Y Y' (toCirc ψ0 hc) (toCirc_cont hc hcont) (toCirc_ne_one hc) W hW
    (fun Φ h x _ => hT Φ h x)
    (fun Φ h b _ => by
      have e : (fun t : Matrix Y Y' k => (toCirc ψ0 hc (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) =
          fun t => ψ0 (∑ i, ∑ j, t i j * b i j) * Φ t := by
        funext t
        simp only [toCirc_apply, mul_comm (b _ _)]
      rw [e]
      exact hM Φ h b)
    Φ₀ h0 hne

theorem modul_mem [CharZero k] {Y Y' : Type} [Fintype Y] [Fintype Y']
    (ψ0 : AddChar k ℂ) (hcont : Continuous ψ0) (hc : ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k])
    {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k)) (z : Matrix Y Y' k) :
    (fun t => ψ0 (∑ i, ∑ j, t i j * z i j) * Φ t) ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k) := by
  have h := GlobalTheory.IrredSB.modul_mem_SB (toCirc ψ0 hc) (toCirc_cont hc hcont) hΦ z
  have e : (fun t : Matrix Y Y' k => (toCirc ψ0 hc (GlobalTheory.IrredSB.pair z t) : ℂ) * Φ t) =
      fun t => ψ0 (∑ i, ∑ j, t i j * z i j) * Φ t := by
    funext t
    simp only [toCirc_apply, GlobalTheory.IrredSB.pair, mul_comm (z _ _)]
  rw [e] at h
  exact h

theorem sum_single_right {m m' : Type} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m']
    (x : Matrix m m' k) (r : m) (q : m') (c : k) :
    ∑ i, ∑ j, x i j * Matrix.single r q c i j = x r q * c := by
  have h := GlobalTheory.IrredSB.pair_single (k := k) r q c x
  simp only [GlobalTheory.IrredSB.pair] at h
  simp_rw [mul_comm (x _ _)]
  rw [h, mul_comm]

theorem sum_single_left {m m' : Type} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m']
    (z : Matrix m m' k) (r : m) (q : m') (c : k) :
    ∑ i, ∑ j, Matrix.single r q c i j * z i j = c * z r q :=
  GlobalTheory.IrredSB.pair_single (k := k) r q c z

end Char

end GlobalTheory.StoneVN

namespace GlobalTheory.StoneVN

theorem intertwiner_matrix : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hcont hc wT wM hTT hMM hTM hspan
  classical
  let χ : Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k → ℂ := fun x z => ψ0 (∑ i, ∑ j, x i j * z i j)
  let τ : Matrix (Fin n) (Fin d) k → ((κ → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) := fun Y => GlobalTheory.VacLoc.schrL ψ0 (wT Y)
  let μ : Matrix (Fin n) (Fin d) k → ((κ → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) := fun z => GlobalTheory.VacLoc.schrL ψ0 (wM z)
  have hτa : ∀ Y f, τ Y f = GlobalTheory.WeilM.schr ψ0 (wT Y) f := fun _ _ => rfl
  have hμa : ∀ z f, μ z f = GlobalTheory.WeilM.schr ψ0 (wM z) f := fun _ _ => rfl
  have hτ : ∀ x x' f, τ x (τ x' f) = τ (x + x') f := by
    intro x x' f
    rw [hτa, hτa, hτa, GlobalTheory.WeilM.schr_schr, hTT, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add]
  have hμ : ∀ z z' f, μ z (μ z' f) = μ (z + z') f := by
    intro z z' f
    rw [hμa, hμa, hμa, GlobalTheory.WeilM.schr_schr, hMM, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add]
  have hτμ : ∀ x z f, τ x (μ z f) = χ x z • μ z (τ x f) := by
    intro x z f
    rw [hτa, hμa, hμa, hτa, GlobalTheory.VacLoc.schr_comm, hTM]
  have hτ0 : ∀ f, τ 0 f = f := fun f => by rw [hτa, map_zero]; exact GlobalTheory.VacLoc.schr_zero_vec ψ0 f
  have hμ0 : ∀ f, μ 0 f = f := fun f => by rw [hμa, map_zero]; exact GlobalTheory.VacLoc.schr_zero_vec ψ0 f
  obtain ⟨f₀, hf₀SB, hf₀ne, hf₀T, hf₀M⟩ := GlobalTheory.T.exists_vacuum_transverseLagrangian_localField ψ0 hcont hc wT wM hTT hMM hTM hspan
  have hint : ∀ z : Matrix (Fin n) (Fin d) k,
      (∀ u : Matrix (Fin n) (Fin d) k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → ∀ r q, z r q ∈ 𝒪[k] := by
    intro z hz r q
    rw [← hc]
    intro y hy
    have h := hz (Matrix.single r q y) (fun r' q' => by
      rw [Matrix.single_apply]
      split_ifs
      · exact hy
      · exact zero_mem _)
    simp only [χ, sum_single_left] at h
    rwa [mul_comm] at h
  have hdual : ∀ x : Matrix (Fin n) (Fin d) k,
      (∀ z, (∀ u : Matrix (Fin n) (Fin d) k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → χ x z = 1) →
        ∀ r q, x r q ∈ 𝒪[k] := by
    intro x hx r q
    rw [← hc]
    intro y hy
    have h := hx (Matrix.single r q y) (fun u hu => by
      simp only [χ, sum_single_right]
      exact triv_int hc (mul_mem (hu r q) hy))
    simpa only [χ, sum_single_right] using h
  obtain ⟨Tm, hTmT, hTmM, hTm1, hTmspan⟩ := GlobalTheory.SchrodExist.exists_intertwiner_matrix k (Fin n) (Fin d)
    (Matrix (Fin n) (Fin d) k) χ
    (fun a b z => by
      simp only [χ, Matrix.add_apply, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul])
    (fun a z z' => by
      simp only [χ, Matrix.add_apply, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul])
    (fun z => by simp [χ]) (fun a => by simp [χ])
    (fun m hm z => ⟨(m : k)⁻¹ • z, by
      rw [smul_comm]
      exact GlobalTheory.SchrodExist.inv_nsmul_nsmul m hm z⟩)
    (fun m hm a b hab => by
      have e : m • a = m • b := hab
      rw [← GlobalTheory.SchrodExist.inv_nsmul_nsmul m hm a, e, GlobalTheory.SchrodExist.inv_nsmul_nsmul m hm b])
    hdual ((κ → k) → ℂ) τ μ hτ hμ hτμ hτ0 hμ0 f₀ (fun u hu => hf₀T u hu) (fun z hz => hf₀M z (hint z hz))

  have hrange : ∀ Φ, Tm Φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
    intro Φ
    refine (Submodule.span_le.2 ?_) (hTmspan Φ)
    rintro _ ⟨w, rfl⟩
    exact GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat ψ0 hcont _ _ (GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat ψ0 hcont _ _ hf₀SB)
  have hmodSB : ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), ∀ z,
      (fun t => χ t z * Φ t) ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) :=
    fun Φ hΦ z => modul_mem ψ0 hcont hc hΦ z
  have hind : Set.indicator {x : Matrix (Fin n) (Fin d) k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) ∈
      GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := GlobalTheory.LastTwoSteps.intInd_mem_SB (Fin n) (Fin d)

  have hinj : Function.Injective Tm := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hW := irr_mat ψ0 hcont hc ((LinearMap.ker Tm).map (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)).subtype)
      (by rintro _ ⟨Φ, _, rfl⟩; exact Φ.2)
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ x
        refine ⟨⟨fun t => Φ.1 (t + x), GlobalTheory.IrredSB.trans_mem_SB Φ.2 x⟩, ?_, rfl⟩
        have hΦ' : Tm Φ = 0 := hΦ
        show Tm _ = 0
        refine (hTmT x Φ _ (fun t => rfl)).trans ?_
        rw [hΦ', map_zero])
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ z
        refine ⟨⟨fun t => χ t z * Φ.1 t, hmodSB Φ.1 Φ.2 z⟩, ?_, rfl⟩
        have hΦ' : Tm Φ = 0 := hΦ
        show Tm _ = 0
        refine (hTmM z Φ _ (fun t => rfl)).trans ?_
        rw [hΦ', map_zero])
      Φ₀.1 ⟨Φ₀, hΦ₀, rfl⟩ (fun h => hΦ₀ne (Subtype.ext h))
    have h1 : Set.indicator {x : Matrix (Fin n) (Fin d) k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) ∈
        (LinearMap.ker Tm).map (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)).subtype := by
      rw [hW]; exact hind
    obtain ⟨Φ, hΦ, hΦe⟩ := h1
    have hΦ' : Tm Φ = 0 := hΦ
    exact hf₀ne ((hTm1 Φ hΦe).symm.trans hΦ')

  have hsurj : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ∃ Φ, Tm Φ = φ := by
    have hstab : ∀ φ ∈ LinearMap.range Tm, ∀ w, GlobalTheory.WeilM.schr ψ0 w φ ∈ LinearMap.range Tm := by
      rintro _ ⟨Φ, rfl⟩ w
      obtain ⟨Y, z, rfl⟩ := hspan w
      let Φ1 : GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := ⟨fun t => χ t z * Φ.1 t, hmodSB Φ.1 Φ.2 z⟩
      let Φ2 : GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := ⟨fun t => Φ1.1 (t + Y), GlobalTheory.IrredSB.trans_mem_SB Φ1.2 Y⟩
      have h1 : Tm Φ1 = μ z (Tm Φ) := hTmM z Φ Φ1 (fun t => rfl)
      have h2 : Tm Φ2 = τ Y (Tm Φ1) := hTmT Y Φ1 Φ2 (fun t => rfl)
      set c := ψ0 (⅟(2 : k) * ((wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2)) with hcdef
      have hne : c ≠ 0 := by
        intro h0
        have := AddChar.map_add_eq_mul ψ0 (⅟(2 : k) * ((wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2))
          (-(⅟(2 : k) * ((wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2)))
        rw [add_neg_cancel, AddChar.map_zero_eq_one, ← hcdef, h0, zero_mul] at this
        exact one_ne_zero this
      have e : GlobalTheory.WeilM.schr ψ0 (wT Y + wM z) (Tm Φ) = c⁻¹ • Tm Φ2 := by
        rw [h2, h1, hτa, hμa, GlobalTheory.WeilM.schr_schr, ← hcdef, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [e]
      exact (LinearMap.range Tm).smul_mem _ ⟨Φ2, rfl⟩
    have hW := GlobalTheory.T.schwartzBruhat_vector_irreducible_translations_characters ψ0 hcont hc (LinearMap.range Tm) (by rintro _ ⟨Φ, rfl⟩; exact hrange Φ)
      (fun φ h v => by
        have h' := hstab φ h (v, 0)
        have e : GlobalTheory.WeilM.schr ψ0 (v, 0) φ = fun x => φ (x + v) := by
          funext x; simp [GlobalTheory.WeilM.schr]
        rwa [e] at h')
      (fun φ h y => by
        have h' := hstab φ h (0, y)
        have e : GlobalTheory.WeilM.schr ψ0 (0, y) φ = fun x => ψ0 (x ⬝ᵥ y) * φ x := by
          funext x; simp [GlobalTheory.WeilM.schr]
        rwa [e] at h')
      f₀ ⟨⟨_, hind⟩, hTm1 ⟨_, hind⟩ rfl⟩ hf₀ne
    intro φ hφ
    rw [← hW] at hφ
    exact hφ

  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (GlobalTheory.WeilM.SB (κ → k))
  let e : GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) ≃ₗ[ℂ] GlobalTheory.WeilM.SB (κ → k) :=
    LinearEquiv.ofBijective (Tm.codRestrict (GlobalTheory.WeilM.SB (κ → k)) hrange)
      ⟨fun a b h => hinj (congrArg Subtype.val h), fun φ => by
        obtain ⟨Φ, hΦ⟩ := hsurj φ.1 φ.2
        exact ⟨Φ, Subtype.ext hΦ⟩⟩
  let ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) :=
    (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)).subtype ∘ₗ e.symm.toLinearMap ∘ₗ
      Submodule.linearProjOfIsCompl (GlobalTheory.WeilM.SB (κ → k)) C hC
  have hιTm : ∀ Φ, ι (Tm Φ) = Φ.1 := by
    intro Φ
    have h1 : Submodule.linearProjOfIsCompl (GlobalTheory.WeilM.SB (κ → k)) C hC (Tm Φ) = ⟨Tm Φ, hrange Φ⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨Tm Φ, hrange Φ⟩
    have h2 : e.symm ⟨Tm Φ, hrange Φ⟩ = Φ := e.symm_apply_eq.2 (Subtype.ext rfl)
    show (e.symm (Submodule.linearProjOfIsCompl (GlobalTheory.WeilM.SB (κ → k)) C hC (Tm Φ))).1 = Φ.1
    rw [h1, h2]
  refine ⟨ι, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨Φ, rfl⟩ := hsurj φ hφ
    rw [hιTm]; exact Φ.2
  · intro φ hφ φ' hφ' h
    obtain ⟨Φ, rfl⟩ := hsurj φ hφ
    obtain ⟨Φ', rfl⟩ := hsurj φ' hφ'
    rw [hιTm, hιTm] at h
    rw [Subtype.ext h]
  · intro Φ hΦ
    exact ⟨Tm ⟨Φ, hΦ⟩, hrange _, hιTm _⟩
  · intro Y φ hφ
    obtain ⟨Φ, rfl⟩ := hsurj φ hφ
    have h2 : Tm ⟨fun t => Φ.1 (t + Y), GlobalTheory.IrredSB.trans_mem_SB Φ.2 Y⟩ = τ Y (Tm Φ) := hTmT Y Φ _ (fun t => rfl)
    rw [hτa] at h2
    rw [← h2, hιTm, hιTm]
  · intro z φ hφ
    obtain ⟨Φ, rfl⟩ := hsurj φ hφ
    have h1 : Tm ⟨fun t => χ t z * Φ.1 t, hmodSB Φ.1 Φ.2 z⟩ = μ z (Tm Φ) := hTmM z Φ _ (fun t => rfl)
    rw [hμa] at h1
    rw [← h1, hιTm, hιTm]

end GlobalTheory.StoneVN
