import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.IndOSelf

open ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

local instance borelFvAt (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

theorem mem_int_iff {v : Pl F} (x : Fv F v) : x ∈ 𝒪[Fv F v] ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem exists_nat_mul_mem (v : Pl F) (x : Fv F v) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : Fv F v) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · have h1 := congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc
    rw [map_mul, map_natCast] at h1
    rw [← h1, mul_assoc, mul_comm _ x]
    exact mul_mem (HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v c) hbx

theorem norm_psiAt (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) (x : Fv F v) :
    ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := by
  obtain ⟨N, hN, hx⟩ := exists_nat_mul_mem v x
  have h1 : GlobalTheory.LatVac.psiAt ψ v ((N : Fv F v) * x) = 1 := by
    have := ((hψ 1).2 (one_mem _)) _ hx
    rwa [one_mul] at this
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  exact Complex.norm_eq_one_of_pow_eq_one h1 hN

def psiC (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) : AddChar (Fv F v) Circle where
  toFun x := ⟨GlobalTheory.LatVac.psiAt ψ v x, mem_sphere_zero_iff_norm.2 (norm_psiAt ψ v hψ x)⟩
  map_zero_eq_one' := Subtype.ext (AddChar.map_zero_eq_one _)
  map_add_eq_mul' x y := Subtype.ext (AddChar.map_add_eq_mul _ x y)

theorem coe_psiC (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) (x : Fv F v) :
    ((psiC ψ v hψ x : Circle) : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := rfl

theorem hasConductor_psiC (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) :
    GlobalTheory.SplitWeil.HasConductor (psiC ψ v hψ) 1 := by
  intro x
  have e1 : ∀ y, psiC ψ v hψ y = 1 ↔ GlobalTheory.LatVac.psiAt ψ v y = 1 := fun y =>
    ⟨fun h => by rw [← coe_psiC ψ v hψ, h]; rfl, fun h => Circle.ext (by rw [coe_psiC ψ v hψ, h]; rfl)⟩
  rw [Units.val_one, map_one, ← Valuation.mem_integer_iff, mem_int_iff, ← hψ x]
  simp only [e1]
  constructor
  · intro h y hy
    apply h
    rw [map_mul]
    have : valuation (Fv F v) y ≤ 1 := (Valuation.mem_integer_iff _ _).1 ((mem_int_iff y).2 hy)
    exact mul_le_of_le_one_right' this
  · intro h y hy
    by_cases hx : x = 0
    · subst hx
      rw [map_zero, le_zero_iff, map_eq_zero] at hy
      subst hy
      exact AddChar.map_zero_eq_one _
    · have hyx : y / x ∈ v.adicCompletionIntegers F := by
        rw [← mem_int_iff, Valuation.mem_integer_iff, map_div₀,
          div_le_one₀ (by rw [zero_lt_iff, Ne, map_eq_zero]; exact hx)]
        exact hy
      have := h _ hyx
      rwa [mul_div_cancel₀ _ hx] at this

theorem indO_mem_SB (v : Pl F) (κ : Type) [Fintype κ] : GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) := by
  set S : Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F} with hSdef
  have hS : S = Set.univ.pi fun _ => ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := by
    ext x; simp [S, mem_int_iff]
  have hc : IsCompact S := hS ▸ isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int _
  have ho : IsOpen S := hS ▸ isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_int _
  have hcl : IsClosed S := hc.isClosed
  have hind : GlobalTheory.SympChange.indO (κ := κ) v = S.indicator 1 := rfl
  rw [hind]
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ S
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem exists_selfDual (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) :
    ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := by
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (Fv F v)
  have h := GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol ν (hasConductor_psiC ψ v hψ) hν
  exact ⟨ν, h.1, fun f hf => h.2 f hf⟩

theorem isUnitVol_measV (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) :
    GlobalTheory.SplitWeil.IsUnitVol (measV ψ v) := by
  have hex := exists_selfDual ψ v hψ
  have hm : measV ψ v = hex.choose := by simp only [measV, dif_pos hex]
  have hs := hex.choose_spec
  rw [hm]
  exact (GlobalTheory.SplitWeil.isUnitVol_iff_isSelfDual (hasConductor_psiC ψ v hψ) _).2 ⟨hs.1, fun f hf => hs.2 f hf⟩

theorem fourV_indO (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) (κ : Type) [Fintype κ] :
    fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v := by
  classical
  have hU := isUnitVol_measV ψ v hψ
  haveI := hU.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have hball : GlobalTheory.SplitWeil.cball (1 : (Fv F v)ˣ) = ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := by
    ext x; simp [GlobalTheory.SplitWeil.cball, Valuation.mem_integer_iff]
  have hbox : GlobalTheory.SplitWeil.FourierPi.box κ (1 : (Fv F v)ˣ) = {x | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    ext x; simp [GlobalTheory.SplitWeil.FourierPi.box, hball, ← mem_int_iff]
  have hvol : (Measure.pi fun _ : κ => measV ψ v).real (GlobalTheory.SplitWeil.FourierPi.box κ 1) = 1 := by
    simp [Measure.real, GlobalTheory.SplitWeil.FourierPi.box, Measure.pi_pi, hball, hU.2]
  funext y
  have h := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi (Measure.pi fun _ : κ => measV ψ v)
    (hasConductor_psiC ψ v hψ) 1 y
  rw [mul_inv_cancel, hvol, hbox] at h
  exact h

theorem indO_self_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F)
    (κ : Type) [Fintype κ], GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) ∧
    (PsiUnr ψ v → fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v) := by
  intro F _ _ ψ _ v κ _
  exact ⟨indO_mem_SB v κ, fun h => fourV_indO ψ v h κ⟩

end GlobalTheory.WeylFour.IndOSelf
