import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenOps
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReTraceEq
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct FourierTransform
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OpCLMH

variable {D : D7} {n : ℕ}

def HasCLM {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ι : GR n →* G D n) (y : GR n) : Prop :=
  ∃ L : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
    ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ),
      (ω (ι y) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩).1 = tens θ τ fr (L S) Ψ

theorem hasCLM_mul {θ : InfFam D} {V : HSp D} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n} {y₁ y₂ : GR n} (h₁ : HasCLM ω τ fr ι y₁)
    (h₂ : HasCLM ω τ fr ι y₂) : HasCLM ω τ fr ι (y₁ * y₂) := by
  obtain ⟨L₁, hL₁⟩ := h₁
  obtain ⟨L₂, hL₂⟩ := h₂
  refine ⟨L₁.comp L₂, fun Ψ hΨ S => ?_⟩
  have e2 : ω (ι y₂) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩ = ⟨tens θ τ fr (L₂ S) Ψ, hΨ.2 _ ⟨L₂ S, rfl⟩⟩ :=
    Subtype.ext (hL₂ Ψ hΨ S)
  rw [map_mul, map_mul, Module.End.mul_apply, e2, hL₁ Ψ hΨ (L₂ S)]
  rfl

section Gens

variable {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}

theorem hasCLM_n (hU : UnipTau) (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ)
    (hb : bᴴ = b) (hyb : mR y = nU b) : HasCLM ω τ fr ι y := by
  refine ⟨(SchwartzMap.smulLeftCLM ℂ
    (fun u : Fin V.rank → Fin n → ℂ => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace))).restrictScalars ℝ,
    fun Ψ hΨ S => ?_⟩
  funext x
  rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y b hb hyb]
  have key : ∀ u : Fin V.rank → Fin n → ℂ, (SchwartzMap.smulLeftCLM ℂ
      (fun u : Fin V.rank → Fin n → ℂ => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace)) S) u =
      Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace) * S u := fun u => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (OpGenAH.hasTemperateGrowth_phase ε (tLoc l τ) b hb), smul_eq_mul]
  simp only [tens, ContinuousLinearMap.coe_restrictScalars']
  rw [key (fr⁻¹ * compAt θ τ x)]
  ring

theorem hasCLM_m (hLv : LeviTau) (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n)
    (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hya : mR y = mM a) : HasCLM ω τ fr ι y := by
  obtain ⟨C, Am, hA1, hA2, hA3, hAf⟩ := hLv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
  refine ⟨(C • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (OpGenAH.rmulEquiv (m := V.rank) a ha)).restrictScalars ℝ,
    fun Ψ hΨ S => ?_⟩
  funext x
  rw [hAf]
  have hx1 : compAt θ τ (HMul.hMul x Am : Mx D V.rank n) = compAt θ τ x * a := by
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA1]
  have hx2 : Ψ (HMul.hMul x Am : Mx D V.rank n) = Ψ x :=
    hΨ.1 _ _ (fun τ' h => by rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA2 τ' h, Matrix.mul_one])
      (by rw [Matrix.map_mul, hA3, Matrix.mul_one])
  simp only [tens]
  rw [hx1, hx2]
  have hm : (fr⁻¹ * (compAt θ τ x * a) : Matrix (Fin V.rank) (Fin n) ℂ) =
      (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) * a := by
    rw [← Matrix.mul_assoc]
    rfl
  have e1 : (⇑S) (fr⁻¹ * (compAt θ τ x * a)) = S (Matrix.of (fr⁻¹ * compAt θ τ x) * a) := congrArg S hm
  rw [e1]
  change C * (S _ * Ψ x) = (C * S (OpGenAH.rmulEquiv (m := V.rank) a ha (fr⁻¹ * compAt θ τ x))) * Ψ x
  rw [mul_assoc]
  rfl

theorem hasCLM_nbar (hU : UnipTau) (hW : WEx) (hS : SchOps) (hF : FTfact) (hl0 : tLoc l τ ≠ 0)
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c)
    (hyc : mR y = nbar c) : HasCLM ω τ fr ι y := by
  obtain ⟨κ, γ, hκ, -, -, hform⟩ := GenOpsH.gen_nbar hU hW hS hF hC y c hc hyc
  obtain ⟨c1, -, h1⟩ := FTD.ftLoc_eq (n := n) ε (tLoc l τ) hl0
  obtain ⟨c2, -, h2⟩ := FTD.ftLoc_eq (n := n) ε (-tLoc l τ) (neg_ne_zero.2 hl0)
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  let FT1 : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℂ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ :=
    (κ * c1) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (FTD.Mt ε (tLoc l τ) hl0)).comp
      ((SchwartzMap.fourierTransformCLM ℂ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ FTD.Lc.symm))
  let FT2 : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℂ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ :=
    (κ⁻¹ * c2) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (FTD.Mt ε (-tLoc l τ) (neg_ne_zero.2 hl0))).comp
      ((SchwartzMap.fourierTransformCLM ℂ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ FTD.Lc.symm))
  let Em : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℂ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ
      (fun u : Fin V.rank → Fin n → ℂ => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u).trace))
  have hFT1 : ∀ S u, FT1 S u = κ * ftLoc ε (tLoc l τ) S u := by
    intro S u
    rw [h1]
    simp only [FT1, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.smul_apply,
      SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, SchwartzMap.fourierTransformCLM_apply,
      smul_eq_mul]
    push_cast
    ring
  have hFT2 : ∀ S u, FT2 S u = κ⁻¹ * ftLoc ε (-tLoc l τ) S u := by
    intro S u
    rw [h2]
    simp only [FT2, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.smul_apply,
      SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, SchwartzMap.fourierTransformCLM_apply,
      smul_eq_mul]
    push_cast
    ring
  have hEm : ∀ S u, Em S u =
      Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u).trace) * S u := by
    intro S u
    simp only [Em, SchwartzMap.smulLeftCLM_apply_apply (OpGenAH.hasTemperateGrowth_phase ε _ (-c) hc'), smul_eq_mul]
  refine ⟨(γ⁻¹ • FT1.comp (Em.comp FT2)).restrictScalars ℝ, fun Ψ hΨ S => ?_⟩
  rw [hform Ψ hΨ (⇑S) ⟨S, rfl⟩]
  congr 1
  funext u
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, hFT1]
  congr 3
  funext v
  rw [hEm, hFT2]

end Gens

end PositivityTheory.Rg.Sw.Glob.OpCLMH

namespace PositivityTheory.Rg.Sw.Glob

theorem opCLM_of (hU : UnipTau) (hLv : LeviTau) (hW : WEx) (hS : SchOps) (hF : FTfact) (hD : Decomp) (hN : LNe) :
    OpCLM := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y
  have hl0 : tLoc l τ ≠ 0 := by
    unfold tLoc
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (hN D ψ θ l hC.hψ hC.hθ hC.hl τ)
  obtain ⟨y₁, y₂, y₃, y₄, rfl, ⟨t, ht⟩, ⟨c, hc, hc'⟩, ⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hD n y
  have h1 : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  exact OpCLMH.hasCLM_mul (OpCLMH.hasCLM_mul (OpCLMH.hasCLM_mul (OpCLMH.hasCLM_n hU hC y₁ _ h1 ht)
    (OpCLMH.hasCLM_nbar hU hW hS hF hl0 hC y₂ c hc hc')) (OpCLMH.hasCLM_m hLv hC y₃ a ha ha'))
    (OpCLMH.hasCLM_n hU hC y₄ b hb hb')

end PositivityTheory.Rg.Sw.Glob
