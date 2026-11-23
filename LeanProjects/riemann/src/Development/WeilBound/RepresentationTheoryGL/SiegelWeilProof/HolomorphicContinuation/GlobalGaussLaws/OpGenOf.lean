import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenC

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def LeviTau : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∃ (C : ℂ) (A : Mx D n n),
      compAt θ τ A = a ∧ (∀ τ', τ' ≠ τ → compAt θ τ' A = 1) ∧ A.map (finPart D) = 1 ∧
      ∀ (Φ : schwartzA θ V.rank n) (x : Mx D V.rank n), (ω (ι y) Φ).1 x = C * Φ.1 (HMul.hMul x A : Mx D V.rank n)

theorem opGen_of' (hU : UnipTau) (hLv : LeviTau) (hW : WEx) (hS : SchOps) (hF : FTfact) : OpGen := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y hy
  obtain ⟨hadd, hcmul, hrmul, hphase, f₁, hf₁, hf₁0⟩ := hS V.rank n
  have unip : ∀ (b : Matrix (Fin n) (Fin n) ℂ) (y' : GR n), bᴴ = b → mR y' = nU b →
      ∀ (Ψ' : Mx D V.rank n → ℂ) (hΨ' : AwayCls θ τ fr Ψ') (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f),
      (ω (ι y') ⟨tens θ τ fr f Ψ', hΨ'.2 f hf⟩).1 =
        tens θ τ fr (fun u => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace) * f u) Ψ' := by
    intro b y' hb hy' Ψ' hΨ' f hf
    funext x
    rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y' b hb hy']
    show _ * tens θ τ fr f Ψ' x = _
    simp only [tens]
    ring
  rcases hy with ⟨b, hb, hyb⟩ | ⟨c, hc, hyc⟩ | ⟨a, ha, hya⟩
  · exact ⟨fun f u => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace) * f u,
      fun f hf => hphase ε (tLoc l τ) b f hb hf, fun Ψ hΨ f hf => unip b y hb hyb Ψ hΨ f hf⟩
  · obtain ⟨w, hw⟩ := hW D n
    have hcn : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
    obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) hcn
    have hconj := OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn
    have hy' : ι y = w * ι yn * w⁻¹ := by rw [hconj]; group
    obtain ⟨κ, Aop, A'op, hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
    have hsch : ∀ f, IsSch f → IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u) ∧
        IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) := fun f hf =>
      ⟨((hFT 0 (OG.awayCls_zero τ fr)).2.2 f hf).1, ((hFT 0 (OG.awayCls_zero τ fr)).2.2 f hf).2.1⟩
    have step : ∀ (Ψ : Mx D V.rank n → ℂ) (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ)
          (fun u' => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u').trace) *
            (κ⁻¹ * ftLoc ε (-tLoc l τ) f u')) u) (Aop (A'op Ψ)) ∧
        tens θ τ fr f Ψ = tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ)
          (fun u' => κ⁻¹ * ftLoc ε (-tLoc l τ) f u') u) (Aop (A'op Ψ)) := by
      intro Ψ hΨ f hf
      obtain ⟨-, hA', hfs⟩ := hFT Ψ hΨ
      obtain ⟨-, s2, -, e2⟩ := hfs f hf
      obtain ⟨-, -, hfs'⟩ := hFT (A'op Ψ) hA'
      have sP := hphase ε (tLoc l τ) (-c) _ hcn s2
      have e1 : ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
          ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A'op Ψ), hA'.2 _ s2⟩ := Subtype.ext e2
      have e4 : ω (ι yn) ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A'op Ψ), hA'.2 _ s2⟩ =
          ⟨_, hA'.2 _ sP⟩ := Subtype.ext (unip (-c) yn hcn hyn (A'op Ψ) hA' _ s2)
      obtain ⟨-, -, e5, -⟩ := hfs' _ sP
      obtain ⟨-, -, e6, -⟩ := hfs' _ s2
      constructor
      · rw [hy', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, e4]
        exact e5
      · have hid : ω w (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩) = ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [e1] at hid
        rw [← e6, hid]
    refine ⟨fun g u => (κ * ftLoc ε (tLoc l τ) (fun u' => κ⁻¹ * ftLoc ε (-tLoc l τ) f₁ u') 0)⁻¹ *
        (κ * ftLoc ε (tLoc l τ) (fun u' => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u').trace) *
          (κ⁻¹ * ftLoc ε (-tLoc l τ) g u')) u), fun g hg => ?_, fun Ψ hΨ f hf => ?_⟩
    · exact hcmul _ _ (hsch _ (hphase ε (tLoc l τ) (-c) _ hcn (hsch g hg).2)).1
    · set c₀ := κ * ftLoc ε (tLoc l τ) (fun u' => κ⁻¹ * ftLoc ε (-tLoc l τ) f₁ u') 0 with hc₀
      have hAA : AwayCls θ τ fr (Aop (A'op Ψ)) := (hFT (A'op Ψ) (hFT Ψ hΨ).2.1).1
      have hrel : ∀ x, Ψ x = c₀ * Aop (A'op Ψ) x := by
        intro x
        obtain ⟨x', hx1, hx2, hx3⟩ := OG.exists_slice hC.hθ τ x (0 : Matrix (Fin V.rank) (Fin n) ℂ)
        have e := congrFun (step Ψ hΨ f₁ hf₁).2 x'
        have hz0 : fr⁻¹ * compAt θ τ x' = (0 : Fin V.rank → Fin n → ℂ) := by
          rw [hx1]; exact Matrix.mul_zero _
        simp only [tens] at e
        rw [hz0, hf₁0, one_mul] at e
        rw [← hΨ.1 x' x hx2 hx3, ← hAA.1 x' x hx2 hx3]
        exact e
      by_cases hz : c₀ = 0
      · have hΨ0 : ∀ x, Ψ x = 0 := fun x => by rw [hrel x, hz, zero_mul]
        have h00 : (⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ : schwartzA θ V.rank n) = 0 := by
          apply Subtype.ext
          funext x
          simp [tens, hΨ0 x]
        rw [h00, map_zero]
        funext x
        simp [tens, hΨ0 x]
      · rw [(step Ψ hΨ f hf).1]
        funext x
        simp only [tens]
        rw [hrel x]
        field_simp
  · obtain ⟨C, A, hA1, hA2, hA3, hact⟩ := hLv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
    refine ⟨fun f u => C * f (Matrix.of u * a), fun f hf => hcmul C _ (hrmul a f ha hf), ?_⟩
    intro Ψ hΨ f hf
    funext x
    rw [hact]
    have hcomp : compAt θ τ (HMul.hMul x A : Mx D V.rank n) = compAt θ τ x * a := by
      rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA1]
    have hPsi : Ψ (HMul.hMul x A : Mx D V.rank n) = Ψ x := by
      apply hΨ.1
      · intro τ' hτ'
        rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA2 τ' hτ', Matrix.mul_one]
      · rw [Matrix.map_mul, hA3, Matrix.mul_one]
    show C * tens θ τ fr f Ψ (HMul.hMul x A : Mx D V.rank n) = tens θ τ fr (fun u => C * f (Matrix.of u * a)) Ψ x
    simp only [tens]
    rw [hcomp, hPsi, ← Matrix.mul_assoc, mul_assoc]
    rfl

end PositivityTheory.Rg.Sw.Glob
