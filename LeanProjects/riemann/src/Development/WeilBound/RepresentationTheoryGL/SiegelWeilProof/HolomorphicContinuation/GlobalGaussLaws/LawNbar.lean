import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LawNbarA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open NbarH GaussH

theorem lawNbar_of (hU : UnipTau) (hW : WEx) (hF : FTfact) (hTI : TensInj) (hLNe : LNe) : LawNbar := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL y c hc hyc f hf
  have htc : |tLoc l τ| = cLoc l τ := abs_tLoc l τ
  have hc0 : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hC.hψ hC.hθ hC.hl τ))
  have hsq : (tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [← htc, sq_abs]
  have hsq' : (-tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [neg_sq, hsq]
  obtain ⟨w, hw⟩ := hW D n
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) hc'
  have hιy : ι y = w * ι yn * w⁻¹ := by rw [OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn]; group
  obtain ⟨κ, A, A', hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
  have hvS : IsSch (vac (n := n) ε (tLoc l τ) (cLoc l τ)) := gZSch V.rank n ε _ _ hc0 htc _ isSiegel_I
  set K : ℂ := ((Real.pi : ℂ) / (cLoc l τ)) ^ (V.rank * n) with hK
  have hK0 : K ≠ 0 := pow_ne_zero _ (div_ne_zero (by exact_mod_cast Real.pi_pos.ne') (by exact_mod_cast hc0.ne'))
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
  have kA := hFT (A' Ψ) hA'Ψ

  have hid : ∀ g (hg : IsSch g), tens θ τ fr g Ψ =
      tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ) (fun v => κ⁻¹ * ftLoc ε (-tLoc l τ) g v) u) (A (A' Ψ)) := by
    intro g hg
    have h1 : ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ =
        ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) g u) (A' Ψ), hA'Ψ.2 _ ((hFΨ g hg).2.1)⟩ :=
      Subtype.ext (hFΨ g hg).2.2.2
    have h2 := (kA.2.2 _ ((hFΨ g hg).2.1)).2.2.1
    have h3 : ω w (ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩) = ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h1] at h3
    rw [← h2, h3]
  have hAA : ∀ x, A (A' Ψ) x = (K * K)⁻¹ * Ψ x := by
    intro x
    have h := congrFun (hid _ hvS) x
    simp only [tens, ftLoc_vac ε _ _ _ hc0 hsq', ftLoc_const_mul', ftLoc_vac ε _ _ _ hc0 hsq] at h
    have hv0 : vac (n := n) ε (tLoc l τ) (cLoc l τ) (fr⁻¹ * compAt θ τ x) ≠ 0 := Complex.exp_ne_zero _
    have hκ' : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
    field_simp at h
    rw [h, hK]
    field_simp

  rw [← hL.2 y Ψ hΨ f hf]
  have hE : IsSch (fun u => chN ε (tLoc l τ) (-c) u * (κ⁻¹ * ftLoc ε (-tLoc l τ) f u)) :=
    OpGenAH.isSch_phase ε (tLoc l τ) (-c) hc' (hFΨ f hf).2.1
  have s1 : ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
      ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ), hA'Ψ.2 _ ((hFΨ f hf).2.1)⟩ :=
    Subtype.ext (hFΨ f hf).2.2.2
  have s2 : ω (ι yn) ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ), hA'Ψ.2 _ ((hFΨ f hf).2.1)⟩ =
      ⟨tens θ τ fr (fun u => chN ε (tLoc l τ) (-c) u * (κ⁻¹ * ftLoc ε (-tLoc l τ) f u)) (A' Ψ), hA'Ψ.2 _ hE⟩ := by
    apply Subtype.ext
    funext x
    rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC yn (-c) hc' hyn]
    simp only [tens, chN, mul_assoc]
  have s3 := (kA.2.2 _ hE).2.2.1
  rw [hιy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, s1, s2, s3]
  funext x
  simp only [tens]
  rw [hAA x]
  have hKK : ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) = (K * K)⁻¹ := by
    rw [hK, htc, ← pow_two, ← pow_mul, ← inv_pow, inv_div]
    push_cast
    ring_nf
  rw [hKK]
  have hκ' : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  have e : (fun v => chN ε (tLoc l τ) (-c) v * (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) =
      fun v => κ⁻¹ * (chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v) := by funext v; ring
  rw [e, ftLoc_const_mul']
  linear_combination (ftLoc ε (tLoc l τ) (fun v => chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v)
    (fr⁻¹ * compAt θ τ x)) * (K * K)⁻¹ * Ψ x * hκ'

end PositivityTheory.Rg.Sw.Glob
