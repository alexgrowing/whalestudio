import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSec_sum_smul_bc {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Frame X.Ψ r → ℂ) (hP : ∀ i, X.IsSec la (P i)) :
    X.IsSec la (fun x => ∑ i, a i * P i x) := by
  refine ⟨DifferentiableOn.fun_sum fun i _ => (hP i).1.const_mul _, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.1 x hx b hb]; ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.2 γ hγ x hx]; ring

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

open Classical in
theorem rdU_unfExt_of_isBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hBC : IsBC hle f' as fs) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) f' k x = ∑ i, σ' (as i) * rdU U (fs i) k x := by
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c' f' ((unfExt hle σ' hσ U).un k ⟨x, h⟩)) else 0) =
    ∑ i, σ' (as i) * (if h : x ∈ (U.X k).dom then toC (evR Xo c (fs i) (U.un k ⟨x, h⟩)) else 0)
  by_cases hx : x ∈ (U.X k).dom
  · simp only [dif_pos hx]
    exact @hBC (CAt σ') _ σ.toAlgebra σ'.toAlgebra hσ _
  · simp only [dif_neg hx, mul_zero, Finset.sum_const_zero]

theorem isUnf_unfExt (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) {U : Unf Xo c σ r} (hU : IsUnf U) : IsUnf (unfExt hle σ' hσ U) := by
  obtain rfl : σ = σ'.comp (incF c c' hle) := RingHom.ext fun a => (hσ a).symm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  refine ⟨h1, h2, fun y => ?_, h4, fun a n hd f' hf' k => ?_, h6⟩
  · exact h3 (FrPt.res hle (S := CAt σ') hσ y)
  · obtain ⟨m, as, fs, hfs, hBC⟩ := (secBC_and_cuspBC E H Dw l Xo c c' hle).1 a n f' hf'
    have e : rdU (unfExt hle σ' hσ U) f' k = fun x => ∑ i, σ' (as i) * rdU U (fs i) k x :=
      funext fun x => rdU_unfExt_of_isBC hle σ' hσ U hBC k x
    rw [e]
    exact isSec_sum_smul_bc (U.X k) (laU U a n k) _ _ fun i => h5 a n hd _ (hfs i) k

theorem rdU_unfExt_smul_rulBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) (u : c'.F) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) (u • rulBC hle f) k x = σ' u * rdU U f k x := by
  rw [map_smulₛₗ]
  have e := rdU_unfExt_of_isBC hle σ' hσ U (GlobalTheory.FieldBCModel.isBC_rulBC hle hf.1) k x
  simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_fin_one, map_one, one_mul] at e
  rw [← e]
  rfl

end Gen

theorem cXiAt_covBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (n r : ℕ) (c c' : Coeff l) (hle : c.F ≤ c'.F) (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n) (u : c'.F)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ)
    (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (h : CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0) :
    CXiAt V hr c'.F.val.toRingHom (covBC hle d u) (covUnf hle d u U₂) dict₂ io x₀ xi ((u : ℂ) * c0) := by
  obtain ⟨h1, h2, g, e, F, ik, φ, th, h3, h4, h5⟩ := h
  refine ⟨isUnf_unfExt (le_covCoeff hle d) _ (fun _ => rfl) h1, h2, g, e, F, ik, φ, th, h3, h4, fun h γ hm => ?_⟩
  have e1 := rdU_unfExt_smul_rulBC (le_covCoeff hle d)
    (c'.F.val.toRingHom.comp ((covBC hle d u).eF.symm : (covBC hle d u).c₂.F →+* c'.F)) (fun _ => rfl) U₂
    (show (covCoeff hle d).F from u) hs (dict₂ h).1 (dict₂ h).2
  refine e1.trans ?_
  rw [h5 h γ hm, ← mul_assoc]
  rfl

end GlobalTheory.OneMapAll
