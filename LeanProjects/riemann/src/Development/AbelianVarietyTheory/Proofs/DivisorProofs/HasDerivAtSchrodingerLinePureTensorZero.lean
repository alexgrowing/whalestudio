import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousBdGen

namespace SchrodingerLinePhase
section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SchrLine

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = fun x : InfiniteAdeleRing F =>
      ((fun v : {w : InfinitePlace F // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
    funext fun x => InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [h]
  exact Continuous.prodMk
    (continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1))
    (continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1))

def arch : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstA F).toRingHom

theorem arch_apply (x : AF F) : arch x = InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := rfl

theorem continuous_arch : Continuous (arch : AF F → mixedEmbedding.mixedSpace F) := by
  have h : (arch : AF F → mixedEmbedding.mixedSpace F) =
      fun x => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := funext fun x => arch_apply x
  rw [h]
  exact continuous_toMixed.comp continuous_fst

def coord (hF : IsTotallyReal F) (w : InfinitePlace F) : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (⟨w, hF.isReal w⟩ : {w : InfinitePlace F // w.IsReal})).comp
    (ContinuousLinearMap.fst ℝ _ _)

theorem re_eq_coord (hF : IsTotallyReal F) (x : Ainf F) (w : InfinitePlace F) :
    re x w = coord hF w (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  have h1 : re x w = (InfinitePlace.Completion.extensionEmbedding w (x w)).re := rfl
  have h2 : coord hF w (InfiniteAdeleRing.ringEquiv_mixedSpace F x) =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w) (x w) := rfl
  rw [h1, h2, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hF.isReal w), Complex.ofReal_re]

theorem arch_line {M : ℝ →+ VA F N} (hM : IsRealLine M) (p : VA F N →+ AF F) (hp : Continuous p) (s : ℝ) :
    arch (p (M s)) = s • arch (p (M 1)) := by
  let f : ℝ →+ mixedEmbedding.mixedSpace F := ((arch (F := F)).toAddMonoidHom).comp (p.comp M)
  have hf : Continuous f := continuous_arch.comp (hp.comp hM.1)
  have h := map_real_smul f hf s 1
  rw [smul_eq_mul, mul_one] at h
  exact h

theorem arch_fst {M : ℝ →+ VA F N} (hM : IsRealLine M) (l : Fin N) (s : ℝ) :
    arch ((M s).1 l) = s • arch ((M 1).1 l) :=
  arch_line hM ((Pi.evalAddMonoidHom (fun _ : Fin N => AF F) l).comp (AddMonoidHom.fst _ _))
    (by show Continuous (fun u : VA F N => u.1 l); exact (continuous_apply l).comp continuous_fst) s

theorem arch_snd {M : ℝ →+ VA F N} (hM : IsRealLine M) (l : Fin N) (s : ℝ) :
    arch ((M s).2 l) = s • arch ((M 1).2 l) :=
  arch_line hM ((Pi.evalAddMonoidHom (fun _ : Fin N => AF F) l).comp (AddMonoidHom.snd _ _))
    (by show Continuous (fun u : VA F N => u.2 l); exact (continuous_apply l).comp continuous_snd) s

def phaseForm (hF : IsTotallyReal F) (lam : InfinitePlace F → ℝ) (B : Fin N → mixedEmbedding.mixedSpace F) :
    (Fin N → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  ∑ w, ∑ l, (lam w * coord hF w (B l)) • (coord hF w).comp (ContinuousLinearMap.proj l)

theorem phaseForm_apply (hF : IsTotallyReal F) (lam : InfinitePlace F → ℝ)
    (B q : Fin N → mixedEmbedding.mixedSpace F) :
    phaseForm hF lam B q = ∑ w, lam w * ∑ l, coord hF w (q l) * coord hF w (B l) := by
  simp only [phaseForm, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem re_fstA_eq_coord_arch (hF : IsTotallyReal F) (u : AF F) (w : InfinitePlace F) :
    re (fstA F u) w = coord hF w (arch u) := by
  first | (rw [re_eq_coord hF, arch_apply]; rfl) | rw [re_eq_coord hF, arch_apply]

theorem phase_line [Invertible (2 : AF F)] (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ}
    {lam : InfinitePlace F → ℝ} (hlam : IsLam ψ lam) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (z : Fin N → AF F) (s : ℝ) :
    ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((s * phaseForm hF lam (fun l => arch ((M 1).2 l)) (fun l => arch (z l)) +
          s ^ 2 * ∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w *
            ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) : ℝ) : ℂ)) := by
  haveI : IsTotallyReal F := hF
  have hy0 : ∀ l, sndA F ((M s).2 l) = 0 := fun l => congrFun (hM.2 s).2 l
  have hsnd : sndA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) = 0 := by
    simp only [dotProduct, map_add, map_mul, map_sum, hy0, mul_zero, Finset.sum_const_zero, add_zero]
  have e1 : ∀ w, re (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) w =
      s * ∑ l, coord hF w (arch (z l)) * coord hF w (arch ((M 1).2 l)) +
        s ^ 2 * (coord hF w (arch ⅟(2 : AF F)) *
          ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) := by
    intro w
    have hxs : ∀ l, arch ((M s).1 l) = s • arch ((M 1).1 l) := fun l => arch_fst hM l s
    have hys : ∀ l, arch ((M s).2 l) = s • arch ((M 1).2 l) := fun l => arch_snd hM l s
    simp only [dotProduct, map_add, map_mul, map_sum, re_add, re_mul, re_sum, re_fstA_eq_coord_arch hF, hxs, hys,
      map_smul, smul_eq_mul]
    first
      | (simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
         refine Finset.sum_congr rfl fun l _ => ?_
         ring)
      | (have h1 : ∑ l, coord hF w (arch (z l)) * (s * coord hF w (arch ((M 1).2 l))) =
            s * ∑ l, coord hF w (arch (z l)) * coord hF w (arch ((M 1).2 l)) := by
           rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
         have h2 : ∑ l, s * coord hF w (arch ((M 1).1 l)) * (s * coord hF w (arch ((M 1).2 l))) =
            s ^ 2 * ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l)) := by
           rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
         rw [h1, h2]
         ring)
  have key : ∑ w, lam w * re (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) w =
      s * phaseForm hF lam (fun l => arch ((M 1).2 l)) (fun l => arch (z l)) +
        s ^ 2 * ∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w *
          ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) := by
    have hms : ∀ (c : ℝ) (h : InfinitePlace F → ℝ), c * ∑ w, h w = ∑ w, c * h w :=
      fun c h => Finset.mul_sum _ _ _
    rw [phaseForm_apply, hms s, hms (s ^ 2), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [e1, re_fstA_eq_coord_arch hF]
    ring
  calc ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))
      = ψ (pairA F (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) 0) := by
        first | (rw [← hsnd]; rfl) | rw [← hsnd]
    _ = _ := by
        have h2 := hlam.2 (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)))
        rw [key] at h2
        exact h2

private theorem hasDerivAt_exp_quadratic_mul_schwartz_line_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (q v : E) (a b : ℝ) (c : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((s * a + s ^ 2 * b : ℝ) : ℂ)) *
        (f (q + s • v) * c))
      ((2 * Real.pi * Complex.I * a * f q + fderiv ℝ f q v) * c) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s * a + s ^ 2 * b) a 0 := by
    have h := ((hasDerivAt_id' (0:ℝ)).mul_const a).add (((hasDerivAt_id' (0:ℝ)).pow 2).mul_const b)
    first
      | exact h.congr_deriv (by simp)
      | (convert h using 1 <;> simp)
  have h3 := (h1.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hl : HasDerivAt (fun s : ℝ => q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add q
  have hf0 : HasFDerivAt (⇑f) (fderiv ℝ f q) (q + (0:ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact f.hasFDerivAt q
  have h4 := (hf0.comp_hasDerivAt (0:ℝ) hl).mul_const c
  have h5 := h3.mul h4
  convert h5 using 1
  all_goals first
    | rfl
    | (simp only [Function.comp_apply]; done)
    | (simp; done)
    | (simp; ring)
    | (funext s; simp [Function.comp_apply])

end GlobalTheory.CompanionTheory.SchrLine

open GlobalTheory.CompanionTheory.SchrLine in

theorem GlobalTheory.CompanionTheory.SchrLine.exists_hasDerivAt_schr_pureA :
    ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F →
    IsCharAF F ψ → ∀ M : ℝ →+ VA F N, IsRealLine M →
    ∀ (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (Fin N → FiniteAdeleRing (𝓞 F) F) →
    ∃ f' : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ z : Fin N → AF F,
      HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) (GlobalTheory.WeilM.pureA F f' g z) 0 := by
  intro F _ _ N _ ψ hF hψ M hM f g hg
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hψ
  let L : (Fin N → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) •
      (Complex.ofRealCLM.comp (phaseForm hF lam (fun l => arch ((M 1).2 l))))
  let v : Fin N → mixedEmbedding.mixedSpace F := fun l => arch ((M 1).1 l)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (⇑L) f + LineDeriv.lineDerivOp v f, fun z => ?_⟩
  let q : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
  let zf : Fin N → FiniteAdeleRing (𝓞 F) F := fun i => (z i).2
  have hfun : ∀ s : ℝ, GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z =
      Complex.exp (2 * Real.pi * Complex.I * ((s * GlobalTheory.CompanionTheory.SchrLine.phaseForm hF lam (fun l => GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).2 l)) (fun l => GlobalTheory.CompanionTheory.SchrLine.arch (z l)) + s ^ 2 * (∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w * ∑ l, GlobalTheory.CompanionTheory.SchrLine.coord hF w (GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).1 l)) * GlobalTheory.CompanionTheory.SchrLine.coord hF w (GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).2 l)))) : ℝ) : ℂ)) *
        (f (q + s • v) * g zf) := by
    intro s
    have hq : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + (M s).1) i).1) = q + s • v := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (z i + (M s).1 i)) = q i + s • v i
      rw [map_add, map_add]
      first
        | exact congrArg₂ (· + ·) rfl (arch_fst hM i s)
        | (congr 1; exact arch_fst hM i s)
    have hz : (fun i => ((z + (M s).1) i).2) = zf := by
      funext i
      show sndA F (z i + (M s).1 i) = (z i).2
      rw [map_add, show sndA F ((M s).1 i) = 0 from congrFun (hM.2 s).1 i]
      exact add_zero _
    show ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) *
        (f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + (M s).1) i).1) *
          g (fun i => ((z + (M s).1) i).2)) = _
    rw [phase_line hF hlam hM z s, hq, hz]
  rw [show (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) = _ from funext hfun]
  refine (hasDerivAt_exp_quadratic_mul_schwartz_line_zero f q v _ _ (g zf)).congr_deriv ?_
  show _ = (SchwartzMap.smulLeftCLM ℂ (⇑L) f + LineDeriv.lineDerivOp v f) q * g zf
  rw [SchwartzMap.add_apply, SchwartzMap.smulLeftCLM_apply_apply L.hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  first
    | rfl
    | (simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply, smul_eq_mul]; rfl)
    | (simp [L, smul_eq_mul]; ring)

end
end

end SchrodingerLinePhase
section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical
theorem _root_.GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin N → FiniteAdeleRing (𝓞 F) F) → ∃ f' : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ z : Fin N → AF F, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) (GlobalTheory.WeilM.pureA F f' g z) 0 :=
  SchrodingerLinePhase.GlobalTheory.CompanionTheory.SchrLine.exists_hasDerivAt_schr_pureA

end
