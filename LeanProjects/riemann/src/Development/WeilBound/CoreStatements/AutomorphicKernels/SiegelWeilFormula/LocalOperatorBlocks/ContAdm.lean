import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OmSch
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.GoodAwayEx
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EqZeroOfEvalReal

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

open Complex in

theorem tg_exp : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => cexp (I * t)) = fun t : ℝ => I ^ n * cexp (I * t) := by
    intro n
    induction n with
    | zero =>
      funext t
      simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have h1 : HasDerivAt (fun s : ℝ => I * (s : ℂ)) I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul I
      have h2 : HasDerivAt (fun s : ℝ => I ^ n * cexp (I * s)) (I ^ n * (cexp (I * t) * I)) t :=
        h1.cexp.const_mul _
      rw [h2.deriv]
      ring
  refine ⟨?_, fun n => ⟨0, 1, fun t => ?_⟩⟩
  · exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd n, norm_mul, norm_pow, Complex.norm_I, one_pow,
      mul_comm I, Complex.norm_exp_ofReal_mul_I]
    simp

section admitted

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def rhoL (ψ : AddChar (AF F) ℂ) (p : (κ → AF F) × (κ → AF F)) : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun := schr ψ p
  map_add' φ φ' := by funext x; simp [schr, mul_add]
  map_smul' a φ := by funext x; simp [schr]; ring

def arc (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1

def phz (p : (κ → AF F) × (κ → AF F)) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (∑ i, y i * arc F p.2 i + InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1) : ℝ) : ℂ))

theorem phz_tg (p : (κ → AF F) × (κ → AF F)) : (phz F p).HasTemperateGrowth := by
  have hlin : Function.HasTemperateGrowth (fun y : κ → mixedEmbedding.mixedSpace F =>
      ∑ i, y i * arc F p.2 i + InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1) := by
    have hi : ∀ i, Function.HasTemperateGrowth (fun y : κ → mixedEmbedding.mixedSpace F => y i * arc F p.2 i) :=
      fun i => ((ContinuousLinearMap.mul ℝ (mixedEmbedding.mixedSpace F)).flip (arc F p.2 i) ∘L
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => mixedEmbedding.mixedSpace F) i).hasTemperateGrowth
    fun_prop
  have hT : Function.HasTemperateGrowth (fun z : mixedEmbedding.mixedSpace F =>
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z) :=
    (LinearMap.toContinuousLinearMap (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).hasTemperateGrowth
  have hg : Function.HasTemperateGrowth (fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * (s : ℂ))) := by
    have h := tg_exp.comp (((-(2 * Real.pi)) • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth)
    convert h using 1
    funext s
    simp only [Function.comp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    push_cast
    ring_nf
  exact hg.comp (hT.comp hlin)

theorem schr_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (p : (κ → AF F) × (κ → AF F))
    (hp : ∀ i, (p.1 i).2 = 0 ∧ (p.2 i).2 = 0) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    schr ψ p (pureA F f g) = pureA F (fun y => phz F p y * f (y + arc F p.1)) g := by
  funext x
  obtain ⟨-, -, hinf⟩ := hψ
  have hs1 : ∀ y z : κ → AF F, (y ⬝ᵥ z).1 = ∑ i, (y i).1 * (z i).1 := fun y z =>
    map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (fun i => y i * z i) Finset.univ
  have hs2 : ∀ y z : κ → AF F, (y ⬝ᵥ z).2 = ∑ i, (y i).2 * (z i).2 := fun y z =>
    map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (fun i => y i * z i) Finset.univ
  have hsnd : (fun i => ((x + p.1) i).2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (p.1 i).2 = (x i).2
    rw [(hp i).1, add_zero]
  have hfst : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p.1) i).1) =
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + arc F p.1 := by
    funext i
    exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (p.1 i).1
  have ha2 : (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).2 = 0 := by
    show (x ⬝ᵥ p.2).2 + (⅟(2 : AF F)).2 * (p.1 ⬝ᵥ p.2).2 = 0
    rw [hs2, hs2]
    simp [(hp _).2]
  have hat : At (evI F) (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) := by
    intro u hu
    have hu1 : u.1 = 0 :=
      (map_eq_zero_iff (InfiniteAdeleRing.ringEquiv_mixedSpace F) (RingEquiv.injective _)).mp hu
    rw [smul_eq_mul]
    refine Prod.ext ?_ ?_
    · show u.1 * (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).2 = 0
      rw [ha2, mul_zero]
  have htr : evI F (x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) =
      ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * arc F p.2 i +
        InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x ⬝ᵥ p.2).1 + (⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)).1) = _
    rw [map_add, hs1, map_sum]
    simp only [map_mul, arc]
  simp only [schr, pureA]
  rw [hinf _ hat, hsnd, hfst, htr]
  simp only [phz]
  ring

theorem rho_adm (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ)
    (p : (κ → AF F) × (κ → AF F)) (hp : ∀ i, (p.1 i).2 = 0 ∧ (p.2 i).2 = 0) :
    l ∘ₗ rhoL F ψ p ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T0, hT0⟩ := hl g hg
  have htr : Function.HasTemperateGrowth (fun y : κ → mixedEmbedding.mixedSpace F => y + arc F p.1) := by
    fun_prop
  have hanti : AntilipschitzWith 1 (fun y : κ → mixedEmbedding.mixedSpace F => y + arc F p.1) :=
    (IsometryEquiv.addRight (arc F p.1)).isometry.antilipschitz
  let S : 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) →L[ℂ] 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) :=
    (SchwartzMap.smulLeftCLM ℂ (phz F p)).comp (SchwartzMap.compCLMOfAntilipschitz ℂ htr hanti)
  refine ⟨T0.comp S, fun f => ?_⟩
  have hf : (⇑(S f)) = fun y => phz F p y * f (y + arc F p.1) := by
    funext y
    simp [S, SchwartzMap.smulLeftCLM_apply_apply (phz_tg F p), smul_eq_mul]
  rw [LinearMap.comp_apply]
  show l (schr ψ p (pureA F f g)) = _
  rw [schr_pureA F ψ hψ p hp, ← hf, hT0]
  rfl

end admitted

end PositivityTheory.SiegelWeilFormula.KLI

end
