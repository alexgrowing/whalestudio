import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_clm (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕)
    (hsb : φ ∈ SB _) (h : UA σ W.J) :
    ∃ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), L f = M.I om (pureA F f φ) h := by
  obtain ⟨h1, h2⟩ := dom_facts hB hp hD hφ hsb
  refine ⟨⟨⟨⟨fun f => M.I om (pureA F f φ) h, fun f f' => ?_⟩, fun c f => ?_⟩, h2 h⟩, fun _ => rfl⟩
  · have e : pureA F (f + f' : SInf F _) φ = pureA F f φ + pureA F f' φ := by
      funext x; simp [pureA, add_mul]
    unfold Model.I
    rw [e, ← integral_add ((h1 f).1 h) ((h1 f').1 h)]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_add hp (pureA_mem f hsb) (pureA_mem f' hsb) g h)
  · have e : pureA F (c • f : SInf F _) φ = c • pureA F f φ := by
      funext x; simp [pureA, mul_assoc]
    change M.I om (pureA F (c • f : SInf F _) φ) h = c * M.I om (pureA F f φ) h
    unfold Model.I
    rw [e, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_smul hp c (pureA_mem f hsb) g h)

theorem one_mem_UAt : (1 : UA σ X.J) ∈ UAt σ X (evI F) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem one_mem_Lines : (1 : Multiplicative ℝ →* UA σ X.J) ∈ Lines σ X := ⟨continuous_const, fun _ => one_mem_UAt⟩

end

theorem iDer_of (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) (hI : IInv) : IDer := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hD φ hφ hsb f hf
  obtain ⟨-, i2, i3⟩ := hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_UAt _ (hγ.2 (Multiplicative.ofAdd t))
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_Lines γ hγ T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have := hd L
    rw [hLf] at this
    convert this using 2 with t
    rw [hLf, ← (hT t).1.1 f φ hsb, i3]
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp _ (hγ.2 (Multiplicative.ofAdd t)) 1 one_mem_UAt
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ 1 one_mem_Lines T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, funext fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have h1 := hd L
    have h2 : (fun t => L (T t f)) = fun _ => M.I om (pureA F f φ) h := funext fun t => by
      rw [hLf, ← (hT t).1.1 f φ hsb, i2]
    rw [h2] at h1
    rw [← hLf]
    exact h1.unique (hasDerivAt_const _ _)

end PositivityTheory.ThKEst

end
