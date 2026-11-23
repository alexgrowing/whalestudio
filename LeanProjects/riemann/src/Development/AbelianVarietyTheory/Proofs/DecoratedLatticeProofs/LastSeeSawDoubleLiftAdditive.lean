import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSmallPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def ker {A S X : HSp D} (oma : Om A S) (omX : Om S X) (C : WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ℂ :=
  omX (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0

theorem biLift_eq {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ C h₂ = ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) ∂vS.μ := rfl

section

variable {A S X : HSp D} {χA χS χS' χX : (AE D)ˣ →* Circle} {oma : Om A S} {omX : Om S X}

theorem ker_sum {n : ℕ} (C : Fin n → WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX (∑ i, C i) h₀ h₁ h₂ = ∑ i, ker oma omX (C i) h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (∑ i, C i) u v) 0) = ∑ i, fun v => oma (h₀, h₁) (fun u => C i u v) 0 := by
    funext v
    have e : (fun u => (∑ i, C i) u v) = ∑ i, fun u => C i u v := by
      funext u; simp only [Finset.sum_apply]
    rw [e, map_sum]; simp only [Finset.sum_apply]
  rw [e1, map_sum]; simp only [Finset.sum_apply]

theorem ker_cont (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) :
    Continuous fun x : GA D A × GA D S × GA D X => ker oma omX C x.1 x.2.1 x.2.2 := by
  have := (hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).2.2.2
  exact this.comp (by fun_prop : Continuous fun x : GA D A × GA D S × GA D X =>
    ((x.1, x.2.1), (x.2.1, x.2.2), ((0 : WO A S), (0 : WO S X))))

theorem ker_left (hwa : IsWeilDatumO ψ A S χA χS oma) {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C)
    {γ : GA D A} (hγ : γ ∈ GQ A) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX C (γ * h₀) h₁ h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (γ * h₀, h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((γ * h₀, h₁) : GA D A × GA D S) = (γ, 1) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut γ hγ 1 (one_mem _) _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  rw [e1]

theorem ker_mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {γ : GA D S} (hγ : γ ∈ GQ S) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ (γ * h₁) h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, γ * h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((h₀, γ * h₁) : GA D A × GA D S) = (1, γ) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut 1 (one_mem _) γ hγ _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((γ * h₁, h₂) : GA D S × GA D X) = (γ, 1) * (h₁, h₂) := by simp
  rw [e1, e, map_mul, Module.End.mul_apply, hwX.om_aut γ hγ 1 (one_mem _) _ (hwX.om_pres _ _ hth)]

theorem ker_right (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {δ : GA D X} (hδ : δ ∈ GQ X) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ h₁ (δ * h₂) = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((h₁, δ * h₂) : GA D S × GA D X) = (1, δ) * (h₁, h₂) := by simp
  rw [e, map_mul, Module.End.mul_apply, hwX.om_aut 1 (one_mem _) δ hδ _ (hwX.om_pres _ _ hth)]

theorem inner (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (vA : Vol A) {φ : GA D A → ℂ}
    (hφ : IsContAut A φ) :
    (∀ h₁ h₂, IntegrableOn (fun h₀ => φ h₀ * ker oma omX C h₀ h₁ h₂) vA.𝓕 vA.μ) ∧
      Continuous fun p : GA D S × GA D X => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ p.1 p.2 ∂vA.μ := by
  have hc : Continuous (Function.uncurry fun (g : GA D A) (p : GA D S × GA D X) => φ g * ker oma omX C g p.1 p.2) := by
    show Continuous fun q : GA D A × (GA D S × GA D X) => φ q.1 * ker oma omX C q.1 q.2.1 q.2.2
    exact (hφ.2.comp continuous_fst).mul ((ker_cont hB hwa hwX hC).comp
      (by fun_prop : Continuous fun q : GA D A × (GA D S × GA D X) => (q.1, q.2.1, q.2.2)))
  have H := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA vA (GA D S × GA D X) (fun g p => φ g * ker oma omX C g p.1 p.2) hc
    (fun γ hγ g p => by rw [hφ.1 γ hγ g, ker_left hwa hC hγ])
  exact ⟨fun h₁ h₂ => H.1 (h₁, h₂), H.2.1⟩

theorem mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S)
    {φ : GA D A → ℂ} (hφ : IsContAut A φ) :
    (∀ h₂, IntegrableOn (fun h₁ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) vS.𝓕 vS.μ) ∧
      Continuous fun h₂ => biLift oma omX vA vS φ C h₂ := by
  have H := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS vS (GA D X) (fun h₁ h₂ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ)
    (inner hB hwa hwX hC hA vA hφ).2 (fun γ hγ g p => by simp only [ker_mid hB hwa hwX hC hγ])
  exact ⟨H.1, H.2.1⟩

theorem outer (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) {T L'' : HSp D} (hT : CoCpt T)
    (vA : Vol A) (vS : Vol S) (vT : Vol T) (o'' : OrthDec X T L'') {φ : GA D A → ℂ} (hφ : IsContAut A φ)
    {F : GA D T → ℂ} (hF : IsContAut T F) :
    IntegrableOn (fun h' => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1))) vT.𝓕 vT.μ := by
  have hc := (mid hB hwa hwX hC hA hS vA vS hφ).2
  have hc' : Continuous fun h' : GA D T => biLift oma omX vA vS φ C (o''.emb (h', 1)) :=
    hc.comp (o''.continuous_emb.comp (by fun_prop : Continuous fun h' : GA D T => ((h', 1) : GA D T × GA D L'')))
  refine (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D T hT vT Unit (fun h' _ => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1)))
    ((hF.2.mul hc').comp continuous_fst) (fun γ hγ g _ => ?_)).1 ()
  have e : ((γ * g, 1) : GA D T × GA D L'') = (γ, 1) * (g, 1) := by simp
  have hδ : o''.emb (γ, 1) ∈ GQ X := o''.emb_mem_GQ hγ (one_mem _)
  rw [hF.1 γ hγ g, e, map_mul, biLift_eq, biLift_eq]
  simp only [ker_right hB hwa hwX hC hδ]

theorem biLift_sum (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : IsContAut A φ) {n : ℕ}
    (C : Fin n → WO A S → WO S X → ℂ) (hC : ∀ i, IsBiTheta ψ A S X (C i)) (h₂ : GA D X) :
    biLift oma omX vA vS φ (∑ i, C i) h₂ = ∑ i, biLift oma omX vA vS φ (C i) h₂ := by
  have e1 : ∀ h₁, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (∑ i, C i) h₀ h₁ h₂ ∂vA.μ =
      ∑ i, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (C i) h₀ h₁ h₂ ∂vA.μ := by
    intro h₁
    simp only [ker_sum, Finset.mul_sum]
    exact integral_finset_sum _ fun i _ => (inner hB hwa hwX (hC i) hA vA hφ).1 h₁ h₂
  rw [biLift_eq]
  simp only [e1]
  rw [integral_finset_sum _ fun i _ => (mid hB hwa hwX (hC i) hA hS vA vS hφ).1 h₂]
  rfl

end

theorem seeSmall : ∀ D : D7, SeeSmall D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ hA hS hT χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hTw hz''
    vA vS vT N Ξ Φ₂ hΞΦ φ F hφ hF
  have hB : BiAct D := GlobalTheory.T.seeSawWeilBiAction_commutes D
  have hSL := GlobalTheory.T.lastSeeSaw_thetaIdentity D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX
    hTw hz''
  have hC : ∀ i, IsBiTheta ψ A S X (lastBi o o'' τ (Ξ i) (Φ₂ i)) := fun i =>
    GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction D ψ h₁.std V₀ A L S X T L'' o o'' τ hτ (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2
  have e0 : (o.resS S).symm (0, 0) = 0 := by rw [← Prod.zero_eq_mk, map_zero]
  have hpt : ∀ i h', biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) (o''.emb (h', 1)) =
      ∫ h in vS.𝓕, omT (h, h') (Φ₂ i) 0 * liftA o om₁ vA φ (Ξ i) h 0 ∂vS.μ := by
    intro i h'
    rw [biLift_eq]
    congr 1
    funext h
    simp only [liftA, e0]
    rw [← integral_const_mul]
    congr 1
    funext h₀
    have key : oma (h₀, h) (fun u' => omX (h, o''.emb (h', 1)) (lastBi o o'' τ (Ξ i) (Φ₂ i) u') 0) 0 =
        omT (h, h') (Φ₂ i) 0 * om₁ (o.emb (h₀, 1), h) (Ξ i) 0 :=
      ((hSL (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2).2 h₀ h h').symm
    have hk := (hB ψ A S X χA χS χS' (χT * χz⁻¹) oma omX ha hX _ (hC i)).2.2.1 (h₀, h) (h, o''.emb (h', 1)) 0 0
    simp only [ker]
    rw [hk, key]
    ring
  have hsum : ∀ h₂, biLift oma omX vA vS φ (∑ i, lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ =
      ∑ i, biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ := fun h₂ =>
    biLift_sum hB ha hX hA hS vA vS hφ (fun i => lastBi o o'' τ (Ξ i) (Φ₂ i)) hC h₂
  simp only [hsum, Finset.mul_sum]
  rw [integral_finset_sum _ fun i _ => outer hB ha hX (hC i) hA hS hT vA vS vT o'' hφ hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smallPair, hpt]

end GlobalTheory.SeeSmallPf

end
