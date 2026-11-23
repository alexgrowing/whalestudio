import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (h γ₁ γ₂ : GA D V) (hγ₁ : γ₁ ∈ GQ V) (hγ₂ : γ₂ ∈ GQ V)
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (G₁ G₂ : Matrix (Fin r) (Fin r) D.host.E)
    (hG₁ : G₁ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hG₂ : G₂ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hL₁ : (L₁ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₁ * h) : Set _))
    (hL₂ : (L₂ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₂ * h) : Set _)) :
    ∃ γ : GL (Fin r) D.host.E,
      (L₁ : Set (Fin r → D.host.E)) = (γ : Matrix (Fin r) (Fin r) D.host.E).mulVec '' (L₂ : Set _) ∧
      (∀ v w, herm G₁ ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec v) ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec w) =
        herm G₂ v w) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ x : Matrix (Fin r) (Fin r) ℂ,
          Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₁ * h)) * x =
            (γ : Matrix (Fin r) (Fin r) D.host.E).map τ *
              (Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₂ * h)) * x) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG₁ hG₂
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V _ (mul_mem hγ₁ (inv_mem hγ₂))
  have hprod : γ₁ * γ₂⁻¹ * (γ₂ * h) * 1 = γ₁ * h := by group
  obtain ⟨ht1, -⟩ := GlobalTheory.ShortMoveIso.transport (finHom V) (latGHat V)
    (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) 1 (γ₁ * γ₂⁻¹) (γ₂ * h) 1 rfl
  rw [hprod] at ht1
  have hmem : ∀ (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V),
      (L : Set (Fin V.rank → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast (rfl : V.rank = V.rank).symm) '' (latG V g : Set _) →
      ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g := fun L g hL v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ L₂ ↔ δ.1 *ᵥ v ∈ L₁ := fun v => by
    rw [hmem _ _ hL₂, hmem _ _ hL₁, ht1, hδf]
  refine ⟨δ, ?_, fun u v => ?_, fun τ θ hθ x => ?_⟩
  · ext v
    constructor
    · intro hv
      have hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hlat u).1 hu
  · rw [hG₁, hG₂]
    exact hδu u v
  · have hmul : ∀ a b : GA D V, archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have e : γ₁ * h = γ₁ * γ₂⁻¹ * (γ₂ * h) := by group
    rw [hre, hre, e, hmul, hδa _ _ hθ, Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in

theorem frames_differ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨-, -, -, -, -, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  obtain ⟨γ₁, hγ₁, hL₁, -, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, hL₂, -, hf₂⟩ := hd₂ h
  obtain ⟨γ, hl, hi, hf⟩ := move (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ _ _ _ (hW₁ _).1 (hW₂ _).1 hL₁ hL₂
  refine ⟨γ, hl, hi, fun τ t₂ t₁ => ?_⟩
  have e₂' := hf₂ ⟨τ, t₂⟩
  have e₁' := hf₁ ⟨τ, t₁⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at e₂'
  rw [e₁', e₂']
  exact hf τ _ (hth₁ _ ⟨τ, t₁⟩) _

end GlobalTheory.CoverFrameMove
