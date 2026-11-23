import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.DictLatPin

variable {D : D7}

theorem latFrame_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r)
    {Comp : Type} {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r}
    (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      ∀ τ : (X (dict h).1).Ψ, ReciprocityTheory.ChartRestriction.G.FD.mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1)
    (g : GA D W) : ∃ γ ∈ GQ W,
      ((X (castDict hV dict g).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin W.rank → D.host.E => v ∘ Fin.cast hr'.symm) '' (latG W (γ * g) : Set _) ∧
      ∀ τ : (X (castDict hV dict g).1).Ψ, ReciprocityTheory.ChartRestriction.G.FD.mat (castDict hV dict g).2 τ =
        Matrix.reindex (finCongr hr') (finCongr hr') (archM W (th (castDict hV dict g).1 τ) (γ * g)) * x₀ τ.1 := by
  subst hV
  exact h g

end GlobalTheory.DictLatPin

open GlobalTheory.DictLatPin in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.DictLatPin.lat_of_frAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i),
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ v : Fin D.R.r → D.host.E,
      v ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).Λ ↔
        (fun m => v (Fin.cast (rank_Wc i) m)) ∈ latG (Wc D i) (γ * g) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ _ hMods _ hT i σ hσ hV γ hγ g hFr v
  subst hσ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hL := hT.laws
  have hg := T.toCore.good_σ₀
  have hP := hL.pins
  obtain ⟨hr, g', e, F', ik, φ, th, -, -, hth, hD⟩ := hL.adPin _ hj _ hg
  have hcl := latFrame_cast hV hr (rank_Wc i) (T.dict ((i : ℕ) + 1) T.σ₀) th (T.x₀ ((i : ℕ) + 1) T.σ₀)
    (fun h => by
      obtain ⟨γ₁, hq, hl, -, hf⟩ := hD.2 h
      exact ⟨γ₁, hq, hl, hf⟩) g
  obtain ⟨γ', hγ', hΛ, hf'⟩ := hcl

  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  set k := (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i T.σ₀ hV g).1 with hk
  have hU := hL.unf _ hj _ hg
  have hΨ := (hU.2.1 k).2
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hτ₀ : tauE D ρ₀ ∈ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ := (hΨ _).2 (hP.1.2.2.2 ρ₀)
  let τ₀ : ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ := ⟨tauE D ρ₀, hτ₀⟩
  have h1 := hFr ρ₀ τ₀ rfl
  have h2 := hf' τ₀
  have hth' : th k τ₀ = R.θ ρ₀ := GlobalTheory.LettersCheck.isInfEmb_unique (tauE D ρ₀) _ _ (hth k τ₀) (hMods.inf ρ₀)
  rw [← hx.mul] at h1
  rw [hth'] at h2
  have h3 : Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (archM (Wc D i) (R.θ ρ₀) (γ' * g)) *
      T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀) =
      Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (archM (Wc D i) (R.θ ρ₀) (γ * g)) *
      T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀) := h2.symm.trans h1
  have hx₀ : IsOrthogonalFrame ((T.U ((i : ℕ) + 1) T.σ₀).X k) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hL.familyUniformisationBasePointOrthogonal _ hj _ hg k
  obtain ⟨-, hu2, -⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E D.R.r
    ((T.U ((i : ℕ) + 1) T.σ₀).X k).p0 ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Gm
    ((T.U ((i : ℕ) + 1) T.σ₀).X k).Gm_herm
  have hdet : IsUnit (T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀)).det :=
    (((hu2 (fun τ => T.x₀ ((i : ℕ) + 1) T.σ₀ τ.1) fun τ => hx₀ τ.1 τ.2).1 τ₀).1).isUnit
  have h4 : archM (Wc D i) (R.θ ρ₀) (γ' * g) = archM (Wc D i) (R.θ ρ₀) (γ * g) := by
    have := congrArg (· * (T.x₀ ((i : ℕ) + 1) T.σ₀ (tauE D ρ₀))⁻¹) h3
    simp only [Matrix.mul_nonsing_inv_cancel_right _ _ hdet] at this
    exact (Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i))).injective this
  have h5 : ∀ δ : GA D (Wc D i), archM (Wc D i) (R.θ ρ₀) δ =
      archM (Wc D i) (R.θ ρ₀) (δ * g) * archM (Wc D i) (R.θ ρ₀) g⁻¹ := fun δ => by
    rw [← GlobalTheory.PointAtPlace.archM_mul, mul_inv_cancel_right]
  have hγγ : γ' = γ := GlobalTheory.AdTh.MarkUniq.rat_eq_of_archM (Wc D i) hγ' hγ (tauE D ρ₀) (R.θ ρ₀) (hMods.inf ρ₀)
    (by rw [h5 γ', h5 γ, h4])
  subst hγγ
  rw [← SetLike.mem_coe, hΛ]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ latG (Wc D i) (γ' * g) := hw
    convert hw' using 1
    funext m
    simp
  · intro hv
    exact ⟨_, hv, funext fun m => by simp⟩
