import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRatFinCongOfMarks

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompFactor

set_option maxHeartbeats 1000000 in

theorem exists_factor_comp : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∃ v : U.Comp → c.F, ∀ h : GA D V, w h = v (dict h).1 := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio _ _ _ hW hD _ w _ h2 h3
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h h', ik (dict h).1 = ik (dict h').1 → w h = w h' := by
    intro h h' hi
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
    have hξ : -(-D.host.xi0) ≠ 0 := by
      rw [← (hW (dict h).1).2]
      exact neg_ne_zero.2 (U.X _).ξ0_ne
    obtain ⟨δ, hδ, u, hu, hc, eu⟩ := GlobalTheory.CompRead.exists_rat_finCong_of_index F V io hio.emb _ _ hi _ _ _ _
      (SetLike.ext' (hΛ.trans (Set.image_id _))) (SetLike.ext' (hΛ'.trans (Set.image_id _))) (φ _) (φ _) _ hξ
      (htr _) (htr _) hm hm'
    rw [← h2 γ' hγ' h', eu, h3 u hu hc, h2 δ hδ, h2 γ hγ]
  have hv : ∀ k : U.Comp, ∃ a : c.F, ∀ h, (dict h).1 = k → w h = a := by
    intro k
    by_cases hex : ∃ h, (dict h).1 = k
    · obtain ⟨h, hi⟩ := hex
      exact ⟨w h, fun h' hi' => key h' h (congrArg ik (hi'.trans hi.symm))⟩
    · exact ⟨0, fun h hi => absurd ⟨h, hi⟩ hex⟩
  choose v hv using hv
  exact ⟨v, fun h => hv _ h rfl⟩

end GlobalTheory.CompFactor
