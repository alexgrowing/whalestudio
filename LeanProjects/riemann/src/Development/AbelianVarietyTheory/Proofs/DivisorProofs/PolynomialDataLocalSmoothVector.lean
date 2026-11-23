import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleArchimedeanComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPlaStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Topology

noncomputable section
open scoped Classical

namespace GlobalTheory.ThKSmooth

theorem polData_smooth : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), ∀ h ∈ U, h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v) → om (1, h) Φ = Φ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT v Φ hΦ
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hA := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ G.M _ _ om _ _ _ _ hP v).2.2
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.V.J) - 1) = 0
    have : mat (1 : UA σ G.V.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  have hc : Filter.Tendsto (fun h : UA σ G.W.J => ((1 : UA σ G.V.J), h)) (𝓝 1) (𝓝 (1 : UA σ G.V.J × UA σ G.W.J)) := by
    have := ((continuous_const (y := (1 : UA σ G.V.J))).prodMk continuous_id).tendsto (1 : UA σ G.W.J)
    exact this
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := hΨ
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    obtain ⟨U, hU, hUa⟩ := hA (φ v) (hSB v)
    obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have hpure : tens (evFin F v) (φ v) ρ = pure f φ := by
      rw [hρt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ v) ρ := ⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    refine ⟨_, hc hU, fun h hh hhv => ?_⟩
    rw [← hpure]
    exact hUa (1, h) hh h1 hhv ρ hRest
  | zero => exact ⟨Set.univ, Filter.univ_mem, fun h _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, hx⟩ := hx
    obtain ⟨U', hU', hy⟩ := hy
    refine ⟨U ∩ U', Filter.inter_mem hU hU', fun h hh hhv => ?_⟩
    rw [map_add, hx h hh.1 hhv, hy h hh.2 hhv]
  | smul c x _ hx =>
    obtain ⟨U, hU, hx⟩ := hx
    exact ⟨U, hU, fun h hh hhv => by rw [map_smul, hx h hh hhv]⟩

end GlobalTheory.ThKSmooth
