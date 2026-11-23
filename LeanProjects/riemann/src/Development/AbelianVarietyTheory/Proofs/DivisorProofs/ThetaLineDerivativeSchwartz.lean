import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsExtra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology

namespace GlobalTheory.OrbitArchSlope

theorem exists_sb_ne_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ y, g y ≠ 0 := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  let W : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => (Formalism.UG.intAd F : Set _)
  have hc : IsCompact W := isCompact_univ_pi fun _ => Formalism.MainNotions.Gaps.LevGap.isCompact_intAd
  have ho : IsOpen W := isOpen_set_pi Set.finite_univ fun _ _ => Formalism.MainNotions.Gaps.LevGap.isOpen_intAd
  have h0 : (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ W := fun i _ => (Formalism.UG.intAd F).zero_mem
  refine ⟨W.indicator 1, GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB hc ⟨hc.isClosed, ho⟩, 0, ?_⟩
  rw [Set.indicator_of_mem h0]
  exact one_ne_zero

theorem orbit_slope_tendsto : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ γ ∈ Lines σ G.W, ∀ (f : SInf F (Fin a' × Fin (a + a'))) (u : ℝ → SInf F (Fin a' × Fin (a + a'))), (∀ t : ℝ, ∀ g ∈ SB (Fin a' × Fin (a + a') → Af F), om' (1, γ (Multiplicative.ofAdd t)) (pureA F f g) = pureA F (u t) g) → ∃ u₁ : SInf F (Fin a' × Fin (a + a')), Tendsto (fun t : ℝ => t⁻¹ • (u t - u 0)) (𝓝[≠] 0) (𝓝 u₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ f u hu
  obtain ⟨c, c', hc0, hlim, hacts⟩ := GlobalTheory.WeilArchSmooth.exists_orbit hK.base G.M' B.ψ X.α (X.α / X.β) om'
    hM.triple.base.cm hM.triple.base.std hM.triple.weil' γ hγ f
  obtain ⟨g, hg, y, hy⟩ := exists_sb_ne_zero F (Fin a' × Fin (a + a'))
  let r : (Fin a' × Fin (a + a') → AF F) → ℂ := fun x => g (fun i => (x i).2)
  have hpure : ∀ h : SInf F (Fin a' × Fin (a + a')), pureA F (⇑h) g = tens (evI F) (⇑h) r := fun h => rfl
  have hRest : Rest (evI F) (⇑f) r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · let e : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
      have he : evI F e = 0 := by
        show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
        exact map_zero _
      have hz2 : ∀ i, (z i).2 = 0 := by
        intro i
        have h1 := congrFun (hz e he) i
        have h2 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd h1
        simpa using h2
      show g (fun i => (x i + z i).2) = g (fun i => (x i).2)
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [hz2 i, add_zero]
    · rw [← hpure]
      exact Submodule.subset_span ⟨f, g, hg, rfl⟩
  have heq : ∀ t, u t = c t := by
    intro t
    have h1 : pureA F (⇑(u t)) g = pureA F (⇑(c t)) g := by
      rw [← hu t g hg, hpure, hpure]
      exact hacts t r hRest
    refine DFunLike.ext _ _ fun x => ?_
    have e := congrFun h1 (fun i => (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)))
    simp only [pureA] at e
    have hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i))) = x :=
      funext fun i => RingEquiv.apply_symm_apply _ _
    rw [hx] at e
    exact mul_right_cancel₀ hy e
  have hc : u = c := funext heq
  subst hc
  refine ⟨c', ?_⟩
  rw [hc0]
  exact hlim

end GlobalTheory.OrbitArchSlope
