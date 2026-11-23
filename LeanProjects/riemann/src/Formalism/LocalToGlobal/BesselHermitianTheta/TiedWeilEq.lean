import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure TwRuleEq {X : ThetaX D} (T : ThetaTied D X)
    (om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Prop where
  twW : ∀ (V W : HSp D) χ χ' ν, V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V g x →
      om V W χ (χ' * ν) (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • om V W χ χ' (g, h)
  twV : ∀ (V W : HSp D) χ χ' ν, V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot W h x →
      om V W (χ * ν) χ' (g, h) = ((T.eChr ν x : Circle) : ℂ) • om V W χ χ' (g, h)

structure WeilCompatibleEquivariance {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) : Prop where

  evS_range : ∀ V W : HSp D, V.rank = W.rank → Set.range (Wl.evS V W) = {f | IsThetaFun Wl.ψ V W f}

  om_heis : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ g h w₀ Φ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W w₀ (Wl.evS V W Φ) →
      Wl.evS V W (Wl.om V W χ χ' (g, h) Φ') = Heisenberg₂ Wl.ψ V W (actHom V W g h w₀) (Wl.evS V W (Wl.om V W χ χ' (g, h) Φ))

  om_aut : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ Φ, Wl.evS V W (Wl.om V W χ χ' (γ, γ') Φ) 0 = Wl.evS V W Φ 0

  om_cont : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ Φ w, Continuous fun p : GA D V × GA D W => Wl.evS V W (Wl.om V W χ χ' p Φ) w

  om_unit : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∀ p Φ, ∫ w in 𝓕, ‖Wl.evS V W (Wl.om V W χ χ' p Φ) w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖Wl.evS V W Φ w‖ ^ 2 ∂μ

  om_split : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : X.Sch V W →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) →
        ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (Wl.om V W χ χ' (g, h) Φ) = (r : ℂ) * (splitFac V W (T.eChr χ) (T.eChr χ') x y : ℂ) * ℓ Φ

  om_tw : TwRuleEq T Wl.om

  th : ∀ (V W : HSp D) χ χ', V.rank = W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → V.SigOK →
    ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ (Φ : X.Sch V W) (F : X.cusp V) (h : GA D W),
      T.ev W (X.th V W χ χ' Φ F) h =
        (T.petC V : ℂ) * ∫ g in 𝓕, Wl.evS V W (Wl.om V W χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

end Formalism.L2.Theta

end
