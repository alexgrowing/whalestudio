import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharEqOneOnPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalWeightEqCharacterExponentAddStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem castDict_laws {D : D7} {V W : HSp D} (hV : V = W) {r : ℕ} (hr : W.rank = r) {Comp : Type}
    (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (Kf : Subgroup (GA D V)) (Kf' : Subgroup (GA D W))
    (hK : ∀ g : GA D W, g ∈ Kf' ↔ cast (congrArg (GA D) hV.symm) g ∈ Kf)
    (hu : ∃ th hr', (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr')
    (hm : ∃ hr' : V.rank = r, ∀ k, ModelW V hr' (X k)) (hmu : MuUnit V dict mu) (hc : Continuous mu) :
    (∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif W (castDict hV dict) Kf' th hr) ∧
      (∀ k, ModelW W hr (X k)) ∧ MuUnit W (castDict hV dict) (castDict hV mu) ∧ Continuous (castDict hV mu) := by
  subst hV
  obtain rfl : Kf' = Kf := Subgroup.ext hK
  obtain ⟨th, hr', h1, h2⟩ := hu
  obtain ⟨hr'', h3⟩ := hm
  exact ⟨⟨th, h1, h2⟩, h3, hmu, hc⟩

theorem goodDict_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → GoodDict R.θ (R.MW i σ) w (rank_Wc i) (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ)) (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM h hpb i σ hσ hV w hw
  obtain ⟨hK, -, hfin, hopen⟩ := GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
  have hj : InR D ((i : ℕ) + 1) := inR i
  obtain ⟨h1, h2, h3, h4⟩ := castDict_laws hV (rank_Wc i) _ _ (T.mu ((i : ℕ) + 1) (res T σ)) _ _ hK
    (h.laws.dictU _ hj _ hσ) (h.laws.modelW _ hj _ hσ) (h.laws.muUnit _ hj _ hσ) (h.laws.muCont _ hj _ hσ)
  have hc : ∀ k, ‖T.cE ((i : ℕ) + 1) (res T σ) k‖ = 1 := h.laws.cUnit _ hj _ hσ
  exact
    { inf := hM.inf
      base := GlobalTheory.T.base_frame_of_realization_models D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV
      unif := h1
      model := h2
      muUnit := h3
      muCont := h4
      chi := h.laws.chiTriv _ hj _ hσ _ _ (dom_wtA (κ i))
      cNe := fun k h0 => by
        have := hc k
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      cBdd := ⟨1, fun k => (hc k).le⟩
      fin := @Finite.of_fintype _ (T.U ((i : ℕ) + 1) (res T σ)).fin
      levFin := hfin
      levOpen := hopen
      muK := GlobalTheory.T.dictionaryChar_eq_one_on_principalLevel D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
      wt := GlobalTheory.T.extremalWeight_eq_character_exponent_add D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV w hw }

end GlobalTheory.HolDict
