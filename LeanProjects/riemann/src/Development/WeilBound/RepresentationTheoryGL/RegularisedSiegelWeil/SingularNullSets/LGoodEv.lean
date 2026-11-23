import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEvB
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.EvGoodSmul

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7}

theorem gen_good {θ : InfFam D} {a b : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e →
      Good S e (fun x : Mx D a b => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) := by
  obtain ⟨S₀, hS₀⟩ := fin_good g hg
  refine ⟨S₀, fun S hS e he x => ?_⟩
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hi1, hi2⟩ := isIdem_eS S
  have heS : e = eS S := ae_ext e (eS S) (fun w => (he1 w).trans (hi1 w).symm)
    (fun v => (he2 v).trans (hi2 v).symm)
  subst heS
  have hinf : ∀ τ (i : Fin a) (j : Fin b), compAt θ τ (eS S • x) i j = compAt θ τ x i j := by
    intro τ i j
    show θ τ (infPart D ((eS S • x) i j)) = θ τ (infPart D (x i j))
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, infPart_eS, one_mul]
  have hfin : (fun (i : Fin a) (j : Fin b) => finPart D ((eS S • x) i j)) =
      sPart S (fun i j => finPart D (x i j)) := by
    funext i j
    show finPart D ((eS S • x) i j) = algebraMap _ _ (indS S) * finPart D (x i j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, finPart_eS]
  simp only [hinf]
  rw [hfin, hS₀ S hS (fun i j => finPart D (x i j))]
  by_cases h : IntOff S x
  · have h' : ∀ v ∉ S, ∀ (i : Fin a) (j : Fin b),
        projV v (fun i j => finPart D (x i j)) i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
      fun v hv i j => by
        have := h v hv i j
        rw [cv_eq] at this
        exact this
    rw [if_pos h', if_pos h]
  · have h' : ¬ ∀ v ∉ S, ∀ (i : Fin a) (j : Fin b),
        projV v (fun i j => finPart D (x i j)) i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
      fun h'' => h (fun v hv i j => by
        have := h'' v hv i j
        rw [cv_eq]
        exact this)
    rw [if_neg h', if_neg h, mul_zero]

end PositivityTheory.Rg.Rsw.L.LGoodEv

namespace PositivityTheory.Rg.Rsw.L

theorem goodEv : IdemEx → GoodEv := by
  intro _ D θ _ a b Φ hΦ
  refine LGoodEv.ev_span _ rfl ?_ Φ hΦ
  rintro φ ⟨f, g, hg, rfl⟩
  exact LGoodEv.gen_good f g hg

end PositivityTheory.Rg.Rsw.L

end
