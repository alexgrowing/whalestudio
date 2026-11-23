import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem prodSB {X : Type} [TopologicalSpace X] {a b : ℕ} (G : Fin a → (Fin 1 → Fin b → X) → ℂ)
    (hG : ∀ i, G i ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → X)) :
    (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → X) := by
  have hG' : ∀ i, IsLocallyConstant (G i) ∧ HasCompactSupport (G i) := hG
  have hrow : ∀ i : Fin a, Continuous fun z : Fin a → Fin b → X => (fun (_ : Fin 1) j => z i j) :=
    fun i => continuous_pi fun _ => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)
  show IsLocallyConstant (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ∧
    HasCompactSupport (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j))
  refine ⟨?_, ?_⟩
  · have hfun : (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) =
        ∏ i, (fun z : Fin a → Fin b → X => G i (fun _ j => z i j)) := by
      funext z
      rw [Finset.prod_apply]
    rw [hfun]
    exact Finset.prod_induction _ IsLocallyConstant (fun f g hf hg => hf.comp₂ hg (· * ·))
      (IsLocallyConstant.const 1) (fun i _ => (hG' i).1.comp_continuous (hrow i))
  · let S : Set (Fin a → Fin b → X) := ⋂ i, (fun z : Fin a → Fin b → X => (fun (_ : Fin 1) j => z i j)) ⁻¹' tsupport (G i)
    let gm : (Fin a → Fin 1 → Fin b → X) → (Fin a → Fin b → X) := fun w i j => w i 0 j
    have hgm : Continuous gm :=
      continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply 0).comp (continuous_apply i))
    have hK : IsCompact (gm '' Set.univ.pi fun i => tsupport (G i)) :=
      (isCompact_univ_pi fun i => (hG' i).2).image hgm
    have hSc : IsClosed S := isClosed_iInter fun i => (isClosed_tsupport (G i)).preimage (hrow i)
    have hsub : tsupport (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ⊆ S := by
      refine closure_minimal ?_ hSc
      intro z hz
      have hz' : ∏ i, G i (fun _ j => z i j) ≠ 0 := hz
      rw [Finset.prod_ne_zero_iff] at hz'
      exact Set.mem_iInter.2 fun i => subset_tsupport _ (hz' i (Finset.mem_univ i))
    have hSK : S ⊆ gm '' Set.univ.pi fun i => tsupport (G i) := by
      intro z hz
      refine ⟨fun i _ j => z i j, fun i _ => Set.mem_iInter.1 hz i, rfl⟩
    exact hK.of_isClosed_subset (isClosed_tsupport _) (hsub.trans hSK)

theorem rowSB (θ : InfFam D) {m n : ℕ} (s : AE D) (hs : infPart D s = 0) (hs' : finPart D s = 1)
    (h : Mx D m n → ℂ) (hh : h ∈ schwartzA θ m n) :
    ∃ G ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E),
      ∀ y : Mx D m n, h (s • y) = G (fun i j => finPart D (y i j)) := by
  change h ∈ Submodule.span ℂ _ at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨f (fun _ _ _ => 0) • g, Submodule.smul_mem _ _ hg, fun y => ?_⟩
    have h1 : (fun τ i j => Formalism.IndefR.Datum.compAt θ τ (s • y) i j) = fun _ _ _ => (0 : ℂ) := by
      funext τ i j
      have hc : Formalism.IndefR.Datum.compAt θ τ (s • y) i j = θ τ (Formalism.L2.Theta.infPart D (s * y i j)) := rfl
      rw [hc, map_mul, hs, zero_mul, map_zero]
    have h2 : (fun i j => Formalism.L2.Theta.finPart D ((s • y) i j)) = fun i j => Formalism.L2.Theta.finPart D (y i j) := by
      funext i j
      have hc : Formalism.L2.Theta.finPart D ((s • y) i j) = Formalism.L2.Theta.finPart D (s * y i j) := rfl
      rw [hc, map_mul, hs', one_mul]
    show f (fun τ i j => Formalism.IndefR.Datum.compAt θ τ (s • y) i j) *
        g (fun i j => Formalism.L2.Theta.finPart D ((s • y) i j)) = _
    rw [h1, h2, Pi.smul_apply, smul_eq_mul]
  | zero => exact ⟨0, Submodule.zero_mem _, fun y => rfl⟩
  | add x z _ _ hx hz =>
    obtain ⟨G1, hG1, e1⟩ := hx
    obtain ⟨G2, hG2, e2⟩ := hz
    exact ⟨G1 + G2, Submodule.add_mem _ hG1 hG2, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨G1, hG1, e1⟩ := hx
    exact ⟨c • G1, Submodule.smul_mem _ _ hG1, fun y => by rw [Pi.smul_apply, Pi.smul_apply, e1]⟩

end PositivityTheory.Rg.Rsw.L.LMajor

end
