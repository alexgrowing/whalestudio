import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvalVIndP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticePlaceCutSmulMemOpenSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionCutIntegralPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAddStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfTrivialAtPlacesStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLoc

variable {D : D7}

theorem latO_mono (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P Q : Pl D → Prop} (h : ∀ v, Q v → P v) : latO S T LS LT Q ≤ latO S T LS LT P := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hvan, rest⟩
  exact ⟨α, hα, fun v hv => hvan v fun hq => hv (h v hq), rest⟩

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem pairA_add (a b : Af D.host.F) :
    pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b := by
  show ((0 : Ainf D.host.F), a + b) = ((0 : Ainf D.host.F), a) + ((0 : Ainf D.host.F), b)
  rw [Prod.mk_add_mk, add_zero]

theorem pairA_mul (a b : Af D.host.F) :
    pairA D.host.F 0 a * pairA D.host.F 0 b = pairA D.host.F 0 (a * b) := by
  show ((0 : Ainf D.host.F), a) * ((0 : Ainf D.host.F), b) = ((0 : Ainf D.host.F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

theorem pairA_zero : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl

open Classical in

theorem latVac_of_places (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hv : ∀ v, P v → Vac ψ S T LS LT (· = v) f) :
    IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f := by

  have one : ∀ (v : Pl D) (w : WO S T), w ∈ latO S T (LS : Set _) (LT : Set _) (fun v' => P v' ∧ v' = v) →
      (heisO ψ S T (2 • w) f = f) ∧ ∀ e, IsSplitIdem D e → IsHalf e w → heisO ψ S T w f = f := by
    intro v w hw
    by_cases hP : P v
    · have hw' : w ∈ latO S T (LS : Set _) (LT : Set _) (· = v) :=
        latO_mono S T _ _ (fun v' h => h.2) hw
      exact ⟨(hv v hP).2.1 w hw', fun e he hh => (hv v hP).2.2 e he w hw' hh⟩
    · have h0 : w = 0 := ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ _ w hw).2.2.2 fun v' h => hP (h.2 ▸ h.1)
      subst h0
      simp [heisO_zero]
  refine ⟨?_, ?_⟩
  · intro u hu
    obtain ⟨U, hUo, hU⟩ := hf.level
    have h2u : 2 • u ∈ latO S T (LS : Set _) (LT : Set _) P := AddSubgroup.nsmul_mem _ hu 2
    obtain ⟨s, hs⟩ := (GlobalTheory.T.homLattice_placeCut_smul_mem_openSubgroup) D S T _ _ P U hUo (2 • u) h2u
    have key : ∀ t : Finset (Pl D), t ⊆ s →
        heisO ψ S T (pairA D.host.F 0 (indP D (↑(s \ t) : Set (Pl D))ᶜ) • (2 • u)) f = f := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        have hγ : ∀ v ∈ s, evalV D.host.F v (indP D (↑(s \ ∅) : Set (Pl D))ᶜ) = 0 := by
          intro v hv; rw [evalV_indP]; simp [hv]
        have hm := hs _ (indicatorAdele_mem_integralAdeles _) hγ
        have hl := ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ P _ h2u).1 _ (indicatorAdele_mem_integralAdeles ((↑(s \ ∅) : Set (Pl D))ᶜ))
        exact hU _ hm (((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ _ _ hl).2.2.1)
      | insert v t hvt ih =>
        intro hts
        have hvs : v ∈ s := hts (Finset.mem_insert_self v t)
        have ih' := ih (fun x hx => hts (Finset.mem_insert_of_mem hx))
        have hset : ((↑(s \ insert v t) : Set (Pl D))ᶜ) = {v} ∪ (↑(s \ t) : Set (Pl D))ᶜ := by
          ext x; simp only [Set.mem_compl_iff, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe,
            Finset.mem_insert, Set.mem_union, Set.mem_singleton_iff]
          constructor
          · intro h; by_cases hx : x = v; · exact Or.inl hx
            right; intro h'; exact h ⟨h'.1, fun h'' => h''.elim hx h'.2⟩
          · rintro (rfl | h) h'; · exact h'.2 (Or.inl rfl)
            exact h ⟨h'.1, fun h'' => h'.2 (Or.inr h'')⟩
        have hdisj : Disjoint ({v} : Set (Pl D)) (↑(s \ t) : Set (Pl D))ᶜ := by
          rw [Set.disjoint_singleton_left]; simp [hvs, hvt]
        rw [hset, ← indicatorAdele_union_of_disjoint hdisj, pairA_add, add_smul]
        have hprod : pairA D.host.F 0 (indP D {v}) * pairA D.host.F 0 (indP D (↑(s \ t) : Set (Pl D))ᶜ) = 0 := by
          rw [pairA_mul, indicatorAdele_singleton_mul_singleton, Set.disjoint_iff_inter_eq_empty.mp hdisj, indicatorAdele_empty, pairA_zero]
        rw [(GlobalTheory.T.heisenbergOperator_disjointSupport_smul_add) D ψ S T _ _ _ _ f hprod, ih']
        have hw := ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ P u hu).1 _ (indicatorAdele_mem_integralAdeles {v})
        have hw' : pairA D.host.F 0 (indP D {v}) • u ∈
            latO S T (LS : Set _) (LT : Set _) (fun v' => P v' ∧ v' = v) := by
          refine latO_mono S T _ _ (fun v' h => ⟨h.1, ?_⟩) hw
          by_contra hne; apply h.2; rw [evalV_indP]; simp [hne]
        rw [smul_comm]
        exact (one v _ hw').1
    have := key s (subset_refl s)
    rwa [Finset.sdiff_self, Finset.coe_empty, Set.compl_empty, indicatorAdele_univ,
      ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ P _ h2u).2.1] at this
  · intro e he u hu hh
    obtain ⟨hee, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := he
    have hα : α ∈ intAf D.host.F := by
      intro v'; by_cases h : v' = v
      · subst h; rw [hα1]; exact one_mem _
      · rw [hα0 v' h]; exact zero_mem _
    have hfix : pairA D.host.F 0 α • u = u := by
      ext i j
      show pairA D.host.F 0 α • u i j = u i j
      rw [Algebra.smul_def, ← hsum, ← hh i j, ← mul_assoc, add_mul, hee, mul_comm (cA D e) e, hec, add_zero]
    have hw := ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ P u hu).1 α hα
    rw [hfix] at hw
    refine (one v u (latO_mono S T _ _ (fun v' h => ⟨h.1, ?_⟩) hw)).2 e
      ⟨hee, hec, v, _, ⟨α, rfl, hα1, hα0⟩, hsum⟩ hh
    by_contra hne; exact h.2 (hα0 v' hne)

theorem vac_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v) → ∀ f, (Vac ψ S T LS LT P f ↔ IsThetaFunO ψ S T f ∧ ∀ v, P v → Vac ψ S T LS LT (· = v) f) ∧ (Vac ψ S T LS LT P f → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, Vac ψ S T LS LT P (om (g, h) f)) ∧ (Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f)) := by
  intro D ψ S T χS χT om hW LS LT hLS hLT P _ f
  refine ⟨⟨fun h => ⟨h.1, fun v hv => ⟨h.1, ?_, ?_⟩⟩, fun h => ⟨h.1, latVac_of_places ψ S T LS LT P f h.1 h.2⟩⟩, ?_, ?_⟩
  · exact fun u hu => h.2.1 u (latO_mono S T _ _ (fun v' h' => h' ▸ hv) hu)
  · exact fun e he u hu => h.2.2 e he u (latO_mono S T _ _ (fun v' h' => h' ▸ hv) hu)
  · intro h g hg k hk
    exact (GlobalTheory.T.thetaLatticeVacuum_of_carriesLatticeCompletions) D ψ S T χS χT om hW LS LT hLS hLT P f h g k LS LT hLS hLT
      ((GlobalTheory.T.carriesLatticeCompletion_of_trivialAtPlaces) D S LS P g hg) ((GlobalTheory.T.carriesLatticeCompletion_of_trivialAtPlaces) D T LT P k hk)
  · intro h g k MS MT hMS hMT hg hk
    exact (GlobalTheory.T.thetaLatticeVacuum_of_carriesLatticeCompletions) D ψ S T χS χT om hW LS LT hLS hLT P f h g k MS MT hMS hMT hg hk

end GlobalTheory.VacLoc

end
