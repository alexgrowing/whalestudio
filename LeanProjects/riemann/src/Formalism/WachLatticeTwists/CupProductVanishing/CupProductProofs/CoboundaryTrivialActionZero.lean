import Formalism.WachLatticeTwists.CupProductVanishing.StatVhEInChi

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

section Triv

variable {O : Type*} [CommRing O] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module O M]

theorem coboundary_trivial_action_zero (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) (c : Γ → M) (hc : c ∈ coB1 ρ) : c = 0 := by
  obtain ⟨v, rfl⟩ := hc
  funext g
  show ρ g v - v = 0
  rw [h, sub_self]

def cocOf (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) : H1z ρ →ₗ[O] (Γ → M) :=
  Submodule.liftQ _ (coZ1s ρ).subtype (fun x hx => by
    rw [LinearMap.mem_ker]
    exact coboundary_trivial_action_zero ρ h _ hx)

theorem unr_vanish (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) (I : Subgroup Γ) (z : coZ1s ρ)
    (hz : (Submodule.mkQ _ z : H1z ρ) ∈ unrH1 ρ I) (g : Γ) (hg : g ∈ I) : (z : Γ → M) g = 0 := by
  have h1 : resH1 ρ I (Submodule.mkQ _ z) = 0 := hz
  have h2 : (Submodule.mkQ _ (restrictCocycles1 ρ I z) : H1z (resRep ρ I)) = 0 := h1
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  have h3 := coboundary_trivial_action_zero (resRep ρ I) (fun g m => h g m) _ h2
  exact congrFun h3 ⟨g, hg⟩

end Triv

theorem vhE : StatVhE := hT2Core.out.vhE

theorem unramified_H1_antitone {O : Type*} [CommRing O] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module O M]
    (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) {I J : Subgroup Γ} (hIJ : I ≤ J) : unrH1 ρ J ≤ unrH1 ρ I := by
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  show resH1 ρ I (Submodule.mkQ _ z) = 0
  have : restrictCocycles1 ρ I z = 0 := Subtype.ext (funext fun g => unr_vanish ρ h J z hx g (hIJ g.2))
  show (Submodule.mkQ _ (restrictCocycles1 ρ I z) : H1z (resRep ρ I)) = 0
  rw [this, map_zero]

theorem vhEInChi : StatVhEInChi := by
  intro E Ω _ _ _ _ _ Av hA l _ O _ _ _ _ _ hl A T' _ _ _ _ M _ _ _ _ e r χ htr D places HcG F Vo VS Io IS hc hcov
  have hρ : ∀ g m, uRep O (M := M) r χ g m = m := fun g m => htr g m
  refine vhE E Ω Av hA l O hl M e (uRep O (M := M) r χ) hρ _ (fun x hx => hc x hx.1.1.1) (fun v x hx => ?_)
  rcases hcov v with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨w, hw, I, hF, hI⟩
  · exact unramified_H1_antitone _ hρ ha ((Submodule.mem_iInf _).1 hx.1.1.2 a)
  · exact unramified_H1_antitone _ hρ ha ((Submodule.mem_iInf _).1 hx.1.2 a)
  · have h1 : resH1 (uRep O (M := M) r χ) (D w) x ∈ F w :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hx.2 w) hw
    have h2 := hF h1
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    show Formalism.NG.resH1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) (Submodule.mkQ _ z) = 0
    have : Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) z = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨g', hg', hgg⟩ := hI g.2
      have h3 := unr_vanish (resRep (uRep O (M := M) r χ) (D w)) (fun g m => hρ g m) I
        (Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (D w) z) h2 g' hg'
      show (z : G E Ω → M) g = 0
      rw [← hgg]
      exact h3
    show (Submodule.mkQ _ (Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) z) :
      H1z (resRep (uRep O (M := M) r χ) (Ine (F := E) (Av v)))) = 0
    rw [this, map_zero]

end Formalism.RepresentationBoundsCohomology.T2
