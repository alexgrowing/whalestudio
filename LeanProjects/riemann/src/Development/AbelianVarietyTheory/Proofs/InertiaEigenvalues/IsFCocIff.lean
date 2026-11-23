import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.ResDual

def CupCob {Γ k M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup M']
    [Module k M'] (χ : Γ → k) (ρ' : Representation k Γ M') (P : M →ₗ[k] M' →ₗ[k] k) (x : Γ → M) (y : Γ → M') : Prop :=
  ∃ f : Γ → k, IsLocallyConstant f ∧ ∀ g h, P (x g) (ρ' g (y h)) = χ g * f h - f (g * h) + f g

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i))

def IsFCoc {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) (y : ↥(DecV N v) → Fin r → X.O0 i) : Prop :=
  (fun g a => (bkP.br i v hv).toLL (y ((bkP.br i v hv).e.symm g) a)) ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ)

variable {bkP i v hv}

theorem isFCoc_iff {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i} :
    IsFCoc bkP i v hv ρ y ↔ ∃ c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ),
      ∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a) := by
  constructor
  · intro h
    exact ⟨_, h, fun g a => by simp only [MulEquiv.symm_apply_apply]⟩
  · rintro ⟨c, hc, h⟩
    have : (fun g a => (bkP.br i v hv).toLL (y ((bkP.br i v hv).e.symm g) a)) = c := by
      funext g a
      rw [← h, MulEquiv.apply_symm_apply]
    unfold IsFCoc
    rw [this]
    exact hc

theorem IsFCoc.continuous {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i}
    (h : IsFCoc bkP i v hv ρ y) : Continuous y := by
  obtain ⟨c, hc, e⟩ := isFCoc_iff.1 h
  refine continuous_pi fun a => ?_
  have h1 : Continuous fun g => (bkP.br i v hv).toLL (y g a) := by
    simp_rw [← e]
    exact (continuous_apply a).comp (hc.1.1.comp (bkP.br i v hv).e_cont)
  have h2 : Continuous fun g => (bkP.br i v hv).eO (y g a) := continuous_induced_rng.2 h1
  simpa [Function.comp_def] using (bkP.br i v hv).eO_symm_cont.comp h2

theorem IsFCoc.cocycle {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i}
    (h : IsFCoc bkP i v hv ρ y) (g g' : ↥(DecV N v)) :
    y (g * g') = y g + ((ρ g : GL (Fin r) (X.O0 i)) : Matrix (Fin r) (Fin r) (X.O0 i)).mulVec (y g') := by
  have e := h.1.2 ((bkP.br i v hv).e g) ((bkP.br i v hv).e g')
  funext a
  have inj : Function.Injective (bkP.br i v hv).toLL := Subtype.val_injective.comp (bkP.br i v hv).eO.injective
  apply inj
  have e2 := congrFun e a
  simp only [← map_mul, MulEquiv.symm_apply_apply, Pi.add_apply] at e2
  rw [e2, Pi.add_apply, map_add]
  congr 1
  simp [LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply]

end GlobalTheory.ResDual
