import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCoh
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.CohTransport

section Res

variable {R : Type*} [CommRing R]
  {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N) (φ : Γ' →* Γ)
  (hσ : ∀ g n, σ' g n = σ (φ g) n)

def rh0 : H0 σ →ₗ[R] H0 σ' :=
  Submodule.inclusion fun m hm g => by
    show σ' g m = m
    rw [hσ]; exact hm (φ g)

@[simp] theorem rh0_coe (m : H0 σ) : ((rh0 σ σ' φ hσ m : H0 σ') : N) = m := rfl

variable (hφ : Continuous φ)

def rz1 : Z1 σ →ₗ[R] Z1 σ' where
  toFun f := ⟨f.1 ∘ φ, f.2.1.comp hφ, fun g h => by
    simp only [Function.comp_apply, map_mul, hσ]; exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rh1 : H1 σ →ₗ[R] H1 σ' :=
  Submodule.mapQ _ _ (rz1 σ σ' φ hσ hφ) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 σ _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨m, fun h => ?_⟩
    show f.1 (φ h) = σ' h m - m
    rw [hσ]; exact hm (φ h)

def rz2 : Z2 σ →ₗ[R] Z2 σ' where
  toFun f := ⟨fun p => f.1 (φ p.1, φ p.2), f.2.1.comp (hφ.prodMap hφ), fun g h k => by
    simp only [map_mul, hσ]; exact f.2.2 _ _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rh2 : H2 σ →ₗ[R] H2 σ' :=
  Submodule.mapQ _ _ (rz2 σ σ' φ hσ hφ) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem σ _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ φ, hc.comp hφ, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    have e := congrFun hcf (φ g, φ h)
    simp only [Submodule.coe_subtype] at e
    change _ = f.1 (φ g, φ h)
    rw [← e]
    simp [d1_apply, hσ, map_mul]

end Res

section Equiv

variable {R : Type*} [CommRing R]
  {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N) (e : Γ' ≃* Γ)
  (he : Continuous e) (he' : Continuous e.symm)

theorem symm_rel (hσ : ∀ g n, σ' g n = σ (e g) n) : ∀ g n, σ g n = σ' (e.symm g) n := fun g n => by
  rw [hσ, MulEquiv.apply_symm_apply]

def eq0 (hσ : ∀ g n, σ' g n = σ (e g) n) : H0 σ ≃ₗ[R] H0 σ' :=
  LinearEquiv.ofLinear (rh0 σ σ' e.toMonoidHom hσ)
    (rh0 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ)) (by ext; rfl) (by ext; rfl)

def eq1 (hσ : ∀ g n, σ' g n = σ (e g) n) : H1 σ ≃ₗ[R] H1 σ' :=
  LinearEquiv.ofLinear (rh1 σ σ' e.toMonoidHom hσ he)
    (rh1 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ) he')
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => by
        show f.1 (e.symm (e g)) = f.1 g
        rw [MulEquiv.symm_apply_apply])))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => by
        show f.1 (e (e.symm g)) = f.1 g
        rw [MulEquiv.apply_symm_apply])))

def eq2 (hσ : ∀ g n, σ' g n = σ (e g) n) : H2 σ ≃ₗ[R] H2 σ' :=
  LinearEquiv.ofLinear (rh2 σ σ' e.toMonoidHom hσ he)
    (rh2 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ) he')
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => by
        show f.1 (e.symm (e p.1), e.symm (e p.2)) = f.1 p
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply])))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => by
        show f.1 (e (e.symm p.1), e (e.symm p.2)) = f.1 p
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])))

end Equiv

theorem bijective_of_conj {R : Type*} [CommRing R] {A B C A' B' C' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
    (b : A →ₗ[R] B →ₗ[R] C) (b' : A' →ₗ[R] B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B')
    (eC : C ≃ₗ[R] C') (h : ∀ a x, b' (eA a) (eB x) = eC (b a x)) (hb : Function.Bijective b') :
    Function.Bijective b := by
  have key : (⇑b' ∘ ⇑eA) = ⇑(LinearEquiv.arrowCongr eB eC) ∘ ⇑b := by
    funext a
    refine LinearMap.ext fun x => ?_
    simp only [Function.comp_apply, LinearEquiv.arrowCongr_apply]
    rw [← h, LinearEquiv.apply_symm_apply]
  have h2 : Function.Bijective (⇑(LinearEquiv.arrowCongr eB eC) ∘ ⇑b) := key ▸ hb.comp eA.bijective
  exact (LinearEquiv.bijective _).of_comp_iff' _ |>.1 h2

theorem dualityClauses_of_mulEquiv : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (h : ContAction ρ) (h' : ContAction (ρ.comp e.toMonoidHom)), (Nonempty (H2 (charRep (χ.comp e.toMonoidHom)) ≃ₗ[R] R) ∧ Function.Bijective (cupH0H2TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)) ∧ Function.Bijective (cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _) (h'.comp' continuous_id)) ∧ Function.Bijective (cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _) (h'.comp' continuous_id)).flip ∧ Function.Bijective (cup20 (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _))) → (Nonempty (H2 (charRep χ) ≃ₗ[R] R) ∧ Function.Bijective (cupH0H2TwistedDual χ ρ (MonoidHom.id _)) ∧ Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id)) ∧ Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id)).flip ∧ Function.Bijective (cup20 χ ρ (MonoidHom.id _))) := by
  intro R _ _ _ Γ Γ' _ _ _ _ M _ _ _ _ _ e he he' χ ρ h h' H
  have hA : ∀ g m, ((ρ.comp e.toMonoidHom).comp (MonoidHom.id Γ')) g m =
      (ρ.comp (MonoidHom.id Γ)) (e g) m := fun _ _ => rfl
  have hB : ∀ g φ, ((twDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).comp
      (MonoidHom.id Γ')) g φ = ((twDual χ ρ).comp (MonoidHom.id Γ)) (e g) φ := by
    intro g φ
    refine TDual.ext fun m => ?_
    simp [twDual_apply, map_inv]
  have hC : ∀ g x, ((charRep (χ.comp e.toMonoidHom)).comp (MonoidHom.id Γ')) g x =
      ((charRep χ).comp (MonoidHom.id Γ)) (e g) x := fun _ _ => rfl
  let E0A := eq0 _ _ e hA
  let E0B := eq0 _ _ e hB
  let FrameLocalData := eq1 _ _ e he he' hA
  let E1B := eq1 _ _ e he he' hB
  let E2A := eq2 _ _ e he he' hA
  let E2B := eq2 _ _ e he he' hB
  let E2C := eq2 _ _ e he he' hC
  have c02 : ∀ m y, cupH0H2TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (E0A m) (E2B y) = E2C (cupH0H2TwistedDual χ ρ (MonoidHom.id _) m y) := by
    intro m y
    induction y using Submodule.Quotient.induction_on with
    | H f => rfl
  have c11 : ∀ y x, cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (h'.comp' continuous_id) (E1B y) (FrameLocalData x) =
      E2C (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id) y x) := by
    intro y x
    induction y using Submodule.Quotient.induction_on with
    | H f =>
      induction x using Submodule.Quotient.induction_on with
      | H f' => rfl
  have c20 : ∀ x m, cup20 (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (E2A x) (E0B m) = E2C (cup20 χ ρ (MonoidHom.id _) x m) := by
    intro x m
    induction x using Submodule.Quotient.induction_on with
    | H f => rfl
  obtain ⟨⟨j⟩, b02, b11, b11', b20⟩ := H
  refine ⟨⟨(eq2 (charRep χ) (charRep (χ.comp e.toMonoidHom)) e he he' (fun _ _ => rfl)).trans j⟩,
    bijective_of_conj _ _ E0A E2B E2C c02 b02, bijective_of_conj _ _ E1B FrameLocalData E2C c11 b11,
    bijective_of_conj _ _ FrameLocalData E1B E2C (fun x y => by simp only [LinearMap.flip_apply]; exact c11 y x) b11',
    bijective_of_conj _ _ E2A E0B E2C c20 b20⟩

end GlobalTheory.CohTransport
