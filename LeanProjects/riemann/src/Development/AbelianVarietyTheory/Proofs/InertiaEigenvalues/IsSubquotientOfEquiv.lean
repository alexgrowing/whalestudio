import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacStages

section Rel

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] {β : α → Type} [∀ i, Fintype (β i)] [∀ i, LinearOrder (β i)]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : ∀ i, β i → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def relUnipD (f : ∀ i, (Σ j, c i j) ≃ m i) : Subgroup (Levi k m) :=
  Subgroup.pi Set.univ fun i => unipRad k (f i)

def relEmbD (f : ∀ i, (Σ j, c i j) ≃ m i) : (∀ i, Levi k (c i)) →* Levi k m :=
  MonoidHom.pi fun i => (leviEmb k (f i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

theorem relEmbD_apply (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) (i : α) :
    relEmbD k f g i = leviEmb k (f i) (g i) := rfl

theorem relEmbD_mem_normalizer (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) :
    relEmbD k f g ∈ Subgroup.normalizer (relUnipD k f : Set (Levi k m)) :=
  Subgroup.mem_normalizer_iff.2 fun u => forall₂_congr fun i _ =>
    Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (f i) (g i)) (u i)

def relDeltaHalfD (c : ∀ i, β i → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] :
    (∀ i, Levi k (c i)) →* ℂˣ :=
  ∏ i, (deltaHalf k (c i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

theorem relDeltaHalfD_apply (g : ∀ i, Levi k (c i)) :
    relDeltaHalfD k c g = ∏ i, deltaHalf k (c i) (g i) := by
  simp [relDeltaHalfD, MonoidHom.finsetProd_apply]

variable {k}

def relJacD (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (∀ i, Levi k (c i)) (Jacquet ρ (relUnipD k f)) :=
  twist (jacquet ρ (relUnipD k f) (relEmbD k f) (relEmbD_mem_normalizer k f)) (relDeltaHalfD k c)⁻¹

theorem relJacD_mk (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (g : ∀ i, Levi k (c i)) (v : W) :
    relJacD f ρ g (Submodule.Quotient.mk v) =
      (((relDeltaHalfD k c g)⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (ρ (relEmbD k f g) v) := rfl

end Rel

section Flat

variable {s : ℕ} {t : Fin s → ℕ}

def refinePlace {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) :
    (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun p : Σ a, Fin (t a) => Fin (d' p.1 p.2)) finSigmaFinEquiv.symm).trans
    ((Equiv.sigmaAssoc fun a b => Fin (d' a b)).trans ((Equiv.sigmaCongrRight e').trans e))

theorem refinePlace_apply {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a))
    (i : Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) :
    refinePlace e e' ⟨c, i⟩ =
      e ⟨(finSigmaFinEquiv.symm c).1, e' _ ⟨(finSigmaFinEquiv.symm c).2, i⟩⟩ := rfl

def flatHom (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    (∀ a b, Γ a b) →* ∀ c : Fin (∑ a, t a), Γ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 where
  toFun g c := g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem flatHom_apply (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] (g : ∀ a b, Γ a b)
    (c : Fin (∑ a, t a)) :
    flatHom Γ g c = g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 := rfl

theorem flatHom_surjective (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    Function.Surjective (flatHom Γ) := by
  have h : ⇑(flatHom Γ) = (Equiv.piCongrLeft' (fun p : Σ a, Fin (t a) => Γ p.1 p.2) finSigmaFinEquiv) ∘
      (Equiv.piCurry fun a b => Γ a b).symm := rfl
  rw [h]
  exact (Equiv.surjective _).comp (Equiv.surjective _)

end Flat

section Pull

variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSubquotient_of_comp {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (ψ : G' →* G)
    (hψ : Function.Surjective ψ) (h : IsSubquotient (σ.comp ψ) (ρ.comp ψ)) : IsSubquotient σ ρ := by
  obtain ⟨S, f, hf⟩ := h
  refine ⟨⟨S.toSubmodule, fun g v hv => ?_⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf⟩
  · obtain ⟨g', rfl⟩ := hψ g
    exact S.apply_mem_toSubmodule g' hv
  · obtain ⟨g', rfl⟩ := hψ g
    exact f.isIntertwining' g'

theorem isSubquotient_of_equiv {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (φ : σ.Equiv ρ) :
    IsSubquotient σ ρ :=
  .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective

end Pull

end GlobalTheory.JacStages
