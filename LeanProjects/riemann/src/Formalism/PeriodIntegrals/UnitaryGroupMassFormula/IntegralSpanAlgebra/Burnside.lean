import Mathlib
import Formalism.PeriodIntegrals.UMultOne

noncomputable section

namespace PI.UMultOne.GelfSpanWork

open Matrix Module

variable {G : Type} [Group G] {N : ℕ}

def repEnd (ρ : G →* GL (Fin N) ℂ) : G →* Module.End ℂ (Fin N → ℂ) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  map_one' := by simp; rfl
  map_mul' x y := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

theorem repEnd_apply (ρ : G →* GL (Fin N) ℂ) (g : G) (v : Fin N → ℂ) :
    repEnd ρ g v = ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v := by
  simp [repEnd, Matrix.toLin'_apply]

def spanAlg (ρ : G →* GL (Fin N) ℂ) : Subalgebra ℂ (Module.End ℂ (Fin N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (repEnd ρ))

instance spanAlg_tower (ρ : G →* GL (Fin N) ℂ) : IsScalarTower ℂ (spanAlg ρ) (Fin N → ℂ) :=
  ⟨fun _ _ _ => rfl⟩

theorem spanAlg_smul (ρ : G →* GL (Fin N) ℂ) (a : spanAlg ρ) (v : Fin N → ℂ) :
    a • v = (a : Module.End ℂ (Fin N → ℂ)) v := rfl

theorem spanAlg_toSubmodule (ρ : G →* GL (Fin N) ℂ) :
    Subalgebra.toSubmodule (spanAlg ρ) = Submodule.span ℂ (Set.range (repEnd ρ)) := by
  rw [spanAlg, Algebra.adjoin_eq_span]
  congr 1
  rw [← MonoidHom.coe_mrange, Submonoid.closure_eq]

theorem repEnd_mem (ρ : G →* GL (Fin N) ℂ) (g : G) : repEnd ρ g ∈ spanAlg ρ :=
  Algebra.subset_adjoin ⟨g, rfl⟩

theorem spanAlg_simple (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ) :
    IsSimpleModule (spanAlg ρ) (Fin N → ℂ) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nontrivial (Fin N → ℂ) := inferInstance
  refine { eq_bot_or_eq_top := fun S => ?_ }
  have hT := hI (S.restrictScalars ℂ) (fun g v hv => by
    have := S.smul_mem ⟨repEnd ρ g, repEnd_mem ρ g⟩ hv
    rw [spanAlg_smul] at this
    simpa [repEnd_apply] using this)
  rcases hT with hT | hT
  · left
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ S.restrictScalars ℂ := hv
    rw [hT] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    have : v ∈ S.restrictScalars ℂ := by rw [hT]; trivial
    exact this

theorem schur (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ)
    (φ : (Fin N → ℂ) →ₗ[spanAlg ρ] (Fin N → ℂ)) : ∃ c : ℂ, ∀ v, φ v = c • v := by
  have := spanAlg_simple ρ hN hI
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrictScalars ℂ)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, fun w => ?_⟩
  let K : Submodule (spanAlg ρ) (Fin N → ℂ) :=
    { carrier := {w | φ w = c • w}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        rw [map_add, ha, hb, smul_add]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_ofPred_eq] at *
        rw [map_smul, hx, spanAlg_smul, spanAlg_smul, map_smul] }
  have hvK : v ∈ K := by
    have := hv.apply_eq_smul
    simpa [K] using this
  have hK : K = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exfalso
      have : v ∈ (⊥ : Submodule (spanAlg ρ) (Fin N → ℂ)) := h ▸ hvK
      exact hv.2 ((Submodule.mem_bot _).mp this)
    · exact h
  have : w ∈ K := hK ▸ Submodule.mem_top
  exact this

theorem spanAlg_eq_top (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ) :
    ∀ f : Module.End ℂ (Fin N → ℂ), f ∈ spanAlg ρ := by
  intro f
  have := spanAlg_simple ρ hN hI
  let F : Module.End (Module.End (spanAlg ρ) (Fin N → ℂ)) (Fin N → ℂ) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro φ v
        obtain ⟨c, hc⟩ := schur ρ hN hI φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image (fun i => Pi.single i (1 : ℂ)))
  have : (r : Module.End ℂ (Fin N → ℂ)) = f := by
    apply (Pi.basisFun ℂ (Fin N)).ext
    intro i
    have := hr (Pi.single i 1) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [Pi.basisFun_apply, ← spanAlg_smul]
    exact this.symm
  exact this ▸ r.2

theorem functional_eq_zero (ρ : G →* GL (Fin N) ℂ) (hI : Irr ρ)
    (ℓ : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ g, ℓ ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 0) : ℓ = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    ext T
    have : T = 0 := Subsingleton.elim _ _
    simp [this]
  let ℓ' : Module.End ℂ (Fin N → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ (Matrix.toLin' (R := ℂ) (m := Fin N) (n := Fin N)).symm.toLinearMap
  have hspan : Submodule.span ℂ (Set.range (repEnd ρ)) ≤ LinearMap.ker ℓ' := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    simp [ℓ', repEnd, h]
  have h' : ∀ f, ℓ' f = 0 := by
    intro f
    have hf : f ∈ Subalgebra.toSubmodule (spanAlg ρ) := spanAlg_eq_top ρ hN hI f
    rw [spanAlg_toSubmodule] at hf
    exact hspan hf
  ext T
  have := h' (Matrix.toLin' T)
  simpa [ℓ'] using this

end PI.UMultOne.GelfSpanWork
