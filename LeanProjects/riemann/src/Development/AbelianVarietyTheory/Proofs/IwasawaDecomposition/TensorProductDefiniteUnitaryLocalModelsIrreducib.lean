import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

theorem subalgebra_eq_top_of_irreducible {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (A : Subalgebra ℂ (Module.End ℂ X))
    (h : ∀ U : Submodule ℂ X, (∀ a ∈ A, ∀ x ∈ U, a x ∈ U) → U = ⊥ ∨ U = ⊤) : A = ⊤ := by
  classical
  rcases subsingleton_or_nontrivial X with hX | hX
  · refine eq_top_iff.2 fun f _ => ?_
    rw [Subsingleton.elim f 0]
    exact A.zero_mem
  haveI : IsSimpleModule A X := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun U => ?_ }
    rcases h (U.restrictScalars ℂ) (fun a ha x hx => U.smul_mem (⟨a, ha⟩ : A) hx) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff ℂ A X).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff ℂ A X).1 h1
  have hscal : ∀ φ : Module.End A X, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := X) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  refine eq_top_iff.2 fun f _ => ?_
  let F : Module.End (Module.End A X) X :=
    { toFun := fun m => f m
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis ℂ X
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have : f = (r : Module.End ℂ X) :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]
  exact r.2

theorem piTensor_irreducible {ι κ : Type} [Finite ι] [DecidableEq ι] {H : ι → Type} [∀ i, AddCommGroup (H i)]
    [∀ i, Module ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] (σ : ∀ i, κ → Module.End ℂ (H i))
    (h : ∀ i, ∀ U : Submodule ℂ (H i), (∀ u, ∀ x ∈ U, σ i u x ∈ U) → U = ⊥ ∨ U = ⊤)
    (U : Submodule ℂ (⨂[ℂ] i, H i))
    (hU : ∀ i u, ∀ x ∈ U,
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i (σ i u)) x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  cases nonempty_fintype ι
  have hcomp : ∀ (f g : ∀ i, H i →ₗ[ℂ] H i) (x : ⨂[ℂ] i, H i),
      PiTensorProduct.map (fun i => f i ∘ₗ g i) x = PiTensorProduct.map f (PiTensorProduct.map g x) := by
    intro f g x
    rw [PiTensorProduct.map_comp]; rfl
  have h1 : ∀ i (a : Module.End ℂ (H i)), ∀ x ∈ U,
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i a) x ∈ U := by
    intro i
    let A : Subalgebra ℂ (Module.End ℂ (H i)) :=
      { carrier := {a | ∀ x ∈ U,
          PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i a) x ∈ U}
        mul_mem' := fun {a b} ha hb x hx => by
          have := ha _ (hb x hx)
          rw [← hcomp] at this
          convert this using 3
          funext ρ
          by_cases hρ : ρ = i
          · subst hρ; simp [Module.End.mul_eq_comp]
          · simp [Function.update_of_ne hρ]
        add_mem' := fun {a b} ha hb x hx => by
          rw [PiTensorProduct.map_update_add]
          exact U.add_mem (ha x hx) (hb x hx)
        algebraMap_mem' := fun c x hx => by
          rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul]
          have : Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i (1 : Module.End ℂ (H i)) =
              fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ) := Function.update_eq_self i _
          rw [this, PiTensorProduct.map_id]
          exact U.smul_mem c hx }
    have hA : A = ⊤ := subalgebra_eq_top_of_irreducible A fun W hW =>
      h i W fun u x hx => hW (σ i u) (hU i u) x hx
    intro a
    have : a ∈ A := hA ▸ Algebra.mem_top
    exact this
  have h2 : ∀ (f : ∀ i, H i →ₗ[ℂ] H i) (s : Finset ι), ∀ x ∈ U,
      PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) x ∈ U := by
    intro f s
    induction s using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert j s hj ih =>
      intro x hx
      have := h1 j (f j) _ (ih x hx)
      rw [← hcomp] at this
      convert this using 3
      funext ρ
      by_cases hρ : ρ = j
      · subst hρ; simp [hj]
      · simp [hρ]
  have h3 : ∀ (f : ∀ i, H i →ₗ[ℂ] H i), ∀ x ∈ U, PiTensorProduct.map f x ∈ U := by
    intro f x hx
    simpa using h2 f Finset.univ x hx
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨x, hxU, hx⟩ := (Submodule.ne_bot_iff U).1 hne
  let b := fun i => Module.finBasis ℂ (H i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr x p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have e : PiTensorProduct.map (fun i => ((b i).coord (p i)).smulRight (v i)) =
      (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
    ext w
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply]
    exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
  have h4 := h3 (fun i => ((b i).coord (p i)).smulRight (v i)) x hxU
  rw [e] at h4
  exact (U.smul_mem_iff hp).1 h4

theorem tensor_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤) → AllPlus M → FiniteDimensional ℂ (SmT M) ∧ Function.Injective (inclT M) ∧ ∃ π, IsTensAct M π ∧ IrrFam π := by
  intro D V S M h _
  classical
  haveI := fun τ => (h τ).1
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (h τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  refine ⟨inferInstance, fun x y hxy => e.injective hxy,
    fun τ u => e.symm.toLinearMap ∘ₗ actT M τ (unfr M τ u) ∘ₗ e.toLinearMap, fun τ u x => ?_, fun U hU => ?_⟩
  · rw [← he, ← he]
    simp
  · have := piTensor_irreducible (fun τ (u : Matrix.unitaryGroup (Fin V.rank) ℂ) => (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ))
      (fun τ => (h τ).2.2) (U.map e.toLinearMap) (by
        rintro τ u _ ⟨x, hx, rfl⟩
        refine ⟨_, hU τ u x hx, ?_⟩
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, actT, rep_unfr])
    rcases this with h1 | h1
    · exact Or.inl ((Submodule.map_eq_bot_iff).1 h1)
    · exact Or.inr ((Submodule.map_eq_top_iff).1 h1)

end GlobalTheory.DefLift
