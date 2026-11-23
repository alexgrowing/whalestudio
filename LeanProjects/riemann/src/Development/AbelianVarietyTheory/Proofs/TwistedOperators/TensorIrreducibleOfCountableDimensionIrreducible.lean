import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TensIrr

theorem eq_smul_of_ann {V : Type} [AddCommGroup V] [Module ℂ V] (SV : Set (Module.End ℂ V))
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤)
    (v₀ w : V) (hv₀ : v₀ ≠ 0)
    (h : ∀ a ∈ Algebra.adjoin ℂ SV, a v₀ = 0 → a w = 0) : ∃ c : ℂ, w = c • v₀ := by
  let A := Algebra.adjoin ℂ SV
  let ev : V → (A →ₗ[ℂ] V) := fun y =>
    { toFun := fun a => (a : Module.End ℂ V) y
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hev : ∀ y (a : A), ev y a = (a : Module.End ℂ V) y := fun _ _ => rfl
  have hsurj : Function.Surjective (ev v₀) := by
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (ev v₀)) (fun s hs x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact ⟨⟨s * a, mul_mem (Algebra.subset_adjoin hs) a.2⟩, rfl⟩) with h0 | h0
    · exfalso; apply hv₀
      have h1 : ev v₀ 1 ∈ LinearMap.range (ev v₀) := LinearMap.mem_range_self _ _
      rw [h0, Submodule.mem_bot] at h1
      simpa [hev] using h1
    · exact h0
  have hker : LinearMap.ker (ev v₀) ≤ LinearMap.ker (ev w) := fun a ha => by
    rw [LinearMap.mem_ker, hev] at ha ⊢
    exact h a a.2 ha
  let φ : Module.End ℂ V := ((LinearMap.ker (ev v₀)).liftQ (ev w) hker).comp
    (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm.toLinearMap
  have hφ : ∀ a : A, φ ((a : Module.End ℂ V) v₀) = (a : Module.End ℂ V) w := by
    intro a
    have h2 : (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm (ev v₀ a) =
        Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hev v₀, h2, Submodule.liftQ_apply, hev]
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar SV V (fun s => s.1) hrank
    (fun N hN => hirr N (fun a ha x hx => hN ⟨a, ha⟩ x hx)) φ (fun s => by
      ext y
      obtain ⟨a, rfl⟩ := hsurj y
      have h1 : φ ((s.1 * (a : Module.End ℂ V)) v₀) = (s.1 * (a : Module.End ℂ V)) w :=
        hφ ⟨s.1 * a, mul_mem (Algebra.subset_adjoin s.2) a.2⟩
      simp only [Module.End.mul_apply, hev] at h1 ⊢
      rw [h1, hφ a])
  refine ⟨c, ?_⟩
  have h3 := hφ 1
  simp only [OneMemClass.coe_one, Module.End.one_apply] at h3
  rw [← h3, hc]
  simp

theorem rTensor_mem_adjoin {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (SV : Set (Module.End ℂ V)) (N : Submodule ℂ (V ⊗[ℂ] U))
    (hN : ∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) :
    ∀ a ∈ Algebra.adjoin ℂ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact hN a ha
  | algebraMap r =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.rTensor_smul, Module.End.one_eq_id,
      LinearMap.rTensor_id]
    simpa using N.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_add, LinearMap.add_apply]
    exact N.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)

theorem tensor_irreducible : ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (SV : Set (Module.End ℂ V))
    (SU : Set (Module.End ℂ U)), Module.rank ℂ V ≤ Cardinal.aleph0 → Nontrivial V →
    (∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    (∀ N : Submodule ℂ U, (∀ b ∈ SU, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (V ⊗[ℂ] U), (∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) →
      (∀ b ∈ SU, ∀ x ∈ N, LinearMap.lTensor V b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro V U _ _ _ _ SV SU hrank _ hV hU N hNV hNU
  classical
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨x₁, hx₁N, hx₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let b := Module.Free.chooseBasis ℂ U
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : ∀ (a : Module.End ℂ V) y j, e (LinearMap.rTensor U a y) j = a (e y j) := by
    intro a y j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  have hex : ∃ n, ∃ y ∈ N, y ≠ 0 ∧ (e y).support.card = n := ⟨_, x₁, hx₁N, hx₁, rfl⟩
  obtain ⟨x, hxN, hx0, hxc⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ N, (e y).support.card < (e x).support.card → y = 0 := by
    intro y hy hlt
    by_contra hy0
    exact Nat.find_min hex (hxc ▸ hlt) ⟨y, hy, hy0, rfl⟩
  obtain ⟨j₀, hj₀⟩ : (e x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact (LinearEquiv.map_ne_zero_iff e).mpr hx0
  set v₀ := e x j₀ with hv₀def
  have hv₀ : v₀ ≠ 0 := Finsupp.mem_support_iff.mp hj₀
  have hA := rTensor_mem_adjoin SV N hNV
  have hcol : ∀ j, ∃ c : ℂ, e x j = c • v₀ := by
    intro j
    refine eq_smul_of_ann SV hrank hV v₀ (e x j) hv₀ (fun a ha hav => ?_)
    have hy := hmin _ (hA a ha x hxN) (by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j₀, hj₀, ?_⟩
        rw [Finsupp.mem_support_iff, not_not, he]
        exact hav
      · intro i hi
        rw [Finsupp.mem_support_iff] at hi ⊢
        intro h0
        apply hi
        rw [he, h0, map_zero])
    have h5 := he a x j
    rw [hy, map_zero, Finsupp.zero_apply] at h5
    exact h5.symm
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hv₀
  let u : U := b.repr.symm ((e x).mapRange ℓ (map_zero ℓ))
  have hxu : x = v₀ ⊗ₜ u := by
    apply e.injective
    ext j
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    simp only [u, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    obtain ⟨c, hc⟩ := hcol j
    rw [hc, map_smul, hℓ, smul_eq_mul, mul_one]
  have hu : u ≠ 0 := by
    intro hu0
    apply hx0
    rw [hxu, hu0, TensorProduct.tmul_zero]
  have hP : N.comap ((TensorProduct.mk ℂ V U).flip u) = ⊤ := by
    rcases hV (N.comap ((TensorProduct.mk ℂ V U).flip u)) (fun a ha v hv => by
      simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hv ⊢
      have h6 := hNV a ha _ hv
      rwa [LinearMap.rTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : v₀ ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply]
        rw [← hxu]; exact hxN
      rw [h0, Submodule.mem_bot] at h7
      exact hv₀ h7
    · exact h0
  have hQ : ∀ v : V, N.comap (TensorProduct.mk ℂ V U v) = ⊤ := by
    intro v
    rcases hU (N.comap (TensorProduct.mk ℂ V U v)) (fun c hc y hy => by
      simp only [Submodule.mem_comap, TensorProduct.mk_apply] at hy ⊢
      have h6 := hNU c hc _ hy
      rwa [LinearMap.lTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : u ∈ N.comap (TensorProduct.mk ℂ V U v) := by
        have h8 : v ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by rw [hP]; trivial
        simpa using h8
      rw [h0, Submodule.mem_bot] at h7
      exact hu h7
    · exact h0
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨m, n, rfl⟩
  have h9 : n ∈ N.comap (TensorProduct.mk ℂ V U m) := by rw [hQ m]; trivial
  simpa using h9

end GlobalTheory.TensIrr
