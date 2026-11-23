import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HopfPoints

theorem integral_of_integral_tensor : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (F : K ⊗[R] CartierDual R A →ₗ[K] K ⊗[R] A) (T : A ⊗[R] A), (∀ s s' : A →ₐ[R] R, algebraMap R K (Algebra.TensorProduct.lift s s' (fun _ _ => .all _ _) T) = Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s') (fun _ _ => .all _ _) (F ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R A)))) → ∀ l : CartierDual R A, ∃ a : A, F ((1 : K) ⊗ₜ[R] l) = (1 : K) ⊗ₜ[R] a := by
  intro R K _ _ _ _ _ _ _ _ A _ _ _ _ _ F T h l
  obtain ⟨hfin, hsep, -⟩ := finite_points_separate_rank R K A
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let p : (A →ₐ[R] R) → (K ⊗[R] A →ₐ[K] K) := fun s =>
    Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s) (fun _ _ => .all _ _)
  have hp : ∀ s (k : K) (a : A), p s (k ⊗ₜ a) = k * algebraMap R K (s a) := fun s k a => by
    simp [p, Algebra.ofId_apply]
  haveI : Finite (A →ₐ[R] R) :=
    Finite.of_injective (fun s : A →ₐ[R] R => (Algebra.ofId R K).comp s) fun s t hst => by
      ext a
      exact hRK (DFunLike.congr_fun hst a)
  have sep : ∀ x : K ⊗[R] A, (∀ s, p s x = 0) → x = 0 := by
    intro x hx
    obtain ⟨⟨a, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors R)
      (TensorProduct.mk R K A 1) x
    have ha : a = 0 := hsep a fun ψ => by
      obtain ⟨g, rfl⟩ := exists_algHom_comp_eq (A := R) (K := K) ψ
      have h1 : p g ((c : R) • x) = 0 := by
        rw [← algebraMap_smul K, map_smul, hx, smul_zero]
      have h2 : (c : R) • x = (1 : K) ⊗ₜ[R] a := hc
      rw [h2, hp, _root_.one_mul] at h1
      exact h1
    have h2 : (c : R) • x = (1 : K) ⊗ₜ[R] a := hc
    rw [ha, TensorProduct.tmul_zero, ← algebraMap_smul K, smul_eq_zero] at h2
    refine h2.resolve_left fun h0 => nonZeroDivisors.coe_ne_zero c (hRK ?_)
    rw [h0, map_zero]
  let g : CartierDual R A →ₗ[R] A :=
    (TensorProduct.lid R A).toLinearMap ∘ₗ (LinearMap.applyₗ T) ∘ₗ
      (LinearMap.rTensorHom A) ∘ₗ (CartierDual.toDual R A).toLinearMap
  have hg : ∀ φ : CartierDual R A, g φ = TensorProduct.lid R A (φ.ofConv.rTensor A T) :=
    fun _ => rfl
  have key : ∀ s : A →ₐ[R] R, F ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R A)) =
      g.baseChange K ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R A)) := by
    intro s
    rw [← sub_eq_zero]
    refine sep _ fun s' => ?_
    rw [map_sub, sub_eq_zero, LinearMap.baseChange_tmul, hp, _root_.one_mul, hg]
    refine (h s s').symm.trans (congrArg _ ?_)
    clear h hg g
    induction T with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp
  let B : K ⊗[R] CartierDual R A →ₗ[K] Module.Dual K (K ⊗[R] A) :=
    (CartierDual.toDual K (K ⊗[R] A)).toLinearMap ∘ₗ CartierDual.baseChangeLinear R K A
  have hB : Function.Injective B :=
    (CartierDual.toDual K (K ⊗[R] A)).injective.comp (CartierDual.baseChangeLinear_bijective K).1
  let v : (A →ₐ[R] R) → K ⊗[R] CartierDual R A := fun s =>
    (1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R A)
  have hBv : ∀ s, B (v s) = (p s).toLinearMap := fun s => by
    ext a
    have := CartierDual.baseChangeLinear_tmul_tmul (R := R) K 1 1 (toConv s.toLinearMap : CartierDual R A) a
    simp only [LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, hp]
    refine this.trans ?_
    simp [Algebra.smul_def]
  have hmem : B ((1 : K) ⊗ₜ[R] l) ∈ Submodule.span K (Set.range fun s => B (v s)) := by
    refine mem_span_of_iInf_ker_le_ker fun x hx => ?_
    have : x = 0 := sep x fun s => by
      have := (Submodule.mem_iInf _).1 hx s
      rwa [hBv] at this
    rw [this]; exact Submodule.zero_mem _
  have hmem' : (1 : K) ⊗ₜ[R] l ∈ Submodule.span K (Set.range v) := by
    have e : (Set.range fun s => B (v s)) = B '' Set.range v := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span] at hmem
    obtain ⟨y, hy, hyl⟩ := hmem
    rwa [← hB hyl]
  refine ⟨g l, ?_⟩
  rw [← LinearMap.baseChange_tmul]
  exact LinearMap.eqOn_span (f := F) (g := g.baseChange K) (by rintro _ ⟨s, rfl⟩; exact key s) hmem'

end GlobalTheory.HopfPoints
