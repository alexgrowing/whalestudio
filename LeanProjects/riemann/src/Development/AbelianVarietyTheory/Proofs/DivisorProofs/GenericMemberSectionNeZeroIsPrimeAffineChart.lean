import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericLinearFormPrime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory.GenericMember

theorem genSec_chart_ne_zero_and_isPrime : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  intro k _ N X X' _ f f' π L hL b V hne hW c hVc j hj
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  intro e he1 he2
  haveI : Nonempty V := hne.to_subtype
  set a : Fin N → Γ(X, V) := fun i => resG X hVc ((b i).f c) with ha
  set t₀ : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) :=
    ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i with ht
  obtain ⟨ht0, hI⟩ := GlobalTheory.GenericForm.span_genericForm_isPrime_or_eq_top k Γ(X, V) N a j hj t₀ rfl
  have hWU : π ⁻¹ᵁ V ≤ (L.pull π).U (fun _ => c) := fun x hx => Set.mem_iInter.2 fun _ => hVc hx
  have hsum : ∀ J, (genSec k N f' π L b).f J =
      ∑ i, resG X' le_top (genVar k N f' i) * (secPull (b i) π).f J := by
    intro J
    let F : (L.pull π).Sec →+ Γ(X', (L.pull π).U J) :=
      { toFun := fun s => s.f J, map_zero' := rfl, map_add' := fun _ _ => rfl }
    show F (∑ i, genVar k N f' i • secPull (b i) π) = _
    rw [map_sum]
    rfl
  have key : resG X' hWU ((genSec k N f' π L b).f (fun _ => c)) = e t₀ := by
    rw [hsum (fun _ => c), map_sum, ht, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    have hq : algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i =
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] (1 : Γ(X, V))) *
          ((1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] a i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hq, map_mul, he1, he2]
    congr 1
    · have e2 : f'.appTop ≫ X'.presheaf.map (homOfLE (le_top : (L.pull π).U (fun _ => c) ≤ ⊤)).op ≫
          X'.presheaf.map (homOfLE hWU).op = f'.appLE ⊤ (π ⁻¹ᵁ V) le_top := by
        simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv.hom
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))) e2
    · have e1 : π.appLE (L.U c) ((L.pull π).U (fun _ => c)) ((GlobalTheory.chartPullPull L π).le (fun _ => c)) ≫
          X'.presheaf.map (homOfLE hWU).op = X.presheaf.map (homOfLE hVc).op ≫ π.app V := by
        rw [Scheme.Hom.naturality]
        simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((b i).f c)) e1
  have hid : (secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ =
      Ideal.span {e t₀} := by
    rw [ideal_secIdeal (LB.isLB_pull hL π) _ ⟨π ⁻¹ᵁ V, hW⟩ (fun _ => c) hWU]
    exact congrArg (fun x => Ideal.span {x}) key
  have hmap : Ideal.span {e t₀} = Ideal.map e (Ideal.span {t₀}) := by
    rw [Ideal.map_span, Set.image_singleton]
  refine ⟨fun h0 => ht0 (e.injective ?_), ?_⟩
  · rw [map_zero, ← key, h0, map_zero]
  · rw [hid]
    rcases hI with h | ⟨hp, hx⟩
    · left
      rw [hmap, h, Ideal.map_top]
    · right
      refine ⟨?_, ?_⟩
      · haveI := hp
        rw [hmap]
        exact Ideal.map_isPrime_of_equiv e
      · rw [eq_bot_iff]
        intro x hx'
        rw [Ideal.mem_bot]
        apply hx x
        rw [Ideal.mem_comap, ← he1, Ideal.mem_span_singleton'] at hx'
        obtain ⟨d, hd⟩ := hx'
        rw [Ideal.mem_span_singleton']
        refine ⟨e.symm d, e.injective ?_⟩
        rw [map_mul, RingEquiv.apply_symm_apply, hd]

end GlobalTheory.GenericMember
