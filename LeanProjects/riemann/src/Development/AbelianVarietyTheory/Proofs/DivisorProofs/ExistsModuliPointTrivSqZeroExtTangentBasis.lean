import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TanBasis

open TensorProduct

theorem exists_tan_basis {R A K ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Fintype ι] {n : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (xr : A →+* K) (hι : Fintype.card ι = n) :
    ∃ Φ : A →+* TrivSqZeroExt K (ι → K), (∀ a, (Φ a).fst = xr a) ∧ (∀ r, (Φ (algebraMap R A r)).snd = 0) ∧
      ∀ M M' : ι → K, (∀ a, ∑ k, (Φ a).snd k * M k = ∑ k, (Φ a).snd k * M' k) → M = M' := by
  classical
  haveI := GlobalTheory.AugCot.smooth_of_locally h
  letI : Algebra A K := xr.toAlgebra
  have hrank : Module.finrank K (K ⊗[A] Ω[A⁄R]) = n := by
    have h1 := Module.rankAtStalk_baseChange (R := A) (M := Ω[A⁄R]) (S := K) (IsLocalRing.closedPoint K)
    rw [Module.rankAtStalk_eq_finrank_of_free, GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally h] at h1
    exact_mod_cast h1
  let b : Module.Basis ι K (K ⊗[A] Ω[A⁄R]) :=
    (Module.finBasisOfFinrankEq K _ hrank).reindex (Fintype.equivFinOfCardEq hι).symm
  let δ : A → (ι → K) := fun a => b.equivFun (1 ⊗ₜ KaehlerDifferential.D R A a)
  have hsm : ∀ (a : A) (m : Ω[A⁄R]), (1 : K) ⊗ₜ[A] (a • m) = xr a • ((1 : K) ⊗ₜ[A] m) := by
    intro a m
    rw [TensorProduct.tmul_smul, ← algebraMap_smul K a]
    rfl
  have hδmul : ∀ a a', δ (a * a') = xr a • δ a' + xr a' • δ a := by
    intro a a'
    simp only [δ, Derivation.leibniz, TensorProduct.tmul_add, hsm, map_add, map_smul]
  have hδadd : ∀ a a', δ (a + a') = δ a + δ a' := by
    intro a a'; simp only [δ, map_add, TensorProduct.tmul_add]
  have hδalg : ∀ r, δ (algebraMap R A r) = 0 := by
    intro r; simp only [δ, Derivation.map_algebraMap, TensorProduct.tmul_zero, map_zero]
  have hδ1 : δ 1 = 0 := by simpa using hδalg 1
  have hδ0 : δ 0 = 0 := by simp only [δ, map_zero, TensorProduct.tmul_zero]
  let Φ : A →+* TrivSqZeroExt K (ι → K) :=
    { toFun := fun a => TrivSqZeroExt.inl (xr a) + TrivSqZeroExt.inr (δ a)
      map_one' := by ext <;> simp [hδ1]
      map_mul' := fun a a' => by
        ext k
        · simp
        · simp [hδmul, TrivSqZeroExt.snd_mul, add_comm]
      map_zero' := by ext <;> simp [hδ0]
      map_add' := fun a a' => by ext <;> simp [hδadd] }
  refine ⟨Φ, fun a => by simp [Φ], fun r => by simp [Φ, hδalg], fun M M' hM => ?_⟩
  let L : (ι → K) → (K ⊗[A] Ω[A⁄R] →ₗ[K] K) := fun M => Fintype.linearCombination K M ∘ₗ b.equivFun.toLinearMap
  have hL : ∀ M : ι → K, ∀ a, L M (1 ⊗ₜ KaehlerDifferential.D R A a) = ∑ k, (Φ a).snd k * M k := by
    intro M a
    simp [L, Φ, δ, Fintype.linearCombination_apply, smul_eq_mul]
  have hLL : L M = L M' := by
    apply (LinearMap.liftBaseChangeEquiv K).symm.injective
    refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A) fun a => ?_
    rw [LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.liftBaseChangeEquiv_symm_apply, hL, hL, hM]
  funext j
  have := LinearMap.congr_fun hLL (b j)
  simpa [L, Finsupp.single_eq_pi_single, Fintype.linearCombination_apply_single] using this

end GlobalTheory.TanBasis

namespace GlobalTheory.TanBasis

theorem exists_point_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι], Fintype.card ι = Dw.dim → ∃ X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x ∧ Function.Injective (fun M : ι → K => spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  intro E _ _ _ H Dw l Xo c K _ _ y ι _ hι
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y.x (IsLocalRing.closedPoint K)) (U := ⊤) trivial
  have hrange : Set.range y.x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]
  let y' := IsOpenImmersion.lift hU.fromSpec y.x hrange
  have hy' : y' ≫ hU.fromSpec = y.x := IsOpenImmersion.lift_fac _ _ _
  let g := Spec.preimage (hU.fromSpec ≫ Xo.s)
  have hg : Spec.map g = hU.fromSpec ≫ Xo.s := Spec.map_preimage _
  let xr := Spec.preimage y'
  have hxr : Spec.map xr = y' := Spec.map_preimage _
  haveI := Xo.smooth
  have hsm : SmoothOfRelativeDimension Dw.dim (Spec.map g) := by
    rw [hg]
    have := (inferInstance : SmoothOfRelativeDimension (0 + Dw.dim) (hU.fromSpec ≫ Xo.s))
    rwa [zero_add] at this
  have hloc := HasRingHomProperty.Spec_iff.1 hsm
  letI : Algebra (KA l) Γ(Xo.X, U) := g.hom.toAlgebra
  obtain ⟨Φ, h1, h2, h3⟩ := exists_tan_basis (R := KA l) (A := Γ(Xo.X, U)) hloc xr.hom hι
  have hbase : ∀ r, xr.hom (g.hom r) = algebraMap c.F K (IntermediateField.inclusion c.le r) := by
    have : Spec.map (g ≫ xr) = sOf c K := by
      rw [Spec.map_comp, hxr, hg, ← Category.assoc, hy', y.x_over]
    intro r
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective this)) r
  have hfst : (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom.comp Φ = xr.hom := by
    ext a; exact h1 a
  refine ⟨spMap Φ ≫ hU.fromSpec, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hg, spMap, ← Spec.map_comp, sOf]
    have hΦg : Φ.comp g.hom =
        (algebraMap c.F (TrivSqZeroExt K (ι → K))).comp (IntermediateField.inclusion c.le).toRingHom := by
      refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
      · rw [RingHom.comp_apply, h1, hbase]
        simp [TrivSqZeroExt.algebraMap_eq_inl']
      · rw [RingHom.comp_apply, show g.hom r = algebraMap (KA l) Γ(Xo.X, U) r from rfl, h2]
        simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [← hΦg]
    rfl
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom.comp Φ)) ≫ _ = _
    rw [hfst]
    change Spec.map xr ≫ _ = _
    rw [hxr, hy']
  · intro M M' hMM
    simp only at hMM
    rw [← Category.assoc, ← Category.assoc, cancel_mono, spMap, spMap, spMap, ← Spec.map_comp,
      ← Spec.map_comp] at hMM
    have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hMM)
    apply h3
    intro a
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hr a)
    simpa using this

end GlobalTheory.TanBasis
