import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CdvrFiniteAlgebra

theorem exists_cdvr_map_of_finite : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (R₁ : Type) [CommRing R₁] [Algebra (FractionRing V) R₁], Module.Finite (FractionRing V) R₁ → Nontrivial R₁ →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V →+* W) (ψ : R₁ →+* FractionRing W),
        GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        ∀ a, ψ (algebraMap (FractionRing V) R₁ (algebraMap V _ a)) = algebraMap W _ (f a) := by
  intro V _ _ _ hV R₁ _ _ hfin hnt
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  let K := FractionRing V
  let F := AlgebraicClosure K
  have hchK : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  have hchF : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

  obtain ⟨m, hm⟩ := Ideal.exists_maximal R₁
  letI : Field (R₁ ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (R₁ ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Algebra.IsAlgebraic K (R₁ ⧸ m) := Algebra.IsAlgebraic.of_finite K (R₁ ⧸ m)
  let t : R₁ →ₐ[K] F := (IsAlgClosed.lift : (R₁ ⧸ m) →ₐ[K] F).comp (Ideal.Quotient.mkₐ K m)

  haveI : IsScalarTower V K F := inferInstance
  haveI : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 (by
    rw [IsScalarTower.algebraMap_eq V K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective V K))
  haveI : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mpr inferInstance
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := K) (M := R₁)
  let s : Finset F := Finset.univ.image (fun i => t (b i))
  obtain ⟨W, hWd, hWc, -, hWfin, -, hWloc, hfrac, -⟩ :=
    GlobalTheory.exists_complete_dvr_finite_subalgebra V F s
  have hWch : CharZero W := ⟨fun m n h => Nat.cast_injective (R := F) (by simpa using congrArg Subtype.val h)⟩
  let φ : FractionRing W →+* F := IsFractionRing.lift (g := W.val.toRingHom) Subtype.val_injective
  have hφ : Function.Injective φ := φ.injective
  have hφa : ∀ w : W, φ (algebraMap W (FractionRing W) w) = w := fun w =>
    IsFractionRing.lift_algebraMap (g := W.val.toRingHom) Subtype.val_injective w
  have hVa : ∀ a : V, ((algebraMap V W a : W) : F) = algebraMap V F a := fun a => rfl
  have hK : ∀ c : K, algebraMap K F c ∈ φ.range := by
    intro c
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := V) c
    refine ⟨algebraMap W _ (algebraMap V W x) / algebraMap W _ (algebraMap V W y), ?_⟩
    rw [map_div₀, map_div₀, hφa, hφa, hVa, hVa, IsScalarTower.algebraMap_apply V K F,
      IsScalarTower.algebraMap_apply V K F]
  have hs : ∀ x ∈ s, x ∈ φ.range := by
    intro x hx
    obtain ⟨a, ha, c, hc, hc0, hxc⟩ := hfrac x hx
    refine ⟨algebraMap W _ ⟨a, ha⟩ / algebraMap W _ ⟨c, hc⟩, ?_⟩
    rw [map_div₀, hφa, hφa]
    show a / c = x
    rw [← hxc, mul_div_cancel_right₀ x hc0]
  have hrange : ∀ r, t r ∈ φ.range := by
    intro r
    have hr : r ∈ Submodule.span K (Set.range b) := hb ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hs _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    | zero => simpa using φ.range.zero_mem
    | add x y _ _ hx hy => simpa using φ.range.add_mem hx hy
    | smul c x _ hx =>
      rw [map_smul, Algebra.smul_def]
      exact φ.range.mul_mem (hK c) hx
  let e : FractionRing W ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y h => hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  let ψ : R₁ →+* FractionRing W := e.symm.toRingHom.comp (t.toRingHom.codRestrict φ.range hrange)
  have hψ : ∀ r, φ (ψ r) = t r := fun r =>
    congrArg Subtype.val (e.apply_symm_apply ⟨t r, hrange r⟩)
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ,
    (GlobalTheory.LN.cDvr_iff W).2 ⟨hWd, hWc, hWch⟩, ?_, hWloc, RingHom.finite_algebraMap.2 hWfin, ?_⟩
  · intro x y h
    exact FaithfulSMul.algebraMap_injective V F (congrArg Subtype.val h)
  · intro a
    apply hφ
    rw [hψ, hφa, AlgHom.commutes, hVa, ← IsScalarTower.algebraMap_apply V K F]

end GlobalTheory.CdvrFiniteAlgebra
