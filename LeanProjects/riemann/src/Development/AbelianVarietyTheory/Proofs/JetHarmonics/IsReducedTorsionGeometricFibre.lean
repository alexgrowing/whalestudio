import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TorsionReduced

theorem isReduced_of_forall_dualNumber (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B]
    (h : ∀ (φ : B →ₐ[F] DualNumber F) (b : B), (φ b).snd = 0) : _root_.IsReduced B := by
  have hs : Subsingleton (KaehlerDifferential F B) := by
    by_contra hne
    have : Nontrivial (KaehlerDifferential F B) := not_subsingleton_iff_nontrivial.mp hne
    obtain ⟨P, hP, -⟩ := (eq_top_or_exists_le_coatom
      (⊥ : Submodule B (KaehlerDifferential F B))).resolve_left bot_ne_top
    have hsimple : IsSimpleModule B (KaehlerDifferential F B ⧸ P) :=
      isSimpleModule_iff_isCoatom.mpr hP
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    letI : Field (B ⧸ m) := Ideal.Quotient.field m
    have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let u : (B ⧸ m) ≃ₐ[F] F := (AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb).symm
    let l : KaehlerDifferential F B →ₗ[B] (B ⧸ m) := e.toLinearMap ∘ₗ P.mkQ
    let D : Derivation F B (B ⧸ m) := l.compDer (KaehlerDifferential.D F B)
    let φ : B →ₐ[F] DualNumber F :=
      { toFun := fun b => TrivSqZeroExt.inl (u (Ideal.Quotient.mk m b)) + TrivSqZeroExt.inr (u (D b))
        map_one' := by ext <;> simp
        map_mul' := fun a b => by
          ext
          · simp
          · simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
        map_zero' := by ext <;> simp
        map_add' := fun a b => by ext <;> simp
        commutes' := fun r => by
          ext
          · simpa [TrivSqZeroExt.algebraMap_eq_inl] using u.commutes r
          · simp [TrivSqZeroExt.algebraMap_eq_inl] }
    have hD : ∀ b, l (KaehlerDifferential.D F B b) = 0 := fun b => by
      have := h φ b
      simpa [φ, D] using this
    have hl : l = 0 := by
      refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation F B) ?_
      rintro _ ⟨b, rfl⟩
      exact hD b
    apply hP.1
    rw [eq_top_iff]
    intro x _
    have := LinearMap.congr_fun hl x
    simpa [l] using this
  have : Algebra.FormallyUnramified F B := ⟨hs⟩
  exact Algebra.FormallyUnramified.isReduced_of_field F B

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem scale_comp_scale (a b : R) :
    TangentPow.scale O a ≫ TangentPow.scale O b = TangentPow.scale O (a * b) := by
  rw [TangentPow.scale, TangentPow.scale, TangentPow.ptMap_comp_ptMap, TangentPow.scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp [_root_.mul_assoc]

theorem eq_const_of_pow_eq_one {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
    {N : ℕ} (hN : IsUnit (N : R)) (y : specO O (DualNumber R) ⟶ G) (hy : y ^ N = 1) :
    y = ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y := by
  set c := ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y with hc
  have h0 : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (TrivSqZeroExt.inlAlgHom O R R) = 𝟙 _ := by
    rw [TangentPow.ptMap_comp_ptMap, ← TangentPow.ptMap_id']
    congr 1
  have h1 : ptMap (TrivSqZeroExt.fstHom O R R) ≫ (y * c⁻¹) = 1 := by
    rw [comp_mul, GrpObj.comp_inv, hc, ← Category.assoc, h0, Category.id_comp, mul_inv_cancel]
  have h2 : c ^ N = 1 := by
    rw [hc, ← MonObj.comp_pow, ← MonObj.comp_pow, hy, comp_one, comp_one]
  have h3 : (y * c⁻¹) ^ N = 1 := by
    rw [mul_pow, inv_pow, hy, h2, inv_one, _root_.mul_one]
  rw [TangentPow.pow_eq_scale_comp h1] at h3
  obtain ⟨a, ha⟩ := hN.exists_left_inv
  have h4 := congrArg (TangentPow.scale O a ≫ ·) h3
  simp only [← Category.assoc, scale_comp_scale, ha, TangentPow.scale_one, Category.id_comp,
    comp_one] at h4
  exact mul_inv_eq_one.mp h4

end GlobalTheory.TorsionReduced

namespace GlobalTheory

theorem isReduced_torsion_geometric_fibre :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G] (N : ℕ), (N : F) ≠ 0 → IsFinite (torsion G N).hom → IsReduced (specO O F ⊗ torsion G N).left := by
  intro O F _ _ _ _ G _ _ N hN hfin
  have : IsAffine (torsion G N).left := isAffine_of_isAffineHom (torsion G N).hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((torsion G N).left.isoSpec.inv ≫ (torsion G N).hom)
  letI : Algebra O Γ((torsion G N).left, ⊤) := ψ.hom.toAlgebra
  let e : specO O Γ((torsion G N).left, ⊤) ≅ torsion G N :=
    Over.isoMk (torsion G N).left.isoSpec.symm hψ.symm
  have h1 : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Module.Finite O Γ((torsion G N).left, ⊤) := (IsFinite.SpecMap_iff ψ).mp h1
  have hred : _root_.IsReduced (TensorProduct O F Γ((torsion G N).left, ⊤)) := by
    refine TorsionReduced.isReduced_of_forall_dualNumber F _ fun φ b => ?_
    let χ : Γ((torsion G N).left, ⊤) →ₐ[O] DualNumber F :=
      (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
    have hy : ((ptMap χ ≫ e.hom) ≫ torsion.ι G N) ^ N = 1 := by
      rw [← MonObj.comp_pow, KernelNoTorsion.torsionι_pow, comp_one]
    have h2 := TorsionReduced.eq_const_of_pow_eq_one hN.isUnit _ hy
    simp only [← Category.assoc] at h2
    have h3 := (cancel_mono e.hom).mp (KernelNoTorsion.torsion_hom_ext h2)
    rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap] at h3
    have h4 := Spec.map_injective (congrArg Over.Hom.left h3)
    have h5 : ∀ a, (χ a).snd = 0 := fun a => by
      have := congrArg TrivSqZeroExt.snd (congrArg (fun f => f.hom a) h4)
      simpa using this
    induction b with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul f a =>
      have : f ⊗ₜ[O] a = f • ((1 : F) ⊗ₜ[O] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, TrivSqZeroExt.snd_smul]
      exact smul_eq_zero_of_right f (h5 a)
  have h4 : IsReduced (Spec (CommRingCat.of (TensorProduct O F Γ((torsion G N).left, ⊤)))) :=
    (affine_isReduced_iff _).mpr hred
  have h3 : IsReduced (specO O F ⊗ specO O Γ((torsion G N).left, ⊤)).left :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O F Γ((torsion G N).left, ⊤)).hom _ h4
  have h0 : IsIso (specO O F ◁ e.inv).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O F ◁ e.inv)))
  exact isReduced_of_isOpenImmersion (specO O F ◁ e.inv).left

end GlobalTheory
