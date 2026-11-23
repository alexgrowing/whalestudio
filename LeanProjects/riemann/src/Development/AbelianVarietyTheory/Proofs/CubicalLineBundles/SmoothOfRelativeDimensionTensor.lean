import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.SerreDim

theorem finrank_tensor_of_algebra (O M k B L : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [CommRing B] [Algebra O B] [Algebra k B]
    [Module.Finite k B] [AddCommGroup L] [Module k L] [Module O L] [Module B L] [IsScalarTower k B L]
    [IsScalarTower O B L] [SMulCommClass O k L] [Module.Finite k L] :
    Module.finrank k (L ⊗[O] M) = Module.finrank O M * Module.finrank k L := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B (B ⊗[O] M) (Module.finrank O M) fun P => by
    letI : Field (B ⧸ P.asIdeal) := Ideal.Quotient.field _
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O B (B ⧸ P.asIdeal) (B ⧸ P.asIdeal) M).finrank_eq]
    exact TenDim.finrank_fibre O M _
  let e : L ⊗[O] M ≃ₗ[B] (Fin (Module.finrank O M) → L) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O B B L M).symm ≪≫ₗ
      (b.equivFun.lTensor L) ≪≫ₗ TensorProduct.piScalarRight B B L _
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_tensor (O M k L : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [AddCommGroup L] [Module k L] [Module O L]
    [SMulCommClass O k L] [Module.Finite k L] :
    Module.finrank k (L ⊗[O] M) = Module.finrank O M * Module.finrank k L := by
  have : SMulCommClass k O L := SMulCommClass.symm _ _ _
  letI : Module (k ⊗[ℤ] O) L := TensorProduct.Algebra.module
  letI : Algebra O (k ⊗[ℤ] O) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k (k ⊗[ℤ] O) L := IsScalarTower.of_algebraMap_smul fun r x => by
    change (r ⊗ₜ[ℤ] (1 : O)) • x = _
    rw [TensorProduct.Algebra.smul_def, one_smul]
  have : IsScalarTower O (k ⊗[ℤ] O) L := IsScalarTower.of_algebraMap_smul fun r x => by
    change ((1 : k) ⊗ₜ[ℤ] r) • x = _
    rw [TensorProduct.Algebra.smul_def, one_smul]
  exact finrank_tensor_of_algebra O M k (k ⊗[ℤ] O) L

theorem dim_eq_of_isPullback {X Y S T X' S' : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ T} {f' : X' ⟶ S'} {a : X' ⟶ X}
    {b : S' ⟶ S} {c : X' ⟶ Y} {d : S' ⟶ T} (h : IsPullback a f' f b) (h' : IsPullback c f' g d)
    {n m : ℕ} {W : X.Opens} {V : Y.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f))
    (hV : SmoothOfRelativeDimension m (V.ι ≫ g)) (x : X') (hx : a x ∈ W) (hx' : c x ∈ V) : n = m := by
  have h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
      ((isPullback_morphismRestrict a W).paste_vert h) hW
  have h₂ : SmoothOfRelativeDimension m ((c ⁻¹ᵁ V).ι ≫ f') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback
      ((isPullback_morphismRestrict c V).paste_vert h') hV
  have e₁ : SmoothOfRelativeDimension (0 + n) ((a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V).ι ≫ f') := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V ≤ a ⁻¹ᵁ W), Category.assoc]; infer_instance
  have e₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V).ι ≫ f') := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V ≤ c ⁻¹ᵁ V), Category.assoc]; infer_instance
  simpa using H1.dim_unique _ e₁ e₂ ⟨x, hx, hx'⟩

theorem isPullback_mul {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    IsPullback (fst G G * snd G G).left (snd G G).left G.hom G.hom := by
  let e : G ⊗ G ≅ G ⊗ G :=
    { hom := lift (fst G G * snd G G) (snd G G)
      inv := lift (fst G G * (snd G G)⁻¹) (snd G G)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  refine h.of_iso ((Over.forget S).mapIso e.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change (fst G G ≫ 𝟙 _).left = (e.inv ≫ (fst G G * snd G G)).left
    congr 1
    simp [e, MonObj.comp_mul]
  · change (snd G G ≫ 𝟙 _).left = (e.inv ≫ snd G G).left
    congr 1
    simp [e]

theorem exists_dim_of_grpObj {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] [Smooth G.hom] :
    ∃ n, SmoothOfRelativeDimension n G.hom := by
  choose n W hW hd using H1.exists_dim G.hom
  let x₀ : G.left := η[G].left (default : PrimeSpectrum k)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨n x₀, IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_⟩
  let p : G ⟶ G ⊗ G := lift 1 (𝟙 G)
  have p₁ : p ≫ fst G G = toUnit G ≫ η[G] := lift_fst _ _
  have p₂ : p ≫ (fst G G * snd G G) = 𝟙 G := by simp [p, MonObj.comp_mul]
  have q₁ : (fst G G).left (p.left y) = x₀ :=
    (congrArg (fun q : G ⟶ G => q.left y) p₁).trans
      (congrArg η[G].left (Subsingleton.elim (α := PrimeSpectrum k) _ _))
  have q₂ : (fst G G * snd G G).left (p.left y) = y := congrArg (fun q : G ⟶ G => q.left y) p₂
  have h : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  rw [dim_eq_of_isPullback h (isPullback_mul G) (hd x₀) (hd y) (p.left y) (q₁ ▸ hW x₀) (by rw [q₂]; exact hW y)]
  exact hd y

theorem dim_eq_field {k O M : Type} [Field k] [CommRing O] [IsDomain O] [Module.Finite ℤ O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] {G A : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M) {g : ℕ}
    (hG : SmoothOfRelativeDimension g G.hom) {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) :
    n = Module.finrank O M * g := by
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis G hG
  obtain ⟨w, hw⟩ := TenDim.exists_isLieBasis A hA
  have := Module.Finite.of_basis (Serre.Lie.basis a hv)
  have h := finrank_tensor O M k (Serre.Lie a)
  rwa [(t.lieEquivBase b).finrank_eq, Module.finrank_eq_card_basis (Serre.Lie.basis b hw),
    Module.finrank_eq_card_basis (Serre.Lie.basis a hv), Fintype.card_fin, Fintype.card_fin] at h

theorem smoothOfRelativeDimension_tensor :
    ∀ (S : Scheme.{0}) (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (g : ℕ), Nonempty (Serre.IsTensor A b G a M) → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension (Module.finrank O M * g) A.hom := by
  rintro S O _ _ _ M _ _ _ _ G A _ _ _ _ a b g ⟨t⟩ hG
  have : Smooth G.hom := hG.smooth
  have : Smooth A.hom := t.smooth
  choose n W hW hd using H1.exists_dim A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank O M * g)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (Module.finrank O M * g)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := A.left.residueField y
  let z : Sp k ⟶ A.left := A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ A.hom
  let z' : Sp k ⟶ pullback A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have : Smooth ((Over.pullback x).obj A).hom := inferInstanceAs (Smooth (pullback.snd A.hom x))
  obtain ⟨m, hm⟩ := exists_dim_of_grpObj ((Over.pullback x).obj A)
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback A.hom x) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hG' : SmoothOfRelativeDimension g (pullback.snd G.hom x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  rw [← dim_eq_field (t.pullback x) hG' hm, ← e₁]
  exact hd y

end GlobalTheory.SerreDim
