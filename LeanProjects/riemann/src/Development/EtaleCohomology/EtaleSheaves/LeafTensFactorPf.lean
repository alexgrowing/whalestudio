import Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf
import Development.EtaleCohomology.TateTwists.EtaleTensorHomDescendsAlongTensorPairing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.E.LeafTensFactorPf

theorem lift_lof {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    τ.lift U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)
      ⟨(s, t), hw⟩ (a ⊗ₜ b)) = τ.mul U s t w hw a b := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]

theorem uniq_mul {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) {M : Shv R}
    (ψ ψ' : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec M U)
    (hψ : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ U y) = ψ V (Sec.res g y))
    (hψ' : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ' U y) = ψ' V (Sec.res g y))
    (h : ∀ U s t (hw : s + t = w) a b, ψ U (τ.mul U s t w hw a b) = ψ' U (τ.mul U s t w hw a b))
    (U : Scheme.{0}) (y : Sec (T.X w) U) : ψ U y = ψ' U y := by
  have hl : ∀ V (x : Tens I J V w), ψ V (τ.lift V w x) = ψ' V (τ.lift V w x) := by
    intro V x
    classical
    induction x using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add]; rw [ha, hb]
    | of p z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add]; rw [ha, hb]
      | tmul a c =>
        obtain ⟨⟨s, t⟩, hw⟩ := p
        rw [lift_lof]
        exact h V s t hw a c
  apply LateralTheory.EtaleFoundations.TensFam.sep M
  obtain ⟨S, hS, h1⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := h1 V g hg
  rw [hψ, hψ', ← hx, hl]

theorem secMap_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map f y) = Sec.map f (Sec.res g y) := by
  have := f.hom.naturality g.op
  exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) y) this).symm

theorem addHom_usmul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (n : ℤˣ) (x : A) :
    φ (n • x) = n • φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

end LateralTheory.E.LeafTensFactorPf

namespace LateralTheory.E.LeafTensFactorPf

theorem phi_exists {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ) :
    ∃ φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧
      ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b := by
  obtain ⟨φ, h1, h2⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing R R τ hτ w (K.X w)
    (fun U => (ν.lift U w).toAddMonoidHom) (fun V U g x => LateralTheory.EtaleFoundations.TensFam.lift_res ν g w x)
  refine ⟨φ, h1, fun U s t hw a b => ?_⟩
  have := h2 U (DirectSum.of _ ⟨(s, t), hw⟩ (a ⊗ₜ b))
  rw [lift_lof] at this
  rw [this]
  exact lift_lof ν U s t w hw a b

theorem phi_smul {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ)
    (φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (h2 : ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b)
    (U : Scheme.{0}) (r : ULift.{1} R) (y : Sec (T.X w) U) : φ U (r • y) = r • φ U y := by
  refine uniq_mul τ hτ w (fun U => (φ U).comp (DistribSMul.toAddMonoidHom _ r))
    (fun U => (DistribSMul.toAddMonoidHom _ r).comp (φ U)) ?_ ?_ ?_ U y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [h1]; congr 1; exact map_smul _ r y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← h1]; exact map_smul _ r _
  · intro U s t hw a b
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← LinearMap.map_smul₂, h2, h2, LinearMap.map_smul₂]

def toHom {R : Type} [CommRing R] {F G : Shv R} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (hsm : ∀ U (r : ULift.{1} R) y, φ U (r • y) = r • φ U y) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom { toFun := φ (unop U), map_add' := map_add _, map_smul' := hsm (unop U) }
      naturality := fun U V g => by
        ext y
        exact (hnat _ _ g.unop y).symm }

theorem sheafHom_ext {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = Sec.map g y) : f = g := by
  apply Sheaf.hom_ext
  ext U y
  exact h (unop U) y

theorem factor {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) :
    ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u := by
  choose φ h1 h2 using fun w => phi_exists τ hτ ν w
  have hsm : ∀ w U (r : ULift.{1} R) y, φ w U (r • y) = r • φ w U y :=
    fun w => phi_smul τ hτ ν w (φ w) (h1 w) (h2 w)
  refine ⟨{ f := fun w => toHom (φ w) (h1 w) (hsm w), comm' := ?_ }, ?_⟩
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    apply sheafHom_ext
    intro U y
    show Sec.map (K.d i (i + 1)) (φ i U y) = φ (i + 1) U (Sec.map (T.d i (i + 1)) y)
    refine uniq_mul τ hτ i (M := K.X (i + 1))
      (fun U => ((K.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom.comp (φ i U))
      (fun U => (φ (i + 1) U).comp ((T.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom) ?_ ?_ ?_ U y
    · intro V U g y
      show Sec.res g (Sec.map (K.d i (i + 1)) (φ i U y)) = Sec.map (K.d i (i + 1)) (φ i V (Sec.res g y))
      rw [secMap_nat, h1]
    · intro V U g y
      show Sec.res g (φ (i + 1) U (Sec.map (T.d i (i + 1)) y)) = φ (i + 1) V (Sec.map (T.d i (i + 1)) (Sec.res g y))
      rw [h1, secMap_nat]
    · intro U s t hw a b
      show Sec.map (K.d i (i + 1)) (φ i U (τ.mul U s t i hw a b)) = φ (i + 1) U (Sec.map (T.d i (i + 1)) (τ.mul U s t i hw a b))
      rw [h2, ν.leibniz, τ.leibniz, map_add, addHom_usmul, h2, h2]
  · intro U s t w hw a b
    rw [LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f, LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f]
    exact h2 w U s t hw a b

end LateralTheory.E.LeafTensFactorPf

theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := by
  intro R _ I J T K τ hτ ν
  exact LateralTheory.E.LeafTensFactorPf.factor τ hτ ν
