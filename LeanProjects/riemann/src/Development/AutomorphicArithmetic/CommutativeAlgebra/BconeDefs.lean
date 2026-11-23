import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Bc

abbrev prodW (W : Scheme.{0}) : Scheme.{0} ⥤ Scheme.{0} := prod.functor.obj W

set_option backward.isDefEq.respectTransparency false in
theorem prodW_compatible (W : Scheme.{0}) :
    CompatiblePreserving Scheme.etaleTopology.{0} (prodW W) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  have hfst : f₁ ≫ prod.fst = f₂ ≫ prod.fst := by
    have h := congrArg (· ≫ (prod.fst : W ⨯ Z ⟶ W)) e
    simpa using h
  have hsnd : (f₁ ≫ prod.snd) ≫ g₁ = (f₂ ≫ prod.snd) ≫ g₂ := by
    have h := congrArg (· ≫ (prod.snd : W ⨯ Z ⟶ Z)) e
    simpa using h
  let u : X ⟶ (prodW W).obj X := prod.lift (f₁ ≫ prod.fst) (𝟙 X)
  have k₁ : f₁ = u ≫ (prodW W).map (f₁ ≫ prod.snd) := by
    apply prod.hom_ext <;> simp [u]
  have k₂ : f₂ = u ≫ (prodW W).map (f₂ ≫ prod.snd) := by
    apply prod.hom_ext <;> simp [u, hfst]
  have hc := hx (f₁ ≫ prod.snd) (f₂ ≫ prod.snd) hg₁ hg₂ hsnd
  calc ℱ.obj.map f₁.op (x g₁ hg₁)
      = ℱ.obj.map u.op (ℱ.obj.map ((prodW W).map (f₁ ≫ prod.snd)).op (x g₁ hg₁)) := by
        rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← k₁]
    _ = ℱ.obj.map u.op (ℱ.obj.map ((prodW W).map (f₂ ≫ prod.snd)).op (x g₂ hg₂)) :=
        congrArg _ hc
    _ = ℱ.obj.map f₂.op (x g₂ hg₂) := by
        rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← k₂]

set_option backward.isDefEq.respectTransparency false in
theorem prodW_cover (W : Scheme.{0}) :
    CoverPreserving Scheme.etaleTopology.{0} Scheme.etaleTopology.{0} (prodW W) := by
  constructor
  intro U S hS
  rw [GlobalTheory.T.mem_etale_covering_sieves_iff_points]
  intro u
  obtain ⟨V, j, v, hj, hv, hS'⟩ := (GlobalTheory.T.mem_etale_covering_sieves_iff_points U S).1 hS ((prod.snd : W ⨯ U ⟶ U) u)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := (prod.snd : W ⨯ U ⟶ U)) (g := j) u v hv.symm
  haveI := hj
  refine ⟨pullback (prod.snd : W ⨯ U ⟶ U) j, pullback.fst _ _, z, ?_, hz1, ?_⟩
  · exact MorphismProperty.pullback_fst _ _ hj
  refine ⟨V, j, prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _), hS', ?_⟩
  apply Limits.prod.hom_ext
  · simp
  · simp [pullback.condition]

instance prodW_cont (W : Scheme.{0}) :
    (prodW W).IsContinuous Scheme.etaleTopology.{0} Scheme.etaleTopology.{0} :=
  Functor.isContinuous_of_coverPreserving (prodW_compatible W) (prodW_cover W)

variable (R : Type) [CommRing R]

def pw (W : Scheme.{0}) : Shv R ⥤ Shv R :=
  (prodW W).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) Scheme.etaleTopology.{0} Scheme.etaleTopology.{0}

instance (W : Scheme.{0}) : (pw R W).Additive where
  map_add {F G} {f g} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

variable {R}

abbrev Bc (W : Scheme.{0}) (I : Cx R) : Cx R := ((pw R W).mapHomologicalComplex _).obj I

instance (W : Scheme.{0}) (I : Cx R) [I.IsStrictlyGE 0] : (Bc W I).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (pw R W).map_isZero (I.isZero_of_isStrictlyGE 0 i hi)

def Supp (Q : Scheme.{0} → Prop) (P : PSh) : Prop := ∀ U : Scheme.{0}, Nonempty (P.obj (op U)) → Q U

def Acy (Q : Scheme.{0} → Prop) (F : Shv ℤ) : Prop :=
  ∀ P : PSh, Supp Q P → ∀ n : ℤ, 0 < n → Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) F n)

def cl {M F : Shv ℤ} (f : M ⟶ F) : HK ℤ (sgl M) F 0 :=
  CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))

end UpperTheory.Bc
end
