import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeDimZeroFibreDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem flat_fromSpecStalk' (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

private theorem spMap_fnMap' {Z W : Scheme.{0}} [IsIntegral Z] [IsIntegral W] (j : W ⟶ Z)
    (hη : j (genericPoint W) ⤳ genericPoint Z) :
    spMap (SmallSec.fnMap j hη) ≫ Z.fromSpecStalk (genericPoint Z) = W.fromSpecStalk (genericPoint W) ≫ j := by
  have e : spMap (SmallSec.fnMap j hη) =
      Spec.map (Z.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint W)) := rfl
  rw [e, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

private theorem birational_props {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {T B : Vert.Model O} (f : Vert.Model.Hom T B) (U : B.X.Opens) (hU : (U : Set B.X).Nonempty) [IsIso (f.f ∣_ U)]
    (hf : f.f (genericPoint T.X) ⤳ genericPoint B.X) :
    f.relDim = 0 ∧ f.fibreDeg 1 = 1 ∧ Function.Bijective (SmallSec.fnMap f.f hf) := by
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict f.f U hU.to_subtype
  have h0 : f.relDim = 0 := by
    have h := GlobalTheory.ModelDom.dim_le_of_birational f.f
    rw [T.dim_eq, B.dim_eq] at h
    have h' : T.relDim + 1 ≤ B.relDim + 1 := by exact_mod_cast h
    unfold Vert.Model.Hom.relDim
    omega
  refine ⟨h0, ?_, ?_⟩
  · rw [(GlobalTheory.Vert.Model.Hom.fibreDeg_one_of_relDim_eq_zero O B T f h0).2]
    have hη : genericPoint B.X ∈ U := ((genericPoint_spec B.X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
    let k : Spec (B.X.residueField (genericPoint B.X)) ⟶ U.toScheme :=
      Spec.map (B.X.residue _) ≫ U.fromSpecStalkOfMem _ hη
    have hk : k ≫ U.ι = B.X.fromSpecResidueField (genericPoint B.X) := by
      rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]; rfl
    have P := f.isPullback_genFibre
    rw [← hk] at P
    have P' := (isPullback_morphismRestrict f.f U)
    have P'' := IsPullback.of_right' P P'.flip
    have : IsIso f.genFibreStr :=
      MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) P'' (inferInstanceAs (IsIso (f.f ∣_ U)))
    have hb : Function.Bijective (algebraMap f.fnField Γ(f.genFibre, ⊤)) := by
      change Function.Bijective ((Scheme.ΓSpecIso (.of f.fnField)).inv ≫ f.genFibreStr.appTop)
      have h₁ : IsIso f.genFibreStr.appTop := inferInstanceAs (IsIso (f.genFibreStr.app ⊤))
      exact (ConcreteCategory.bijective_of_isIso f.genFibreStr.appTop).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of f.fnField)).inv)
    have : Module.finrank f.fnField Γ(f.genFibre, ⊤) = 1 := by
      rw [← (AlgEquiv.ofBijective (Algebra.ofId f.fnField Γ(f.genFibre, ⊤)) hb).toLinearEquiv.finrank_eq]
      exact Module.finrank_self _
    rw [this]; rfl
  · have e : f.f (genericPoint T.X) = genericPoint B.X := (hf.antisymm (genericPoint_specializes _)).eq
    have : IsIso (B.X.presheaf.stalkSpecializes hf) :=
      inferInstanceAs (IsIso (B.X.presheaf.stalkCongr (.of_eq e.symm)).hom)
    exact ConcreteCategory.bijective_of_isIso (B.X.presheaf.stalkSpecializes hf ≫ f.f.stalkMap (genericPoint T.X))

private theorem exists_modification {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : Vert.Model O) {Z : Scheme.{0}} (q : Z ⟶ Sp O) (hq : IsProjOver q) (w : Sp B.X.functionField ⟶ Z)
    (hw : B.X.fromSpecStalk (genericPoint B.X) ≫ B.str = w ≫ q) :
    ∃ (T : Vert.Model O) (f : Vert.Model.Hom T B) (g : T.X ⟶ Z) (t : Sp B.X.functionField ⟶ T.X) (_ : IsDominant t),
      GlobalTheory.IsNormalScheme T.X ∧ g ≫ q = T.str ∧ t ≫ f.f = B.X.fromSpecStalk (genericPoint B.X) ∧ t ≫ g = w ∧
      ∃ U : B.X.Opens, (U : Set B.X).Nonempty ∧ IsIso (f.f ∣_ U) := by
  let j : Sp B.X.functionField ⟶ B.X := B.X.fromSpecStalk (genericPoint B.X)
  let r := pullback.fst B.str q
  let u : Sp B.X.functionField ⟶ pullback B.str q := pullback.lift j w hw
  have hr : u ≫ r = j := pullback.lift_fst _ _ _
  have hr' : u ≫ pullback.snd B.str q = w := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ B.str) := GlobalTheory.ProjSpace.isProjOver_pullback B.isProjOver hq
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have hj : IsPreimmersion j := inferInstanceAs (IsPreimmersion (B.X.fromSpecStalk (genericPoint B.X)))
  have hjf : Flat j := flat_fromSpecStalk' _ _
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ B.str)
  have hφf : φ.hom.Flat := Flat.SpecMap_iff.mp (hφ ▸ inferInstance)
  have hφinj : Function.Injective φ.hom := by
    letI := φ.hom.toAlgebra
    have : Module.Flat O B.X.functionField := hφf
    exact FaithfulSMul.algebraMap_injective O B.X.functionField
  have : CharZero B.X.functionField := charZero_of_injective_ringHom hφinj
  have : CharZero (Sp B.X.functionField).functionField := charZero_of_injective_ringHom
    ((Scheme.ΓSpecIso (.of B.X.functionField)).inv ≫ (Sp B.X.functionField).presheaf.germ ⊤ (genericPoint _) trivial).hom.injective
  have : SurjectiveOnStalks (u ≫ r) := by rw [hr]; infer_instance
  have : SurjectiveOnStalks u := SurjectiveOnStalks.of_comp u r
  have hfin : IsFinite u.fromNormalization :=
    isFinite_fromNormalization_of_isIntegral (o := .of O) u (r ≫ B.str)
      (RingHom.FiniteType.of_surjective _ (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType
  have e₁ : u.toNormalization ≫ u.fromNormalization ≫ r = j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : u.toNormalization ≫ u.fromNormalization ≫ pullback.snd B.str q = w := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hfl : Flat (u.fromNormalization ≫ r ≫ B.str) := by
    have : Flat (u.toNormalization ≫ u.fromNormalization ≫ r ≫ B.str) := by
      rw [← Category.assoc u.fromNormalization, ← Category.assoc, e₁]
      infer_instance
    exact flat_normalization u _
  obtain ⟨U, hne, hU⟩ :=
    GlobalTheory.ModelDom.exists_isIso_restrict u.toNormalization (u.fromNormalization ≫ r) j e₁
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (u.fromNormalization ≫ r) U hne.to_subtype
  have hs := surjective_of_isDominant_of_isClosed_range (u.fromNormalization ≫ r)
    (u.fromNormalization ≫ r).isClosedMap.isClosed_range
  let T : Vert.Model O :=
    { X := u.normalization
      str := u.fromNormalization ≫ r ≫ B.str
      isIntegral := inferInstance
      isProjOver := isProjOver_comp_of_isFinite _ hW
      flat := hfl }
  refine ⟨T, ⟨u.fromNormalization ≫ r, Category.assoc _ _ _⟩, u.fromNormalization ≫ pullback.snd B.str q,
    u.toNormalization, inferInstanceAs (IsDominant u.toNormalization),
    GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, ?_, e₁, e₂, U, hne, hU⟩
  change (u.fromNormalization ≫ pullback.snd B.str q) ≫ q = u.fromNormalization ≫ r ≫ B.str
  rw [Category.assoc, ← pullback.condition]

theorem UpperTheory.exists_normal_vertical_model :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (b : 𝓞 F →+* O) (B : Vert.Model O) (μ : Match Y b B) (Q : TrueGeo.Model Y) [IsIntegral Q.X], ∃ (T : Vert.Model O) (f : Vert.Model.Hom T B) (μ' : Match Y b T) (g : T.X ⟶ Q.X) (hf : f.f (genericPoint T.X) ⤳ genericPoint B.X) (f' : μ'.U.toScheme ⟶ μ.U.toScheme), GlobalTheory.IsNormalScheme T.X ∧ f.relDim = 0 ∧ f.fibreDeg 1 = 1 ∧ Function.Bijective (SmallSec.fnMap f.f hf) ∧ μ'.φ = (SmallSec.fnMap f.f hf).comp μ.φ ∧ f' ≫ μ.U.ι = μ'.U.ι ≫ f.f ∧ f' ≫ μ.h = μ'.h ∧ Extends μ' Q g ∧ g (genericPoint T.X) ⤳ genericPoint Q.X := by
  intro F _ _ Y O _ _ _ _ b B μ Q _
  have hs : (μ.h ≫ Q.j) ≫ Q.p = (μ.U.ι ≫ B.str) ≫ spMap b := by
    rw [Category.assoc, Q.pb.w, μ.h_str, Category.assoc]
  let k : Sp B.X.functionField ⟶ μ.U.toScheme := μ.U.fromSpecStalkOfMem _ μ.mem
  have hk : k ≫ μ.U.ι = B.X.fromSpecStalk (genericPoint B.X) := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  obtain ⟨T, f, g₀, t, _, hT, hg₀, htf, htg, U, hU, _⟩ := exists_modification B (pullback.snd Q.p (spMap b))
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd b Q.ar.isProjOver) (k ≫ pullback.lift _ _ hs)
    (by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hk])
  have hη : f.f (genericPoint T.X) = genericPoint B.X := by
    have h := (genericPoint_spec T.X).image f.f.continuous
    rw [Set.image_univ, f.f.surjective.range_eq, closure_univ] at h
    exact h.eq (genericPoint_spec B.X)
  have hf : f.f (genericPoint T.X) ⤳ genericPoint B.X := hη ▸ specializes_rfl
  have hmem : genericPoint T.X ∈ f.f ⁻¹ᵁ μ.U := show f.f _ ∈ μ.U from hη ▸ μ.mem
  have hspec : (f.f ⁻¹ᵁ μ.U).fromSpecStalkOfMem _ hmem ≫ f.f ∣_ μ.U = spMap (SmallSec.fnMap f.f hf) ≫ k := by
    rw [← cancel_mono μ.U.ι, Category.assoc, Category.assoc, hk, morphismRestrict_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι_assoc, spMap_fnMap']
  let μ' : Match Y b T :=
    { U := f.f ⁻¹ᵁ μ.U
      mem := hmem
      h := f.f ∣_ μ.U ≫ μ.h
      h_str := by
        rw [Category.assoc, μ.h_str, ← Category.assoc, morphismRestrict_ι, ← f.comp_str]
        simp only [Category.assoc]
      φ := (SmallSec.fnMap f.f hf).comp μ.φ
      φ_spec := by
        rw [← Category.assoc, hspec, Category.assoc]
        erw [μ.φ_spec]
        rw [← Category.assoc]
        congr 1
        simp only [spMap, ← Spec.map_comp]; rfl }
  have hgp : (g₀ ≫ pullback.fst Q.p (spMap b)) ≫ Q.p = T.str ≫ spMap b := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg₀]
  have hext : μ'.U.ι ≫ g₀ ≫ pullback.fst Q.p (spMap b) = μ'.h ≫ Q.j := by
    have : IsProper Q.p := (isProper_and_exists_isAmpleLB_of_isProjOver Q.ar.isProjOver).1
    let t' := (isPullback_morphismRestrict f.f μ.U).lift k t (hk.trans htf.symm)
    have h1 : t' ≫ f.f ∣_ μ.U = k := IsPullback.lift_fst _ _ _ _
    have h2 : t' ≫ μ'.U.ι = t := IsPullback.lift_snd _ _ _ _
    have : IsDominant (t' ≫ μ'.U.ι) := h2 ▸ inferInstance
    have : IsDominant t' := IsDominant.of_comp_of_isOpenImmersion t' μ'.U.ι
    refine ext_of_isDominant_of_isSeparated Q.p ?_ t' ?_
    · rw [Category.assoc, hgp, Category.assoc, Q.pb.w, μ'.h_str]
    · rw [← Category.assoc, h2, ← Category.assoc, htg, Category.assoc, pullback.lift_fst]
      change _ = t' ≫ (f.f ∣_ μ.U ≫ μ.h) ≫ Q.j
      rw [← h1]
      simp only [Category.assoc]
  obtain ⟨h1, h2, h3⟩ := birational_props f U hU hf
  refine ⟨T, f, μ', g₀ ≫ pullback.fst Q.p (spMap b), hf, f.f ∣_ μ.U, hT, h1, h2, h3, rfl,
    morphismRestrict_ι _ _, rfl, ⟨hext, hgp⟩, ?_⟩
  have e : T.X.fromSpecStalk (genericPoint T.X) ≫ g₀ ≫ pullback.fst Q.p (spMap b) =
      spMap μ'.φ ≫ Y.X.fromSpecStalk (genericPoint Y.X) ≫ Q.j := by
    rw [← Scheme.Opens.fromSpecStalkOfMem_ι μ'.U _ μ'.mem, Category.assoc, hext, ← Category.assoc, μ'.φ_spec,
      Category.assoc]
  have e' : (g₀ ≫ pullback.fst Q.p (spMap b)) (T.X.fromSpecStalk (genericPoint T.X) (closedPoint _)) =
      Q.j (Y.X.fromSpecStalk (genericPoint Y.X) (spMap μ'.φ (closedPoint _))) := congrArg (fun a => a (closedPoint _)) e
  have e₂ : spMap μ'.φ (closedPoint _) = closedPoint (Y.X.presheaf.stalk (genericPoint Y.X)) :=
    Subsingleton.elim (α := PrimeSpectrum Y.X.functionField) _ _
  rw [Scheme.fromSpecStalk_closedPoint, e₂, Scheme.fromSpecStalk_closedPoint] at e'
  rw [e']
  exact SmallSec.j_gen_specializes Q
