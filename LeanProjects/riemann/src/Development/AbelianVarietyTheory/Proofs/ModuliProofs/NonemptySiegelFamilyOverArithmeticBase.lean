import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDenseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerShapeDependsOnlyOnMatricesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBoundStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaFamilyOverOpenClosureStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExtStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassE8SharpStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpObjectFibreFromComplexCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelArithFamily

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [spMap, spMap, ← Spec.map_comp]; rfl

theorem comp_spMap_id {A : Type} [CommRing A] {S : Scheme.{0}} (s : S ⟶ Sp A) : s ≫ spMap (RingHom.id A) = s := by
  have : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _
  rw [this, Category.comp_id]

theorem locallyOfFiniteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

theorem charZero_residueField {o : Type} [CommRing o] [CharZero o] {S : Scheme.{0}} (s : S ⟶ Sp o) (p : S)
    (hp : (s p).asIdeal = ⊥) : CharZero (S.residueField p) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S.fromSpecResidueField p ≫ s)
  have h1 : (Spec.map φ) (⊥ : PrimeSpectrum (S.residueField p)) = s p := by
    rw [hφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg s (Scheme.fromSpecResidueField_apply p _))
  have h2 : Ideal.comap φ.hom ⊥ = ⊥ := by
    rw [← hp, ← h1]; rfl
  have h3 : Function.Injective φ.hom := (RingHom.injective_iff_ker_eq_bot _).2 h2
  exact charZero_of_injective_ringHom (R := o) h3

theorem dir_over {o K : Type} [CommRing o] [Field K] {r : ℕ} (β : o →+* K) (lam : (Fin r → K) →ₗ[K] K) :
    spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      constPt (spMap (dirMap lam)) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) := by
  rw [constPt, spMap_comp_spMap, spMap_comp_spMap, spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_matrices {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) :
    ∃ (a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ) (w w' : (Fin 8 × Fin 8) ⊕ Bool),
      (W + W.transpose) * a w = W ∧ (W + W.transpose) * a w' = W.transpose ∧
        ∀ u v, ∃ j, a j = Matrix.single u v 1 := by
  refine ⟨Sum.elim (fun uv => Matrix.single uv.1 uv.2 1)
    (fun c => (W + W.transpose).adjugate * (if c then W else W.transpose)), .inr true, .inr false, ?_, ?_,
    fun u v => ⟨.inl (u, v), rfl⟩⟩
  · simp only [Sum.elim_inr, if_true]
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hW.2, one_smul, Matrix.one_mul]
  · simp only [Sum.elim_inr, Bool.false_eq_true, if_false]
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hW.2, one_smul, Matrix.one_mul]

theorem nonempty_sFam : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ), ArBase em → Nonempty (SFam h ((n ^ j) ^ 2) (b.ζ : o)) := by
  intro L1 L2 hT hU h n hh hn hodd
  obtain ⟨W, hW, hbas⟩ := exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas h
  obtain ⟨a, w, w', hw, hw', hu⟩ := exists_matrices hW
  obtain ⟨Mat, κ, hgood⟩ := GlobalTheory.T.isGoodThetaComplexClass_E8Sharp L1 L2 hT hU h _ W _ a w w' bas hW hb hw hw' hu
  obtain ⟨j₁, hj₁⟩ := hgood n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.nonempty_thetaFamily_over_open_closure L1 L2 _ _ Mat κ n w w' hn hodd
  obtain ⟨j₃, hj₃⟩ := GlobalTheory.T.existsUnique_map_to_thetaFamily_openPart L1 L2 _ _ Mat κ n w w' hn hodd
  refine ⟨max (max j₁ 1) (max j₂ j₃), fun j hj o _ b em hem => ?_⟩
  have hj1 : j ≥ j₁ := by omega
  have hj0 : j ≠ 0 := by omega
  have hj2 : j ≥ j₂ := by omega
  have hj3 : j ≥ j₃ := by omega
  have h3 : 3 ≤ n ^ j := by
    have h2 := hn.two_le
    have : n ≠ 2 := fun e => by rw [e] at hodd; exact absurd hodd (by decide)
    exact le_trans (by omega) (Nat.le_self_pow hj0 n)
  have hoN : Odd (n ^ j) := hodd.pow
  have hok : Odd ((n ^ j) ^ 2) := hoN.pow
  have h3k : 3 ≤ (n ^ j) ^ 2 := h3.trans (Nat.le_self_pow two_ne_zero _)
  have hζ : b.ζ ^ ((n ^ j) ^ 2) = 1 := by
    refine Units.ext (hem.2.2 ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, (b.prim ℂ em).pow_eq_one, Units.val_one, map_one]
  have hG := hj₁ j hj1 _ rfl o b em
  obtain ⟨F⟩ := hj₂ j hj2 o b em _ _ hem hG
  obtain ⟨hq, hflat, hred, hinj⟩ := GlobalTheory.T.thetaClosureOpenFamily_qproj_flat_reduced_ext L1 L2 o _ n _ _ b em _ Mat κ F hoN
  haveI := hem.1
  haveI : CharZero o := em.charZero
  have hq : IsQProjOver (F.U.ι ≫ F.Y.s) := hq.resolve_right (not_not.2 inferInstance)
  have hft := locallyOfFiniteType_of_qproj hq
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨c, hc, hsc⟩ := GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense L1 L2 hT h _ W _ a bas hW hb hu _ o b em _ _ F.univ hok F.dense

  have pull : ∀ (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (f : S' ⟶ F.U.toScheme), f ≫ F.U.ι ≫ F.Y.s = s' →
      ∃ (c' : SiegPre h ((n ^ j) ^ 2) (b.ζ : o) s') (t : TObj (8 * h) ((n ^ j) ^ 2) _ b s'),
        SiegPB c' c f ∧ c'.Principal ∧ IsSharp W a bas t c' := by
    intro S' s' f hf
    obtain ⟨p1, p2, -⟩ := GlobalTheory.T.siegelPre_pullback_principal_ringChange h ((n ^ j) ^ 2) o o (b.ζ : o) (b.ζ : o) (RingHom.id o) _ S' _ s' f rfl
      (hf.trans (comp_spMap_id s').symm)
    obtain ⟨c', hc'⟩ := p1 c
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h _ W _ a bas hW hb _ o b S' s' c' hok h3k hζ (p2 c c' hc' hc)
    exact ⟨c', t, hc', p2 c c' hc' hc, ht⟩
  refine ⟨⟨F.U.toScheme, F.U.ι ≫ F.Y.s, ?_, hq, c, hc, ?_, ?_⟩⟩
  · refine GlobalTheory.T.smoothOfRelativeDimension_of_flat_dedekind_tangent_le o _ _ _ hem.2.1 hflat hft
      (fun R _ _ x hx hs => GlobalTheory.T.le_ringKrullDim_thetaFamily_genericFibre L1 L2 _ n _ _ Mat κ w w' o b em _ _ F h3 hoN hem hG R x hx hs) ?_
    intro K _ _ r β x hx hlam
    obtain ⟨c', t, hp, hc', ht⟩ := pull _ _ x hx
    have htx : TMap t F.univ x :=
      (GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t x hc hc' hsc ht).1 hp
    refine GlobalTheory.T.siegelFamily_tangent_dimension_bound L1 L2 hT h _ W _ a bas hW hb w w' hw hw' _ o b K r β t c' hc' ht fun lam t' h1 h2 => hlam lam ?_
    have e : constPt (spMap (dirMap lam) ≫ x) = constPt (spMap (dirMap lam)) ≫ x := by
      simp only [constPt, Category.assoc]
    rw [e]
    refine hinj _ _ _ _ t' ?_ (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o _ _ _ b _ _ _ _ _ _ F.univ t t').2 x _ htx).1 h1)
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o _ _ _ b _ _ _ _ _ _ F.univ t t').2 x _ htx).1 h2)
    rw [Category.assoc, Category.assoc, hx]
    exact dir_over β lam
  · intro S s' c' hS hd hc'
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h _ W _ a bas hW hb _ o b S s' c' hok h3k hζ hc'
    have hfrom : ∀ p : S, (s' p).asIdeal = ⊥ →
        FromC em (SharpClass (b := b) W a bas em) t (K := S.residueField p) (S.fromSpecResidueField p) := by
      intro p hp
      haveI := charZero_residueField s' p hp
      exact GlobalTheory.T.fromC_sharpClass_fibre_of_charZero L1 L2 h _ W _ a w w' bas hW hb hw hw' hu _ o b em hem S s' t c' hc' ht _ _
    have hdense : Dense (fromSet em (SharpClass (b := b) W a bas em) t) :=
      hd.mono fun p hp => ⟨S.residueField p, inferInstance, S.fromSpecResidueField p,
        ⟨default, Scheme.fromSpecResidueField_apply p _⟩, hfrom p hp⟩
    have hshape : t.FibShape Mat κ := by
      intro K _ _ x t' ht'
      have : Nonempty S := ⟨x (⊥ : PrimeSpectrum K)⟩
      obtain ⟨p, hp⟩ := hd.nonempty
      obtain ⟨_, _, _, _, _, _, _, tc, -, -, -, -, -, htc⟩ := hfrom p hp
      have hsh := (hG.shape tc htc).1
      obtain ⟨cc, hcc, hscc⟩ := htc
      exact (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o _ _ _ b Mat κ w w' _ _ _ _ x t t' ht').1
        (GlobalTheory.T.eighthPower_shape_depends_only_on_matrices L1 L2 h _ W _ a bas hW hb _ o b Mat κ _ _ _ _ cc c' tc t hh ⟨(⊥ : PrimeSpectrum ℂ)⟩ hcc hc' hscc ht hsh)
    obtain ⟨f, ⟨hf, htf⟩, -⟩ := hj₃ j hj3 o b em _ _ hem hG F S s' t hS hdense hshape
    exact ⟨f, hf, (GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t f hc hc' hsc ht).2 hu htf⟩
  · intro R _ _ x y s' c₀ hxy hx hy
    obtain ⟨c', t, hp, hc', ht⟩ := pull _ _ x rfl
    have h1 : SiegPB c' c₀ (𝟙 _) :=
      ((GlobalTheory.SiegelPullComp.id_comp_cancel h _ o o o _ _ _ _ _ _ _ _ _ c c₀ c' x (𝟙 _)).2 hx).2
        (by rwa [Category.id_comp])
    have h2 : SiegPB c' c y := by
      have := ((GlobalTheory.SiegelPullComp.id_comp_cancel h _ o o o _ _ _ _ _ _ _ _ _ c c₀ c' y (𝟙 _)).2 hy).1 h1
      rwa [Category.id_comp] at this
    exact hinj R x y _ t hxy
      ((GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t x hc hc' hsc ht).1 hp)
      ((GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t y hc hc' hsc ht).1 h2)

end GlobalTheory.ZM.SiegelArithFamily
