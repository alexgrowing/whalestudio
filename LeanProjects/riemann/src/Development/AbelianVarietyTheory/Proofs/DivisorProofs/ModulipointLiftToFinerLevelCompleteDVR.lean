import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOverLaOfNotCharZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

namespace GlobalTheory.LevelLift

open scoped TensorProduct

theorem exists_field_over (K F M : Type) [Field K] [Field F] [Field M] [Algebra K F] [FiniteDimensional K F]
    (io : K →+* M) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : Algebra M L₀) (_ : FiniteDimensional M L₀) (io' : F →+* L₀),
      io'.comp (algebraMap K F) = (algebraMap M L₀).comp io := by
  letI : Algebra K M := io.toAlgebra
  haveI : Nontrivial (M ⊗[K] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K M F io.injective
      (algebraMap K F).injective
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (M ⊗[K] F)
  letI : Field (M ⊗[K] F ⧸ I) := Ideal.Quotient.field I
  refine ⟨M ⊗[K] F ⧸ I, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk I).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext k
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply K M (M ⊗[K] F), Ideal.Quotient.mk_algebraMap]
  rfl

theorem exists_point_finite_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : IsFinite f) (hs : Surjective f)
    (L₀ : Type) [Field L₀] (y : Sp L₀ ⟶ Y) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra L₀ L) (_ : FiniteDimensional L₀ L) (x : Sp L ⟶ X),
      x ≫ f = spMap (algebraMap L₀ L) ≫ y := by
  haveI := hf
  haveI := hs
  haveI : Surjective (pullback.snd f y) := inferInstance
  haveI : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  let P := pullback f y
  let g' : Spec Γ(P, ⊤) ⟶ Sp L₀ := P.isoSpec.inv ≫ pullback.snd f y
  haveI : IsFinite g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  haveI : Nonempty (Sp L₀) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨p, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Sp L₀))
  haveI : Nontrivial Γ(P, ⊤) := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨P.isoSpec.hom p⟩
  obtain ⟨I, hI⟩ := Ideal.exists_maximal Γ(P, ⊤)
  letI : Field (Γ(P, ⊤) ⧸ I) := Ideal.Quotient.field I
  letI : Algebra L₀ (Γ(P, ⊤) ⧸ I) := ((Ideal.Quotient.mk I).comp φ.hom).toAlgebra
  have hfin : ((Ideal.Quotient.mk I).comp φ.hom).Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hφf
  refine ⟨Γ(P, ⊤) ⧸ I, inferInstance, inferInstance, hfin,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ P.isoSpec.inv ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv]
  change _ ≫ g' ≫ y = _
  rw [← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem lift_to_finer_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l₂ : Level H) (Xo : Moduli Dw l) (Xo₂ : Moduli Dw l₂) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.Dvd l₂ → l₂.A = l.A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∃ (c₂ : Coeff l₂) (la₂ : HeightOneSpectrum (𝓞 c₂.F)) (T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V) (e' : ℕ) (io₂ : c₂.F →+* T'.Fr) (e₂ : ℕ) (x₂ : Sp T'.Fr ⟶ Xo₂.X) (r : Xo₂.X ⟶ Xo.X) (_ : SABMap Xo₂.univ.t Xo.univ.t r), 0 < e' ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e' : ℤ) * vV T.V a) ∧ (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ OverLa la₂ T'.V io₂ e₂ ∧ x₂ ≫ Xo₂.s = spMap (io₂.comp (IntermediateField.inclusion c₂.le).toRingHom) ∧ x₂ ≫ r = spMap iT ≫ x := by
  intro E _ _ _ H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hx
  obtain ⟨r, jK, m, -, -, -, -, -, hrF⟩ :=
    ((GlobalTheory.moduliScheme_levelMaps_heckePoints).2 E H Dw hpq).1 l l₂ Xo Xo₂ hd
  let F₂ : IntermediateField ℚ ℂ := c.F ⊔ IntermediateField.adjoin ℚ {zeta l₂.M'}
  have hle : c.F ≤ F₂ := le_sup_left
  have hpos : 0 < l₂.M' := Nat.lcm_pos (by have := l₂.three_le; omega) l₂.A_pos
  have hint : IsIntegral ℚ (zeta l₂.M') :=
    ((Complex.isPrimitiveRoot_exp l₂.M' hpos.ne').isIntegral hpos).tower_top
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l₂.M'}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfin : FiniteDimensional ℚ F₂ := IntermediateField.finiteDimensional_sup _ _
  have hKA : KA l₂ = KA l := by unfold KA; rw [hA]
  let c₂ : Coeff l₂ :=
    { F := F₂, fin := hfin, conj := fun τ a => hle (c.conj τ a),
      zeta_mem := le_sup_right (a := c.F) (IntermediateField.subset_adjoin ℚ _ rfl),
      le := hKA ▸ c.le.trans hle }
  let c' : Coeff l :=
    { F := F₂, fin := hfin, conj := fun τ a => hle (c.conj τ a), zeta_mem := hle c.zeta_mem,
      le := c.le.trans hle }
  obtain ⟨rF, hr1, hr2, hfinr, -, hsurj, -⟩ := hrF c' c₂ rfl
  letI : Algebra c.F F₂ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ c.F F₂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp
  haveI : FiniteDimensional c.F F₂ := Module.Finite.of_restrictScalars_finite ℚ c.F F₂
  obtain ⟨L₀, _, _, _, io', hio'⟩ := exists_field_over c.F F₂ T.Fr io
  have cond : (spMap (algebraMap T.Fr L₀) ≫ x) ≫ Xo.s =
      spMap io' ≫ spMap (IntermediateField.inclusion c'.le).toRingHom := by
    rw [Category.assoc, hx, Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
    congr 1
    ext a
    have h := RingHom.congr_fun hio' (IntermediateField.inclusion c.le a)
    exact h.symm
  let z' : Sp L₀ ⟶ Xo.XF c' := pullback.lift (spMap (algebraMap T.Fr L₀) ≫ x) (spMap io') cond
  obtain ⟨L, _, _, _, x', hx'⟩ := exists_point_finite_surjective rF hfinr hsurj L₀ z'
  letI : Algebra T.Fr L := ((algebraMap L₀ L).comp (algebraMap T.Fr L₀)).toAlgebra
  haveI : IsScalarTower T.Fr L₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional T.Fr L := Module.Finite.trans L₀ L
  obtain ⟨T', iT, e', ψ, φ, he', hv, hψ, hφ, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
  let io₂ : c₂.F →+* T'.Fr := ψ.toRingHom.comp ((algebraMap L₀ L).comp io')
  haveI : NumberField c₂.F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨la₂, e₂, ho₂⟩ := GlobalTheory.LocalDepthCompare.exists_overLa_of_not_charZero (V := T'.V) io₂
    (GlobalTheory.LocalDepthCompare.not_charZero_of_overLa (ho.bc iT he' hv))
  have hid : spMap (IntermediateField.inclusion (le_of_eq (rfl : c'.F = c₂.F))).toRingHom = 𝟙 (Sp c₂.F) := by
    have : (IntermediateField.inclusion (le_of_eq (rfl : c'.F = c₂.F))).toRingHom = RingHom.id _ :=
      RingHom.ext fun _ => rfl
    rw [this]
    exact (congrArg Spec.map (CommRingCat.ofHom_id)).trans (Spec.map_id _)
  have hs : x' ≫ pullback.snd _ _ = spMap ((algebraMap L₀ L).comp io') := by
    have h := congrArg (· ≫ pullback.snd _ _) hx'
    simp only [Category.assoc, hr2, pullback.lift_snd, z'] at h
    rw [hid, Category.comp_id] at h
    rw [h, Formalism.L2.PjFree.spMap_comp']
  have hf : x' ≫ pullback.fst _ _ ≫ r = spMap (algebraMap T.Fr L) ≫ x := by
    have h := congrArg (· ≫ pullback.fst _ _) hx'
    simp only [Category.assoc, hr1, pullback.lift_fst, z'] at h
    rw [h, ← Category.assoc, Formalism.L2.PjFree.spMap_comp']
  refine ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, spMap ψ.toRingHom ≫ x' ≫ pullback.fst _ _, r, m, he', hv, hφ, ho₂,
    ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc x', hs, ← Category.assoc,
      Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
  · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, Formalism.L2.PjFree.spMap_comp']
    have hc : ψ.toRingHom.comp (algebraMap T.Fr L) = iT := RingHom.ext fun a => hψ a
    rw [hc]

end GlobalTheory.LevelLift
