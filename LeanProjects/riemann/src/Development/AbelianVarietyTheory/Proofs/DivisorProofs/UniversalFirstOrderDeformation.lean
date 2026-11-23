import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModuliPointTrivSqZeroExtTangentBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivialStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan.KSUniv

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

noncomputable def reparam {K : Type} [Field K] (F : Type) [Field F] [Algebra F K] {ι : Type} [Fintype ι]
    (P : Matrix ι ι K) : TrivSqZeroExt K (ι → K) →ₐ[F] TrivSqZeroExt K (ι → K) :=
  (TrivSqZeroExt.map (Matrix.mulVecLin P.transpose)).restrictScalars F

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {ι : Type} [Fintype ι] {X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X} (h1 : X ≫ Xo.s = sOf c _)
    (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x) (M : ι → K) :
    GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, sOf, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (GlobalTheory.FlagTan.dir c M).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp

theorem dir_comp_reparam {K : Type} [Field K] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} {c : Coeff l} [Algebra c.F K] {ι : Type} [Fintype ι] (P : Matrix ι ι K) (M : ι → K) :
    (GlobalTheory.FlagTan.dir c M).toRingHom.comp (reparam c.F P).toRingHom = (GlobalTheory.FlagTan.dir c (P.mulVec M)).toRingHom := by
  ext z
  · simp [reparam]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.FlagTan.snd_dir, reparam,
      AlgHom.restrictScalars_apply, GlobalTheory.FlagTan.fst_dir, TrivSqZeroExt.snd_map, Matrix.mulVecLin_apply]
    have e := Matrix.dotProduct_mulVec z.snd P M
    rw [← Matrix.mulVec_transpose] at e
    simpa [dotProduct, mul_comm] using e.symm

open GlobalTheory.FlagTan in

theorem ksUniv : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  classical
  obtain ⟨X₀, h1, h2, hinj⟩ :=
    GlobalTheory.T.exists_moduliPoint_trivSqZeroExt_tangentBasis E H Dw l Xo c K y (HIx Dw (psiSet H)) (card_HIx (isHalf_psiSet H))
  choose N hN using fun k : HIx Dw (psiSet H) =>
    GlobalTheory.T.kodaira_spencer_matrix_exists hP E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 (Pi.single k 1))
  have hL := GlobalTheory.T.tangent_flag_hodge_index_vanishing hP E H Dw l Xo c K y _ X₀ hpq h1 h2 N hN
  let L : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K) := Fintype.linearCombination K N
  have hLa : ∀ M, L M = ∑ k, M k • N k := fun M => Fintype.linearCombination_apply _ _ _
  have h0 : spMap (dir c (0 : HIx Dw (psiSet H) → K)).toRingHom ≫ X₀ =
      spMap (algebraMap K (DualNumber K)) ≫ y.x := by
    rw [← h2, ← Category.assoc, spMap_comp_spMap']
    congr 2
    ext z <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have Linj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun M hM =>
    hinj ((GlobalTheory.T.kodaira_spencer_zero_tangent_trivial hP hG E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 M)
      (by rw [← hM, hLa]; exact hL M)).trans h0.symm)
  let e := LinearEquiv.ofInjectiveEndo L Linj
  let P := LinearMap.toMatrix' (e.symm : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K))
  have hP' : ∀ M, P.mulVec M = e.symm M := fun M => LinearMap.toMatrix'_mulVec _ M
  refine ⟨spMap (reparam c.F P).toRingHom ≫ X₀, ?_, ?_, fun M => ?_⟩
  · rw [Category.assoc, h1, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (reparam c.F P).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp [reparam]
  · rw [← Category.assoc, spMap_comp_spMap', dir_comp_reparam, hP']
    have := hL (e.symm M)
    rwa [← hLa, show L (e.symm M) = M from e.apply_symm_apply M] at this

end GlobalTheory.FlagTan.KSUniv
