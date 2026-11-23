import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitiveAtUniformisedTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListsUniqueUpToPermScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CmpTrait

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem comp_pow'' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem card_le_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N ≤ N' := by
  let e : Over.mk (spMap (RingHom.id K) ≫ x) ⟶ Over.mk x := Over.homMk (spMap (RingHom.id K)) rfl
  have key : ∀ a, ∃ b, pt a = pt' b := fun a => by
    have hp : (e ≫ pt a) ^ (m ^ 2) = 1 := by
      rw [← comp_pow'', (h.2.1 a).1, MonObj.comp_one]
    obtain ⟨b, hb⟩ := h'.2.2 K (RingHom.id K) (e ≫ pt a) hp
    refine ⟨b, Over.OverMorphism.ext ?_⟩
    have hb' : spMap (RingHom.id K) ≫ (pt a).left = spMap (RingHom.id K) ≫ (pt' b).left := hb
    rwa [spMap_id', Category.id_comp, Category.id_comp] at hb'
  choose s hs using key
  have hs' : Function.Injective s := fun a a' he => h.1 ((hs a).trans ((congrArg pt' he).trans (hs a').symm))
  simpa using Fintype.card_le_of_injective s hs'

theorem card_eq_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N = N' :=
  le_antisymm (card_le_of_thList h h') (card_le_of_thList h' h)

theorem isGenSec_of_nz {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {g : ℕ} {K : Type}
    [Field K] {x : Sp K ⟶ S} (hP : PolFib G L g x) {θ : SecAt G L x} (hθ : NZ G L x θ) : IsGenSec G L _ θ := by
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id', Category.id_comp]
  obtain ⟨a, ha⟩ := he.ex (RingHom.id K) h0 (SecM.ofSec G θ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_smul] at ha
    obtain ⟨q, -, hq⟩ := hθ
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    have e0 : θ.f j = 0 := congrArg (fun s => s.1 j) ha
    rw [e0, Scheme.basicOpen_zero] at hj
    exact hj
  refine (isGenSec_iff θ).2 fun s => ?_
  obtain ⟨b, hb⟩ := he.ex (RingHom.id K) h0 s
  refine ⟨fnR x (b * a⁻¹), ?_⟩
  rw [hb, ha, smul_smul, ← map_mul, _root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]

theorem prim_of_finite {V V' K : Type} [CommRing V] [CommRing V'] [Field K] (f : V →+* V') (i : V' →+* K) {J : Type}
    (c : J → K) (hf : f.Finite) (h : Prim i c) : Prim (i.comp f) c := by
  letI := f.toAlgebra
  letI := i.toAlgebra
  letI := (i.comp f).toAlgebra
  haveI : IsScalarTower V V' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have key : ∀ z : K, i.IsIntegralElem z → (i.comp f).IsIntegralElem z := fun z hz =>
    isIntegral_trans (R := V) (A := V') z hz
  obtain ⟨h1, a, ha, ha'⟩ := h
  exact ⟨fun b => key _ (h1 b), a, ha, key _ ha'⟩

theorem exists_ext {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (f : V →+* V')
    (fK : FractionRing V →+* FractionRing V') {K : Type} [Field K] [IsAlgClosed K] (io : FractionRing V →+* K)
    (hf : f.Finite) (hfK : ∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) :
    ∃ io' : FractionRing V' →+* K, io'.comp fK = io := by
  letI := fK.toAlgebra
  letI := io.toAlgebra
  letI := f.toAlgebra
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have hint : ∀ b : V', IsAlgebraic (FractionRing V) (algebraMap V' (FractionRing V') b) := fun b => by
    obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := V) b
    refine (show IsIntegral (FractionRing V) (algebraMap V' (FractionRing V') b) from
      ⟨p.map (algebraMap V (FractionRing V)), hp.map _, ?_⟩).isAlgebraic
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (FractionRing V) (FractionRing V')).comp (algebraMap V (FractionRing V)) =
        (algebraMap V' (FractionRing V')).comp (algebraMap V V') := RingHom.ext hfK
    rw [e, ← Polynomial.hom_eval₂, hp0, map_zero]
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing V') := ⟨fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V') z
    exact (hint a).mul (hint b).inv⟩
  let φ : FractionRing V' →ₐ[FractionRing V] K := IsAlgClosed.lift
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem prim_comp {V K : Type} [CommRing V] [Field K] {i : V →+* K} {J J' : Type} {c : J → K} (h : Prim i c)
    (s : J' → J) (hs : Function.Surjective s) : Prim i (c ∘ s) := by
  obtain ⟨h1, a, ha, ha'⟩ := h
  obtain ⟨b, rfl⟩ := hs a
  exact ⟨fun b => h1 _, b, ha, ha'⟩

theorem cmp_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ Xo.XF c) (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' (spMap io ≫ y ≫ pullback.fst _ _) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV y K _ _ io m m' N N' d d' hmo hm3 hmu hmo' hm3' hmu' hd
  have hbase : GlobalTheory.Mum.Base V := ⟨ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hV, hV.2.2⟩
  obtain ⟨T, f, fK, -, -, hff, hfK, hTy⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V hbase hV.1 y
  obtain ⟨io', hio'⟩ := exists_ext f fK io hff hfK
  set i : T.V →+* K := io'.comp (algebraMap T.V (FractionRing T.V)) with hi
  have hinj : Function.Injective i := io'.injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨tK, ⟨mK⟩, ⟨mx⟩⟩ := T.gen
  obtain ⟨m0, -⟩ := ObjMaps.exists_sab_id T.t
  have hpol : GlobalTheory.LN.PolAt T.t (jK T.V) := UnifAfterExt.polAt_of_sabMap m0 mK mx Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv (jK T.V) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
  obtain ⟨σ, hσ⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H (Sp T.V) T.t T.V (𝟙 _) T.t m0
    hpol
  have h0 : spMap (RingHom.id T.V) ≫ 𝟙 (Sp T.V) = 𝟙 _ := by rw [Category.comp_id, spMap_id']
  have hσσ : VVRank.pullS T.t.G _ (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) σ = σ := by
    have e : (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) = 𝟙 _ :=
      Over.OverMorphism.ext (spMap_id' T.V)
    rw [e]
    have := VVRank.pullM_id T.t.G T.t.PP.isLB ((1 : ℕ) : ℤ) (SecM.ofSec T.t.G σ)
    rw [VVRank.pullM_ofSec] at this
    exact congrArg (SecM.toSec T.t.G) this
  have hnz : NZ T.t.G T.t.PP.L (𝟙 _) σ := by
    have := hσ T.V (RingHom.id _) _ h0
    rwa [hσσ] at this
  have hmT : ∀ {k : ℕ}, IsUnit (k : V) → IsUnit (k : T.V) := fun h => by simpa using h.map f
  have hmK : ∀ {k : ℕ}, IsUnit (k : V) → (k : K) ≠ 0 := fun h => by
    have := h.map (io.comp (algebraMap V (FractionRing V))); simpa using this.ne_zero
  set x₁ : Sp K ⟶ Sp T.V := spMap i ≫ 𝟙 (Sp T.V) with hx₁
  have ex₁ : spMap io' ≫ jK T.V = x₁ := by rw [hx₁, Category.comp_id, hi, spMap_comp']
  set x : Sp K ⟶ Xo.X := spMap io ≫ y ≫ pullback.fst _ _ with hx
  have ex : spMap io' ≫ T.y ≫ pullback.fst _ _ = x := by rw [hx, hTy, ← hio', spMap_comp']; simp only [Category.assoc]
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hPx : PolFib Xo.univ.t.G Xo.univ.t.PP.L g x := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c K x
  obtain ⟨wK, hwK, -⟩ := mK.lin
  obtain ⟨wx, hwx, -⟩ := mx.lin
  have hPK : PolFib tK.G tK.PP.L g (spMap io') :=
    ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ Xo.univ.t.PP.isLB tK.PP.isLB mx.cart ⟨wx, hwx⟩ g K (spMap io')).1).2 (ex ▸ hPx)
  have hP₁ : PolFib T.t.G T.t.PP.L g x₁ :=
    ex₁ ▸ ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ T.t.PP.isLB tK.PP.isLB mK.cart ⟨wK, hwK⟩ g K (spMap io')).1).1 hPK
  set θ := SecAt.pull T.t.G T.t.PP.L σ i with hθdef
  have hθnz : NZ T.t.G T.t.PP.L x₁ θ := hσ K i x₁ rfl
  have hθ : IsGenSec T.t.G T.t.PP.L _ θ := isGenSec_of_nz T.t.PP.isLB hP₁ hθnz
  obtain ⟨pt, cc, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m _ K x₁ θ hmo (hmK hmu)
    rfl hP₁
  obtain ⟨pt', cc', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m' _ K x₁ θ hmo'
    (hmK hmu') rfl hP₁
  have hpr : Prim i cc := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m _ hmo hm3 (hmT hmu)
    K i pt cc hinj hc
  have hpr' : Prim i cc' := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m' _ hmo' hm3'
    (hmT hmu') K i pt' cc' hinj hc'
  have h₁ : HasTh₂ T.t.G T.t.PP.L T.t.PP.rig m m' x₁ cc cc' := ⟨θ, pt, pt', hθ, hc, hc'⟩
  have hK : HasTh₂ tK.G tK.PP.L tK.PP.rig m m' (spMap io') cc cc' :=
    (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen _ tK.G tK.PP.L tK.PP.rig (jK T.V) mK.φ
      tK.PP.isLB tK.PP.rigGen mK.cart ⟨wK, hwK⟩ m m' _ _ K (spMap io') cc cc').2 (ex₁ ▸ h₁)
  have hX : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' x cc cc' :=
    ex ▸ (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ tK.G
      tK.PP.L tK.PP.rig (T.y ≫ pullback.fst _ _) mx.φ tK.PP.isLB tK.PP.rigGen mx.cart ⟨wx, hwx⟩ m m' _ _ K (spMap io')
      cc cc').1 hK
  have eN : N = m ^ (4 * g) := by
    obtain ⟨_, _, _, _, hd1, -⟩ := hd
    obtain ⟨_, _, _, _, hc1, -⟩ := hX
    exact card_eq_of_thList hd1 hc1
  have eN' : N' = m' ^ (4 * g) := by
    obtain ⟨_, _, _, _, -, hd2⟩ := hd
    obtain ⟨_, _, _, _, -, hc2⟩ := hX
    exact card_eq_of_thList hd2 hc2
  subst eN eN'
  obtain ⟨a, s, s', ha, hds, hds'⟩ := (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m m' _ _ K x hmo (hmK hmu) hmo' (hmK hmu') hPx).2 cc d cc' d' hX hd
  have ei : i.comp f = io.comp (algebraMap V (FractionRing V)) := by
    ext v
    simp only [hi, RingHom.comp_apply, ← hfK, ← hio']
  have e1 : (fun b => d b / a) = cc ∘ s := funext fun b => by
    rw [hds b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  have e2 : (fun b => d' b / a) = cc' ∘ s' := funext fun b => by
    rw [hds' b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  refine ⟨a, ha, ?_, ?_⟩
  · rw [e1, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr s s.surjective)
  · rw [e2, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr' s' s'.surjective)

end GlobalTheory.UMin.CmpTrait
