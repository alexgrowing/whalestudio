import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextValAxioms
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GrpPullbackSquareProductLift
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsBXOfFactorSystems
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsFibreProduct
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TransportRightSmulFrame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulEqZeroOfSqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawProduct
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompatibleBasis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ModPToValuationResidueFieldSurjective
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantGeneratorDescendsMulN
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextPairingNondegenerateGeometricFibre
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorsionInvariantDescendsFibre
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdCocycleMul
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingNondegenerateIntegralTorsion
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsDivisibleAndTorsionOfValuationIntegers
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NonemptyIsBiextOfCubeGen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPeriodDatum

section SlopeTestRemainingChoices

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {B : BX R₀}
  {e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)}

private theorem e_zero (hm : ∀ R x y, e R (x + y) = e R x * e R y) (R : LAlg R₀) : e R 0 = 1 := by
  have h := hm R 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

private theorem e_nsmul (hm : ∀ R x y, e R (x + y) = e R x * e R y) (R : LAlg R₀) (n : ℕ) (x : B.G R) :
    e R (n • x) = e R x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, e_zero hm]
  | succ n ih => rw [succ_nsmul, hm, ih, pow_succ]

private theorem divisible_and_card [IsCommMonObj G] (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y) (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ)
    (hv : v.Integers (O : Type)) (hf : IsFinite ((𝟙 G) ^ p : G ⟶ G).left) (hs : Surjective ((𝟙 G) ^ p : G ⟶ G).left) :
    (∀ x : B.G O, ∃ y, p • y = x) ∧
      Nat.card {x : B.G O // p • x = 0} = Nat.card {z : sp (R₀ := R₀) C ⟶ G // z ^ p = 1} := by
  obtain ⟨h₁, h₂⟩ := GlobalTheory.points_divisible_and_torsion_of_valuation_integers G O C v p hv hf hs
  have tors : ∀ x : B.G O, p • x = 0 ↔ e O x ^ p = 1 := fun x => by
    rw [← e_nsmul hm, ← e_zero hm O]
    exact (hb O).1.eq_iff.symm
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := h₁ (e O x)
    obtain ⟨y, rfl⟩ := (hb O).2 y
    exact ⟨y, (hb O).1 ((e_nsmul hm O p y).trans hy)⟩
  · refine Nat.card_congr (Equiv.ofBijective
      (fun x => ⟨spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O x.1, ?_⟩) ⟨fun x y hxy => ?_, fun z => ?_⟩)
    · rw [← MonObj.comp_pow, (tors _).1 x.2, MonObj.comp_one]
    · have hxy' : spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O x.1 =
          spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O y.1 := congrArg Subtype.val hxy
      have hz : (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O y.1) ^ p = 1 := by
        rw [← MonObj.comp_pow, (tors _).1 y.2, MonObj.comp_one]
      exact Subtype.ext ((hb O).1 ((h₂ _ hz).unique ⟨(tors _).1 x.2, hxy'⟩ ⟨(tors _).1 y.2, rfl⟩))
    · obtain ⟨y, ⟨hy, hy'⟩, -⟩ := h₂ z.1 z.2
      obtain ⟨y, rfl⟩ := (hb O).2 y
      exact ⟨⟨y, (tors y).2 hy⟩, Subtype.ext hy'⟩

private theorem ring_laws (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y) (O : LAlg R₀)
    (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left)
    (gp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ)
    (O₀ : Type) [CommRing O₀] (cj : O₀ → O₀) (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct G' O₀) (Ad : O₀ → OAdj B O)
    (ha : ∀ a {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act a).left ≫ φ = (e R ((Ad a).a.f s x)).left)
    (hab : ∀ a {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act (cj a)).left ≫ φ = (e R ((Ad a).ab.f s x)).left) :
    (∀ a, (Ad a).ab = (Ad (cj a)).a) ∧
    (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (Ad 1).a.f s x = x ∧
      ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
        (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) := by
  choose E hE using fun (R : LAlg R₀) (s : LHom O R) => GlobalTheory.adjPoints gp _ _ (GlobalTheory.adjBase s)
  have hl : ∀ R s x, ((E R s).symm (e R x)).left ≫ φ = (e R x).left := fun R s x =>
    (hE R s _).symm.trans (congrArg (fun q => q.left) ((E R s).apply_symm_apply _))
  have inj : ∀ R (x y : B.G R), (e R x).left = (e R y).left → x = y := fun R x y h =>
    (hb R).1 (Over.OverMorphism.ext h)
  refine ⟨fun a => ?_, fun {R} s x => ⟨?_, fun a b => ⟨?_, ?_⟩⟩⟩
  · have h : ∀ {R : LAlg R₀} (s : LHom O R), (Ad a).ab.f s = (Ad (cj a)).a.f s := fun {R} s =>
      AddMonoidHom.ext fun x => inj R _ _ ((hab a s x _ (hl R s x)).symm.trans (ha (cj a) s x _ (hl R s x)))
    generalize (Ad a).ab = u at h
    generalize (Ad (cj a)).a = w at h
    obtain ⟨u, hu⟩ := u
    obtain ⟨w, hw⟩ := w
    obtain rfl : @u = @w := funext fun R => funext fun s => h s
    rfl
  · refine inj R _ _ ((ha 1 s x _ (hl R s x)).symm.trans ?_)
    rw [ρ.map_one, Category.comp_id]
    exact hl R s x
  · refine inj R _ _ ((ha (a + b) s x _ (hl R s x)).symm.trans ?_)
    have h₁ : e R ((Ad a).a.f s x) = E R s ((E R s).symm (e R x) ≫ ρ.act a) :=
      Over.OverMorphism.ext ((ha a s x _ (hl R s x)).symm.trans (hE R s _).symm)
    have h₂ : e R ((Ad b).a.f s x) = E R s ((E R s).symm (e R x) ≫ ρ.act b) :=
      Over.OverMorphism.ext ((ha b s x _ (hl R s x)).symm.trans (hE R s _).symm)
    have h₃ : (E R s).symm (e R x) ≫ ρ.act (a + b) =
        ((E R s).symm (e R x) ≫ ρ.act a) * ((E R s).symm (e R x) ≫ ρ.act b) := by
      rw [ρ.map_add]
      exact MonObj.comp_mul _ _ _
    rw [hm, h₁, h₂, h₃]
    exact (hE R s _).symm.trans (congrArg (fun q => q.left) (map_mul (E R s) _ _))
  · refine inj R _ _ ((ha (a * b) s x _ (hl R s x)).symm.trans ?_)
    rw [ρ.map_mul, ← Category.assoc]
    exact ha a s _ _ (ha b s x _ (hl R s x))

end SlopeTestRemainingChoices

theorem main : (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ) (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left), ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → P.IsLB → (∃ θ : LB.Gen (Theta (G ⊗ G) P), θ.IsGen) → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd G G) (fst G G)).left) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left → ∀ [Algebra ((Ainf.ainfTowerL p O hv ε hε).O : Type) C] [Algebra (Ainf.R0 p O ε) C] [IsScalarTower (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type) C], v.Integers ((Ainf.ainfTowerL p O hv ε hε).O : Type) → (∀ x : sp (R₀ := (Ainf.R0 p O ε)) C ⟶ G, (∃ t : (P.pull (lift (snd G (sp (R₀ := (Ainf.R0 p O ε)) C) ≫ x) (fst G (sp (R₀ := (Ainf.R0 p O ε)) C))).left).Gen, t.IsGen) → x = 1) → Nat.card {z : sp (R₀ := (Ainf.R0 p O ε)) C ⟶ G // z ^ p = 1} = p ^ (2 * g) → ∀ (G' : Over (Spec (CommRingCat.of ((Ainf.ainfTowerL p O hv ε hε).O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left), ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G' → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type)))) φ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ → ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct G' O₀), (∀ a, cj (cj a) = a) → (∀ a, (∃ t : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (fst G' G' ≫ ρ.act a) (snd G' G')).left ≫ φ₂, (lift (fst G' G') (snd G' G' ≫ ρ.act (cj a))).left ≫ φ₂] ![1, -1]), t.IsGen)) → ∃ (B : BX (Ainf.R0 p O ε)) (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧ (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧ (∀ a, (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act a).left ≫ φ = (e R ((Ad a).a.f s x)).left)) ∧ ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c), D.H.P = 0 ∧ D.H.PL = 0 ∧ (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) → (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧ ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε g G _ _ P hA hsm hP hθ h1 h2 hsym hf hfl hsu _ _ _ hvi hnd hcard
    G' _ _ φ φ₂ hA' gp sq _ O₀ _ cj ρ hcj hros
  haveI : IsLocalRing (Ainf.R0 p O ε) := GlobalTheory.WdAinf.ainf_thetaQuotRing_isLocalRing p O hv ε hε
  obtain ⟨β⟩ := GlobalTheory.nonempty_isBiext_of_cube_gen _ G hA P hP hθ h1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.BiextSym.main GlobalTheory.globalFns_holds _ G hA P β hsym
  obtain ⟨B, e, hb, hm, hn, b, J, hJ, ha1, ha2⟩ := @GlobalTheory.BXOf.main
    (@GlobalTheory.GroupPointsBX.main (@GlobalTheory.NilCoord.nilpotent_coordinates) (@GlobalTheory.points_fibre_product))
    (@GlobalTheory.exists_BX_of_factorSystems) _ _ G _ _ _ g hsm P β s hs
  have hAd := fun a : O₀ => @GlobalTheory.exists_oAdj_of_rosatiAdjoint (@GlobalTheory.bx_frame_pairing_adj) GlobalTheory.biext_val_axioms
    GlobalTheory.globalFns_holds _ _ G _ _ P β B e b J hb hm hn hJ ha1 ha2 (Ainf.ainfTowerL p O hv ε hε).O G' _ _ φ φ₂ hA' gp sq
    (ρ.act a) (ρ.act (cj a)) (ρ.hom a) (ρ.hom (cj a)) (hros a)
  choose Ad ha hab using hAd
  obtain ⟨hadj, hring⟩ := ring_laws hb hm _ G' φ gp O₀ cj ρ Ad ha hab
  obtain ⟨hdiv, hc⟩ := divisible_and_card hb hm (Ainf.ainfTowerL p O hv ε hε).O C v p hvi hf hsu
  have hsmooth : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  have hpair := @GlobalTheory.pairing_nondegenerate_integral_torsion (@GlobalTheory.bx_frame_pairing_adj)
    (GlobalTheory.biext_pairing_nondegenerate_geometric_fibre
      (GlobalTheory.invariantGenerator_descends_mulN GlobalTheory.torsion_invariant_descends_fibre)
      (GlobalTheory.TorsionGen.main GlobalTheory.biext_val_axioms))
    (@GlobalTheory.points_divisible_and_torsion_of_valuation_integers) GlobalTheory.biext_val_axioms
    _ _ G _ _ P β B e b J hb hm hn hJ ha1 ha2 (Ainf.ainfTowerL p O hv ε hε).O C _ _ _ v _ _ _ p
    (Fact.out : p.Prime).ne_zero hvi hsmooth hf hfl hsu hnd
  exact ⟨B, e, Ad, hb, hm, hn, ha, GlobalTheory.PeriodDatum.main p O hv ε hε g G B e hb hm hn hsm hf hfl hdiv
    (hc.trans hcard) hpair O₀ cj Ad hadj hcj hring⟩

end GlobalTheory.AbelianPeriodDatum
