import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHTLatOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankLineHyperplane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlgOfFlagClSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelReductionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFree
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
open CategoryTheory AlgebraicGeometry NumberField MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open scoped NNReal
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.KernelNoTorsion GlobalTheory.TangentPow
open GlobalTheory.GmPoints GlobalTheory.RaynaudTorsionMap GlobalTheory.HodgeTateImage GlobalTheory.CompHt.FormalChar GlobalTheory.HodgeTateLevel

namespace GlobalTheory.TorsCharDlog

section Transfer

variable {X : Scheme.{0}} {O : Type} [CommRing O] {z : Sp O ⟶ X} {G : Over (Sp O)} [GrpObj G]
  {G' : Over X} [GrpObj G'] {φ : G.left ⟶ G'.left} (hφ : IsGrpPullback G G' z φ)

def toOver (R : Type) [CommRing R] [Algebra O R] (y : specO O R ⟶ G) : overAt z R ⟶ G' :=
  Over.homMk (y.left ≫ φ) (by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w y]
    rfl)

variable (R : Type) [CommRing R] [Algebra O R]

theorem toOver_left (y : specO O R ⟶ G) : (toOver hφ R y).left = y.left ≫ φ := rfl

theorem toOver_mul (y y' : specO O R ⟶ G) : toOver hφ R (y * y') = toOver hφ R y * toOver hφ R y' :=
  Over.OverMorphism.ext (hφ.2 (specO O R) y y' (toOver hφ R y) (toOver hφ R y') rfl rfl).symm

def toOverHom : (specO O R ⟶ G) →* (overAt z R ⟶ G') := MonoidHom.mk' (toOver hφ R) (toOver_mul hφ R)

theorem toOver_pow (y : specO O R ⟶ G) (k : ℕ) : toOver hφ R (y ^ k) = toOver hφ R y ^ k :=
  map_pow (toOverHom hφ R) y k

theorem toOver_one : toOver hφ R (1 : specO O R ⟶ G) = 1 := map_one (toOverHom hφ R)

theorem toOver_injective : Function.Injective (toOver hφ R) := fun y y' h =>
  Over.OverMorphism.ext (hφ.1.hom_ext (congrArg CommaMorphism.left h) (by rw [Over.w y, Over.w y']))

theorem toOver_surjective : Function.Surjective (toOver hφ R) := fun w =>
  ⟨Over.homMk (hφ.1.lift w.left (specO O R).hom (Over.w w)) (hφ.1.lift_snd _ _ _),
    Over.OverMorphism.ext (hφ.1.lift_fst _ _ _)⟩

theorem homAt_toOver {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (y : specO O R ⟶ G) :
    homAt z f ≫ toOver hφ R y = toOver hφ R' (ptMap f ≫ y) :=
  Over.OverMorphism.ext (by
    change spMap _ ≫ y.left ≫ φ = (Spec.map _ ≫ y.left) ≫ φ
    rw [Category.assoc]
    rfl)

omit [GrpObj G] [GrpObj G'] in
theorem homAt_comp_homAt {A B D : Type} [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] [CommRing D]
    [Algebra O D] (f : A →ₐ[O] B) (g : B →ₐ[O] D) : homAt z g ≫ homAt z f = homAt z (g.comp f) :=
  Over.OverMorphism.ext (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp]
    rfl)

end Transfer

end GlobalTheory.TorsCharDlog

namespace GlobalTheory.TorsCharDlog

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [hO : IsAdicComplete (Ideal.span {(p : O)}) O]
  [HenselianLocalRing O] [Algebra ℤ_[p] O] {Λ : Type} [CommRing Λ] [StarRing Λ]

theorem snd_chi_eq (P : Point p v O Λ) (z : Sp O ⟶ X) (φ : P.G.left ⟶ t.G.left) (hφ : IsGrpPullback P.G t.G z φ)
    (n : ℕ) (c : TorsChar t z (p ^ n)) (s : P.T)
    (hc : ∀ (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) (a : GlobalTheory.ChTor.Pts P.A.A), w ^ (p ^ n) = 1 →
      a.left ≫ P.gen ≫ φ = spMap (algebraMap O C) ≫ w.left →
        algebraMap O C (c.χ O w : O) = (GlobalTheory.HTLat.weil P.A (p ^ n) a (s.lev n) : C))
    (x : LieG P.Gt) (g : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ z) ⟶ t.G)
    (hg : g.left = spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}))) ≫ (P.lieCmp x).1.left ≫ φ) :
    (c.χ _ g : DualNumber (O ⧸ Ideal.span {(p : O) ^ n})).snd =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((P.al₀ s).1 x) := by
  have hv := P.integers
  have hp0 := (Fact.out : p.Prime).ne_zero
  have hN := one_le_ppow p n
  have hq : p ^ n ≠ 0 := pow_ne_zero n hp0
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI := ValuationRing.of_integers v hv
  haveI := P.isLocalRing
  haveI := (P.finite_flat _ hN).1
  haveI := (P.finite_flat _ hN).2

  obtain ⟨A₀, _, _, u, _, _, hu, hrep⟩ :=
    GlobalTheory.TorsionRep.exists_finite_free_torsion_rep X t.G t.semi O z (p ^ n) hq

  obtain ⟨A, _, _, Y, I, m, _, _, hsep, hY, hI, hl⟩ := exists_connected_part hv hp0 P.Gt (p ^ n) hq
  have hAc : IsAdicComplete (Ideal.span {(p : A)}) A := by
    have := FlatComplete.isAdicComplete_of_finite_flat _ _ hO A
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  have hYp : (Y ≫ torsion.ι P.Gt (p ^ n)) ^ (p ^ n) = 1 := by
    rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]
  let q : ∀ k : ℕ, specO O (A ⧸ Ideal.span {(p : A) ^ k}) ⟶ P.G := fun k =>
    P.cmp _ (nilpR k) (ptMap (redR p O A k) ≫ Y ≫ torsion.ι P.Gt (p ^ n))
  have hqp : ∀ k, toOver hφ _ (q k) ^ (p ^ n) = 1 := fun k => by
    rw [← toOver_pow]
    simp only [q]
    rw [← map_pow, ← MonObj.comp_pow, hYp, MonObj.comp_one, map_one, toOver_one]
  have hfin : ∀ k, Module.Finite O (A ⧸ Ideal.span {(p : A) ^ k}) := fun k =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O (Ideal.span {(p : A) ^ k})).toLinearMap
      Ideal.Quotient.mk_surjective
  have ex : ∀ k, ∃ ψ : A₀ →ₐ[O] A ⧸ Ideal.span {(p : A) ^ k}, homAt z ψ ≫ u = toOver hφ _ (q k) := fun k => by
    haveI := hfin k
    obtain ⟨ψ, hψ, -⟩ := hrep _ (toOver hφ _ (q k)) (hqp k)
    exact ⟨ψ, hψ⟩
  choose ψ hψ using ex
  have hψc : ∀ k, (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr
      (pow_dvd_pow (p : A) (Nat.le_succ k)))).comp (ψ (k + 1)) = ψ k := fun k => by
    haveI := hfin k
    refine (hrep _ (toOver hφ _ (q k)) (hqp k)).unique ?_ (hψ k)
    rw [← homAt_comp_homAt, Category.assoc, hψ, homAt_toOver]
    congr 1
    simp only [q]
    rw [← P.cmp_nat _ _ (nilpR (k + 1)) (nilpR k), ← Category.assoc, factor_redR]
  obtain ⟨Q', hQ'⟩ := exists_lim_affine hAc (fun k => ptMap (ψ k)) fun k => by
    rw [ptMap_comp_ptMap, hψc]
  obtain ⟨L, rfl⟩ := GlobalTheory.TorsionCharacter.exists_ptMap Q'
  have hL : ∀ k, (redR p O A k).comp L = ψ k := fun k => ptMap_inj (by rw [← ptMap_comp_ptMap]; exact hQ' k)
  obtain ⟨Q, hQw⟩ := toOver_surjective hφ A (homAt z L ≫ u)
  have hQc : Corr P (Y ≫ torsion.ι P.Gt (p ^ n)) Q := fun k => toOver_injective hφ _ (by
    rw [← homAt_toOver, hQw, ← Category.assoc, homAt_comp_homAt, hL, hψ])
  have hQp : toOver hφ A Q ^ (p ^ n) = 1 := by rw [hQw, ← MonObj.comp_pow, hu, MonObj.comp_one]

  have e : (c.χ A (toOver hφ A Q) : A) = (unitOf (Y ≫ (P.weilChar s).χ n) : A) :=
    hsep _ _ fun f => hv.hom_inj (by
      have h1 : P.toG ((ptMap f ≫ Y) ≫ torsion.ι P.Gt (p ^ n)) = ptMap f ≫ Q :=
        P.hom_ext_red fun k => by
          rw [P.red_toG, Category.assoc (ptMap f)]
          exact (hQc.comp f k).symm
      have h2 := hc (toOver hφ O (ptMap f ≫ Q)) (P.toA ((ptMap f ≫ Y) ≫ torsion.ι P.Gt (p ^ n)))
        (by rw [← homAt_toOver, ← MonObj.comp_pow, hQp, MonObj.comp_one])
        (by rw [← Category.assoc, (P.eq_toA_iff _ _).1 rfl, h1, Category.assoc]; rfl)
      have h3 := c.nat A O f (toOver hφ A Q) (toOver hφ O (ptMap f ≫ Q)) hQp (by
        rw [toOver_left, toOver_left, Over.comp_left, Category.assoc]; rfl)
      rw [← h3, h2, ← unitOf_ptMap, ← Category.assoc, P.isWeilChar_weilChar])

  have hR : (p : O ⧸ Ideal.span {(p : O) ^ n}) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hn : IsNilpotent (p : DualNumber (O ⧸ Ideal.span {(p : O) ^ n})) :=
    ⟨n, by rw [← map_natCast (algebraMap (O ⧸ Ideal.span {(p : O) ^ n}) (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))), ← map_pow, hR, map_zero]⟩
  have hx1 := fst_bc (O := O) (G := P.Gt) (O ⧸ Ideal.span {(p : O) ^ n}) x
  have hpow : bc (O := O) (G := P.Gt) (O ⧸ Ideal.span {(p : O) ^ n}) x ^ (p ^ n) = 1 := by
    rw [pow_eq_scale_comp hx1, Nat.cast_pow, hR, scale_zero_comp hx1]
  obtain ⟨ψ', hψ'⟩ := hl _ (torsionLift _ hpow) (by rw [torsionLift_ι]; exact hx1)
  have hx : (ptMap ψ' ≫ Y) ≫ torsion.ι P.Gt (p ^ n) =
      ptMap (dualBC (Algebra.ofId O (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ x.1 := by
    rw [← hψ', torsionLift_ι]
    rfl
  have h5 : ptMap ψ' ≫ Q = ptMap (dualBC (Algebra.ofId O (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ (P.lieCmp x).1 := by
    rw [← GlobalTheory.CompHt.FormalChar.cmp_of_corr P hQc ψ' hn,
      ← GlobalTheory.CompHt.FormalChar.cmp_of_corr P (P.corr_lieCmp x) _ hn, ← hx, Category.assoc]
  have hgQ : g.left = spMap ψ'.toRingHom ≫ (toOver hφ A Q).left := by
    rw [hg, ← GlobalTheory.FinPartAt.ptMap_dualBC_left, ← Category.assoc, ← Over.comp_left, ← h5, Over.comp_left,
      Category.assoc]
    rfl
  rw [c.nat A _ ψ' (toOver hφ A Q) g hQp hgQ, e, ← unitOf_ptMap, ← Category.assoc,
    isAl_dlogTv (P.weilChar s) n _ hR x _ hx, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    zero_add]
  rfl

end GlobalTheory.TorsCharDlog
