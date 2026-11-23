import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationDataOfSemiAbelianSymmetry
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperUniformisedSemiAbelianOverOpenInAbLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEvenUnimodularCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerSemiAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SplitPowEight

def isPowGrpOfUnique {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (pr : Fin j → (G' ⟶ G))
    (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin j → (T ⟶ G)), ∃! x : T ⟶ G', ∀ u, x ≫ pr u = y u) : IsPowGrp G' G j :=
  ⟨pr, hpr, Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose) (fun s u => (hu s.pt s.proj).choose_spec.1 u)
    fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm⟩

def powPullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) : IsPowGrp ((Over.pullback f).obj G') ((Over.pullback f).obj G) j :=
  ⟨fun u => (Over.pullback f).map (p.pr u), fun u => by have := p.hom u; infer_instance,
    isLimitFanMkObjOfIsLimit (Over.pullback f) _ _ p.lim⟩

theorem exists_unif_pow8 : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  intro V _ _ _ hV A G _ _ hG ψ hψ
  obtain ⟨hd, hc, hch⟩ := hV
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hψ
  obtain ⟨G8, _, prG, hG8, hprG, huG⟩ := GlobalTheory.MBLow.exists_eighthPower_semiAbelianScheme V G hG
  have : IsCommMonObj G8 := hG8.comm
  let p8 : IsPowGrp G8 G 8 := isPowGrpOfUnique prG hprG huG
  let F := AlgebraicClosure (FractionRing V)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 (by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  obtain ⟨W, hWd, hWc, hWf, hsplit⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G8 hG8
  have : CharZero F := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective V F)
  have : CharZero W := RingHom.charZero (algebraMap W F)
  have hio : Function.Injective (algebraMap V W) := fun a b h =>
    FaithfulSMul.algebraMap_injective V F (congrArg Subtype.val h)
  let io : V →+* W := algebraMap V W
  let H := (Over.pullback (spMap io)).obj G8
  let pH : IsPowGrp H ((Over.pullback (spMap io)).obj G) 8 := powPullback (spMap io) p8
  have hH : IsSemiAbelian H := IsSemiAbelian.pullback _ G8 hG8
  obtain ⟨A', ψ', hψ'⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback V A G gen hgen W io hio
  obtain ⟨d, -, hQ⟩ := GlobalTheory.MBLow.PowEightField.exists_eighthPower_evenUnimodular_charZero
  obtain ⟨Q, pr, inc, -, hS, hP⟩ := hQ (FractionRing W) A'
  let pQ : IsPowGrp Q.A A'.A 8 := isPowGrpOfUnique pr hP.1 hP.2.2.1
  obtain ⟨φ₀, hφ₀, -⟩ := GlobalTheory.PowFibre.exists_pow_pullback pH pQ hψ'
  obtain ⟨genH, hgenH, -⟩ := grpPullback_iso (isGrpPullback_pullback H (jK W)) hφ₀
  obtain ⟨L₁, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hE : ∃ E : SplitExt (Sp (ResidueField W)), E.IsGt ((Over.pullback (spMap (residue W))).obj H) := hsplit
  obtain ⟨s, -⟩ := GlobalTheory.ZH.exists_setting_of_hypS L₁ GlobalTheory.homExtension_semiAbelian_dvr_unconditional W hWc Q H hH hE
    hS genH hgenH
  obtain ⟨D, U, -, -, hU⟩ := GlobalTheory.uniformisation_dvr_unconditional W Q H s
  obtain ⟨i₀, hi₀, -⟩ := huG G (fun _ => 𝟙 G)
  refine ⟨W, inferInstance, inferInstance, inferInstance, io, algebraMap W F, D, Q, H, inferInstance, inferInstance, U,
    (Over.pullback (spMap io)).map i₀, pH.pr, ⟨hWd, hWc, inferInstance⟩, RingHom.finite_algebraMap.2 hWf, hio,
    Subtype.val_injective, fun v => ?_, hH, hU, pH.hom, ?_, fun T x y h => Fan.IsLimit.hom_ext pH.lim _ _ h⟩
  · exact IsScalarTower.algebraMap_apply V (FractionRing V) F v
  · show (Over.pullback (spMap io)).map i₀ ≫ (Over.pullback (spMap io)).map (prG 0) = _
    rw [← CategoryTheory.Functor.map_comp, hi₀ 0, CategoryTheory.Functor.map_id]

end GlobalTheory.SplitPowEight
