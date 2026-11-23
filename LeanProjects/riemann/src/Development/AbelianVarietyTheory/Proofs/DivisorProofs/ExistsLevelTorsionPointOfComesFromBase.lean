import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPartMemTautologicalPointTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUniv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivSol

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def mulPull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (n : ℕ) :
    IsPullDeg φ (mulDeg D n) (mulDeg D' n) where
  e := hD.e
  e_hom := hD.e_hom
  w := hD.w
  w_gen := hD.w_gen
  he := hD.he
  w_rig := hD.w_rig
  xe := hD.xe
  c_pr := fun (x : D'.X) => by
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    show (D'.c (n • x)).left ≫ _ = specOf φ ≫ (D.c (n • hD.xe x)).left
    rw [← hx]
    exact hD.c_pr (n • x)
  W := hD.W
  psiW := ⟨fun (χ : D.X) => hD.psiW.psi (n • χ), fun (χ : D.X) => hD.psiW.psi_gen (n • χ), fun (χ : D.X) => hD.psiW.psi_eq (n • χ)⟩
  g := hD.g
  g_comm := hD.g_comm
  psi_pr := fun (x : D'.X) => by
    have h := hD.psi_pr (n • x)
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    rw [hx] at h
    exact h

theorem mulDeg_psiEven (D : DegPre R) (n : ℕ) (h : D.PsiEven) : (mulDeg D n).PsiEven :=
  fun (a : D.X) => MulDeg.corr_even_degenerationData_negPoint D h (n • a) (n • (-a)) (neg_nsmul a n)

theorem mulDeg_tauBimult (D : DegPre R) (n : ℕ) (h : D.TauBimult) : (mulDeg D n).TauBimult :=
  fun (a a' b : D.X) => MulDeg.corr_bimultiplicative_degenerationData_sums D h (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
    (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _)

theorem mulDeg_psiUnitOn (D : DegPre R) (n : ℕ) (h : ∀ y, PsiUnitOn D y Set.univ) :
    ∀ y, PsiUnitOn (mulDeg D n) y Set.univ :=
  fun (y : D.X) => h (n • y)

end GlobalTheory.DivSol

namespace GlobalTheory.DivSol

theorem exists_qkPt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  intro E _ _ _ H D' l c L R _ _ _ _hB t P iw I _ s ε e _hbal hs hdf y
  obtain ⟨g, hD, hg, -, -⟩ := hdf
  obtain ⟨DR, hR, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg polBaseChange_holds L.W R iw L.D ⊤
    (GlobalTheory.ArcPull.nonempty_psiOn_top L.D L.gen) trivial
  have hbiR : DR.TauBimult := GlobalTheory.tauBimult_of_isPullDeg globalFns_holds _ _ iw L.D DR hR L.bimult
  have hunR : ∀ y, PsiUnitOn DR y Set.univ := GlobalTheory.PullDegTop.psiUnitOn_univ hR L.gen
  have hevR : DR.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull globalFns_holds _ _ iw L.D DR hR L.even
  have hC : IsPullDeg (RingHom.id R) (mulDeg DR l.M') (GlobalTheory.PolDeg.rescale P.D.toPre g) :=
    (GlobalTheory.Mum.isPullDeg_unique_any L.W R iw (mulDeg L.D l.M') _ _ ⟨mulPull hR l.M'⟩ ⟨hD⟩).some
  obtain ⟨T, ib, β, ββ, w, hF⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData (RingHom.id R) DR hbiR hunR l.M'
  let e' : P.D.toPre.X ≃+ (Fin T.r → ℤ) := hC.xe.trans ib
  let x : (Fin T.r → ℤ) ≃+ L.D.X := e'.symm.trans e.toAddEquiv
  have hx : ∀ a, x (e' a) = e a := fun a => by simp [x]
  let ε' : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    LinearMap.mk₂ ℤ (fun u v => ε k (x u) (H.w0 • x v) + ε k (x v) (H.w0 • x u))
      (fun m₁ m₂ n => by simp only [map_add, smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x m)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
      (fun m n₁ n₂ => by simp only [map_add, smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x n)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
  have hne : ∀ i, algebraMap R (FractionRing R) (s i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hs i)
  have hgv : ∀ y, ((g y : (FractionRing R)ˣ) : FractionRing R) =
      (∏ k, algebraMap R (FractionRing R) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg y, Units.val_inv_eq_inv_val, inv_inv]
  have hcoc : ∀ a a' : P.D.toPre.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing R)ˣ) : FractionRing R) =
      ∏ i, algebraMap R (FractionRing R) (s i) ^ ((l.M' : ℤ) * ε' i (e' a) (e' a')) := by
    intro a a'
    rw [Units.val_mul, Units.val_mul, hg (a + a'), hgv a, hgv a', ← Finset.prod_inv_distrib,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i)]
    congr 1
    simp only [ε', LinearMap.mk₂_apply, hx, map_add, smul_add, LinearMap.add_apply]
    ring
  obtain ⟨β', ββ', w', hF'⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg DR l.M') (mulDeg_psiEven _ _ hevR)
    (mulDeg_tauBimult _ _ hbiR) (mulDeg_psiUnitOn _ _ hunR) ib β ββ w hF R (RingHom.id R) Function.injective_id
    P.D.toPre g hC s ε' e' (fun _ => rfl) hcoc
  obtain ⟨p, hp, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε' l.M' R P.D.toPre (RingHom.id R) s e' β' ββ' w'
    P.D.tau_bimult hF' hs (FractionRing R) (e' y)
  exact ⟨p, by rw [hp]; simp⟩

end GlobalTheory.DivSol
