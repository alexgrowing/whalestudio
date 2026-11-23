import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFielStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FibreTheta

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport GlobalTheory.ValuesPullIso GlobalTheory.LabTrans

theorem isThetaPt_of_homMk {S X : Scheme.{0}} {P : PolAV S} {k : ℕ} {h₁ h₂ : X ⟶ S} (e : h₁ = h₂) {I : Type}
    (x : I → (Over.mk h₁ ⟶ P.A)) {v : I → Γ(X, ⊤)}
    (H : IsThetaPt P k (fun i => (Over.homMk (x i).left ((Over.w (x i)).trans e) : Over.mk h₂ ⟶ P.A)) v) :
    IsThetaPt P k x v := by
  subst e
  exact H

theorem pow_homMk {S X : Scheme.{0}} {A : Over S} [GrpObj A] {h₁ h₂ : X ⟶ S} (e : h₁ = h₂) (x : Over.mk h₁ ⟶ A)
    {k : ℕ} (hx : x ^ k = 1) : (Over.homMk x.left ((Over.w x).trans e) : Over.mk h₂ ⟶ A) ^ k = 1 := by
  subst e
  exact hx

theorem theta_consts_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (n : ℕ), n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → ∀ (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → ∀ (B : PolAV (Sp (Kb W))) (b : B.A.left ⟶ A'.A.left), IsGrpPullback B.A A'.A (spMap (algebraMap (FractionRing W) (Kb W))) b → LBIso B.L (A'.L.pull b) → ∀ j : ℕ, 1 ≤ j → ∃ (C : Type) (_ : Field C) (jC : Kb W →+* C) (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R), (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ (∀ i, x i ^ ((n ^ j) ^ 2) = 1) ∧ IsThetaPt B (n ^ j) (fun i => (Over.homMk (spMap jC) (Category.comp_id _) : Over.mk (spMap jC) ⟶ baseOver (Sp (Kb W))) ≫ x i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (jC (e₀ (v i)))) := by
  intro R _ _ _ hR D n _ ho hnR W _ _ _ hW φ iφ lφ D' G' _ _ A' hD hG hU e₀ he₀ B b hb hLB j _
  obtain ⟨hD⟩ := hD
  obtain ⟨U'⟩ := hU
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  haveI := lφ
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have b₀ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hm : Odd (n ^ j) := ho.pow
  have hmR : IsUnit (((n ^ j : ℕ)) : R) := by rw [Nat.cast_pow]; exact hnR.pow j
  have hk : 1 ≤ (n ^ j) ^ 2 := pow_pos hm.pos 2
  generalize n ^ j = m at *
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := exists_complete_isAlgClosed_cExt W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((gam.comp e₀).comp (algebraMap (FractionRing R) (Kb R))).toAlgebra
  let em : Kb R →ₐ[FractionRing R] C := { toRingHom := gam.comp e₀, commutes' := fun _ => rfl }
  have cC : Compat φ C := fun r => (congrArg gam (he₀ r)).trans (hgam _)
  have hCR : CExt R (maximalIdeal R) C :=
    ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
  obtain ⟨N', ν', -⟩ := ValuesExist.exists_integral_values hL W D'.toPre D'.psi_even hB' C ⊤ fun _ => trivial
  obtain ⟨J, hJX, hJ⟩ := OneTraitTheta.exists_values_iso hL hD cC ν ν'
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause W _ b₀ D' A' G' hG U' C (m ^ 2) hk
  let f₀ := spMap (algebraMap (FractionRing W) (Kb W))
  let T : Over (Sp (Kb W)) := Over.mk (spMap gam)
  let ιC : T ⟶ baseOver (Sp (Kb W)) := Over.homMk (spMap gam) (Category.comp_id _)
  obtain ⟨e, he⟩ : ∃ e : (T ⟶ B.A) ≃* (Over.mk (T.hom ≫ f₀) ⟶ A'.A), ∀ y, (e y).left = y.left ≫ b :=
    LiePull.exists_pushEquiv hb T _ rfl
  have heq : spMap gam ≫ f₀ = jFK (R := W) C := by
    rw [← Geo.Tor.spMap_comp]
    exact congrArg spMap (RingHom.ext hgam)
  let Ix := {z : baseOver (Sp (Kb W)) ⟶ B.A // z ^ (m ^ 2) = 1}
  have tz : ∀ i : Ix, (ιC ≫ i.1) ^ (m ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, i.2, MonObj.comp_one]
  let x₀ : Ix → (Over.mk (T.hom ≫ f₀) ⟶ A'.A) := fun i => e (ιC ≫ i.1)
  have tx₀ : ∀ i, x₀ i ^ (m ^ 2) = 1 := fun i => by
    show e (ιC ≫ i.1) ^ (m ^ 2) = 1
    rw [← map_pow, tz, map_one]
  let x' : Ix → (TFK (R := W) C ⟶ A'.A) := fun i => Over.homMk (x₀ i).left ((Over.w (x₀ i)).trans heq)
  have hx' : ∀ i, x' i ^ (m ^ 2) = 1 := fun i => pow_homMk heq _ (tx₀ i)
  choose p' hp' using fun i => hf.2.1 (x' i) (hx' i)
  choose p₁ hp₁ using fun i => pullQk_surjective hD hGF cC hB hB' (k := m ^ 2) (p' i)
  have e₂ : ∀ i, (p' i).y = hD.xe.symm (p₁ i).y ∧ IsPullGtF φ hD C (p₁ i).g (p' i).g :=
    fun i => (eq_pullQk_iff hD hGF cC hB hB' _ _).1 (hp₁ i).symm
  have hQ := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre C em (m ^ 2) hk
  choose p hp using fun i => (hQ.2 (p₁ i)).exists
  have hGt := GlobalTheory.T.torus_torsion_points_correspond_values
  choose q hq using fun i => (((hGt R D.toPre D.psi_even hB C N ν).2.2.2.2 _).1 (p₁ i)).exists
  choose q' hq' using fun i => (((hGt W D'.toPre D'.psi_even hB' C N' ν').2.2.2.2 _).1 (p' i)).exists
  obtain ⟨v, hv⟩ := GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField R hR D m hm hmR Ix p
  obtain ⟨s, hs⟩ := hv C hCR em N ν p₁ q hp hq
  have e₅ : ∀ i, QkToAkU U'.toUnifPre C (m ^ 2) (p' i) (x' i) := fun i => (hf.1 _ _).2 (hp' i).symm
  have Q := GlobalTheory.T.theta_constants_eq_degeneration_series hV hGt (GlobalTheory.T.families_values_correspond hL hL₂) W _ hW rfl D' A' G' hG U' C hC N' ν' m hm _ p' q' x' e₅ hq'
  have hval : ∀ i, em (v i) = ((s * J.lam : Cˣ) : C) * N'.tx m (q' i) := fun i => by
    have e := (RelabelCoords.series_iso J hm (p := q' i) (p' := q i) (ν.eX.injective (by
      rw [hJX, (hq i).1, (hq' i).1, (e₂ i).1, AddEquiv.apply_symm_apply])) (hJ _ _ _ _ (hq i).2 (hq' i).2 (e₂ i).2)).1
    rw [e, Units.val_mul, _root_.mul_assoc, Units.mul_inv_cancel_left]
    exact hs i
  have Q₁ : IsThetaPt A' m x' (fun i => fnOf (em (v i))) :=
    GenericObject.isThetaPt_unit_mul A' m x' _ _ (fnOf ((s * J.lam : Cˣ) : C))
      ((Units.isUnit (s * J.lam)).map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      (fun i => by rw [hval i]; exact map_mul _ _ _) Q
  have Q₂ : IsThetaPt A' m x₀ (fun i => fnOf (em (v i))) := isThetaPt_of_homMk heq x₀ Q₁
  have Q₃ := (ThetaPtUp.isThetaPt_iff hb hLB (x := fun i : Ix => ιC ≫ i.1) (x₀ := x₀) (fun i => he _) tz _).2 Q₂
  exact ⟨C, inferInstance, gam, Ix, Subtype.val, v, fun z hz => ⟨⟨z, hz⟩, rfl⟩, fun i => i.2, Q₃⟩

end GlobalTheory.Mum.FibreTheta
