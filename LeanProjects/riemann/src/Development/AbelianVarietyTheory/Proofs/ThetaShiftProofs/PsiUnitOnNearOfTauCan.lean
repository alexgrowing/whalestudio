import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation

noncomputable section

namespace GlobalTheory.ArcCM

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.UnramTorsion GlobalTheory.BXOf GlobalTheory.TauTwist

theorem mem_range_units_of_pow {W K : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [Field K] [Algebra W K]
    [IsFractionRing W K] {m : ℕ} (hm : 0 < m) {x : Kˣ}
    (h : x ^ m ∈ (Units.map (algebraMap W K).toMonoidHom).range) : x ∈ (Units.map (algebraMap W K).toMonoidHom).range := by
  obtain ⟨u, hu⟩ := h
  have hu' : (x : K) ^ m = algebraMap W K u := (congrArg Units.val hu).symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := W) (K := K) (x := (x : K)) hm
    (hu' ▸ isIntegral_algebraMap)
  have e : y ^ m = u := IsFractionRing.injective W K (by rw [map_pow, hy, hu'])
  have hyu : IsUnit y := (isUnit_pow_iff hm.ne').1 (e ▸ u.isUnit)
  exact ⟨hyu.unit, Units.ext hy⟩

variable {R : Type} [CommRing R] [IsDomain R]

theorem psiUnitOn_near_of_tauCan [IsIntegrallyClosed R] (D : DegPre R) {n : ℕ} (hn : 0 < n) (hE : D.PsiEven)
    (hB : D.TauBimult) (hT : TauCan D n) (y : D.X) (P : PrimeSpectrum R) :
    ∃ V : (Sp R).Opens, P ∈ V ∧ PsiUnitOn D y V := by
  obtain ⟨hc, hκ⟩ := hT
  choose J₀ h₀ using fun x : D.P.A.left => exists_chart D.P.isLB x
  let W := Localization.AtPrime P.asIdeal
  have : IsFractionRing W (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl _ _
  have : IsIntegrallyClosed W :=
    isIntegrallyClosed_of_isLocalization W P.asIdeal.primeCompl P.asIdeal.primeCompl_le_nonZeroDivisors
  let i : W →+* FractionRing R := algebraMap W (FractionRing R)
  let φ : R →+* W := algebraMap R W
  have sq : spMap i ≫ spMap φ = jK R := by
    rw [← spMap_comp]
    exact congrArg spMap (IsScalarTower.algebraMap_eq R W (FractionRing R)).symm
  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good_ext D.P.isLB i (IsFractionRing.injective W (FractionRing R)) J₀ h₀
  let z : (TK R).left := closedPoint (FractionRing R)
  have hJ : Good D.P.L z J := hJ
  let H : Subgroup (FractionRing R)ˣ := (Units.map (algebraMap W (FractionRing R)).toMonoidHom).range
  obtain ⟨w, hw⟩ : ∃ w : ((TK R).left.presheaf.stalk z)ˣ →* (FractionRing R)ˣ ⧸ H,
      ∀ u, w u = 1 ↔ sig (FractionRing R) u ∈ H :=
    ⟨(QuotientGroup.mk' H).comp (sig (FractionRing R)), fun _ => QuotientGroup.eq_one_iff _⟩
  have tf : ∀ (m : ℕ) u, 0 < m → w u ^ m = 1 → w u = 1 := fun m u hm e => by
    rw [← map_pow, hw] at e
    exact (hw u).2 (mem_range_units_of_pow hm ((map_pow (sig (FractionRing R)) u m) ▸ e))
  have hint : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (ψ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L ψ ε)) (r : Sp R ⟶ Y) (q : (TK R).left ⟶ Y), q = jK R ≫ r → w (val t q z J) = 1 := by
    intro Y K _ ψ ε t r q hq
    obtain ⟨u, hu⟩ := val_integral i h₀ eJ t (spMap φ ≫ r)
    have : q = spMap i ≫ spMap φ ≫ r := by rw [hq, ← Category.assoc, sq]
    subst this
    exact (hw _).2 ⟨u, Units.ext hu.symm⟩
  let p : D.X → (FractionRing R)ˣ ⧸ H := fun a => w (val (D.psi a) (𝟙 (TK R).left) z J)
  have hadd : ∀ a b, p (a + b) = p a * p b := fun a b => by
    have e₁ : val (D.tau a b) (𝟙 (TK R).left) z J ^ n ^ 2 =
        val (D.tau (n • a) (n • b)) (𝟙 (TK R).left) z J * val (canK hc a b) (𝟙 (TK R).left) z J :=
      val_tau_pow hc hB a b (𝟙 (TK R)) hJ
    rw [← unitAt_kappa hc a b hJ, hκ, map_one, _root_.one_mul] at e₁
    have e₂ : w (val (canK hc a b) (𝟙 (TK R).left) z J) = 1 :=
      (congrArg w (val_pull hJ _ _ _)).trans (hint _ _ _ _ _ (𝟙 _) _ ((Category.id_comp _).trans (Category.comp_id _).symm))
    have e₃ : w (val D.rigK (𝟙 (TK R).left) z J) = 1 :=
      (congrArg w (val_pull hJ _ _ _)).trans (hint _ _ _ _ _ (𝟙 _) _ ((Category.id_comp _).trans (Category.comp_id _).symm))
    have e₄ := tf _ _ (pow_pos hn 2) ((map_pow w _ _).symm.trans ((congrArg w e₁).trans e₂))
    rw [val_tau D a b _ hJ, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, e₃, inv_one, _root_.mul_one,
      mul_inv_eq_one, mul_inv_eq_iff_eq_mul, mul_comm] at e₄
    exact e₄
  have heven : p (-y) = p y := by
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
      (val_corr hJ (hE y) (𝟙 (TK R).left))
    have r := hint _ _ _ _ D.sym (D.c y).left (𝟙 (TK R).left ≫ D.xK y) (Category.id_comp _)
    exact ((congrArg w e).symm.trans ((map_mul _ _ _).trans ((congrArg (_ * ·) r).trans (_root_.mul_one _)))).symm
  have p0 : p 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have py : p y = 1 := tf 2 _ two_pos (by
    have := hadd y (-y)
    rw [add_neg_cancel, p0, heven] at this
    exact (pow_two _).trans this.symm)
  have hcp : spMap φ (closedPoint W) = P := PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := P.asIdeal))
  have hj : J (𝟙 (TK R).left ≫ D.xK y) = J₀ ((D.c y).left P) := by
    have h : 𝟙 (TK R).left ≫ D.xK y = spMap i ≫ spMap φ ≫ (show Sp R ⟶ D.P.A.left from (D.c y).left) := by
      rw [← Category.assoc, sq]; exact Category.id_comp _
    exact (congrArg J h).trans ((eJ _).trans (congrArg (fun q => J₀ ((D.c y).left q)) hcp))
  obtain ⟨u, hu⟩ := (hw _).1 py
  rw [val_of (D.psi y) _ z J (fun _ => J₀ ((D.c y).left P)) fun _ => hj] at hu
  have e : (psiLoc D y (J₀ ((D.c y).left P)) : FractionRing R) = algebraMap W (FractionRing R) u :=
    (congrArg Units.val hu).symm
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.asIdeal.primeCompl (u : W)
  refine psiUnitOn_near y P _ (h₀ _) r s ?_ s.2 ?_
  · exact (IsLocalization.AtPrime.isUnit_to_map_iff W P.asIdeal r).1 (hrs ▸ u.isUnit.mul (IsLocalization.map_units _ s))
  · rw [e, IsScalarTower.algebraMap_apply R W (FractionRing R),
      IsScalarTower.algebraMap_apply R W (FractionRing R) r, ← map_mul]
    exact congrArg _ hrs

theorem psiUnitOn_of_tauCan : Known → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (D₀ : Out.DegPre R) (n : ℕ), 0 < n → D₀.PsiEven → D₀.TauBimult → TauCan D₀ n → ∀ y, PsiUnitOn D₀ y Set.univ :=
  fun _ _ _ _ _ _ D₀ _ hn hE hB hT y =>
    GlobalTheory.PsiAbelian.psiUnitOn_of_height_one D₀ y _ fun P _ _ => psiUnitOn_near_of_tauCan D₀ hn hE hB hT y P

end GlobalTheory.ArcCM
