import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValForm

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem hasVal_coord {D : DegPre V} {χ : D.X} {n : ℤ} {r : V} (hn : QForm.QVal D ϖ χ n) (hr : PsiCoord D χ r) :
    HasVal ϖ (algebraMap V (FractionRing V) r) n := by
  obtain ⟨j, hj, h, e⟩ := hr
  have htop : LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) j = ⊤ :=
    eq_top_of_closedPoint_mem _ (Set.mem_iInter.2 fun _ => hj trivial)
  obtain ⟨c, hc, eV, hce⟩ := genHasVal_top D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => -1) (D.psi χ) hn j htop h
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) (DegPre.toOpen (R := V) ⊤ r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hnat
  have hid : (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (DegPre.toOpen ⊤ r) = r := by
    simp only [DegPre.toOpen, RingHom.coe_comp, Function.comp_apply]
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    simp
  have hval : algebraMap V (FractionRing V) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (DegPre.toOpen ⊤ r)) =
      c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hce]
    erw [← hnat]
    rw [CommRingCat.comp_apply]
    exact congrArg _ e
  rw [hid] at hval
  rw [hval]
  exact hasVal_mul_unit hc eV

omit [IsDiscreteValuationRing V] in
theorem hasVal_mul (hϖ : Irreducible ϖ) {a b : V} {n m : ℤ} (ha : HasVal ϖ (algebraMap V (FractionRing V) a) n)
    (hb : HasVal ϖ (algebraMap V (FractionRing V) b) m) :
    HasVal ϖ (algebraMap V (FractionRing V) (a * b)) (n + m) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  refine ⟨u * v, ?_⟩
  rw [map_mul, hu, hv, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero),
    Units.val_mul, map_mul]
  ring

omit [IsDiscreteValuationRing V] in
theorem logb_of_hasVal {a : V} {n : ℤ} (hn : 0 ≤ n) (ha : HasVal ϖ (algebraMap V (FractionRing V) a) n)
    {C : Type} [NormedField C] (f : V →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (p : ℝ) :
    Real.logb p ‖f a‖ = n * Real.logb p ‖f ϖ‖ := by
  obtain ⟨u, hu⟩ := ha
  lift n to ℕ using hn
  rw [zpow_natCast, ← map_pow, ← map_mul] at hu
  rw [IsFractionRing.injective V (FractionRing V) hu, map_mul, norm_mul, GlobalTheory.PeriodBalance.norm_unit f hf u,
    _root_.mul_one, map_pow, norm_pow, Real.logb_pow, Int.cast_natCast]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (Q : P.D.toPre.X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), QForm.IsQ P.D.toPre ϖ Q ∧ (∀ a, 0 ≤ Q a) ∧ (∀ a b, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = QForm.bOf P.D.toPre Q a b) ∧ (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧ ∀ (C : Type) [NormedField C] (f : V →+* C) (p : ℕ), Function.Injective f → (∀ a, ‖f a‖ ≤ 1) → ∀ a b, betaAt P.D.toPre f p a b = -Real.logb p ‖f ϖ‖ * (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b := by
  intro E _ _ _ H V _ _ _ _ _ G P ϖ hϖ cj hcj
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main V P.D inferInstance χ).1).imp fun _ h => h.1
  have hv : ∀ χ, HasVal ϖ (algebraMap V (FractionRing V) (hex χ).choose) (Q χ) := fun χ =>
    hasVal_coord (hQ χ) (hex χ).choose_spec
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  have hbal : ∀ (x : 𝓞 E) a b, QForm.bOf P.D.toPre Q (x • a) b = QForm.bOf P.D.toPre Q a (H.bar x • b) := by
    intro x a b
    obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance P.D.toPre P.oD x a b (hex (x • a + b)).choose_spec
      (hex (x • a)).choose_spec (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec
      (hex (H.bar x • b)).choose_spec
    have h1 := hasVal_mul_unit (hasVal_mul hϖ (hasVal_mul hϖ (hv (x • a + b)) (hv a)) (hv (H.bar x • b))) u
    have h2 := hasVal_mul hϖ (hasVal_mul hϖ (hv (a + H.bar x • b)) (hv (x • a))) (hv b)
    rw [← map_mul, _root_.mul_comm, hu] at h1
    have := hasVal_unique hϖ h1 h2
    simp only [QForm.bOf]
    linarith
  let β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ :=
    LinearMap.mk₂ ℤ (fun a b => (QForm.bHom hϖ P.D hQ' a b : ℝ))
      (fun a a' b => by simp only [map_add, AddMonoidHom.add_apply, Int.cast_add])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, Int.cast_id])
      (fun a b b' => by simp only [map_add, Int.cast_add])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, Int.cast_id])
  have hβ : ∀ a b, β a b = (QForm.bOf P.D.toPre Q a b : ℝ) := fun _ _ => rfl
  refine ⟨Q, ⟨β, fun a b => ?_, fun c c' hc a b => ?_⟩, hQ', h0, hβ, fun a => ?_, fun C _ f p _ hf a b => ?_⟩
  · rw [hβ, hβ, QForm.bOf_comm]
  · obtain rfl : c' = H.bar c := RingOfIntegers.ext (by rw [hc, hcj, H.bar_eq])
    rw [hβ, hβ, hbal]
  · show β a a = _
    rw [hβ, ← QForm.two_Q_eq hϖ P.D hQ']
    push_cast
    rfl
  · have hp : ∀ χ, vPsiAt P.D.toPre f p χ = -(Q χ * Real.logb p ‖f ϖ‖) := fun χ =>
      (dif_pos (hex χ)).trans (by rw [logb_of_hasVal (h0 χ) (hv χ) f hf])
    show _ = _ * β a b
    rw [hβ]
    simp only [betaAt, hp, QForm.bOf]
    push_cast
    ring

end GlobalTheory.ValForm
