import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FamInt

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

open Classical in

def ordFn (hϖ : Irreducible ϖ) (c : FractionRing V) : WithTop ℚ :=
  if h : c = 0 then ⊤ else (((hasVal_of_ne_zero hϖ h).choose : ℚ) : WithTop ℚ)

theorem ordFn_of_hasVal (hϖ : Irreducible ϖ) {c : FractionRing V} {n : ℤ} (h : HasVal ϖ c n) :
    ordFn hϖ c = ((n : ℚ) : WithTop ℚ) := by
  have h0 := ne_zero_of_hasVal hϖ h
  rw [ordFn, dif_neg h0, hasVal_unique hϖ (hasVal_of_ne_zero hϖ h0).choose_spec h]

theorem ordFn_zero (hϖ : Irreducible ϖ) : ordFn hϖ 0 = ⊤ := by rw [ordFn, dif_pos rfl]

theorem le_ordFn_iff (hϖ : Irreducible ϖ) (c : FractionRing V) (n : ℤ) :
    ((n : ℚ) : WithTop ℚ) ≤ ordFn hϖ c ↔
      ∃ b : V, c = algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) b := by
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  constructor
  · intro h
    by_cases hc : c = 0
    · exact ⟨0, by simp [hc]⟩
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    rw [ordFn_of_hasVal hϖ hm] at h
    have hnm : n ≤ m := by exact_mod_cast h
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, m = n + d := ⟨(m - n).toNat, by omega⟩
    obtain ⟨u, hu⟩ := hm
    exact ⟨ϖ ^ d * u, by rw [hu, zpow_add₀ hπ, zpow_natCast, map_mul, map_pow, _root_.mul_assoc]⟩
  · rintro ⟨b, rfl⟩
    by_cases hb : b = 0
    · rw [hb, map_zero, mul_zero, ordFn_zero]; exact le_top
    obtain ⟨d, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    rw [ordFn_of_hasVal hϖ (n := n + d) ⟨u, by rw [zpow_add₀ hπ, zpow_natCast, map_mul, map_pow]; ring⟩]
    exact_mod_cast (by omega : n ≤ n + d)

def ordVal (hϖ : Irreducible ϖ) : AddValuation (FractionRing V) (WithTop ℚ) :=
  AddValuation.of (ordFn hϖ) (ordFn_zero hϖ)
    (by rw [ordFn_of_hasVal hϖ (n := 0) ⟨1, by simp⟩]; simp)
    (fun x y => by
      by_cases hx : x = 0
      · rw [hx, zero_add]; exact min_le_right _ _
      by_cases hy : y = 0
      · rw [hy, add_zero]; exact min_le_left _ _
      obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
      obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hy
      obtain ⟨a, ha⟩ := (le_ordFn_iff hϖ x (min n m)).1
        (by rw [ordFn_of_hasVal hϖ hn]; exact_mod_cast min_le_left n m)
      obtain ⟨b, hb⟩ := (le_ordFn_iff hϖ y (min n m)).1
        (by rw [ordFn_of_hasVal hϖ hm]; exact_mod_cast min_le_right n m)
      refine le_trans ?_ ((le_ordFn_iff hϖ (x + y) (min n m)).2 ⟨a + b, by rw [map_add, mul_add, ← ha, ← hb]⟩)
      rw [ordFn_of_hasVal hϖ hn, ordFn_of_hasVal hϖ hm]
      exact_mod_cast le_rfl)
    (fun x y => by
      have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
      by_cases hx : x = 0
      · rw [hx, MulZeroClass.zero_mul, ordFn_zero, top_add]
      by_cases hy : y = 0
      · rw [hy, mul_zero, ordFn_zero, add_top]
      obtain ⟨n, u, hn⟩ := hasVal_of_ne_zero hϖ hx
      obtain ⟨m, w, hm⟩ := hasVal_of_ne_zero hϖ hy
      rw [ordFn_of_hasVal hϖ ⟨u, hn⟩, ordFn_of_hasVal hϖ ⟨w, hm⟩, ordFn_of_hasVal hϖ (n := n + m)
        ⟨u * w, by rw [hn, hm, zpow_add₀ hπ, Units.val_mul, map_mul]; ring⟩]
      push_cast; rfl)

theorem valOver_ordVal (hϖ : Irreducible ϖ) : ValOver ϖ (FractionRing V) (ordVal hϖ) :=
  fun _ _ h => ordFn_of_hasVal hϖ h

theorem exists_eq_of_pos (hϖ : Irreducible ϖ) {c : FractionRing V} (h : 0 < ordVal hϖ c) :
    ∃ b : V, c = algebraMap V (FractionRing V) (ϖ * b) := by
  have h1 : (((1 : ℤ) : ℚ) : WithTop ℚ) ≤ ordFn hϖ c := by
    by_cases hc : c = 0
    · rw [hc, ordFn_zero]; exact le_top
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    change 0 < ordFn hϖ c at h
    rw [ordFn_of_hasVal hϖ hm] at h ⊢
    have : (0 : ℤ) < m := by exact_mod_cast h
    exact_mod_cast (by omega : (1 : ℤ) ≤ m)
  obtain ⟨b, hb⟩ := (le_ordFn_iff hϖ c 1).1 h1
  exact ⟨b, by rw [hb, zpow_one, map_mul]⟩

def secLin {X : Scheme.{0}} {L : LB X} {n : ℕ} (c : Fin n → Γ(X, ⊤)) (t : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (c i) * (t i).f j
  compat := fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (c i) (t i)).compat j j'

variable {D : DegData V (maximalIdeal V)}

theorem exists_pull {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ} {α : D.toPre.X}
    (β : D.toPre.SecB k α) :
    ∃ s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k)),
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) β (DegPre.prB D.toPre F).left 1 := by
  have hL := D.toPre.P.isLB
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α i) (DegPre.famε k)
      (DegPre.famφ D.toPre F α) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ β (DegPre.prB D.toPre F).left)
  exact ⟨t, SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
    ((ht _ _ y J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ)).symm⟩

theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 < r) (hs : VGe D (FractionRing V) (ordVal hϖ) k α s r) :
    ∃ f f' : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      SecIsMul D.toPre.P.A.hom ϖ f f' := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  choose b hb using fun i => exists_eq_of_pos hϖ (lt_of_lt_of_le (by exact_mod_cast hr) (hva i))
  refine ⟨secLin (fun i => scal D.toPre.P.A.hom (ϖ * b i)) σ, secLin (fun i => scal D.toPre.P.A.hom (b i)) σ,
    SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun j => ?_⟩
  · rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (ϖ * b i)) σ (fun _ => rfl) _ y hJ,
      SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
    refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
    have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (ϖ * b i)) =
        cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (ϖ * b i) :=
      gs_pull _ _ y ⊤ trivial _
    have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
        cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
      gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
    have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
        ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
          spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
      rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
      exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
    rw [e1, e2, e3, cst_comp, cst_comp, hb i]
    rfl
  · show ∑ i, resTop _ (scal D.toPre.P.A.hom (ϖ * b i)) * (σ i).f j =
      resTop _ (scal D.toPre.P.A.hom ϖ) * ∑ i, resTop _ (scal D.toPre.P.A.hom (b i)) * (σ i).f j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [scal, resTop, map_mul, _root_.mul_assoc]

end FamInt

theorem integralFamily_of_strictMin : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (q : ℕ), 1 ≤ q → ∀ (χ : D.toPre.X) (β : D.toPre.SecB q χ), (∀ z, z ≠ 0 → Q χ < Q (χ + q • z)) → ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) ∧ f χ = β ∧ (∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0) ∧ ∀ α, α ≠ χ → ∃ f' : D.toPre.SecB q α, SecIsMul D.toPre.P.A.hom ϖ (f α) f' := by
  intro hL V _ _ _ ϖ hϖ D Q hQ q hq χ β hmin
  classical
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing V) hL.globalFns D.tau_bimult q χ (fun a b h => by
    have h' : (q : ℤ) • a = (q : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : (q : ℤ) ≠ 0) h') σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) ∧
      (α ≠ χ → ∃ f' : D.toPre.SecB q α, SecIsMul D.toPre.P.A.hom ϖ f f') := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0), fun h => absurd rfl h⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have hz : z ≠ 0 := by rintro rfl; exact hα (by simp)
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hlt := hmin z hz
      rw [q_shift hϖ hQ, lt_add_iff_pos_right] at hlt
      have hpos : (0 : ℤ) < q * Q z + QForm.bOf D.toPre Q z χ := (pos_iff_pos_of_mul_pos hlt).1 (by omega)
      obtain ⟨f, f', h1, h2⟩ := FamInt.exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z), fun _ => ⟨f', h2⟩⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl, fun _ => ⟨SecOps.secZero, fun j => (mul_zero _).symm⟩⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 h4 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3, h4⟩

end GlobalTheory
