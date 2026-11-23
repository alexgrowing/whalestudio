import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.PsiForm

open ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V]

theorem hasVal_valF {ϖ : V} [IsDiscreteValuationRing V] {X : Scheme.{0}} (L : LB X)
    (x : Spec (CommRingCat.of V) ⟶ X) (x' : Spec (CommRingCat.of (FractionRing V)) ⟶ X) (hx : x' = jK V ≫ x)
    (ε : ℤ) (t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε))) {n : ℤ}
    (hn : GenHasVal ϖ L (fun _ => x) (fun _ => x') (fun _ => hx) (fun _ => ε) t n)
    (j : PUnit → L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    HasVal ϖ (valF (𝟙 (Sp (FractionRing V))) _ (t.s j).val) n := by
  subst hx
  have htop : LB.wchart L (fun _ : PUnit => x) j = ⊤ :=
    eq_top_iff.2 fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤ LB.wchart L (fun _ : PUnit => jK V ≫ x) j :=
    fun y _ => by
      have hy : (jK V).base y ∈ LB.wchart L (fun _ : PUnit => x) j := by rw [htop]; trivial
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  obtain ⟨c, hc, eV, hce⟩ := genHasVal_top L (fun _ : PUnit => x) (fun _ => ε) t hn j htop hK
  have e : valF (𝟙 (Sp (FractionRing V))) _ (t.s j).val = c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hce]
    exact (dif_pos hK).trans rfl
  rw [e]
  exact hasVal_mul_unit hc eV

variable {F : Type} [NormedField F] [Algebra (FractionRing V) F]
  (hle : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))

omit [IsDomain V] in
include hle in
theorem norm_unit (w : Vˣ) : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
  have h1 := (hle _).2 ⟨(w : V), rfl⟩
  have h2 := (hle _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
  have h3 : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V))‖ *
      ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_pos_of_irreducible {ϖ : V} (hϖ : Irreducible ϖ) :
    0 < ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ :=
  norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero))

include hle in
theorem norm_lt_one_of_irreducible {ϖ : V} (hϖ : Irreducible ϖ) :
    ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ < 1 := by
  by_contra h
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  obtain ⟨w, hw⟩ := (hle (algebraMap V (FractionRing V) ϖ)⁻¹).1 (by
    rw [map_inv₀, norm_inv]
    exact inv_le_one_of_one_le₀ (not_lt.1 h))
  refine hϖ.not_isUnit (IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_))
  rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]

include hle in
theorem norm_of_hasVal {ϖ : V} (hϖ : Irreducible ϖ) {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) :
    ‖algebraMap (FractionRing V) F c‖ =
      Real.exp (-(-Real.log ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ * n)) := by
  obtain ⟨w, rfl⟩ := hc
  rw [map_mul, norm_mul, norm_unit hle, _root_.mul_one, map_zpow₀, norm_zpow, neg_mul, neg_neg,
    ← Real.rpow_def_of_pos (norm_pos_of_irreducible hϖ), Real.rpow_intCast]

theorem tendsto_val [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) :
    Filter.Tendsto Q Filter.cofinite Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => Filter.eventually_cofinite.2 ((D.psi_tendsto b.toNat).subset fun χ hχ hin => hχ ?_)
  exact (Int.self_le_toNat b).trans (genHasVal_ge_of_in hϖ D.toPre.P.L D.toPre.P.isLB (D.toPre.c χ).left (D.toPre.xK χ)
    (QForm.ptK_eq D.toPre χ) (-1) (D.toPre.psi χ) b.toNat hin (hQ χ))

theorem exists_quadraticMap [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) (a : ℝ) :
    ∃ q : QuadraticMap ℤ D.toPre.X ℝ, ∀ χ, q χ = a * Q χ := by
  have h0 := QForm.Q_zero hϖ D hQ
  have hd : HasConstSecondDiff fun χ => a * (Q χ : ℝ) := by
    refine (hasConstSecondDiff_iff _).2 fun b m ν => ?_
    have h := QForm.bOf_add_left hϖ D hQ b m ν
    simp only [QForm.bOf] at h
    have h' : Q (b + m + ν) - Q (b + m) - Q (b + ν) + Q b = Q (m + ν) - Q m - Q ν + Q 0 := by rw [h0]; linarith
    have h'' := congrArg (fun z : ℤ => a * (z : ℝ)) h'
    push_cast at h''
    linarith
  refine ⟨hd.quadraticMap fun χ => by rw [QForm.Q_neg hϖ D hQ], fun χ => ?_⟩
  simp [h0]

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ q : QuadraticMap ℤ u.D.toPre.X ℝ, Filter.Tendsto q Filter.cofinite Filter.atTop ∧ ∀ χ, u.PsiNorm χ (Real.exp (-q χ)) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using QForm.exists_QVal hϖ u.D
  obtain ⟨q, hq⟩ := exists_quadraticMap hϖ u.D hQ
    (-Real.log ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖)
  refine ⟨q, ?_, fun χ j hj => ?_⟩
  · refine Filter.Tendsto.congr (fun χ => (hq χ).symm) (Filter.Tendsto.const_mul_atTop ?_ ?_)
    · exact neg_pos.2 (Real.log_neg (norm_pos_of_irreducible hϖ) (norm_lt_one_of_irreducible u.norm_le hϖ))
    · exact tendsto_intCast_atTop_atTop.comp (tendsto_val hϖ u.D hQ)
  · rw [hq]
    exact norm_of_hasVal u.norm_le hϖ (hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) j hj)

end GlobalTheory.ZH.PsiForm
