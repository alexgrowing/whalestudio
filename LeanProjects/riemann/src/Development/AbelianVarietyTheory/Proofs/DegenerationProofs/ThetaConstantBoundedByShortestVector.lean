import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibreStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.TestVal

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem odd_level (ρ : S.Real) : Odd (S.r * S.N) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow

theorem powFrame_one {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) :
    powFrame A L x τ 1 = τ :=
  congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))

theorem mk_add_smul {X : Type} [AddCommGroup X] (m : ℕ) (χ y : X) :
    (QuotientAddGroup.mk y : X ⧸ (nsmulAddMonoidHom m : X →+ X).range) = QuotientAddGroup.mk (m • χ + y) :=
  QuotientAddGroup.eq.2 ⟨χ, by simp⟩

attribute [local instance] gtGroup in

theorem exists_scale (hL : Laws) (hL₂ : Laws2) {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}
    (u : ρ.UTest p y₀) (l : u.Lab) (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) :
    ∃ sc : ℝ, 0 ≤ sc ∧
      (∀ a, ∃ w : u.D.toPre.X, l.yy a = QuotientAddGroup.mk w ∧
        ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ sc * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) ∧
      (∀ a, sc ≠ 0 → ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = sc → a ∈ l.yy.ker) ∧
      ∀ n : ℕ, 2 ≤ n → n ∣ S.r * S.N → ∀ a ∈ l.yy.ker, ∃ a' ∈ l.yy.ker, n • (a' - a) = 0 ∧
        ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ = sc := by
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have := charZero u
  have hm := odd_level ρ
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨ϖ, hϖ, Q, hQ, v, hv, lam, hlam, v₁, v₂, hq⟩ := exists_val u
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.T.uniformised_model_labelled_torsion_points o Ω S ρ p y₀ u
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.T.exists_frames_on_uniformisedModel_fibre o Ω S ρ p y₀ u x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW u.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ _ v hv u.A u.G
    u.semi u.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ _ v hv u.A u.G u.semi u.U w₀ rig hw₀ th ϑ hE hP
    _ hm (isUnit_level u h)
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv).2 r
  have tv : ∀ a z J, Good u.A.L z J → cst (R := u.V) (PadicAlgCl p) z sc *
      @id ((TF (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (sA th (ptSecT u.A.A (x a)).left z J) =
      cst (R := u.V) (PadicAlgCl p) z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z)
        (val (powFrame u.A.A u.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x a) ∧ l.yy a = QuotientAddGroup.mk q.y :=
    fun a => by
      obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
      exact ⟨q, (f₁ _ _).2 hq.symm, l.yy_eq a q _ ((f₁ _ _).2 hq.symm) (hx a)⟩
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨S.th a, S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := u.V) (F := PadicAlgCl p)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := u.V) (PadicAlgCl p)).left) u.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := u.V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    refine ⟨0, le_rfl, fun a => ?_, fun a hne => absurd rfl hne, fun n _ _ a ha => ⟨a, ha, by simp, by simp [z0]⟩⟩
    obtain ⟨q, -, hq⟩ := ex a
    exact ⟨q.y, hq, by simp [z0]⟩
  have hsc : 0 < ‖sc‖ := norm_pos_iff.2 h0
  have tv' : ∀ a z J, Good u.A.L z J → sA th (ptSecT u.A.A (x a)).left z J =
      @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z)
        (cst (R := u.V) (PadicAlgCl p) z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame u.A.A u.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := u.V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = ‖sc‖ := fun a => by
    refine (v₁ _ 0).trans ?_
    rw [norm_mul, norm_inv, Rat.cast_zero, mul_zero, neg_zero, Real.exp_zero, inv_mul_eq_one₀ hsc.ne', eq_comm]
  refine ⟨‖sc‖, hsc.le, fun a => ?_, fun a _ ha => ?_, fun n hn hnm a ha => ?_⟩
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((S.r * S.N) • χ + q.y) = k)
      ⟨0, by
        rintro _ ⟨χ, rfl⟩
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ u.D hQ]
        · exact zero_le_one.trans (QForm.Q_pos hϖ u.D hQ c)⟩ ⟨_, 0, rfl⟩
    refine ⟨_, hq₂.trans (mk_add_smul _ χ _), ?_⟩
    have b := (v₂ _ _).1 (((key q _ hq₁).1 _ _ (he a) (tv' a)).1
      ((Q ((S.r * S.N) • χ + q.y) : ℚ) / ((S.r * S.N) ^ 2 : ℕ)) fun χ' =>
        div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _))
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hsc] at b
    refine b.trans (le_of_eq ?_)
    rw [hq]
    push_cast
    rw [mul_div_assoc]
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := ((key q _ hq₁).1 _ _ (he a) (tv' a)).2 ((nz a).2 ha)
    exact hq₂.trans ((QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz.symm⟩)
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).1 (hq₂.symm.trans ha)
    have hz' : (S.r * S.N) • z = q.y := hz
    let q₀ : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N) := qkMk hB 0 (q.g + iota hB _ (-z)) (by
      rw [smul_add, qk_nsmul hB, ← map_nsmul, ← map_add, smul_neg, hz', add_neg_cancel])
    have e₀ : f q = f q₀ := (f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨-z, by
      rw [smul_neg, hz', add_neg_cancel]; rfl, rfl⟩)
    obtain ⟨q', x', hy', hx', hpow, hval⟩ := (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 n hn hnm rfl
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := u.A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', (l.yy_eq a' q' _ hx' (hx a')).trans (by rw [hy']; rfl), xinj ?_, (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

theorem norm_le_delta {p : ℕ} [Fact p.Prime] (ρ : S.Real) (y₀ : S.R →+* PadicAlgCl p) (a : S.Gam) :
    ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ S.delta y₀ := by
  have : NeZero (S.r * S.N) := ⟨(odd_level ρ).pos.ne'⟩
  exact le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove a

theorem main : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
  intro hL hL₂ _ o Ω _ _ _ _ S ρ p _ y₀ u l h a _
  obtain ⟨sc, -, h₁, -, h₃⟩ := exists_scale hL hL₂ u l h
  have h2 : 2 ≤ S.r * S.N := S.N_ge.trans (Nat.le_mul_of_pos_left _ S.r_pos)
  obtain ⟨a', -, -, ha'⟩ := h₃ _ h2 dvd_rfl 0 (zero_mem _)
  obtain ⟨w, hw, b⟩ := h₁ a
  exact ⟨w, hw, b.trans (mul_le_mul_of_nonneg_right (ha' ▸ norm_le_delta ρ y₀ a') (Real.exp_pos _).le)⟩

end GlobalTheory.ZH.TestVal
end
