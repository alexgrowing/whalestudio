import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEntireMulEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistPullMulFn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.MulFrame

open GlobalTheory.ThetaFn GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter

theorem exists_two_mul_dot {g : ℕ} {a : Fin g → ℂ} (ha : Half a) (M : Fin g → ℤ) :
    ∃ n : ℤ, 2 * (a ⬝ᵥ cv M) = n := by
  have h : ∀ i, ∃ n : ℤ, 2 * a i = n := fun i => by
    rcases ha i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using h
  refine ⟨∑ i, n i * M i, ?_⟩
  simp only [dotProduct, cv, Finset.mul_sum, ← _root_.mul_assoc, hn]
  push_cast
  rfl

theorem cv_nsmul {g : ℕ} (m : ℕ) (M : Fin g → ℤ) : cv (m • M) = (m : ℂ) • cv M := by
  funext i
  simp [cv]

theorem perV_nsmul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (M N : Fin g → ℤ) :
    perV τ (m • M) (m • N) = (m : ℂ) • perV τ M N := by
  rw [perV, perV, cv_nsmul, cv_nsmul, Matrix.mulVec_smul, smul_add]

theorem autV_nsmul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b) (m : ℕ)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    autV τ a b (m • M) (m • N) ((m : ℂ) • z) = autV τ a b M N z ^ (m ^ 2) := by
  obtain ⟨p, hp⟩ := exists_two_mul_dot ha M
  obtain ⟨q, hq⟩ := exists_two_mul_dot hb N
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self (m : ℤ)
  have hk' : (m : ℂ) * (m - 1) = k + k := by exact_mod_cast hk
  rw [autV, autV, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(k * (p - q)), ?_⟩
  simp only [cv_nsmul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  rw [← hp, ← hq]
  linear_combination (-(2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N))) * hk'

section Origin

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T}

theorem val_origin {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) {m : T ⊗ A ⟶ A} {ε : Fin 2 → ℤ} {c : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ε)}
    (hn : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L rig T c)) (i : L.ι)
    (hi : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] (fun _ => i)) :
    valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] (fun _ => i)) (α.s fun _ => i).val = u.fr i 0 ^ c := by
  have he := comp_ptSecT u p (comp_one_eq_ex_zero u p)
  have h1 : ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun k => (ptSecT A (1 : T ⟶ A)).left ≫ ![(snd T A).left, m.left] k)
      (fun _ => i) := by
    rw [← he] at hj
    exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k
  have h2 := (mem_ptChart_iff (comp_one_eq_ex_zero u p) (fun _ => i)).2 hi
  have h12 := (le_preimage_inf p.left _ _).2 ⟨h1, h2⟩
  have e := congrArg (fun t => valAt' p.left _ (Units.val t))
    (hn (fun _ => i) (fun _ => i) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl))
  refine Eq.trans ?_ (((ThetaFn.valAt'_res p.left inf_le_left h12 _).symm.trans
    (e.trans (ThetaFn.valAt'_res p.left inf_le_right h12 _))).trans (valAt'_rigT p hrig c (fun _ => i) hi))
  rw [← he]
  exact (valAt'_appLE' p.left (ptSecT A (1 : T ⟶ A)).left _ h1 _).symm

end Origin

theorem fnT_iff {g : ℕ} {P : PolAV (Sp ℂ)} (u : HolUnif P.A P.L g) (k : ℕ)
    (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) :
    FnT u k t f ↔ IsFnAt u basePt (k : ℤ) t f := by
  constructor
  · intro h j z hj
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    rw [zpow_natCast]
    exact h i z ((exAt_mem_chart_iff u basePt _ _ z).1 hj)
  · intro h i z hi
    rw [← zpow_natCast]
    exact h (fun _ => i) z ((exAt_mem_chart_iff u basePt _ _ z).2 hi)

end GlobalTheory.MBLow.Cl.MulFrame

namespace GlobalTheory.MBLow.Cl

open GlobalTheory.ThetaFn GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter MulFrame in

theorem exists_normalised_mulPull_fnT : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ), FnT u 1 th f → ∃ (α : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![(snd (baseOver (Sp ℂ)) x.P.A).left, (snd (baseOver (Sp ℂ)) x.P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)))), α.IsGen ∧ LB.Gen.Corr x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (ptSecT x.P.A 1).left) (rigT x.P.A x.P.L x.rig (baseOver (Sp ℂ)) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧ IsTwistPull x.P.A x.P.L (mulT x.P.A (baseOver (Sp ℂ)) m) (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧ FnT u (m ^ 2) s₁ fun z => f ((m : ℂ) • z) := by
  intro g x hg u τ a b c W hNF m th f hf
  have hfr := frame_eq_autV_mul g x hg u τ a b c W hNF
  obtain ⟨-, -, ha, hb, -, hΛ, hrig, -⟩ := hNF
  have hL := x.P.isLB
  have H := GlobalTheory.exists_mulPull_gen_over GlobalTheory.abelianSchemeLaws_all.1.mulPull x.P (baseOver (Sp ℂ)) m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
    (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₀ hα₀
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A (baseOver (Sp ℂ)) m)
    (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  refine ⟨α, s₁, hα, hn, hs₁, ?_⟩
  have hψ := exAt_mulT u basePt m
  have hΦ : ∀ z, exAt u basePt z ≫ (snd (baseOver (Sp ℂ)) x.P.A ^ m).left = (u.ex ((m : ℂ) • z)).left := fun z => by
    rw [← lift_snd (fst (baseOver (Sp ℂ)) x.P.A) (snd (baseOver (Sp ℂ)) x.P.A ^ m), Over.comp_left, ← Category.assoc]
    exact (congrArg (· ≫ _) (hψ z)).trans (exAt_snd _ _ _)
  obtain ⟨r, hr, hne, hrj⟩ := exists_fn_of_isGen (Φ := fun z => (m : ℂ) • z) hL (by fun_prop) hΦ hα
  haveI := u.discrete
  obtain ⟨-, -, k3⟩ := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 (fun _ => 1) r
    Matrix.isHermitian_zero (fun _ => norm_one) hr hne (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
      obtain ⟨i', hi'⟩ := exists_chart u valueRules hL ((m : ℂ) • z)
      have hj := (exAt_mem_pairChart_iff (hΦ z) ![i, i']).2 ⟨hi, hi'⟩
      have hj' := hj
      rw [← exAt_add_period u basePt z l l.2] at hj'
      rw [hrj _ _ hj', hrj _ _ hj, exAt_add_period u basePt z l l.2]
      obtain ⟨M, N, hl⟩ := (hΛ l).1 l.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hermForm, Matrix.zero_mulVec, dotProduct_zero]
      rw [hfr M N i z hi, hfr (m • M) (m • N) i' _ hi', autV_nsmul τ ha hb, perV_nsmul, hl, smul_add]
      have n1 : autV τ a b M N z ≠ 0 := Complex.exp_ne_zero _
      simp only [_root_.zpow_neg, zpow_natCast, mul_pow, pow_one, mul_zero, add_zero, Complex.exp_zero]
      field_simp)
  have h0 : r 0 = 1 := by
    obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
    have hj := (exAt_mem_pairChart_iff (hΦ 0) (fun _ => i)).2 ⟨hi, by rw [smul_zero]; exact hi⟩
    have n := u.fr_ne i 0 hi
    rw [hrj _ _ hj, val_origin hrig hn i hi hj, smul_zero, ← zpow_add₀ n, ← zpow_add₀ n]
    simp
  have hc : IsPullConst u basePt (fun z => (m : ℂ) • z) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α 1 := fun j z hj => by
    have n := zpow_ne_zero ((m ^ 2 : ℕ) : ℤ) (u.fr_ne _ _ ((exAt_mem_pairChart_iff (hΦ z) j).1 hj).1)
    rw [← h0, ← k3 z, hrj j z hj, _root_.zpow_neg, inv_mul_cancel_right₀ n]
  have h2 := isFnAt_fnAt u basePt hL _ s₁
  have e := funext (hc.fn_eq hL hψ hs₁ ((fnT_iff u 1 th f).1 hf) h2)
  rw [fnT_iff]
  simpa only [e, _root_.one_mul] using h2

end GlobalTheory.MBLow.Cl

end
