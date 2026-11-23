import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
open GlobalTheory.UnifPoint

noncomputable section

namespace GlobalTheory.HeckeLift

theorem int_eq_of_exp_eq_coprime {m n : ℤ} {p : ℕ} (hp : 0 < p)
    (h : ∀ k : ℕ, 0 < k → k.Coprime p → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  set K : ℕ := 1 + (n - m).natAbs * p with hK
  have hk : 0 < K := by omega
  have hcop : K.Coprime p := by
    rw [hK]
    first
      | exact (Nat.coprime_add_mul_right_left 1 p _).2 (Nat.coprime_one_left p)
      | exact (Nat.coprime_add_mul_left_left 1 p _).2 (Nat.coprime_one_left p)
      | simp
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hk hcop)
  have h0 : ((K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = (((K : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize ((K : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have hlt : (n - m).natAbs < K := by
    have : (n - m).natAbs ≤ (n - m).natAbs * p := Nat.le_mul_of_pos_right _ hp
    omega
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact hlt)
  omega

theorem exists_linearMap_of_isHkIsog : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → IsHkIsog p (F.u i P) (F.u j P') C ψ ψp → ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ ∀ z, F.ex j P' (h z) = ψp (F.ex i P z) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hk
  obtain ⟨-, -, hfib, hact, hsurj, hker, hweil, -⟩ := hk
  obtain ⟨e, he⟩ : ∃ e : (Fin g → ℂ) → (Over.mk (F.u j P') ⟶ Xo.univ.t.G), ∀ z, e z = ψp (F.ex i P z) :=
    ⟨_, fun _ => rfl⟩
  have hpow : ∀ (n : ℕ) z, F.ex i P (n • z) = F.ex i P z ^ n := fun n z => by
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact (F.ex_ker i P hP 0).2 ⟨0, map_zero P⟩
    | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hkerC : ∀ z, e z = 1 → ∃ a, P a = (p ^ 2) • z := fun z hz => by
    have hmem : F.ex i P z ∈ C := by rw [← hker, MonoidHom.mem_ker, ← he, hz]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 ((hpow _ z).trans (hC _ hmem))
    exact ⟨a, ha⟩
  have hhol : IsHolTo Set.univ (fun z => (e z).left) := by
    have h1 := (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G _ g (F.ex i P)
      (GlobalTheory.ClassUniq.isHolTo_ex F i P hP)).2 _ (ψ ≫ pullback.fst _ _)
    convert h1 using 2 with z
    rw [← Category.assoc, hfib, he]
    unfold fibPt
    exact (pullback.lift_fst _ _ _).symm
  have hc : {z | e z = 1}.Countable := by
    refine ((countable_periods hP).image fun w => ((p ^ 2 : ℕ) : ℂ)⁻¹ • w).mono fun z hz => ?_
    obtain ⟨a, ha⟩ := hkerC z hz
    refine ⟨P a, ⟨a, rfl⟩, ?_⟩
    have h0 : ((p ^ 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
    simp only [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]
  have hexp : IsExp (F.ex j P') := ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP',
    (F.ex_diff j P' hP').1, (F.ex_diff j P' hP').2⟩
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' hexp (F.ex_ker j P' hP') (e₀ := e)
    (fun z w => by rw [he, he, he, F.ex_add i P hP, map_mul]) (fun y => by
      obtain ⟨z, hz⟩ := hsurj.comp (F.ex_onto i P hP) y
      exact ⟨z, (he z).trans hz⟩) hhol hc
  have hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a := fun a z => by
    rw [he, he, F.ex_lin i P hP, hact]
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (F.ex_ker j P' hP' _).1 ((eq_iff_sub_of_add (F.ex_add j P' hP') _ _).1
          (((hh _).trans (hlin a x)).trans (by rw [← hh]; exact (F.ex_lin j P' hP' a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a =>
    (F.ex_ker j P' hP' _).1 ((hh _).trans (by rw [he, (F.ex_ker i P hP _).2 ⟨a, rfl⟩, map_one]))
  choose r₀ hr₀ using hmem
  let r₁ : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add, hr₀, hr₀, hr₀, map_add, map_add])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  refine ⟨r₁, h, fun a b => ?_, hr₀, fun b => ?_, fun z => (hh z).trans (he z)⟩
  · refine int_eq_of_exp_eq_coprime hp.pos fun k hk hcop => ?_
    have w := F.ex_weil i P hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w1 := hweil k _ _ _ hcop w
    have w' := F.ex_weil j P' hP' k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh, he, he] at w'
    have := congrArg Units.val (weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ (F.u j P') k _ _ _ _ w' w1)
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val] at this
    rw [show r₁ a = r₀ a from rfl, show r₁ b = r₀ b from rfl, this, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · obtain ⟨a, ha⟩ := hkerC (h.symm (P' b)) (by
      rw [← hh, h.apply_symm_apply]; exact (F.ex_ker j P' hP' _).2 ⟨b, rfl⟩)
    refine ⟨a, hP'.2.1 ?_⟩
    change P' (r₀ a) = _
    rw [hr₀, ha, map_nsmul, h.apply_symm_apply, map_nsmul]

end GlobalTheory.HeckeLift
