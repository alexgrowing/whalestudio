import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt
open MvPolynomial

private theorem zp {k : Type} [NormedField k] [IsUltrametricDist k] {u : k} {ε : ℝ} (h0 : 0 ≤ ε) (hu : ‖u‖ = 1) (h : ‖u - 1‖ ≤ ε)
    (n : ℤ) : ‖u ^ n - 1‖ ≤ ε := by
  have hu0 : u ≠ 0 := fun e => by simp [e] at hu
  have step : ∀ w x : k, ‖w‖ = 1 → ‖w - 1‖ ≤ ε → ‖x - 1‖ ≤ ε → ‖x * w - 1‖ ≤ ε := fun w x hw h1 h2 => by
    rw [show x * w - 1 = (x - 1) * w + (w - 1) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
    rwa [norm_mul, hw, mul_one]
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih => rw [zpow_add_one₀ hu0]; exact step _ _ hu h ih
  | pred n ih =>
    rw [zpow_sub_one₀ hu0]
    refine step _ _ (by rw [norm_inv, hu, inv_one]) ?_ ih
    rw [show u⁻¹ - 1 = -(u⁻¹ * (u - 1)) by field_simp; ring, norm_neg, norm_mul, norm_inv, hu, inv_one, one_mul]
    exact h

theorem UpperTheory.Gal.Wt.deltaNear_h : DeltaNear := by
  intro l _ ι a ν h hI
  let m : GL (Fin a) ℂ → Fin a × Fin a → Qbar l := fun g p => ι.symm ((g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1)
  let D : MvPolynomial (Fin a × Fin a) ℤ := (Matrix.of fun i j => (X (j, i) : MvPolynomial (Fin a × Fin a) ℤ)).det
  have hmap : ∀ (w : Fin a × Fin a → ℂ) (P : MvPolynomial (Fin a × Fin a) ℤ),
      ι.symm (aeval w P) = aeval (fun j => ι.symm (w j)) P := by
    intro w P
    induction P using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  have hD : ∀ g : GL (Fin a) ℂ, ι.symm (g : Matrix (Fin a) (Fin a) ℂ).det = aeval (m g) D := fun g => by
    rw [← hmap, AlgHom.map_det]
    congr 2
    ext i j
    simp
  have hδ : ∀ g : GL (Fin a) ℂ, ι.symm (delta ν g) = (aeval (m g) D) ^ ν.detShift * aeval (m g) (extremal ℤ a ν) := fun g => by
    have e1 : (aeval fun p : Fin a × Fin a => (1 : Matrix (Fin a) (Fin a) ℂ) p.1 p.2).comp
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (g : Matrix (Fin a) (Fin a) ℂ).transpose) =
        aeval fun p : Fin a × Fin a => (g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1 :=
      MvPolynomial.algHom_ext fun v => by simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
    have e2 : delta ν g = (g : Matrix (Fin a) (Fin a) ℂ).det ^ ν.detShift *
        aeval (fun p : Fin a × Fin a => (g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1) (extremal ℤ a ν) := by
      change aeval _ (sqAct ℂ a ν g (extremal ℂ a ν)) = _
      rw [sqAct, map_smul, ← AlgHom.comp_apply, e1, detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
        ← Formalism.L2.DIV.map_extremal (algebraMap ℤ ℂ), aeval_map_algebraMap, smul_eq_mul]
    rw [e2, map_mul, map_zpow₀, hD, hmap]
  have hm : ∀ p, ‖m h p‖ ≤ 1 := fun p => (hI _ _).1
  have hb : ∀ (x : Fin a × Fin a → Qbar l), (∀ p, ‖x p‖ ≤ 1) → ∀ P : MvPolynomial (Fin a × Fin a) ℤ, ‖aeval x P‖ ≤ 1 :=
    fun x hx P => (aeval_sub_le le_rfl hx hx (fun _ => by simp) P).1
  have hd1 : ‖aeval (m h) D‖ = 1 := by
    have h1 := hb _ hm D
    have h2 := hb (m h⁻¹) (fun p => (hI _ _).2) D
    have h3 : ‖aeval (m h) D‖ * ‖aeval (m h⁻¹) D‖ = 1 := by
      rw [← norm_mul, ← hD, ← hD, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, norm_one]
    nlinarith [norm_nonneg (aeval (m h) D), norm_nonneg (aeval (m h⁻¹) D)]
  refine ⟨by rw [hδ, norm_mul, norm_zpow, hd1, one_zpow, one_mul]; exact hb _ hm _, fun ε hε hN => ?_⟩
  have h1 : ∀ p, ‖m 1 p‖ ≤ 1 := fun p => by
    simp only [m, Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  have hc : ∀ p, ‖m h p - m 1 p‖ ≤ ε := fun p => by
    have := hN p.2 p.1
    rwa [map_sub] at this
  have eD : aeval (m 1) D = 1 := by rw [← hD]; simp
  have eE : aeval (m 1) (extremal ℤ a ν) = 1 := by
    rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det]
    rw [show ∀ M : Matrix (Fin (s.val + 1)) (Fin (s.val + 1)) (Qbar l), M = 1 → M.det ^ (ν.natW s - Formalism.GradedWeylDivisibility.nuNext ν.natW s) = 1 from
      fun M hM => by rw [hM, Matrix.det_one, one_pow]]
    ext i j
    simp [m, Matrix.one_apply, eq_comm]
  have c1 : ‖aeval (m h) D - 1‖ ≤ ε := by rw [← eD]; exact (aeval_sub_le hε hm h1 hc D).2.2
  have c2 : ‖aeval (m h) (extremal ℤ a ν) - 1‖ ≤ ε := by rw [← eE]; exact (aeval_sub_le hε hm h1 hc (extremal ℤ a ν)).2.2
  rw [map_sub, map_one, hδ, show ∀ x y : Qbar l, x * y - 1 = x * (y - 1) + (x - 1) from fun x y => by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (zp hε hd1 c1 _))
  rwa [norm_mul, norm_zpow, hd1, one_zpow, one_mul]
