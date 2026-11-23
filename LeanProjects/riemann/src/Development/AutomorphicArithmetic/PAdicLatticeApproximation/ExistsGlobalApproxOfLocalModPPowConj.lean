import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private lemma normPPow {p : ℕ} [Fact p.Prime] (k : ℕ) :
    ‖((p : PadicAlgCl p)) ^ k‖ = ((p : ℝ) ^ k)⁻¹ := by
  rw [norm_pow, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
    Padic.norm_p, inv_pow]

private lemma stepAt {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {n : ℕ}
    (S : Matrix (Fin n) (Fin n) K) (hS : S.det ≠ 0) (a v : Fin n → K) (k : ℕ) (e C : ℝ) (he : 0 ≤ e)
    (hC : ∀ i, ∑ j, ‖(S i j : PadicAlgCl p)‖ ≤ C) (hCe : C * e = ((p : ℝ) ^ k)⁻¹)
    (hv : ∀ i, ‖((v i - (S⁻¹ *ᵥ a) i : K) : PadicAlgCl p)‖ < e) :
    ∃ a' : Fin n → K, (∀ i, ‖(a' i : PadicAlgCl p)‖ ≤ 1) ∧ S *ᵥ v = a + p ^ k • a' := by
  obtain ⟨d, hd⟩ : ∃ d : Fin n → K, d = v - S⁻¹ *ᵥ a := ⟨_, rfl⟩
  have hv' : ∀ j, ‖(d j : PadicAlgCl p)‖ < e := by
    intro j
    rw [hd]
    exact hv j
  have hSd : S *ᵥ v - a = S *ᵥ d := by
    rw [hd, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS), Matrix.one_mulVec]
  have hbound : ∀ i, ‖(((S *ᵥ v - a) i : K) : PadicAlgCl p)‖ ≤ ((p : ℝ) ^ k)⁻¹ := by
    intro i
    rw [hSd, ← hCe]
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    calc ‖∑ j, (S i j : PadicAlgCl p) * (d j : PadicAlgCl p)‖
        ≤ ∑ j, ‖(S i j : PadicAlgCl p) * (d j : PadicAlgCl p)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖(S i j : PadicAlgCl p)‖ * e := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (le_of_lt (hv' j)) (norm_nonneg _)
      _ = (∑ j, ‖(S i j : PadicAlgCl p)‖) * e := (Finset.sum_mul _ _ _).symm
      _ ≤ C * e := mul_le_mul_of_nonneg_right (hC i) he
  have hp0 : (0 : ℝ) < (p : ℝ) ^ k :=
    pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) k
  have hpK : ((p : K) ^ k) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine ⟨fun i => ((p : K) ^ k)⁻¹ * (S *ᵥ v - a) i, ?_, ?_⟩
  · intro i
    have hi := hbound i
    have hnorm : ‖((((p : K) ^ k)⁻¹ * (S *ᵥ v - a) i : K) : PadicAlgCl p)‖
        = (p : ℝ) ^ k * ‖(((S *ᵥ v - a) i : K) : PadicAlgCl p)‖ := by
      push_cast
      rw [norm_mul, norm_inv, normPPow, inv_inv]
    rw [hnorm]
    calc (p : ℝ) ^ k * ‖(((S *ᵥ v - a) i : K) : PadicAlgCl p)‖
        ≤ (p : ℝ) ^ k * ((p : ℝ) ^ k)⁻¹ := mul_le_mul_of_nonneg_left hi hp0.le
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  · funext i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, mul_inv_cancel_left₀ hpK,
      Pi.sub_apply, add_sub_cancel]

theorem UpperTheory.exists_global_approx_of_local_mod_p_pow_conj :
    UpperTheory.Gal.W2.FApprox → ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (S B : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)), (∀ w, (S w).det ≠ 0) → (∀ w, (B w).det ≠ 0) → ∀ (a b : Loc G) (k : ℕ), ∃ (y : Fin G.n → G.F) (a' b' : Loc G), IntL a' ∧ IntL b' ∧ (∀ w, S w *ᵥ (fun i => G.embW w (y i)) = a w + p ^ k • a' w) ∧ ∀ w, B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (y i))) = b w + p ^ k • b' w := by
  intro hF p _ G S B hS hB a b k
  classical
  set C : ℝ := 1 + ∑ w, ∑ i, ∑ j,
    (‖(S w i j : PadicAlgCl p)‖ + ‖(B w i j : PadicAlgCl p)‖) with hCdef
  have hnn : ∀ w i, 0 ≤ ∑ j, (‖(S w i j : PadicAlgCl p)‖ + ‖(B w i j : PadicAlgCl p)‖) :=
    fun w i => Finset.sum_nonneg fun j _ => by positivity
  have hbig : ∀ w i, ∑ j, (‖(S w i j : PadicAlgCl p)‖ + ‖(B w i j : PadicAlgCl p)‖) ≤ C := by
    intro w i
    have h2 := Finset.single_le_sum
      (f := fun i' => ∑ j, (‖(S w i' j : PadicAlgCl p)‖ + ‖(B w i' j : PadicAlgCl p)‖))
      (fun i' _ => hnn w i') (Finset.mem_univ i)
    have h3 := Finset.single_le_sum
      (f := fun w' => ∑ i', ∑ j, (‖(S w' i' j : PadicAlgCl p)‖ + ‖(B w' i' j : PadicAlgCl p)‖))
      (fun w' _ => Finset.sum_nonneg fun i' _ => hnn w' i') (Finset.mem_univ w)
    linarith
  have hrowS : ∀ w i, ∑ j, ‖(S w i j : PadicAlgCl p)‖ ≤ C := by
    intro w i
    refine le_trans ?_ (hbig w i)
    exact Finset.sum_le_sum fun j _ => le_add_of_nonneg_right (norm_nonneg _)
  have hrowB : ∀ w i, ∑ j, ‖(B w i j : PadicAlgCl p)‖ ≤ C := by
    intro w i
    refine le_trans ?_ (hbig w i)
    exact Finset.sum_le_sum fun j _ => le_add_of_nonneg_left (norm_nonneg _)
  have hCpos : 0 < C := by
    have : 0 ≤ ∑ w, ∑ i, ∑ j, (‖(S w i j : PadicAlgCl p)‖ + ‖(B w i j : PadicAlgCl p)‖) :=
      Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => hnn w i
    linarith
  have hp0 : (0 : ℝ) < (p : ℝ) ^ k :=
    pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) k
  set e : ℝ := ((p : ℝ) ^ k)⁻¹ / C with he_def
  have he : 0 < e := div_pos (inv_pos.mpr hp0) hCpos
  have hCe : C * e = ((p : ℝ) ^ k)⁻¹ := by
    rw [he_def, mul_div_cancel₀ _ hCpos.ne']
  have hy : ∀ i : Fin G.n, ∃ x : G.F, ∀ w,
      ‖((G.embW w x - ((S w)⁻¹ *ᵥ a w) i : G.Fw w) : PadicAlgCl p)‖ < e ∧
      ‖((G.embW w (IsCMField.complexConj G.F x) - ((B w)⁻¹ *ᵥ b w) i : G.Fw w) :
        PadicAlgCl p)‖ < e :=
    fun i => hF p G (fun w => ((S w)⁻¹ *ᵥ a w) i) (fun w => ((B w)⁻¹ *ᵥ b w) i) e he
  choose y hy using hy
  have hA : ∀ w, ∃ c : Fin G.n → G.Fw w, (∀ i, ‖(c i : PadicAlgCl p)‖ ≤ 1) ∧
      S w *ᵥ (fun i => G.embW w (y i)) = a w + p ^ k • c :=
    fun w => stepAt (S w) (hS w) (a w) _ k e C he.le (hrowS w) hCe (fun i => (hy i w).1)
  have hB' : ∀ w, ∃ c : Fin G.n → G.Fw w, (∀ i, ‖(c i : PadicAlgCl p)‖ ≤ 1) ∧
      B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (y i))) = b w + p ^ k • c :=
    fun w => stepAt (B w) (hB w) (b w) _ k e C he.le (hrowB w) hCe (fun i => (hy i w).2)
  choose a' ha'1 ha'2 using hA
  choose b' hb'1 hb'2 using hB'
  exact ⟨y, a', b', fun w i => ha'1 w i, fun w i => hb'1 w i, ha'2, hb'2⟩
