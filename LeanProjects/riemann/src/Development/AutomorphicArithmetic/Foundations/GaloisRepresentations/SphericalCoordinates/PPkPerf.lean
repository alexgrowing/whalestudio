import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

noncomputable section

namespace UpperTheory.Gal.W2

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

private def mv (h : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (z : Loc G) : Loc G :=
  fun w => h w *ᵥ z w

private lemma pairL_add_left (a a' b : Loc G) : pairL (a + a') b = pairL a b + pairL a' b := by
  simp only [pairL, Pi.add_apply, add_dotProduct, map_add, Finset.sum_add_distrib]

private lemma pairL_comm (a b : Loc G) : pairL a b = pairL b a := by
  simp only [pairL, dotProduct_comm]

private lemma pairL_add_right (a b b' : Loc G) : pairL a (b + b') = pairL a b + pairL a b' := by
  rw [pairL_comm, pairL_add_left, pairL_comm b, pairL_comm b']

private lemma pairL_smul_left (c : ℚ_[p]) (a b : Loc G) : pairL (c • a) b = c * pairL a b := by
  simp only [pairL, Pi.smul_apply, smul_dotProduct, map_smul, smul_eq_mul, Finset.mul_sum]

private lemma pairL_nsmul_left (n : ℕ) (a b : Loc G) : pairL (n • a) b = (n : ℚ_[p]) * pairL a b := by
  rw [← pairL_smul_left, Nat.cast_smul_eq_nsmul]

private lemma pairL_nsmul_right (n : ℕ) (a b : Loc G) : pairL a (n • b) = (n : ℚ_[p]) * pairL a b := by
  rw [pairL_comm, pairL_nsmul_left, pairL_comm]

private lemma pairL_tr (h : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (a b : Loc G) :
    pairL (mv (fun w => (h w)ᵀ) a) b = pairL a (mv h b) := by
  simp only [pairL, mv, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

private lemma pairL_fw (e : ∀ w : Fin G.m, G.Fw w) (a b : Loc G) :
    pairL (fun w => e w • a w) b = pairL a (fun w => e w • b w) := by
  simp only [pairL, smul_dotProduct, dotProduct_smul]

private lemma mv_add (h : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (a b : Loc G) :
    mv h (a + b) = mv h a + mv h b := by
  funext w; simp only [mv, Pi.add_apply, Matrix.mulVec_add]

private lemma mv_nsmul (h : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (n : ℕ) (a : Loc G) :
    mv h (n • a) = n • mv h a := by
  funext w
  simp only [mv, Pi.smul_apply]
  rw [← Nat.cast_smul_eq_nsmul (G.Fw w), Matrix.mulVec_smul, Nat.cast_smul_eq_nsmul]

private lemma norm_nsmul_fw (n : ℕ) (w : Fin G.m) (x : G.Fw w) :
    ‖((n • x : G.Fw w) : PadicAlgCl p)‖ = ‖(n : ℚ_[p])‖ * ‖(x : PadicAlgCl p)‖ := by
  have e : ((n • x : G.Fw w) : PadicAlgCl p) = (n : ℚ_[p]) • (x : PadicAlgCl p) := by
    rw [Nat.cast_smul_eq_nsmul]; rfl
  rw [e, norm_smul]

private lemma int_add {a b : Loc G} (ha : IntL a) (hb : IntL b) : IntL (a + b) := fun w i => by
  have e : (((a + b) w i : G.Fw w) : PadicAlgCl p) = (a w i : PadicAlgCl p) + (b w i : PadicAlgCl p) := rfl
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha w i) (hb w i))

private lemma small (C : ℝ) : ∀ᶠ k : ℕ in Filter.atTop, ‖((p ^ k : ℕ) : ℚ_[p])‖ * C ≤ 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h0 : Filter.Tendsto (fun k : ℕ => ((p : ℝ)⁻¹) ^ k * C) Filter.atTop (nhds (0 * C)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp)).mul_const C
  rw [zero_mul] at h0
  filter_upwards [h0.eventually (gt_mem_nhds (zero_lt_one))] with k hk
  have e : ‖((p ^ k : ℕ) : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ k := by
    rw [Nat.cast_pow, norm_pow, Padic.norm_p]
  rw [e]; exact hk.le

private lemma int_vec (v : Loc G) : ∀ᶠ k : ℕ in Filter.atTop, IntL ((p ^ k) • v) := by
  have h : ∀ᶠ k : ℕ in Filter.atTop, ∀ w i, ‖((p ^ k : ℕ) : ℚ_[p])‖ * ‖(v w i : PadicAlgCl p)‖ ≤ 1 :=
    Filter.eventually_all.2 fun w => Filter.eventually_all.2 fun i => small _
  filter_upwards [h] with k hk w i
  have e : (((p ^ k) • v) w i : G.Fw w) = (p ^ k) • (v w i) := rfl
  rw [e, norm_nsmul_fw]
  exact hk w i

private lemma int_mat (h : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ a : Loc G, IntL a → IntL (mv h ((p ^ k) • a)) := by
  have h1 : ∀ᶠ k : ℕ in Filter.atTop, ∀ w i j, ‖((p ^ k : ℕ) : ℚ_[p])‖ * ‖(h w i j : PadicAlgCl p)‖ ≤ 1 :=
    Filter.eventually_all.2 fun w => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => small _
  filter_upwards [h1] with k hk a ha w i
  have e : ((mv h ((p ^ k) • a) w i : G.Fw w) : PadicAlgCl p) =
      ∑ j, (h w i j : PadicAlgCl p) * (((p ^ k) • a w j : G.Fw w) : PadicAlgCl p) := by
    simp only [mv, Matrix.mulVec, dotProduct, Pi.smul_apply, IntermediateField.coe_sum,
      MulMemClass.coe_mul]
  rw [e]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  rw [norm_mul, norm_nsmul_fw]
  have h2 := hk w i j
  have h3 := ha w j
  calc _ = (‖((p ^ k : ℕ) : ℚ_[p])‖ * ‖(h w i j : PadicAlgCl p)‖) * ‖(a w j : PadicAlgCl p)‖ := by ring
    _ ≤ 1 * 1 := by gcongr
    _ = 1 := one_mul 1

private lemma nm_add {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private lemma nm_sub {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact nm_add hx (by rwa [norm_neg])

private lemma pk_ne (k : ℕ) : ((p ^ k : ℕ) : ℚ_[p]) ≠ 0 := by
  exact_mod_cast pow_ne_zero k (Fact.out : p.Prime).ne_zero

private lemma pair_unif (d : ∀ w : Fin G.m, G.Fw w)
    (hdual : ∀ a : Loc G, (∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w)) :
    ∃ C : ℝ, ∀ a b : Loc G, IntL a → IntL b → ‖pairL a b‖ ≤ C := by
  obtain ⟨k, hk⟩ := (int_mat (G := G) (fun w => d w • (1 : Matrix (Fin G.n) (Fin G.n) (G.Fw w)))).exists
  refine ⟨‖((p ^ k : ℕ) : ℚ_[p])‖⁻¹, fun a b ha hb => ?_⟩
  have h1 : IntL (fun w => d w • ((p ^ k) • a) w) := by
    have e : mv (fun w => d w • (1 : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) ((p ^ k) • a) =
        fun w => d w • ((p ^ k) • a) w := by
      funext w
      simp only [mv, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← e]; exact hk a ha
  have h2 := (hdual _).2 h1 b hb
  rw [pairL_nsmul_left, norm_mul] at h2
  have h3 : 0 < ‖((p ^ k : ℕ) : ℚ_[p])‖ := norm_pos_iff.2 (pk_ne k)
  calc ‖pairL a b‖ = ‖((p ^ k : ℕ) : ℚ_[p])‖⁻¹ * (‖((p ^ k : ℕ) : ℚ_[p])‖ * ‖pairL a b‖) := by
        rw [inv_mul_cancel_left₀ h3.ne']
    _ ≤ ‖((p ^ k : ℕ) : ℚ_[p])‖⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

private lemma pair_vec {C : ℝ} (hC : ∀ a b : Loc G, IntL a → IntL b → ‖pairL a b‖ ≤ C) (v : Loc G) :
    ∃ C' : ℝ, ∀ a : Loc G, IntL a → ‖pairL a v‖ ≤ C' := by
  obtain ⟨k, hk⟩ := (int_vec v).exists
  refine ⟨‖((p ^ k : ℕ) : ℚ_[p])‖⁻¹ * C, fun a ha => ?_⟩
  have h2 := hC _ _ ha hk
  rw [pairL_nsmul_right, norm_mul] at h2
  have h3 : 0 < ‖((p ^ k : ℕ) : ℚ_[p])‖ := norm_pos_iff.2 (pk_ne k)
  calc ‖pairL a v‖ = ‖((p ^ k : ℕ) : ℚ_[p])‖⁻¹ * (‖((p ^ k : ℕ) : ℚ_[p])‖ * ‖pairL a v‖) := by
        rw [inv_mul_cancel_left₀ h3.ne']
    _ ≤ _ := by gcongr

private lemma pair_mat {C : ℝ} (hC : ∀ a b : Loc G, IntL a → IntL b → ‖pairL a b‖ ≤ C)
    (h : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) :
    ∃ C' : ℝ, ∀ a z : Loc G, IntL a → IntL z → ‖pairL a (mv h z)‖ ≤ C' := by
  obtain ⟨k, hk⟩ := (int_mat h).exists
  refine ⟨‖((p ^ k : ℕ) : ℚ_[p])‖⁻¹ * C, fun a z ha hz => ?_⟩
  have h2 := hC _ _ ha (hk z hz)
  rw [mv_nsmul, pairL_nsmul_right, norm_mul] at h2
  have h3 : 0 < ‖((p ^ k : ℕ) : ℚ_[p])‖ := norm_pos_iff.2 (pk_ne k)
  calc ‖pairL a (mv h z)‖ = ‖((p ^ k : ℕ) : ℚ_[p])‖⁻¹ * (‖((p ^ k : ℕ) : ℚ_[p])‖ * ‖pairL a (mv h z)‖) := by
        rw [inv_mul_cancel_left₀ h3.ne']
    _ ≤ _ := by gcongr

private lemma err {ci x : ℚ_[p]} {C : ℝ} {k : ℕ} (hs : ‖((p ^ k : ℕ) : ℚ_[p])‖ * (‖ci‖ * C) ≤ 1) (hx : ‖x‖ ≤ C) :
    ‖ci * (((p ^ k : ℕ) : ℚ_[p]) * x)‖ ≤ 1 := by
  rw [norm_mul, norm_mul]
  calc _ = ‖((p ^ k : ℕ) : ℚ_[p])‖ * (‖ci‖ * ‖x‖) := by ring
    _ ≤ ‖((p ^ k : ℕ) : ℚ_[p])‖ * (‖ci‖ * C) := by gcongr
    _ ≤ 1 := hs

private lemma den_iff (q : ℚ) : q.den.Coprime p ↔ ‖(q : ℚ_[p])‖ ≤ 1 := by
  rw [Padic.norm_rat_le_one_iff_padicValuation_le_one, Rat.padicValuation_le_one_iff,
    Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]

variable {D : Datum p} {L : Link D G} {β : G.Cˣ}

private lemma perf_core (A : PFrame L β) (g : Gp G) (d : ∀ w : Fin G.m, G.Fw w) (hd0 : ∀ w, d w ≠ 0)
    (hdual : ∀ a : Loc G, (∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w)) (x : VQ D) :
    A.Mem g x ↔ ∀ u, A.Mem g u →
      ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * (pairL (A.T' u) (A.T x) - pairL (A.T' x) (A.T u))‖ ≤ 1 := by
  set ci : ℚ_[p] := ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) with hci
  have hci0 : ci ≠ 0 := (g.1⁻¹).ne_zero
  let gm : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) := fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w))
  let gi : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    fun w => (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))
  have hgg : ∀ z, mv gi (mv gm z) = z := fun z => by
    funext w
    simp only [mv, gi, gm, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hgg' : ∀ z, mv gm (mv gi z) = z := fun z => by
    funext w
    simp only [mv, gi, gm, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hmem : ∀ u, A.Mem g u ↔ IntL (mv gi (A.T u)) ∧
      ∀ z : Loc G, IntL z → ‖ci * pairL (A.T' u) (mv gm z)‖ ≤ 1 := fun u => Iff.rfl
  simp only [hmem]
  constructor
  · rintro ⟨h1, h2⟩ u ⟨u1, u2⟩
    have t1 := u2 _ h1
    have t2 := h2 _ u1
    rw [hgg'] at t1 t2
    rw [mul_sub]
    exact nm_sub t1 t2
  · intro H
    obtain ⟨C, hC⟩ := pair_unif d hdual
    obtain ⟨Cg, hCg⟩ := pair_mat hC gm
    obtain ⟨C1, hC1⟩ := pair_vec hC (A.T x)
    obtain ⟨C2, hC2⟩ := pair_vec hC (A.T' x)
    obtain ⟨k, hk0, hk1, hk2, hk3⟩ := ((int_mat gi).and ((small (p := p) (‖ci‖ * Cg)).and
      ((small (p := p) (‖ci‖ * C1)).and (small (p := p) (‖ci‖ * C2))))).exists
    refine ⟨?_, ?_⟩
    ·
      have key : IntL (fun w => d w • (fun w => (d w)⁻¹ • mv gi (A.T x) w) w) := by
        refine (hdual _).1 fun z hz => ?_
        let y : Loc G := fun w => (d w)⁻¹ • z w
        have hy : ∀ z', IntL z' → ‖pairL y z'‖ ≤ 1 := by
          refine (hdual y).2 ?_
          have e : (fun w => d w • y w) = z := by
            funext w; simp only [y, smul_smul, mul_inv_cancel₀ (hd0 w), one_smul]
          rw [e]; exact hz
        obtain ⟨u, a', b', ha', hb', hTu, hTu'⟩ := A.dense 0 (ci⁻¹ • mv (fun w => (gi w)ᵀ) y) k
        have hu : IntL (mv gi (A.T u)) ∧ ∀ z : Loc G, IntL z → ‖ci * pairL (A.T' u) (mv gm z)‖ ≤ 1 := by
          refine ⟨?_, fun z' hz' => ?_⟩
          · rw [hTu, zero_add]; exact hk0 a' ha'
          · rw [hTu', pairL_add_left, pairL_smul_left, pairL_tr, hgg, pairL_nsmul_left, mul_add,
              ← _root_.mul_assoc, mul_inv_cancel₀ hci0, _root_.one_mul]
            exact nm_add (hy _ hz') (err hk1 (hCg _ _ hb' hz'))
        have hh := H u hu
        rw [hTu', hTu, zero_add, pairL_add_left, pairL_smul_left, pairL_tr, pairL_nsmul_left,
          pairL_nsmul_right] at hh
        have e : pairL (fun w => (d w)⁻¹ • mv gi (A.T x) w) z =
            ci * (ci⁻¹ * pairL y (mv gi (A.T x)) + ((p ^ k : ℕ) : ℚ_[p]) * pairL b' (A.T x) -
                ((p ^ k : ℕ) : ℚ_[p]) * pairL (A.T' x) a') -
              ci * (((p ^ k : ℕ) : ℚ_[p]) * pairL b' (A.T x)) +
              ci * (((p ^ k : ℕ) : ℚ_[p]) * pairL (A.T' x) a') := by
          have e0 : pairL (fun w => (d w)⁻¹ • mv gi (A.T x) w) z = pairL y (mv gi (A.T x)) :=
            (pairL_fw _ _ _).trans (pairL_comm _ _)
          rw [e0]
          field_simp
          ring
        rw [e]
        refine nm_add (nm_sub hh (err hk2 (hC1 _ hb'))) (err hk3 ?_)
        rw [pairL_comm]; exact hC2 _ ha'
      have e : (fun w => d w • (fun w => (d w)⁻¹ • mv gi (A.T x) w) w) = mv gi (A.T x) := by
        funext w; simp only [smul_smul, mul_inv_cancel₀ (hd0 w), one_smul]
      rw [e] at key
      exact key
    ·
      intro z hz
      obtain ⟨u, a', b', ha', hb', hTu, hTu'⟩ := A.dense (mv gm z) 0 k
      have hu : IntL (mv gi (A.T u)) ∧ ∀ z : Loc G, IntL z → ‖ci * pairL (A.T' u) (mv gm z)‖ ≤ 1 := by
        refine ⟨?_, fun z' hz' => ?_⟩
        · rw [hTu, mv_add, hgg]; exact int_add hz (hk0 a' ha')
        · rw [hTu', zero_add, pairL_nsmul_left]
          exact err hk1 (hCg _ _ hb' hz')
      have hh := H u hu
      rw [hTu', hTu, zero_add, pairL_nsmul_left, pairL_add_right, pairL_nsmul_right] at hh
      have e : ci * pairL (A.T' x) (mv gm z) =
          ci * (((p ^ k : ℕ) : ℚ_[p]) * pairL b' (A.T x)) -
            ci * (((p ^ k : ℕ) : ℚ_[p]) * pairL (A.T' x) a') -
            ci * (((p ^ k : ℕ) : ℚ_[p]) * pairL b' (A.T x) -
              (pairL (A.T' x) (mv gm z) + ((p ^ k : ℕ) : ℚ_[p]) * pairL (A.T' x) a')) := by
        ring
      rw [e]
      refine nm_sub (nm_sub (err hk2 (hC1 _ hb')) (err hk3 ?_)) hh
      rw [pairL_comm]; exact hC2 _ ha'

end SlopeTestRemainingChoices

end UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.pkPerf_of :
    UpperTheory.Gal.W2.MemDual → UpperTheory.Gal.W2.PkPerf := by
  intro hMD p _ D G L β A g s hs M hM x
  obtain ⟨d, hd0, hdual⟩ := hMD p G
  have hn : ‖(s : ℚ_[p])‖ = ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ := by
    have h1 : ‖(g.1 : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 g.1.ne_zero
    rw [Units.val_inv_eq_inv_val, norm_inv]
    rw [norm_mul] at hs
    exact eq_inv_of_mul_eq_one_left hs
  rw [hM x, perf_core A g d hd0 hdual x]
  refine forall_congr' fun u => ?_
  rw [hM u]
  refine imp_congr_right fun _ => ?_
  rw [den_iff, Rat.cast_mul, A.form, norm_mul, norm_mul, hn]
