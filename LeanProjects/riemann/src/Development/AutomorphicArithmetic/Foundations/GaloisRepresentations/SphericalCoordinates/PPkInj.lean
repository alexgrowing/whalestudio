import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

noncomputable section

namespace UpperTheory.Gal.W2.PeriodInjective

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

private abbrev MF (G : HTGroup p) : Type := ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)

private def IntM (A : MF G) : Prop := ∀ w i j, ‖(A w i j : PadicAlgCl p)‖ ≤ 1

private def mv (A : MF G) (z : Loc G) : Loc G := fun w => A w *ᵥ z w

private def sc (k : ℕ) (A : MF G) : MF G := fun w => (p ^ k) • A w

private theorem int_mul {w : Fin G.m} {a b : G.Fw w} (ha : ‖(a : PadicAlgCl p)‖ ≤ 1)
    (hb : ‖(b : PadicAlgCl p)‖ ≤ 1) : ‖((a * b : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := by
  rw [IntermediateField.coe_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

private theorem int_sum {w : Fin G.m} (f : Fin G.n → G.Fw w) (h : ∀ i, ‖(f i : PadicAlgCl p)‖ ≤ 1) :
    ‖((∑ i, f i : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := by
  have e : ((∑ i, f i : G.Fw w) : PadicAlgCl p) = ∑ i, (f i : PadicAlgCl p) :=
    map_sum (G.Fw w).val f Finset.univ
  rw [e]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => h i

private theorem mv_int {A : MF G} {z : Loc G} (hA : IntM A) (hz : IntL z) : IntL (mv A z) :=
  fun w i => int_sum _ fun j => int_mul (hA w i j) (hz w j)

private theorem intM_mul {A B : MF G} (hA : IntM A) (hB : IntM B) : IntM (fun w => A w * B w) :=
  fun w i j => by
    show ‖(((A w * B w) i j : G.Fw w) : PadicAlgCl p)‖ ≤ 1
    rw [Matrix.mul_apply]
    exact int_sum _ fun l => int_mul (hA w i l) (hB w l j)

private theorem intL_add {a b : Loc G} (ha : IntL a) (hb : IntL b) : IntL (a + b) := fun w i => by
  have h := IsUltrametricDist.norm_add_le_max ((a w i : G.Fw w) : PadicAlgCl p) ((b w i : G.Fw w) : PadicAlgCl p)
  exact h.trans (max_le (ha w i) (hb w i))

private theorem intL_sub {a b : Loc G} (ha : IntL a) (hb : IntL b) : IntL (a - b) := fun w i => by
  have e : (((a - b) w i : G.Fw w) : PadicAlgCl p) = (a w i : PadicAlgCl p) + -(b w i : PadicAlgCl p) := by
    rw [← sub_eq_add_neg]
    rfl
  have h := IsUltrametricDist.norm_add_le_max ((a w i : G.Fw w) : PadicAlgCl p) (-((b w i : G.Fw w) : PadicAlgCl p))
  rw [norm_neg] at h
  rw [e]
  exact h.trans (max_le (ha w i) (hb w i))

private theorem norm_p_lt : ‖((p : ℕ) : PadicAlgCl p)‖ < 1 := by
  have h := norm_algebraMap' (PadicAlgCl p) (p : ℚ_[p])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

private theorem small (A : MF G) : ∀ᶠ k in Filter.atTop, IntM (sc k A : MF G) := by
  simp only [IntM, Filter.eventually_all]
  intro w i j
  have ht : Filter.Tendsto (fun k : ℕ => ‖((p : ℕ) : PadicAlgCl p)‖ ^ k * ‖(A w i j : PadicAlgCl p)‖)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_p_lt).mul_const
      ‖(A w i j : PadicAlgCl p)‖
  filter_upwards [ht.eventually (Iio_mem_nhds zero_lt_one)] with k hk
  have e : ((sc k A w i j : G.Fw w) : PadicAlgCl p) = ((p : ℕ) : PadicAlgCl p) ^ k * (A w i j : PadicAlgCl p) := by
    simp [sc, Matrix.smul_apply, nsmul_eq_mul]
  rw [e, norm_mul, norm_pow]
  exact le_of_lt hk

private theorem mv_mv (A B : MF G) (z : Loc G) : mv A (mv B z) = mv (fun w => A w * B w) z := by
  funext w
  exact Matrix.mulVec_mulVec _ _ _

private theorem mv_one (z : Loc G) : mv (fun _ => 1) z = z := by
  funext w
  exact Matrix.one_mulVec _

private theorem mv_add_sc (B : MF G) (a a' : Loc G) (k : ℕ) :
    mv B (a + p ^ k • a') = mv B a + mv (sc k B) a' := by
  funext w
  simp only [mv, sc, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.mulVec_smul]

private theorem intM_of {C : MF G} (h : ∀ z, IntL z → IntL (mv C z)) : IntM C := by
  intro w i j
  have hz : IntL (Pi.single w (Pi.single j 1) : Loc G) := by
    intro w' i'
    by_cases hw : w' = w
    · subst hw
      by_cases hi : i' = j
      · subst hi; simp
      · simp [Pi.single_eq_of_ne hi]
    · simp [Pi.single_eq_of_ne hw]
  have := h _ hz w i
  simpa [mv, Matrix.mulVec_single_one] using this

variable {D : Datum p} {L : Link D G} {β : G.Cˣ}

private theorem core (A : PFrame L β) {P P' Q Q' R S : MF G}
    (hP : ∀ w, P' w * R w = 1) (hQ : ∀ w, Q' w * S w = 1)
    (h : ∀ x, IntL (mv P' (A.T x)) → IntL (mv Q' (A.T' x)) → IntL (mv P (A.T x)) ∧ IntL (mv Q (A.T' x)))
    {z z' : Loc G} (hz : IntL z) (hz' : IntL z') :
    IntL (mv (fun w => P w * R w) z) ∧ IntL (mv (fun w => Q w * S w) z') := by
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ((small P).and ((small P').and ((small Q).and (small Q')))).exists
  obtain ⟨x, a', b', ha', hb', hT, hT'⟩ := A.dense (mv R z) (mv S z') k
  have e1 : ∀ B : MF G, mv B (A.T x) = mv (fun w => B w * R w) z + mv (sc k B) a' := fun B => by
    rw [hT, mv_add_sc, mv_mv]
  have e2 : ∀ B : MF G, mv B (A.T' x) = mv (fun w => B w * S w) z' + mv (sc k B) b' := fun B => by
    rw [hT', mv_add_sc, mv_mv]
  have h1 : IntL (mv P' (A.T x)) := by
    rw [e1, show (fun w => P' w * R w) = (fun _ => 1 : MF G) from funext hP, mv_one]
    exact intL_add hz (mv_int hk2 ha')
  have h2 : IntL (mv Q' (A.T' x)) := by
    rw [e2, show (fun w => Q' w * S w) = (fun _ => 1 : MF G) from funext hQ, mv_one]
    exact intL_add hz' (mv_int hk4 hb')
  obtain ⟨r1, r2⟩ := h x h1 h2
  rw [e1] at r1
  rw [e2] at r2
  constructor
  · simpa using intL_sub r1 (mv_int hk1 ha')
  · simpa using intL_sub r2 (mv_int hk3 hb')

private def Pm (g : Gp G) : MF G :=
  fun w => (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))

private def Gm (g : Gp G) : MF G := fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w))

private def sca (t : ℚ_[p]) (w : Fin G.m) : G.Fw w := algebraMap ℚ_[p] (G.Fw w) t

private def Bm (d : ∀ w : Fin G.m, G.Fw w) (g : Gp G) : MF G :=
  fun w => (d w * sca ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) w) • (Gm g w)ᵀ

private def Qi (d : ∀ w : Fin G.m, G.Fw w) (g : Gp G) : MF G :=
  fun w => (sca (g.1 : ℚ_[p]) w * (d w)⁻¹) • (Pm g w)ᵀ

private theorem pm_gm (g : Gp G) (w : Fin G.m) : Pm g w * Gm g w = 1 := Units.inv_mul _

private theorem gm_pm (g : Gp G) (w : Fin G.m) : Gm g w * Pm g w = 1 := Units.mul_inv _

private theorem norm_sca (t : ℚ_[p]) (w : Fin G.m) : ‖(sca t w : PadicAlgCl p)‖ = ‖t‖ :=
  norm_algebraMap' (PadicAlgCl p) t

private theorem pair_mv (t : ℚ_[p]) (a z : Loc G) (B : MF G) :
    t * pairL a (mv B z) = pairL (fun w => sca t w • ((B w)ᵀ *ᵥ a w)) z := by
  simp only [pairL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (sca t w • ((B w)ᵀ *ᵥ a w)) ⬝ᵥ z w = t • (a w ⬝ᵥ mv B z w) := by
    rw [smul_dotProduct, smul_eq_mul, Algebra.smul_def t, mv, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rfl
  rw [e, map_smul, smul_eq_mul]

private theorem mem_iff {d : ∀ w : Fin G.m, G.Fw w}
    (hd : ∀ a : Loc G, (∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w))
    (A : PFrame L β) (g : Gp G) (x : VQ D) :
    A.Mem g x ↔ IntL (mv (Pm g) (A.T x)) ∧ IntL (mv (Bm d g) (A.T' x)) := by
  have key : (∀ z : Loc G, IntL z →
      ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (mv (Gm g) z)‖ ≤ 1) ↔ IntL (mv (Bm d g) (A.T' x)) := by
    simp_rw [pair_mv]
    rw [hd]
    have e : (fun w => d w • sca ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) w • ((Gm g w)ᵀ *ᵥ A.T' x w)) = mv (Bm d g) (A.T' x) := by
      funext w
      simp only [mv, Bm, Matrix.smul_mulVec, smul_smul]
    rw [e]
  exact and_congr Iff.rfl key

private theorem bq {d : ∀ w : Fin G.m, G.Fw w} (hd0 : ∀ w, d w ≠ 0) (g g' : Gp G) (w : Fin G.m) :
    Bm d g w * Qi d g' w = sca ((g.1⁻¹ * g'.1 : ℚ_[p]ˣ) : ℚ_[p]) w • (Pm g' w * Gm g w)ᵀ := by
  simp only [Bm, Qi, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.transpose_mul]
  congr 1
  have e : sca ((g.1⁻¹ * g'.1 : ℚ_[p]ˣ) : ℚ_[p]) w = sca ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) w * sca (g'.1 : ℚ_[p]) w := by
    simp [sca, Units.val_mul, map_mul]
  rw [e]
  field_simp [hd0 w]

private theorem bq_self {d : ∀ w : Fin G.m, G.Fw w} (hd0 : ∀ w, d w ≠ 0) (g : Gp G) (w : Fin G.m) :
    Bm d g w * Qi d g w = 1 := by
  rw [bq hd0, pm_gm]
  simp [sca]

private theorem half {d : ∀ w : Fin G.m, G.Fw w} (hd0 : ∀ w, d w ≠ 0)
    (hd : ∀ a : Loc G, (∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w))
    (hw : Nonempty (Fin G.m)) (A : PFrame L β) (g g' : Gp G) (h : ∀ x, A.Mem g' x → A.Mem g x) :
    IntM (fun w => Pm g w * Gm g' w) ∧ ‖((g.1⁻¹ * g'.1 : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := by
  have hc : ∀ z : Loc G, IntL z → IntL (mv (fun w => Pm g w * Gm g' w) z) ∧ IntL (mv (fun w => Bm d g w * Qi d g' w) z) :=
    fun z hz => core A (P' := Pm g') (Q' := Bm d g') (pm_gm g') (bq_self hd0 g')
      (fun x h1 h2 => (mem_iff hd A g x).1 (h x ((mem_iff hd A g' x).2 ⟨h1, h2⟩))) hz hz
  have h1 : IntM (fun w => Pm g w * Gm g' w) := intM_of fun z hz => (hc z hz).1
  have h2 : IntM (fun w => Bm d g w * Qi d g' w) := intM_of fun z hz => (hc z hz).2
  refine ⟨h1, ?_⟩
  have h1t : IntM (fun w => (Pm g w * Gm g' w)ᵀ) := fun w i j => h1 w j i
  have h3 := intM_mul h2 h1t
  obtain ⟨w⟩ := hw
  have i : Fin G.n := ⟨0, G.n_pos⟩
  have e : Bm d g w * Qi d g' w * (Pm g w * Gm g' w)ᵀ = sca ((g.1⁻¹ * g'.1 : ℚ_[p]ˣ) : ℚ_[p]) w • 1 := by
    rw [bq hd0, Matrix.smul_mul, ← Matrix.transpose_mul]
    have : Pm g w * Gm g' w * (Pm g' w * Gm g w) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Gm g' w), gm_pm, Matrix.one_mul, pm_gm]
    rw [this, Matrix.transpose_one]
  have h4 : ‖(((Bm d g w * Qi d g' w * (Pm g w * Gm g' w)ᵀ) i i : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := h3 w i i
  rw [e] at h4
  simpa [Matrix.smul_apply, norm_sca] using h4

private theorem inv_val (g g' : Gp G) (w : Fin G.m) :
    ((((g⁻¹ * g').2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) = Pm g' w * Gm g w := by
  have e : (((g⁻¹ * g').2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) = (g'.2 w)⁻¹ * g.2 w := by
    show ((g.2 w)⁻¹ * g'.2 w)⁻¹ = _
    rw [_root_.mul_inv_rev, _root_.inv_inv]
  rw [e]
  rfl

private theorem norm_swap (g g' : Gp G) :
    ‖((g'.1⁻¹ * g.1 : ℚ_[p]ˣ) : ℚ_[p])‖ = ‖((g.1⁻¹ * g'.1 : ℚ_[p]ˣ) : ℚ_[p])‖⁻¹ := by
  have e : (g'.1⁻¹ * g.1 : ℚ_[p]ˣ) = (g.1⁻¹ * g'.1)⁻¹ := by
    rw [_root_.mul_inv_rev, _root_.inv_inv]
  rw [e, Units.val_inv_eq_inv_val, norm_inv]

private theorem intPt_of {g g' : Gp G} (hH : IntM (fun w => Pm g w * Gm g' w))
    (hI : IntM (fun w => Pm g' w * Gm g w)) (hs : ‖((g.1⁻¹ * g'.1 : ℚ_[p]ˣ) : ℚ_[p])‖ = 1) :
    IntPt (g⁻¹ * g') := by
  refine ⟨hs, fun w i j => ⟨hH w i j, ?_⟩⟩
  rw [inv_val]
  exact hI w i j

private theorem mono {d : ∀ w : Fin G.m, G.Fw w} (hd0 : ∀ w, d w ≠ 0)
    (hd : ∀ a : Loc G, (∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w))
    (A : PFrame L β) (g g' : Gp G) (hH : IntM (fun w => Pm g w * Gm g' w))
    (hI : IntM (fun w => Pm g' w * Gm g w)) (hs : ‖((g'.1⁻¹ * g.1 : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1)
    (x : VQ D) (hx : A.Mem g x) : A.Mem g' x := by
  obtain ⟨h1, h2⟩ := (mem_iff hd A g x).1 hx
  refine (mem_iff hd A g' x).2 ⟨?_, ?_⟩
  · have e : mv (Pm g') (A.T x) = mv (fun w => Pm g' w * Gm g w) (mv (Pm g) (A.T x)) := by
      rw [mv_mv]
      congr 1
      funext w
      rw [Matrix.mul_assoc, gm_pm, Matrix.mul_one]
    rw [e]
    exact mv_int hI h1
  · have hB : IntM (fun w => Bm d g' w * Qi d g w) := fun w i j => by
      show ‖(((Bm d g' w * Qi d g w) i j : G.Fw w) : PadicAlgCl p)‖ ≤ 1
      rw [bq hd0, Matrix.smul_apply, smul_eq_mul]
      exact int_mul (by rw [norm_sca]; exact hs) (hH w j i)
    have e : mv (Bm d g') (A.T' x) = mv (fun w => Bm d g' w * Qi d g w) (mv (Bm d g) (A.T' x)) := by
      rw [mv_mv]
      congr 1
      funext w
      rw [Matrix.mul_assoc, _root_.mul_eq_one_comm.1 (bq_self hd0 g w), Matrix.mul_one]
    rw [e]
    exact mv_int hB h2

end UpperTheory.Gal.W2.PeriodInjective

open UpperTheory.Gal.W2.PeriodInjective in
theorem UpperTheory.Gal.W2.pkInj_of :
    UpperTheory.Gal.W2.MemDual → UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.PkInj := by
  intro hMD hEA p _ D G L β A g g'
  obtain ⟨d, hd0, hd⟩ := hMD p G
  have hw : Nonempty (Fin G.m) := by
    obtain ⟨w, -⟩ := hEA p G ((IsAlgClosed.lift : G.F →ₐ[ℚ] PadicAlgCl p) : G.F →+* PadicAlgCl p)
    exact ⟨w⟩
  constructor
  · intro h
    obtain ⟨a1, a2⟩ := half hd0 hd hw A g g' fun x => (h x).2
    obtain ⟨b1, b2⟩ := half hd0 hd hw A g' g fun x => (h x).1
    refine intPt_of a1 b1 (le_antisymm a2 ?_)
    rw [norm_swap] at b2
    exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 b2
  · intro h x
    have hH : IntM (fun w => Pm g w * Gm g' w) := fun w i j => (h.2 w i j).1
    have hI : IntM (fun w => Pm g' w * Gm g w) := fun w i j => by
      have h2 := (h.2 w i j).2
      rw [inv_val] at h2
      exact h2
    have hs : ‖((g.1⁻¹ * g'.1 : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := h.1
    exact ⟨mono hd0 hd A g g' hH hI (by rw [norm_swap, hs, inv_one]) x,
      mono hd0 hd A g' g hI hH hs.le x⟩
