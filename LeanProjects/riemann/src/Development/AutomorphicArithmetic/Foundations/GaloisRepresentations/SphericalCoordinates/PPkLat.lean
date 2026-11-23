import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem norm_nat_le {p : ℕ} [Fact p.Prime] (n : ℕ) : ‖(n : PadicAlgCl p)‖ ≤ 1 := by
  have h : (n : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (n : ℚ_[p]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact_mod_cast Padic.norm_int_le_one (n : ℤ)

private theorem norm_nat_cop {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : m.Coprime p) : ‖(m : PadicAlgCl p)‖ = 1 := by
  have h : (m : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (m : ℚ_[p]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  have h1 : ¬ ‖((m : ℤ) : ℚ_[p])‖ < 1 := by
    intro hd0
    have hd : (p : ℤ) ∣ (m : ℤ) := by
      rw [← PadicInt.norm_int_lt_one_iff_dvd]
      simpa [PadicInt.norm_def] using hd0
    have : p ∣ m := Int.natCast_dvd_natCast.1 hd
    exact hp.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hm this dvd_rfl)
  have h2 : ‖((m : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one _
  have := le_antisymm h2 (not_lt.1 h1)
  exact_mod_cast this

private theorem norm_p_lt {p : ℕ} [hp : Fact p.Prime] : ‖(p : PadicAlgCl p)‖ < 1 := by
  have h : (p : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

private theorem norm_int_emb {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (τ : F →+* PadicAlgCl p) {y : F} (h : IsIntegral ℤ y) : ‖τ y‖ ≤ 1 := by
  have h1 : IsIntegral ℤ (τ y) := h.map τ.toIntAlgHom
  exact GlobalTheory.CoefCoord.norm_le_one_of_isIntegral _ (h1.tower_top)

private theorem pow_bd {p : ℕ} [Fact p.Prime] {ι' : Type} [Fintype ι'] (f : ι' → PadicAlgCl p) :
    ∃ j : ℕ, ∀ i, ‖(p : PadicAlgCl p) ^ j * f i‖ ≤ 1 := by
  have h1 : ∀ i, ∃ j : ℕ, ‖(p : PadicAlgCl p) ^ j * f i‖ ≤ 1 := by
    intro i
    by_cases h0 : f i = 0
    · exact ⟨0, by simp [h0]⟩
    have hpos : 0 < ‖f i‖⁻¹ := inv_pos.2 (norm_pos_iff.2 h0)
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hpos (norm_p_lt (p := p))
    refine ⟨j, ?_⟩
    rw [norm_mul, norm_pow]
    calc _ ≤ ‖f i‖⁻¹ * ‖f i‖ := by gcongr
      _ ≤ 1 := by rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  choose J hJ using h1
  refine ⟨Finset.univ.sup J, fun i => ?_⟩
  have hle : J i ≤ Finset.univ.sup J := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  rw [hr, pow_add, _root_.mul_comm ((p : PadicAlgCl p) ^ J i), _root_.mul_assoc, norm_mul, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) norm_p_lt.le) (norm_nonneg _) (hJ i)

private noncomputable def mv {p : ℕ} [Fact p.Prime] {G : HTGroup p} (A : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w))
    (a : Loc G) : Loc G :=
  fun w => A w *ᵥ a w

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

private theorem intL_zero : IntL (0 : Loc G) := fun w i => by simp

private theorem intL_add {a b : Loc G} (ha : IntL a) (hb : IntL b) : IntL (a + b) := fun w i =>
  (PadicAlgCl.isNonarchimedean p (a w i : PadicAlgCl p) (b w i)).trans (max_le (ha w i) (hb w i))

private theorem intL_neg {a : Loc G} (ha : IntL a) : IntL (-a) := fun w i => by
  show ‖-(a w i : PadicAlgCl p)‖ ≤ 1
  rw [norm_neg]; exact ha w i

private theorem intL_scal (t : ∀ w, G.Fw w) (ht : ∀ w, ‖(t w : PadicAlgCl p)‖ ≤ 1) {a : Loc G} (ha : IntL a) :
    IntL (fun w => t w • a w) := fun w i => by
  show ‖(t w : PadicAlgCl p) * (a w i : PadicAlgCl p)‖ ≤ 1
  rw [norm_mul]; exact mul_le_one₀ (ht w) (norm_nonneg _) (ha w i)

private theorem coe_nsmul (N : ℕ) (a : Loc G) (w : Fin G.m) (i : Fin G.n) :
    (((N • a) w i : G.Fw w) : PadicAlgCl p) = (N : PadicAlgCl p) * (a w i : PadicAlgCl p) := by
  show ((N • a w i : G.Fw w) : PadicAlgCl p) = _
  simp [nsmul_eq_mul]

private theorem intL_nsmul (N : ℕ) {a : Loc G} (ha : IntL a) : IntL (N • a) := fun w i => by
  rw [coe_nsmul, norm_mul]; exact mul_le_one₀ (norm_nat_le N) (norm_nonneg _) (ha w i)

private theorem intL_of_nsmul {m : ℕ} (hm : m.Coprime p) {a : Loc G} (h : IntL (m • a)) : IntL a := fun w i => by
  have := h w i
  rwa [coe_nsmul, norm_mul, norm_nat_cop hm, _root_.one_mul] at this

private theorem intL_le {j k : ℕ} (hjk : j ≤ k) {a : Loc G} (h : IntL (p ^ j • a)) : IntL (p ^ k • a) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_comm, pow_add, mul_smul]
  exact intL_nsmul _ h

private theorem mv_add (A : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (a b : Loc G) :
    mv A (a + b) = mv A a + mv A b := funext fun w => Matrix.mulVec_add _ _ _

private theorem mv_neg (A : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (a : Loc G) :
    mv A (-a) = -mv A a := funext fun w => Matrix.mulVec_neg _ _

private theorem mv_zero (A : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) :
    mv A (0 : Loc G) = 0 := funext fun w => Matrix.mulVec_zero _

private theorem mv_nsmul (A : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (N : ℕ) (a : Loc G) :
    mv A (N • a) = N • mv A a := _root_.funext fun w => by
  show A w *ᵥ (N • a w) = N • (A w *ᵥ a w)
  exact Matrix.mulVec_smul _ _ _

private theorem mv_scal (A : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (t : ∀ w, G.Fw w) (a : Loc G) :
    mv A (fun w => t w • a w) = fun w => t w • mv A a w := funext fun w => Matrix.mulVec_smul _ _ _

private theorem mv_mv {A B : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)} (h : ∀ w, B w * A w = 1) (a : Loc G) :
    mv B (mv A a) = a := funext fun w => by
  show B w *ᵥ (A w *ᵥ a w) = a w
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

private theorem mv_bd (A : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)) :
    ∃ j : ℕ, ∀ a : Loc G, IntL a → IntL (p ^ j • mv A a) := by
  obtain ⟨j, hj⟩ := pow_bd (p := p) (fun q : Fin G.m × Fin G.n × Fin G.n => (A q.1 q.2.1 q.2.2 : PadicAlgCl p))
  refine ⟨j, fun a ha w i => ?_⟩
  rw [coe_nsmul]
  have e : ((mv A a w i : G.Fw w) : PadicAlgCl p) = ∑ k, (A w i k : PadicAlgCl p) * (a w k : PadicAlgCl p) := by
    simp [mv, Matrix.mulVec, dotProduct]
  rw [e, Finset.mul_sum]
  refine Finset.sum_induction _ (fun y : PadicAlgCl p => ‖y‖ ≤ 1)
    (fun u v hu hv => (PadicAlgCl.isNonarchimedean p u v).trans (max_le hu hv)) (by simp) (fun k _ => ?_)
  rw [← _root_.mul_assoc, norm_mul]
  refine mul_le_one₀ ?_ (norm_nonneg _) (ha w k)
  simpa using hj (w, i, k)

private theorem vec_bd {α : Type} (s : Finset α) (f : α → Loc G) :
    ∃ j : ℕ, ∀ x ∈ s, IntL (p ^ j • f x) := by
  obtain ⟨j, hj⟩ := pow_bd (p := p) (fun q : s × (Fin G.m × Fin G.n) => (f q.1 q.2.1 q.2.2 : PadicAlgCl p))
  refine ⟨j, fun x hx w i => ?_⟩
  rw [coe_nsmul]
  simpa using hj (⟨x, hx⟩, w, i)

private theorem core (hPL : PLatOf) {D : Datum p} (T T' : VQ D →+ Loc G)
    (P P' Q Q' : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w))
    (hP : ∀ w, P' w * P w = 1) (hQ : ∀ w, Q' w * Q w = 1)
    (hact : ∀ c : D.O, ∃ t t' : ∀ w, G.Fw w, (∀ w, ‖(t w : PadicAlgCl p)‖ ≤ 1) ∧ (∀ w, ‖(t' w : PadicAlgCl p)‖ ≤ 1) ∧
      ∀ x, T (actQ D c x) = (fun w => t w • T x w) ∧ T' (actQ D c x) = (fun w => t' w • T' x w))
    (hb : ∃ (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ ∧
      ∀ x, IntL (T x) → IntL (T' x) → ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))) :
    ∃ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ IntL (mv P (T x)) ∧ IntL (mv Q (T' x))) ∧ IsPLat D M := by
  let M : AddSubgroup (VQ D) :=
    { carrier := {x | IntL (mv P (T x)) ∧ IntL (mv Q (T' x))}
      add_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_⟩
        · rw [map_add, mv_add]; exact intL_add ha.1 hb.1
        · rw [map_add, mv_add]; exact intL_add ha.2 hb.2
      zero_mem' := by
        refine ⟨?_, ?_⟩
        · rw [map_zero, mv_zero]; exact intL_zero
        · rw [map_zero, mv_zero]; exact intL_zero
      neg_mem' := fun {a} ha => by
        refine ⟨?_, ?_⟩
        · rw [map_neg, mv_neg]; exact intL_neg ha.1
        · rw [map_neg, mv_neg]; exact intL_neg ha.2 }
  have hMem : ∀ x, x ∈ M ↔ IntL (mv P (T x)) ∧ IntL (mv Q (T' x)) := fun x => Iff.rfl
  refine ⟨M, hMem, ?_⟩
  obtain ⟨s, k₀, hs, hbd⟩ := hb
  obtain ⟨j1, h1⟩ := mv_bd (p := p) P'
  obtain ⟨j2, h2⟩ := mv_bd (p := p) Q'
  obtain ⟨j3, h3⟩ := mv_bd (p := p) P
  obtain ⟨j4, h4⟩ := mv_bd (p := p) Q
  obtain ⟨j5, h5⟩ := vec_bd (p := p) s (fun x => T x)
  obtain ⟨j6, h6⟩ := vec_bd (p := p) s (fun x => T' x)
  refine hPL p D M s (k₀ + (j1 + j2) + (j3 + j4 + j5 + j6)) hs ?_ ?_ ?_ ?_
  · intro c x hx
    obtain ⟨t, t', ht, ht', he⟩ := hact c
    obtain ⟨hx1, hx2⟩ := (hMem x).1 hx
    refine (hMem _).2 ⟨?_, ?_⟩
    · rw [(he x).1, mv_scal]; exact intL_scal t ht hx1
    · rw [(he x).2, mv_scal]; exact intL_scal t' ht' hx2
  · intro m x hm hx
    obtain ⟨hx1, hx2⟩ := (hMem _).1 hx
    rw [map_nsmul, mv_nsmul] at hx1 hx2
    exact (hMem x).2 ⟨intL_of_nsmul hm hx1, intL_of_nsmul hm hx2⟩
  · intro x hx
    refine (hMem _).2 ⟨?_, ?_⟩
    · have h := h3 _ (h5 x hx)
      rw [mv_nsmul, ← mul_smul, ← pow_add] at h
      rw [map_nsmul, mv_nsmul]
      exact intL_le (by omega) h
    · have h := h4 _ (h6 x hx)
      rw [mv_nsmul, ← mul_smul, ← pow_add] at h
      rw [map_nsmul, mv_nsmul]
      exact intL_le (by omega) h
  · intro x hx
    obtain ⟨hx1, hx2⟩ := (hMem x).1 hx
    have a1 : IntL (T (p ^ (j1 + j2) • x)) := by
      have h := h1 _ hx1
      rw [mv_mv hP] at h
      rw [map_nsmul]
      exact intL_le (by omega) h
    have a2 : IntL (T' (p ^ (j1 + j2) • x)) := by
      have h := h2 _ hx2
      rw [mv_mv hQ] at h
      rw [map_nsmul]
      exact intL_le (by omega) h
    obtain ⟨m, hm, hc⟩ := hbd _ a1 a2
    refine ⟨m, hm, ?_⟩
    have e : (m * p ^ (k₀ + (j1 + j2) + (j3 + j4 + j5 + j6))) • x =
        p ^ (j3 + j4 + j5 + j6) • ((m * p ^ k₀) • (p ^ (j1 + j2) • x)) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      ring
    rw [e]
    exact nsmul_mem hc _

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.W2.pkLat_of :
    UpperTheory.Gal.W2.OOnto → UpperTheory.Gal.W2.MemDual → UpperTheory.Gal.W2.PLatOf → UpperTheory.Gal.W2.PkLat := by
  intro hO hMD hPL p _ D G L β A hm g
  obtain ⟨d, hd, hdual⟩ := hMD p G
  let c : ℚ_[p] := ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])
  have hc : c ≠ 0 := Units.ne_zero _
  let gm : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) := fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w))
  let gi : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    fun w => (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))
  have hgi : ∀ w, gm w * gi w = 1 := fun w => by simp [gm, gi]
  let Q : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) := fun w => d w • c • (gm w)ᵀ
  let Q' : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w) := fun w => (d w)⁻¹ • c⁻¹ • (gi w)ᵀ
  have hQ : ∀ w, Q' w * Q w = 1 := fun w => by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul, ← Matrix.transpose_mul, hgi, Matrix.transpose_one]
    rw [smul_comm c (d w)⁻¹, smul_inv_smul₀ (hd w), smul_inv_smul₀ hc]
  have hdu : ∀ a : Loc G, (∀ z : Loc G, IntL z → ‖c * pairL a (mv gm z)‖ ≤ 1) ↔ IntL (mv Q a) := by
    intro a
    have e : ∀ z : Loc G, pairL (fun w => c • ((gm w)ᵀ *ᵥ a w)) z = c * pairL a (mv gm z) := by
      intro z
      simp only [pairL, Finset.mul_sum, smul_dotProduct, map_smul, Matrix.mulVec_transpose, mv,
        ← Matrix.dotProduct_mulVec, smul_eq_mul]
    have e2 : mv Q a = fun w => d w • c • ((gm w)ᵀ *ᵥ a w) := by
      funext w
      simp only [mv, Q, Matrix.smul_mulVec]
    rw [e2, ← hdual]
    simp only [e]
  have hact : ∀ c' : D.O, ∃ t t' : ∀ w, G.Fw w, (∀ w, ‖(t w : PadicAlgCl p)‖ ≤ 1) ∧ (∀ w, ‖(t' w : PadicAlgCl p)‖ ≤ 1) ∧
      ∀ x, A.T (actQ D c' x) = (fun w => t w • A.T x w) ∧ A.T' (actQ D c' x) = (fun w => t' w • A.T' x w) := by
    intro c'
    obtain ⟨c₀, rfl⟩ := hO p D hm c'
    have hint : IsIntegral ℤ (L.e (c₀ : D.F)) := c₀.2.map L.e.toRingHom.toIntAlgHom
    have hint' : IsIntegral ℤ (IsCMField.complexConj G.F (L.e (c₀ : D.F))) :=
      hint.map (IsCMField.complexConj G.F : G.F →+* G.F).toIntAlgHom
    refine ⟨fun w => G.embW w (L.e (c₀ : D.F)), fun w => G.embW w (IsCMField.complexConj G.F (L.e (c₀ : D.F))),
      fun w => norm_int_emb (G.emb w) hint, fun w => norm_int_emb (G.emb w) hint', fun x => ⟨?_, ?_⟩⟩
    · funext w
      rw [← L.rep_F, A.act, G.rho_F]
      ext i
      simp [HTGroup.embW, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    · funext w
      have hs : (β : G.C) * sh G (algebraMap G.F G.C (L.e (c₀ : D.F))) * ((β⁻¹ : G.Cˣ) : G.C) =
          algebraMap G.F G.C (IsCMField.complexConj G.F (L.e (c₀ : D.F))) := by
        rw [sh_algebraMap, ← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      rw [← L.rep_F, A.act', hs, G.rho_F]
      ext i
      simp [HTGroup.embW, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  obtain ⟨M, hM, hLat⟩ := core hPL A.T A.T' gi gm Q Q' hgi hQ hact A.bound
  refine ⟨M, fun x => ?_, hLat⟩
  rw [hM x, ← hdu]
  rfl
