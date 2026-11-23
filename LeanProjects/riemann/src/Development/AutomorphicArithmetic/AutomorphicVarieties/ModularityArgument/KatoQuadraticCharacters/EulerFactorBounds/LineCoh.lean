import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.NatCastNeOfCop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TrConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelElemExponentShimura
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

noncomputable section

namespace UpperTheory.V.Z.Kato.Nb.LineCohomology

open UpperTheory.V.Z.Kato.Nb.TrConj

section Cg
variable {K : Type} [Field K] {m : ℕ}

private theorem cg_refl (a : Kˣ) : Cgr m a a := ⟨1, by simp⟩

private theorem cg_symm {a b : Kˣ} (h : Cgr m a b) : Cgr m b a := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k⁻¹, by simp⟩

private theorem cg_mul {a b a' b' : Kˣ} (h : Cgr m a b) (h' : Cgr m a' b') : Cgr m (a * a') (b * b') := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨k', rfl⟩ := h'
  exact ⟨k * k', by rw [mul_pow, mul_mul_mul_comm]⟩

private theorem cg_trans {a b c : Kˣ} (h : Cgr m a b) (h' : Cgr m b c) : Cgr m a c := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨k', rfl⟩ := h'
  exact ⟨k' * k, by rw [mul_pow, mul_assoc]⟩

private theorem cg_prod {ι : Type} (S : Finset ι) {a b : ι → Kˣ} (h : ∀ i ∈ S, Cgr m (a i) (b i)) :
    Cgr m (∏ i ∈ S, a i) (∏ i ∈ S, b i) := by
  choose! k hk using h
  exact ⟨∏ i ∈ S, k i, by rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl hk⟩

private theorem cg_pow {a b : Kˣ} (k : ℕ) (h : Cgr m a b) : Cgr m (a ^ k) (b ^ k) := cgr_map (powMonoidHom k) h

end Cg

private def sc {M : ℕ} (k : ZMod M) (u : Row M) : Row M := ![u 0, k * u 1]

private theorem sc_sc {M : ℕ} (k k' : ZMod M) (u : Row M) : sc k (sc k' u) = sc (k * k') u := by
  simp [sc, mul_assoc]

private theorem sc_one {M : ℕ} (u : Row M) : sc 1 u = u := by
  funext i
  fin_cases i <;> simp [sc]

private theorem rt_apply {M : ℕ} (x : Row M) (γ : SL(2, ℤ)) (i : Fin 2) :
    rt x γ i = x 0 * (en γ 0 i : ZMod M) + x 1 * (en γ 1 i : ZMod M) := by
  simp [rt, en, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem rt_mul {M : ℕ} (x : Row M) (γ γ' : SL(2, ℤ)) : rt (rt x γ) γ' = rt x (γ * γ') := by
  simp only [rt, Matrix.vecMul_vecMul, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

private theorem rt_one {M : ℕ} (x : Row M) : rt x 1 = x := by
  simp [rt]

private theorem ne_rt {M : ℕ} {x : Row M} (γ : SL(2, ℤ)) (h : (2 : ZMod M) • x ≠ 0) : (2 : ZMod M) • rt x γ ≠ 0 := by
  intro h0
  apply h
  have e : rt ((2 : ZMod M) • rt x γ) γ⁻¹ = (2 : ZMod M) • x := by
    rw [rt, Matrix.smul_vecMul, ← rt, rt_mul, mul_inv_cancel, rt_one]
  rw [← e, h0, rt, Matrix.zero_vecMul]

private theorem ne_sc {M : ℕ} {x : Row M} {k : ZMod M} (hk : IsUnit k) (h : (2 : ZMod M) • x ≠ 0) :
    (2 : ZMod M) • sc k x ≠ 0 := by
  intro h0
  apply h
  have h1 := congrFun h0 0
  have h2 := congrFun h0 1
  simp only [sc, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h1 h2
  funext i
  fin_cases i
  · exact h1
  · exact hk.mul_right_eq_zero.1 (by rw [← h2]; simp; ring)

private def Cj {M : ℕ} (k : ZMod M) (γ γ' : SL(2, ℤ)) : Prop :=
  (en γ' 0 0 : ZMod M) = en γ 0 0 ∧ (en γ' 0 1 : ZMod M) = k * en γ 0 1 ∧ k * (en γ' 1 0 : ZMod M) = en γ 1 0 ∧
    (en γ' 1 1 : ZMod M) = en γ 1 1

private theorem rt_sc {M : ℕ} {k : ZMod M} {γ γ' : SL(2, ℤ)} (h : Cj k γ γ') (v : Row M) :
    rt (sc k v) γ' = sc k (rt v γ) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, rt_apply, sc, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h0, ← h2]; ring
  · simp only [Fin.mk_one, rt_apply, sc, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h1, h3]; ring

private theorem mem0 (p : ℕ) (η γ : SL(2, ℤ)) : η * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 p ↔
    (en η 1 0 : ZMod p) * en γ 1 1 - en η 1 1 * en γ 1 0 = 0 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, sub_eq_add_neg]

private theorem conjD {p : ℕ} {β : SL(2, ℤ)} (h : β ∈ CongruenceSubgroup.Gamma0 p) : ∃ β' : SL(2, ℤ),
    !![(p : ℤ), 0; 0, 1] * (β : Matrix (Fin 2) (Fin 2) ℤ) = (β' : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, 1] ∧
      ∀ M : ℕ, Cj (p : ZMod M) β β' := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 h)
  have hd := β.det_coe
  rw [Matrix.det_fin_two] at hd
  have hc' : en β 1 0 = p * c := hc
  refine ⟨⟨!![en β 0 0, p * en β 0 1; c, en β 1 1], ?_⟩, ?_, fun M => ⟨rfl, ?_, ?_, rfl⟩⟩
  · rw [Matrix.det_fin_two_of, ← hd, hc]; unfold en; ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [en, Matrix.mul_apply, Fin.sum_univ_two, hc, mul_comm]
  · simp [en]
  · rw [hc']; simp [en]

private def gam (p N : ℕ) : Option (Fin p) → SL(2, ℤ)
  | none => 1
  | some j => ⟨!![0, -1; 1, N * ((j : ℕ) : ℤ)], by simp [Matrix.det_fin_two_of]⟩

private theorem gam_row (p N : ℕ) (o : Option (Fin p)) (i : Fin 2) : lin p N o i = (en (gam p N o) 1 i : ZMod p) := by
  cases o <;> fin_cases i <;> simp [gam, lin, en]

private theorem gam_surj (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0) (η : SL(2, ℤ)) :
    ∃ o, η * (gam p N o)⁻¹ ∈ CongruenceSubgroup.Gamma0 p := by
  simp only [mem0, ← gam_row]
  by_cases h : (en η 1 0 : ZMod p) = 0
  · exact ⟨none, by simp [lin, h]⟩
  · refine ⟨some ⟨((en η 1 1 : ZMod p) / (N * en η 1 0)).val, ZMod.val_lt _⟩, ?_⟩
    simp [lin]
    field_simp
    ring

private theorem lin_inj (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0) (o o' : Option (Fin p))
    (h : lin p N o 0 * lin p N o' 1 - lin p N o 1 * lin p N o' 0 = 0) : o = o' := by
  cases o <;> cases o' <;> simp [lin] at h ⊢
  rename_i j j'
  have h2 : ((j : ℕ) : ZMod p) = ((j' : ℕ) : ZMod p) := mul_left_cancel₀ hN (by linear_combination -h)
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt j'.2] at h2
  exact Fin.ext h2

private theorem hP_eq (l p N : ℕ) (hN : N ≠ 0) (hl : l ≠ 0) (hc : Nat.Coprime p N) (o : Option (Fin p)) :
    ∃ δ : SL(2, ℤ), hP l p N o =
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * (!![(p : ℤ), 0; 0, 1] * (gam p N o : Matrix (Fin 2) (Fin 2) ℤ)) := by
  cases o with
  | none =>
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      (CongruenceSubgroup.Gamma0_mem.1 (GlobalTheory.KZ.Betti.isDiam_sgD hN hl hc).1.1)
    have hd := (sgD N l p).det_coe
    rw [Matrix.det_fin_two] at hd
    have hc' : en (sgD N l p) 1 0 / N = c := by
      rw [show en (sgD N l p) 1 0 = N * c from hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hN)]
    refine ⟨⟨!![en (sgD N l p) 0 0, N * en (sgD N l p) 0 1; c, en (sgD N l p) 1 1], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of, ← hd, hc]; unfold en; ring
    · simp [hP, gam, hc']
  | some j => exact ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩, by simp [hP, gam]⟩

private def zr (p : ℕ) {M : ℕ} (γ : SL(2, ℤ)) (x : Row M) : Row M := sc (p : ZMod M) (rt x γ⁻¹)

private theorem adj_row (p : ℕ) {M : ℕ} (γ δ : SL(2, ℤ)) (x : Row M) :
    x ᵥ* ((δ : Matrix (Fin 2) (Fin 2) ℤ) * (!![(p : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ))).adjugate.map
      (Int.castRingHom (ZMod M)) = rt (zr p γ x) δ⁻¹ := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.map_mul, Matrix.map_mul, ← Matrix.vecMul_vecMul,
    ← Matrix.vecMul_vecMul]
  unfold zr rt
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv]
  congr 1
  funext i
  fin_cases i <;> simp [sc, Matrix.adjugate_fin_two_of, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

private theorem ok_zr {p M : ℕ} (hp : IsUnit (p : ZMod M)) (γ : SL(2, ℤ)) {x y : Row M} (h : Ok x y) :
    Ok (zr p γ x) (zr p γ y) := ⟨ne_sc hp (ne_rt _ h.1), ne_sc hp (ne_rt _ h.2)⟩

private theorem zr_left {p M : ℕ} {β β' : SL(2, ℤ)} (h : Cj (p : ZMod M) β β') (γ : SL(2, ℤ)) (x : Row M) :
    rt (zr p (β * γ) x) β' = zr p γ x := by
  rw [zr, rt_sc h, rt_mul, mul_inv_rev, inv_mul_cancel_right, zr]

private theorem zr_right {p M : ℕ} (γ η : SL(2, ℤ)) (x : Row M) : zr p (γ * η) (rt x η) = zr p γ x := by
  rw [zr, rt_mul, mul_inv_rev, mul_inv_cancel_left, zr]

private theorem zr_gal {p M : ℕ} {e e' : ZMod M} (he : e * e' = 1) {η γ : SL(2, ℤ)} (h : Cj e η γ) (x : Row M) :
    zr p η (sc e' x) = sc e' (zr p γ x) := by
  have h1 := rt_sc h (rt (sc e' x) η⁻¹)
  rw [rt_mul, inv_mul_cancel, rt_one, sc_sc, he, sc_one] at h1
  have h2 : rt x γ⁻¹ = sc e (rt (sc e' x) η⁻¹) := by
    conv_lhs => rw [← h1]
    rw [rt_mul, mul_inv_cancel, rt_one]
  rw [zr, zr, h2, sc_sc, sc_sc]
  congr 1
  linear_combination (-(p : ZMod M)) * he

private theorem cj_down {L K : ℕ} (h : K ∣ L) {i : ℕ} {η γ : SL(2, ℤ)} (c : Cj (i : ZMod L) η γ) : Cj (i : ZMod K) η γ := by
  obtain ⟨h0, h1, h2, h3⟩ := c
  refine ⟨cast_down h h0, ?_, ?_, cast_down h h3⟩
  · simpa only [map_mul, map_natCast, map_intCast] using congrArg (ZMod.castHom h (ZMod K)) h1
  · simpa only [map_mul, map_natCast, map_intCast] using congrArg (ZMod.castHom h (ZMod K)) h2

private theorem rz_val {M : ℕ} [NeZero M] (x : Row M) : rz M (fun i => ((x i).val : ℤ)) = x := by
  funext i
  simp [rz]

private theorem rt_rz {M : ℕ} (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    rt (rz M a) γ = rz M fun i => a 0 * en γ 0 i + a 1 * en γ 1 i := by
  funext i
  simp [rt_apply, rz]

private theorem tp_rz (p M : ℕ) [NeZero p] (a : Fin 2 → ℤ) : tp p M (rz p a) = rz (p * M) ((M : ℤ) • a) := by
  funext i
  have h1 : (((rz p a i).val : ℤ)) = a i % (p : ℤ) := ZMod.val_intCast (a i)
  have h2 : tp p M (rz p a) i = (((M : ℤ) * (a i % (p : ℤ)) : ℤ) : ZMod (p * M)) := by
    rw [← h1, tp]; push_cast; rfl
  rw [h2]
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨a i / (p : ℤ), ?_⟩
  have := Int.emod_add_mul_ediv (a i) (p : ℤ)
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  linear_combination (-(M : ℤ)) * this

private theorem rt_up_tp (p M : ℕ) [NeZero p] [NeZero M] (u : Row M) (t : Row p) (γ : SL(2, ℤ)) :
    rt (up p M u + tp p M t) γ = up p M (rt u γ) + tp p M (rt t γ) := by
  rw [← rz_val u, ← rz_val t, rt_rz, rt_rz, up_rz, up_rz, tp_rz, tp_rz]
  funext i
  simp only [rt_apply, rz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem dn_up_tp (p M : ℕ) (u : Row M) (t : Row p) [NeZero M] (i : Fin 2) :
    dn p M (up p M u + tp p M t) i = p * u i := by
  unfold dn up tp
  rw [Pi.add_apply, map_add, map_natCast, map_natCast]
  simp

private theorem ne_up_tp {p M : ℕ} [NeZero M] (hp : IsUnit (p : ZMod M)) {u : Row M} (t : Row p)
    (h : (2 : ZMod M) • u ≠ 0) : (2 : ZMod (p * M)) • (up p M u + tp p M t) ≠ 0 := by
  intro h0
  apply h
  funext i
  have h1 := congrArg (ZMod.castHom (dvd_mul_left M p) (ZMod M)) (congrFun h0 i)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_ofNat, Pi.zero_apply, map_zero] at h1
  have h2 := dn_up_tp p M u t i
  unfold dn at h2
  rw [h2] at h1
  exact hp.mul_right_eq_zero.1 (by rw [← h1]; simp; ring)

private theorem prod_fib {G : Type} [CommMonoid G] (p M : ℕ) [NeZero p] [NeZero M] [NeZero (p * M)] (u : Row M)
    (S : Finset (Row (p * M))) (hS : ∀ z, z ∈ S ↔ z 0 = up p M (sc p u) 0 ∧ dn p M z 1 = sc (p : ZMod M) u 1)
    (f : Row (p * M) → G) : ∏ z ∈ S, f z = ∏ t : ZMod p, f (up p M u + tp p M ![0, t]) := by
  symm
  refine Finset.prod_nbij (fun t => up p M u + tp p M ![0, t]) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro t _
    rw [hS]
    exact ⟨by simp [up, tp, sc], dn_up_tp p M u _ 1⟩
  · intro s _ t _ h
    have h1 : ((M * s.val : ℕ) : ZMod (p * M)) = ((M * t.val : ℕ) : ZMod (p * M)) := congrFun (add_left_cancel h) 1
    rw [ZMod.natCast_eq_natCast_iff, mul_comm p M] at h1
    have h2 := Nat.ModEq.mul_left_cancel' (NeZero.ne M) h1
    rw [← ZMod.natCast_eq_natCast_iff] at h2
    simpa using h2
  · intro z hz
    obtain ⟨h0, h1⟩ := (hS z).1 hz
    have h : ZMod.castHom (dvd_mul_left M p) (ZMod M) (z 1 - up p M u 1) = 0 := by
      rw [map_sub, sub_eq_zero]
      refine h1.trans ?_
      unfold up
      rw [map_natCast]
      simp [sc]
    rw [← ZMod.natCast_zmod_val (z 1 - _), map_natCast, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have hlt : k < p := by
      have := ZMod.val_lt (z 1 - up p M u 1)
      rw [hk, mul_comm p M] at this
      exact Nat.lt_of_mul_lt_mul_left this
    refine ⟨(k : ZMod p), by simp, ?_⟩
    funext i
    fin_cases i
    · simpa [up, tp, sc] using h0.symm
    · change up p M u 1 + ((M * (k : ZMod p).val : ℕ) : ZMod (p * M)) = z 1
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ← hk, ZMod.natCast_zmod_val, add_sub_cancel]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem fac (X : Tower Ω ε) {m p N M : ℕ} [Fact p.Prime] [NeZero M] (hp : IsUnit (p : ZMod M))
    {b : Fam X (p * M)} (hb : Eqv X m (p * M) b) (o : Option (Fin p)) {x y : Row M} (h : Ok x y) :
    Cgr m (slU X (ofSL (gam p N o)) (pushH X p M b (zr p (gam p N o) x) (zr p (gam p N o) y)))
      (∏ i : ZMod p, ∏ j : ZMod p, b (up p M x + tp p M (i • lin p N o)) (up p M y + tp p M (j • lin p N o))) := by
  haveI : NeZero (p * M) := ⟨mul_ne_zero (NeZero.ne p) (NeZero.ne M)⟩
  have e : ∀ (v : Row M) (i : ZMod p), rt (up p M (rt v (gam p N o)⁻¹) + tp p M ![0, i]) (gam p N o) =
      up p M v + tp p M (i • lin p N o) := fun v i => by
    rw [rt_up_tp, rt_mul, inv_mul_cancel, rt_one]
    congr 2
    funext k
    simp [rt_apply, gam_row]
  unfold pushH zr
  rw [prod_fib p M _ _ (fun z => by rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]), map_prod]
  refine cg_prod _ fun i _ => ?_
  rw [prod_fib p M _ _ (fun z => by rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]), map_prod]
  refine cg_prod _ fun j _ => ?_
  rw [← e, ← e]
  exact (hb _ _ ⟨ne_up_tp hp _ (ne_rt _ h.1), ne_up_tp hp _ (ne_rt _ h.2)⟩).2 _

private theorem conj [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (p M : ℕ) [Fact p.Prime] [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (f : X.Kˣ)
    (γ : SL(2, ℤ)) : ∃ η : SL(2, ℤ), galU X s (slU X (ofSL η) f) = slU X (ofSL γ) (galU X s f) ∧
      Cj (cyc p s) η γ ∧ Cj (cyc M s) η γ := by
  obtain ⟨L, hL, hf⟩ := X.level f
  have h1 : 0 < p * M * L := Nat.mul_pos (Nat.mul_pos (NeZero.pos p) (NeZero.pos M)) hL
  obtain ⟨ζ, hζ, i, hi, hs, -⟩ := GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter p 0 _ h1 (by simp) s
  obtain ⟨η, hη⟩ := GlobalTheory.exists_sl2_conj_diag_zmod _ i hi γ
  have key : ∀ K : ℕ, K ∣ p * M * L → Cj (cyc K s) η γ := fun K hK => by
    obtain ⟨k, hk⟩ := hK
    have hK0 : K ≠ 0 := by rintro rfl; omega
    haveI : NeZero K := ⟨hK0⟩
    have ht : IsPrimitiveRoot (ζ ^ k) K := hζ.pow h1 (hk.trans (mul_comm _ _))
    have h2 : s (ζ ^ k) = (ζ ^ k) ^ i := by rw [map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]
    have h3 : ∀ z : Ω, z ^ K = 1 → s z = z ^ (cyc K s).val :=
      Classical.epsilon_spec (p := fun y : ZMod K => ∀ z : Ω, z ^ K = 1 → s z = z ^ y.val) ⟨(i : ZMod K), fun z hz => by
        obtain ⟨j, -, rfl⟩ := ht.eq_pow_of_pow_eq_one hz
        rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hz, map_pow, h2, ← pow_mul, mul_comm, pow_mul]⟩
    have hfin : IsOfFinOrder (ζ ^ k) := isOfFinOrder_iff_pow_eq_one.2 ⟨K, NeZero.pos _, ht.pow_eq_one⟩
    have h4 := hfin.pow_eq_pow_iff_modEq.1 (h2.symm.trans (h3 _ ht.pow_eq_one))
    rw [← ht.eq_orderOf] at h4
    rw [← ZMod.natCast_zmod_val (cyc K s), ← (ZMod.natCast_eq_natCast_iff _ _ _).2 h4]
    exact cj_down ⟨k, hk⟩ hη
  refine ⟨η, Units.ext ?_, key _ ⟨M * L, by ring⟩, key _ ⟨p * L, by ring⟩⟩
  exact X.recip _ f h1 (fun δ hδ => hf δ (gamma_le (dvd_mul_left L _) hδ)) ζ hζ s i (by rw [zpow_natCast, hs]) η γ
    (by simpa only [Int.cast_natCast] using hη)

private theorem cyc_inv [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) : cyc M s * cyc M s⁻¹ = 1 := by
  have h := (sSlD Ω ε X 1 one_pos).2.2.2.2.2.2.2 M
  have h1 : cycM M (1 : Ω ≃ₐ[ℚ] Ω) = 1 := by
    have := (h 1).2.1 1
    rw [mul_one] at this
    exact left_eq_mul.1 this
  rw [(h s).1, (h s⁻¹).1, ← Units.val_mul, ← (h s).2.1, mul_inv_cancel, h1, Units.val_one]

private def AA (X : Tower Ω ε) (p : ℕ) {M : ℕ} (a : Fam X M) (γ : SL(2, ℤ)) : Fam X M := fun x y =>
  slU X (ofSL γ) (a (zr p γ x) (zr p γ y))

private theorem AA_left (X : Tower Ω ε) {m p M : ℕ} (hp : IsUnit (p : ZMod M)) {a : Fam X M} (ha : EqvH X m p M a)
    {η γ : SL(2, ℤ)} (h : η * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 p) {x y : Row M} (hxy : Ok x y) :
    Cgr m (AA X p a η x y) (AA X p a γ x y) := by
  obtain ⟨β', h1, h2⟩ := conjD h
  have h3 := cgr_map (slU X (ofSL γ)) ((ha _ _ (ok_zr hp (η * γ⁻¹ * γ) hxy)).2 _ _ h1)
  rw [zr_left (h2 M), zr_left (h2 M), ← slU_mul, inv_mul_cancel_right] at h3
  exact h3

private theorem AA_perm (X : Tower Ω ε) {m p N M : ℕ} [Fact p.Prime] (hN : (N : ZMod p) ≠ 0) (hp : IsUnit (p : ZMod M))
    {a : Fam X M} (ha : EqvH X m p M a) (η : Option (Fin p) → SL(2, ℤ))
    (hη : ∀ o o', η o * (η o')⁻¹ ∈ CongruenceSubgroup.Gamma0 p → o = o') {x y : Row M} (hxy : Ok x y) :
    Cgr m (∏ o, AA X p a (η o) x y) (∏ o, AA X p a (gam p N o) x y) := by
  choose π hπ using fun o => gam_surj p N hN (η o)
  have hi : Function.Injective π := fun o o' e => hη o o' (by
    have := Subgroup.mul_mem _ (hπ o) (Subgroup.inv_mem _ (hπ o'))
    rwa [e, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] at this)
  rw [← (Finite.injective_iff_bijective.1 hi).prod_comp fun o => AA X p a (gam p N o) x y]
  exact cg_prod _ fun o _ => AA_left X hp ha (hπ o) hxy

end UpperTheory.V.Z.Kato.Nb.LineCohomology

open UpperTheory.V.Z.Kato.Nb.LineCohomology UpperTheory.V.Z.Kato.Nb.TrConj in
theorem UpperTheory.V.Z.Kato.Nb.sLineCoh :
    UpperTheory.V.Z.Kato.Nb.SLineCoh := by
  intro Ω _ _ _ ε X l _ n N M p c d _ _ _ hc ws hL hlv
  have hpN : Nat.Coprime p N := (Nat.Coprime.coprime_mul_right_right hc).coprime_mul_left_right
  have hN : (N : ZMod p) ≠ 0 := natCast_ne_of_cop Fact.out hpN
  have hp : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime _ _).2 hc.coprime_mul_left_right
  have hlv' : Lv c d M := ⟨NeZero.pos M, hlv.2.1.coprime_mul_left_right, hlv.2.2.coprime_mul_left_right⟩
  obtain ⟨-, -, hsl, hmul, hun, -, hgr, -⟩ := sSlD Ω ε X 1 one_pos
  obtain ⟨a, ha, hcob⟩ := hL.isog n p M hlv
  refine ⟨fun x y => ∏ o, AA X p a (gam p N o) x y, fun x y hxy => ⟨?_, fun γ => ?_⟩, fun s x y hxy => ?_⟩
  · exact Finset.prod_induction _ (· ∈ X.Un (l ^ n)) (fun f f' h h' => ((hgr _).2 f h f' h').1) (hgr _).1
      fun o _ => hun _ _ _ (ha _ _ (ok_zr hp _ hxy)).1
  · have h := AA_perm X hN hp ha (fun o => gam p N o * γ) (fun o o' h => lin_inj p N hN o o' (by
      rw [mul_inv_rev, mul_assoc, mul_inv_cancel_left, mem0] at h
      simpa only [gam_row] using h)) (⟨ne_rt γ hxy.1, ne_rt γ hxy.2⟩ : Ok (rt x γ) (rt y γ))
    simp only [AA, zr_right, slU_mul] at h
    rw [map_prod]
    exact h
  · have he := cyc_inv X M s
    have hu : IsUnit (cyc M s⁻¹) := IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans he)
    have hu' : cyc p s ≠ 0 := left_ne_zero_of_mul_eq_one (cyc_inv X p s)
    choose η h1 h2 h3 using fun o => conj X p M s
      (a (gr M s⁻¹ (zr p (gam p N o) x)) (gr M s⁻¹ (zr p (gam p N o) y))) (gam p N o)
    have hT := cg_pow (cyc (l ^ n) s).val (cgr_map (galU X s) (AA_perm X hN hp ha η (fun o o' h => lin_inj p N hN o o' (by
      rw [mem0, ← (h2 o).2.2.1, ← (h2 o).2.2.2, ← (h2 o').2.2.1, ← (h2 o').2.2.2] at h
      simp only [gam_row]
      exact mul_left_cancel₀ hu' (by linear_combination h)))
      (⟨ne_sc hu hxy.1, ne_sc hu hxy.2⟩ : Ok (gr M s⁻¹ x) (gr M s⁻¹ y))))
    have hT' : galU X s (∏ o, AA X p a (η o) (gr M s⁻¹ x) (gr M s⁻¹ y)) ^ (cyc (l ^ n) s).val =
        ∏ o, slU X (ofSL (gam p N o)) (tw X (l ^ n) M s a (zr p (gam p N o) x) (zr p (gam p N o) y)) := by
      rw [map_prod, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun o _ => ?_
      rw [tw, map_pow, ← h1, AA]
      exact congrArg₂ (fun u v => galU X s (slU X (ofSL (η o)) (a u v)) ^ (cyc (l ^ n) s).val)
        (zr_gal he (h3 o) x) (zr_gal he (h3 o) y)
    rw [hT'] at hT
    have hH : Cgr (l ^ n) (∏ o, slU X (ofSL (gam p N o)) (slU X (toGQ !![(p : ℤ), 0; 0, 1])
        (ws n M s (zr p (gam p N o) x) (zr p (gam p N o) y)))) (heF X l p N M (ws n M s) x y) := by
      refine cg_prod _ fun o _ => cg_symm ?_
      obtain ⟨δ, hδ⟩ := hP_eq l p N (NeZero.ne N) (NeZero.ne l) hpN o
      have hD : (0 : ℤ) < (!![(p : ℤ), 0; 0, 1]).det := by
        rw [Matrix.det_fin_two_of]; simpa using NeZero.pos p
      have hz := ok_zr hp (gam p N o) hxy
      have h := cgr_map (slU X (ofSL (gam p N o))) (cgr_map (slU X (toGQ !![(p : ℤ), 0; 0, 1]))
        ((((hL.coc n M hlv').eqv s) _ _ ⟨ne_rt δ⁻¹ hz.1, ne_rt δ⁻¹ hz.2⟩).2 δ))
      rw [rt_mul, rt_mul, inv_mul_cancel, rt_one, rt_one] at h
      rw [hδ, adj_row, adj_row, hmul _ _ (by simp) (by rwa [Matrix.det_mul, (gam p N o).det_coe, mul_one]), hmul _ _ hD (by simp), hsl, hsl]
      convert h using 1
      exact Units.ext ((X.sl_mul _ _ _).trans (X.sl_mul _ _ _))
    refine cg_trans (cg_prod _ fun o _ => cg_trans (cg_symm (fac X hp ((hL.coc n _ hlv).eqv s) o hxy))
      (cgr_map _ (hcob s _ _ (ok_zr hp _ hxy)))) ?_
    simp only [map_div, map_mul, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact cg_mul (cg_mul hH hT) (cg_refl _)

end
