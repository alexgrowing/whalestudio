import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVectorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVectorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowRescale
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.AdmissibleUnits

open GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem ent_ext {g h : GQ} (e : ∀ i j, ent g i j = ent h i j) : g = h :=
  Subtype.ext (Matrix.GeneralLinearGroup.ext e)

private theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem ent_dg {N : ℕ} (hN : 0 < N) (i j : Fin 2) :
    ent (toGQ !![(N : ℤ), 0; 0, 1]) i j = (!![(N : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j := by
  fin_cases i <;> fin_cases j <;> simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem ent_sl (γ : SL(2, ℤ)) (i j : Fin 2) : ent (ofSL γ) i j = (en γ i j : ℚ) := rfl

private theorem dg_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    toGQ !![(a : ℤ), 0; 0, 1] * toGQ !![(b : ℤ), 0; 0, 1] = toGQ !![((a * b : ℕ) : ℤ), 0; 0, 1] := by
  refine ent_ext fun i j => ?_
  rw [ent_mul, ent_dg (Nat.mul_pos ha hb)]
  simp only [ent_dg ha, ent_dg hb]
  fin_cases i <;> fin_cases j <;> simp

private theorem exists_conj {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) (k : ℤ) (hk : en γ 1 0 = N * k) :
    ∃ δ : SL(2, ℤ), en δ 0 0 = en γ 0 0 ∧ en δ 0 1 = N * en γ 0 1 ∧ en δ 1 0 = k ∧ en δ 1 1 = en γ 1 1 ∧
      toGQ !![(N : ℤ), 0; 0, 1] * ofSL γ = ofSL δ * toGQ !![(N : ℤ), 0; 0, 1] := by
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  let δ : SL(2, ℤ) := ⟨!![en γ 0 0, N * en γ 0 1; k, en γ 1 1], by
    rw [Matrix.det_fin_two_of, ← hd, hk]; ring⟩
  have h00 : en δ 0 0 = en γ 0 0 := rfl
  have h01 : en δ 0 1 = N * en γ 0 1 := rfl
  have h10 : en δ 1 0 = k := rfl
  have h11 : en δ 1 1 = en γ 1 1 := rfl
  refine ⟨δ, h00, h01, h10, h11, ent_ext fun i j => ?_⟩
  rw [ent_mul, ent_mul]
  simp only [ent_dg hN, ent_sl]
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, hk, mul_comm]

private theorem admissible_of_integral_conj_le {c D : ℕ} (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcD : Nat.Coprime c D) (hD : 0 < D) {a b : ℤ}
    (hab : ¬ ((D : ℤ) ∣ a ∧ (D : ℤ) ∣ b)) : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D] := by
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : IsCoprime (D : ℤ) (c : ℤ) := Nat.isCoprime_iff_coprime.2 hcD.symm
  have key : ∀ z : ℤ, (c : ℚ) * ((z : ℚ) / D) ∈ Set.range ((↑) : ℤ → ℚ) → (D : ℤ) ∣ z := by
    rintro z ⟨k, hk⟩
    have e : (c : ℚ) * z = D * k := by rw [hk]; field_simp
    exact hz.dvd_of_dvd_mul_left ⟨k, by exact_mod_cast e⟩
  exact ⟨hc, h6, fun h => hab ⟨key a h.1, key b h.2⟩⟩

private theorem siegel_per {ε : Ω →+* ℂ} (X : Tower Ω ε) {c : ℕ} {x y : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (p q : ℤ)
    (h0 : y 0 = x 0 + p) (h1 : y 1 = x 1 + q) : siegel X c y = siegel X c x := by
  have hy : y = fun i => x i + ((![p, q] : Fin 2 → ℤ) i : ℚ) := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have e : sgC c y = sgC c x := by
    funext z
    rw [hy]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ _ hx
  unfold siegel
  rw [e]

private theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x y : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (p q : ℤ)
    (h0 : y 0 = x 0 + p) (h1 : y 1 = x 1 + q) : GlobalTheory.Sieg.admitted c y := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ => hx.2.2 ⟨⟨u - c * p, ?_⟩, ⟨v - c * q, ?_⟩⟩⟩
  · push_cast; rw [hu, h0]; ring
  · push_cast; rw [hv, h1]; ring

private theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) : GlobalTheory.Sieg.admitted c (act x γ) := by
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hq : (en γ 0 0 : ℚ) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by exact_mod_cast hd
  refine ⟨hx.1, hx.2.1, fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ =>
    hx.2.2 ⟨⟨u * en γ 1 1 - v * en γ 1 0, ?_⟩, ⟨v * en γ 0 0 - u * en γ 0 1, ?_⟩⟩⟩
  all_goals
    simp only [act, Fin.sum_univ_two] at hu hv
    simp only [en] at hq ⊢
    push_cast
    rw [hu, hv]
  · linear_combination (c * x 0) * hq
  · linear_combination (c * x 1) * hq

private theorem sl_dg_siegel [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c N : ℕ} (hN : 0 < N) {x y : Fin 2 → ℚ}
    (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) (k : ℤ) (hk : en γ 1 0 = N * k) (p q : ℤ)
    (h0 : y 0 = x 0 * en γ 0 0 + x 1 * k + p) (h1 : y 1 = x 0 * (N * en γ 0 1) + x 1 * en γ 1 1 + q) :
    X.sl (ofSL γ) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c x)) = X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c y) := by
  obtain ⟨δ, h00, h01, h10, h11, e⟩ := exists_conj hN γ k hk
  rw [← X.sl_mul, e, X.sl_mul, GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c x δ hx]
  congr 1
  simp only [en] at h00 h01 h10 h11 h0 h1
  refine (siegel_per X (admissible_act_SL2 hx δ) p q ?_ ?_).symm
  · simp only [act, Fin.sum_univ_two]; rw [h0, h00, h10]
  · simp only [act, Fin.sum_univ_two]; rw [h1, h01, h11]; push_cast; ring

private theorem gal_siegel_fix [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c D : ℕ} (hD : 0 < D) {a b : ℤ}
    (hx : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D]) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ z : Ω, z ^ D = 1 → s z = z) :
    X.gal s (siegel X c ![(a : ℚ) / D, (b : ℚ) / D]) = siegel X c ![(a : ℚ) / D, (b : ℚ) / D] := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨a', ha'⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg a hz)
  obtain ⟨b', hb'⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg b hz)
  have hlt : a' < D := by
    have := Int.emod_lt_of_pos a (by exact_mod_cast hD : (0 : ℤ) < D)
    omega
  have ea : (a : ℚ) = a' + D * ((a / D : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv a D
    rw [ha'] at this
    exact_mod_cast this.symm
  have eb : (b : ℚ) = b' + D * ((b / D : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv b D
    rw [hb'] at this
    exact_mod_cast this.symm
  have f0 : (![(a' : ℚ) / D, (b' : ℚ) / D] : Fin 2 → ℚ) 0 = (![(a : ℚ) / D, (b : ℚ) / D] : Fin 2 → ℚ) 0 + ((-(a / D) : ℤ) : ℚ) := by
    show (a' : ℚ) / D = (a : ℚ) / D + ((-(a / D) : ℤ) : ℚ)
    rw [Int.cast_neg]; field_simp; linear_combination -ea
  have f1 : (![(a' : ℚ) / D, (b' : ℚ) / D] : Fin 2 → ℚ) 1 = (![(a : ℚ) / D, (b : ℚ) / D] : Fin 2 → ℚ) 1 + ((-(b / D) : ℤ) : ℚ) := by
    show (b' : ℚ) / D = (b : ℚ) / D + ((-(b / D) : ℤ) : ℚ)
    rw [Int.cast_neg]; field_simp; linear_combination -eb
  have hy := isAdmissibleSmoothingFactor_add_intVector hx _ _ f0 f1
  rw [← siegel_per X hx _ _ f0 f1]
  have := GlobalTheory.T.galois_action_siegelUnitInTower Ω ε X c D a' b' 1 s hD hlt
    (by rw [Nat.cast_one]; exact hs _ (isPrimitiveRoot_eOm ε hD.ne').pow_eq_one) hy (by rwa [one_mul])
  rwa [one_mul] at this

private theorem gal_dg {ε : Ω →+* ℂ} (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) {f : X.K} (hf : X.gal s f = f) :
    X.gal s (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f := by
  apply X.exp.toRingHom.injective
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, GlobalTheory.DlRescale.exp_sl_diag ε X N hN, GlobalTheory.DlRescale.resc_coeff, ← X.gal_exp, hf]

private theorem sgN_mem [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c N D M : ℕ} (hN : 0 < N) (hD : 0 < D)
    (hM : N * D ∣ M) {a b : ℤ} (hx : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D]) :
    sgN X c N D (a, b) ∈ topF X M ∧ sgN X c N D (a, b) ≠ 0 := by
  refine ⟨(mem_mdl_iff X _ _ _).2 ⟨?_, fun s hs => ?_⟩, ?_⟩
  · rw [mem_lev_iff]
    intro γ hγ
    obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have hMz : ((N * D : ℕ) : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.2 hM
    obtain ⟨u, hu⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 0 0 - 1 :=
      hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; exact sub_eq_zero.2 h00))
    obtain ⟨v, hv⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 0 1 := hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h01)
    obtain ⟨w, hw⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 1 0 := hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h10)
    obtain ⟨t, ht⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 1 1 - 1 :=
      hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; exact sub_eq_zero.2 h11))
    have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    refine sl_dg_siegel X hN hx γ (D * w) (by rw [hw]; push_cast; ring) (-(a * N * u + b * w)) (-(a * N * N * v + b * N * t)) ?_ ?_
    · show (a : ℚ) / D = (a : ℚ) / D * _ + (b : ℚ) / D * _ + _
      rw [sub_eq_iff_eq_add.1 hu]; push_cast; field_simp; ring
    · show (b : ℚ) / D = (a : ℚ) / D * _ + (b : ℚ) / D * _ + _
      rw [sub_eq_iff_eq_add.1 ht, hv]; push_cast; field_simp; ring
  · refine gal_dg X hN s (gal_siegel_fix X hD hx s fun z hz => (mem_fixMu_iff s).1 hs z ?_)
    obtain ⟨e, rfl⟩ := (Dvd.intro_left N rfl : D ∣ N * D).trans hM
    rw [pow_mul, hz, one_pow]
  · exact (map_ne_zero _).2 (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c _ hx)

end UpperTheory.Kd.L.AdmissibleUnits

open UpperTheory.Kd.L.AdmissibleUnits in
theorem UpperTheory.Kd.L.units :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → ((sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0)) ∈ topF X (topMu l n m N) ∧ (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0)) ≠ 0 ∧ (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))) ∈ topF X (topMu l n m N) ∧ (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))) ≠ 0) ∧ ∀ g ∈ CongruenceSubgroup.Gamma0 N, X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) = sgN X c (N ^ 3) (N ^ 3 * l ^ (m + n)) ((N : ℤ) ^ 2 * (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n))), (N : ℤ) ^ 2 * ((N : ℤ) ^ 2 * en g 0 1)) ∧ X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ)))) = sgN X d (N ^ 3) (N ^ 3 * l ^ (m + n)) ((N : ℤ) ^ 2 * (en g 0 0 * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n) + en g 1 0), (N : ℤ) ^ 2 * ((N : ℤ) * en g 1 1)) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm P x m n hm
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hL : 0 < l ^ (m + n) := pow_pos hl _
  have hD : 0 < N * l ^ (m + n) := Nat.mul_pos hN hL
  have hlL : l ∣ l ^ (m + n) := dvd_pow_self l (by omega)
  have cop : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e 6 ∧ Nat.Coprime e (N * l ^ (m + n)) := fun e he =>
    ⟨he.coprime_mul_right_right.coprime_mul_right_right,
      Nat.Coprime.mul_right he.coprime_mul_left_right
        (Nat.Coprime.pow_right _ he.coprime_mul_right_right.coprime_mul_left_right)⟩
  have hlD : (l : ℤ) ∣ ((N * l ^ (m + n) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (hlL.mul_left N)
  have hlN : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => P.cop (Int.natCast_dvd_natCast.1 h)
  have hM : N * (N * l ^ (m + n)) ∣ topMu l n m N := ⟨1, by unfold topMu; ring⟩
  generalize (topT l (m + n) N : ℤ) = t
  have hu := admissible_of_integral_conj_le P.c1 (cop c P.cc).1 (cop c P.cc).2 hD
    (a := (N : ℤ) + (x.val : ℤ) * t * (l : ℤ) ^ (m + n)) (b := 0) (fun h => hlN
      ((dvd_add_left ((dvd_pow_self (l : ℤ) (by omega)).mul_left _)).1 (hlD.trans h.1)))
  have hv := admissible_of_integral_conj_le P.d1 (cop d P.dc).1 (cop d P.dc).2 hD
    (a := t * (l : ℤ) ^ (m + n)) (b := (N : ℤ)) (fun h => by
      have h2 := Nat.le_of_dvd hN (Int.natCast_dvd_natCast.1 h.2)
      have h3 : 1 < l ^ (m + n) := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
      nlinarith)
  refine ⟨⟨(sgN_mem X hN hD hM hu).1, (sgN_mem X hN hD hM hu).2, (sgN_mem X hN hD hM hv).1, (sgN_mem X hN hD hM hv).2⟩,
    fun g hg => ?_⟩
  obtain ⟨k, hk⟩ : (N : ℤ) ∣ en g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 hg)
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have e3 : N * (N * N) = N ^ 3 := by ring
  unfold sgN
  constructor
  · rw [← e3, ← dg_mul hN (Nat.mul_pos hN hN), X.sl_mul]
    congr 1
    refine sl_dg_siegel X hN hu g k hk 0 (-(x.val * t * en g 0 1)) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
  · rw [← e3, ← dg_mul hN (Nat.mul_pos hN hN), X.sl_mul]
    congr 1
    refine sl_dg_siegel X hN hv g k hk 0 (-(t * en g 0 1)) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hk]; push_cast; field_simp; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
