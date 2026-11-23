import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiDist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SXiCoh

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

noncomputable section

namespace UpperTheory.V.Z.Kato.Nb.one_le_level_alt

private def rU (l L N M₀ : ℕ) (x : ZMod N) : Row M₀ :=
  ![((N + x.val * topT l L N * l ^ L : ℕ) : ZMod M₀), 0]

private def rV (l L N M₀ : ℕ) : Row M₀ :=
  ![((topT l L N * l ^ L : ℕ) : ZMod M₀), ((N : ℕ) : ZMod M₀)]

private theorem nat_frac (a M : ℕ) [NeZero M] :
    ∃ j : ℤ, (a : ℚ) / (M : ℚ) = (((a : ZMod M).val : ℕ) : ℚ) / M + j := by
  refine ⟨((a / M : ℕ) : ℤ), ?_⟩
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [ZMod.val_natCast]
  have h : (a : ℚ) = ((a % M : ℕ) : ℚ) + (M : ℚ) * ((a / M : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mod_add_div a M).symm
  rw [Int.cast_natCast]
  field_simp
  exact h

private theorem ixU_rU (l L N M₀ : ℕ) [NeZero M₀] (h : M₀ = N * l ^ L) (x : ZMod N) (i : Fin 2) :
    ∃ j : ℤ, ixU l L N x i = toQ M₀ (rU l L N M₀ x) i + j := by
  fin_cases i
  · obtain ⟨j, hj⟩ := nat_frac (N + x.val * topT l L N * l ^ L) M₀
    refine ⟨j, ?_⟩
    simp only [ixU, toQ, rU, ← h, Fin.zero_eta, Matrix.cons_val_zero]
    rw [← hj]; push_cast; rfl
  · exact ⟨0, by simp [ixU, toQ, rU]⟩

private theorem ixV_rV (l L N M₀ : ℕ) [NeZero M₀] (h : M₀ = N * l ^ L) (i : Fin 2) :
    ∃ j : ℤ, ixV l L N i = toQ M₀ (rV l L N M₀) i + j := by
  fin_cases i
  · obtain ⟨j, hj⟩ := nat_frac (topT l L N * l ^ L) M₀
    refine ⟨j, ?_⟩
    simp only [ixV, toQ, rV, ← h, Fin.zero_eta, Matrix.cons_val_zero]
    rw [← hj]; push_cast; rfl
  · obtain ⟨j, hj⟩ := nat_frac N M₀
    refine ⟨j, ?_⟩
    simp only [ixV, toQ, rV, ← h, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← hj]; push_cast; rfl

private theorem N_ne (l N : ℕ) [Fact l.Prime] (hc : Nat.Coprime l N) : (N : ZMod l) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hc

private theorem two_ne (l : ℕ) [Fact l.Prime] (h2 : l ≠ 2) : (2 : ZMod l) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)

private theorem ok_r (l L N M₀ : ℕ) [Fact l.Prime] (hl : l ∣ M₀) (hL : L ≠ 0) (h2 : l ≠ 2) (hc : Nat.Coprime l N)
    (x : ZMod N) : Ok (rU l L N M₀ x) (rV l L N M₀) := by
  have hN := mul_ne_zero (two_ne l h2) (N_ne l N hc)
  constructor
  · intro h
    have := congrArg (ZMod.castHom hl (ZMod l)) (congrFun h 0)
    simp only [rU, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, map_mul, map_natCast, map_ofNat,
      Pi.zero_apply, map_zero] at this
    apply hN
    simpa [hL] using this
  · intro h
    have := congrArg (ZMod.castHom hl (ZMod l)) (congrFun h 1)
    simp only [rV, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, map_mul, map_natCast, map_ofNat,
      Pi.zero_apply, map_zero] at this
    exact hN this

private theorem bas_r (l L N M₀ : ℕ) [Fact l.Prime] [NeZero M₀] (hl : l ∣ M₀) (hL : L ≠ 0) (hc : Nat.Coprime l N)
    (x : ZMod N) : Bas l N (rU l L N M₀ x) (rV l L N M₀) := by
  refine ⟨hc, ?_⟩
  have hv : ∀ a : ℕ, (((a : ZMod M₀).val : ℕ) : ZMod l) = a := fun a => by
    rw [ZMod.natCast_val, ZMod.cast_natCast hl]
  simp only [rU, rV, Matrix.cons_val_zero, Matrix.cons_val_one, hv, ZMod.val_zero]
  simpa [hL] using N_ne l N hc

private theorem topT_step (l L N M₀ : ℕ) [NeZero N] (h : M₀ = N * l ^ L) (hc : Nat.Coprime l N) :
    ((topT l (L + 1) N * l ^ (L + 1) : ℕ) : ZMod M₀) = ((topT l L N * l ^ L : ℕ) : ZMod M₀) := by
  rw [ZMod.natCast_eq_natCast_iff, h, pow_succ', ← mul_assoc]
  apply Nat.ModEq.mul_right'
  rw [← ZMod.natCast_eq_natCast_iff]
  have hu : ((ZMod.unitOfCoprime l hc : (ZMod N)ˣ) : ZMod N) = l := ZMod.coe_unitOfCoprime l hc
  simp only [topT, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
  rw [← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ZMod.inv_coe_unit, ZMod.inv_coe_unit,
    ← Units.val_mul]
  congr 1
  group

private theorem dn_rU (l L N M₀ : ℕ) [NeZero N] (h : M₀ = N * l ^ L) (hc : Nat.Coprime l N) (x : ZMod N) :
    dn l M₀ (rU l (L + 1) N (l * M₀) x) = rU l L N M₀ x := by
  have := topT_step l L N M₀ h hc
  funext i
  fin_cases i
  · simp only [dn, rU, Fin.zero_eta, Matrix.cons_val_zero, map_natCast]
    rw [mul_assoc, mul_assoc, Nat.cast_add, Nat.cast_add, Nat.cast_mul x.val, Nat.cast_mul x.val, this]
  · simp [dn, rU]

private theorem dn_rV (l L N M₀ : ℕ) [NeZero N] (h : M₀ = N * l ^ L) (hc : Nat.Coprime l N) :
    dn l M₀ (rV l (L + 1) N (l * M₀)) = rV l L N M₀ := by
  have := topT_step l L N M₀ h hc
  funext i
  fin_cases i
  · simp only [dn, rV, Fin.zero_eta, Matrix.cons_val_zero, map_natCast]
    exact this
  · simp only [dn, rV, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, map_natCast]

private theorem lev_r {l N c d : ℕ} {g : SL(2, ℤ)} (H : Hyp l N c d g) (n r M₀ : ℕ) (hn : 1 ≤ n)
    (h : M₀ = N * l ^ (r + n)) : Lev l n N M₀ (topM l n r (N * N)) g :=
  ⟨by rw [h, topM]; ring, h ▸ Dvd.intro _ rfl, h ▸ Dvd.dvd.mul_left (pow_dvd_pow l (Nat.le_add_left n r)) N, hn, H.cop, H.g0⟩

private theorem lv_r {l N c d : ℕ} [Fact l.Prime] [NeZero N] {g : SL(2, ℤ)} (H : Hyp l N c d g) (L M₀ : ℕ)
    (h : M₀ = N * l ^ L) : Lv c d M₀ := by
  have k : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e M₀ := fun e he => by
    rw [h]
    exact Nat.Coprime.mul_right (he.coprime_dvd_right (Dvd.intro_left _ rfl))
      (Nat.Coprime.pow_right _ (he.coprime_dvd_right (Dvd.dvd.mul_right (Dvd.intro_left 6 rfl) N)))
  exact ⟨h ▸ Nat.mul_pos (NeZero.pos N) (pow_pos (Fact.out : l.Prime).pos _), k c H.cc, k d H.cd⟩

private def redMh (l n r N : ℕ) : (ZMod (topM l n r N))ˣ →* (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) N) (ZMod (l ^ r))).toMonoidHom

private def redLh (l r : ℕ) : (ZMod (l ^ (r + 1)))ˣ →* (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem kap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] :
    (fun s : Ω ≃ₐ[ℚ] Ω => (redMh l n r N (cycM _ s))⁻¹) = fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹ := by
  funext s
  rw [(sCycZ Ω l r s).1]
  congr 1
  exact ((sSlD Ω ε X 1 one_pos).2.2.2.2.2.2.2 (topM l n r N) s).2.2.2.2 (l ^ r) _

private theorem kap' (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (r : ℕ) :
    (fun s : Ω ≃ₐ[ℚ] Ω => redLh l r (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l (r + 1) s)⁻¹) =
      fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹ := by
  funext s
  rw [(sCycZ Ω l r s).1, (sCycZ Ω l (r + 1) s).1, map_inv]
  congr 1
  exact ((sSlD Ω ε X 1 one_pos).2.2.2.2.2.2.2 (l ^ (r + 1)) s).2.2.2.2 (l ^ r) _

private theorem zeta_class_cohomology_compat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ))
    (H : Hyp l N c d g) (ws) (hws : Laws X l c d ws) (hL : LiftsWith X l N w (cL X l N w)) (n r L M₀ : ℕ) [NeZero M₀]
    (hn : 1 ≤ n) (hL' : L = r + n) (h : M₀ = N * l ^ L) :
    CohB X l N w n (fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (Y0 X l n r N x c d w g)
      fun s t => Xi X l n N M₀ (topM l n r (N * N)) w g (rU l L N M₀ x) (rV l L N M₀)
        (fun z => redMh l n r (N * N) z = t) (ws n M₀ s) := by
  subst hL'
  have lev := lev_r H n r M₀ hn h
  have lv := lv_r H (r + n) M₀ h
  have ok : Ok (rU l (r + n) N M₀ x) (rV l (r + n) N M₀) :=
    ok_r l (r + n) N M₀ (h ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N) (by omega) H.odd H.cop x
  obtain ⟨β, hβ, hrel⟩ := sTopRel Ω ε X l n N M₀ _ w g lev hL c d ws hws lv _ _ ok _ _
    (ixU_rU l (r + n) N M₀ h x) (ixV_rV l (r + n) N M₀ h)
  have := sBridge Ω ε X l n N M₀ _ w g lev hL _ _ ok _ (hws.coc n M₀ lv) _ β hβ hrel _ (redMh l n r (N * N))
  rw [kap X] at this
  exact this

end UpperTheory.V.Z.Kato.Nb.one_le_level_alt

open UpperTheory.V.Z.Kato.Nb.one_le_level_alt in
theorem UpperTheory.V.Z.Kato.Nb.kato_norm_compatible_cyclotomic_tower :
    UpperTheory.V.Z.Kato.Nb.KatoClassNormCompatibleCyclotomic := by
  intro Ω _ _ _ ε X l _ N _ x c d w g H ⟨ws, hws⟩ hL n r
  have api := sCohApi Ω ε X l N w n (NeZero.pos N) _ (fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact api.2.2.2.2.2.1 _ _
  obtain ⟨M₀, h⟩ : ∃ M₀, M₀ = N * l ^ (r + n) := ⟨_, rfl⟩
  have h' : l * M₀ = N * l ^ (r + n + 1) := by rw [h]; ring
  have h'' : l * M₀ = N * l ^ (r + 1 + n) := by rw [h]; ring
  have lv := lv_r H _ M₀ h
  have lv' := lv_r H _ _ h'
  haveI : NeZero M₀ := ⟨lv.1.ne'⟩
  haveI : NeZero (l * M₀) := ⟨lv'.1.ne'⟩
  have lev := lev_r H n r M₀ hn h
  have lev' := lev_r H n (r + 1) _ hn h''
  have ok : Ok (rU l (r + n) N M₀ x) (rV l (r + n) N M₀) :=
    ok_r l (r + n) N M₀ (h ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N) (by omega) H.odd H.cop x
  have ok' : Ok (rU l (r + n + 1) N (l * M₀) x) (rV l (r + n + 1) N (l * M₀)) :=
    ok_r l _ N _ (Dvd.intro _ rfl) (by omega) H.odd H.cop x
  have A := zeta_class_cohomology_compat X l N x c d w g H ws hws hL n r _ M₀ hn rfl h
  have B := zeta_class_cohomology_compat X l N x c d w g H ws hws hL n (r + 1) (r + n + 1) (l * M₀) hn (by omega) h'
  have B' := (sCohApi Ω ε X l N w n (NeZero.pos N) _ _).2.2.2.2.2.2.1 _ (redLh l r) _ _ B
  rw [kap' X] at B'
  have C := sXiCoh Ω ε X l n N M₀ _ w g lev hL _ _ ok _ (redMh l n r (N * N)) _ _ (hws.dist n l M₀ lv')
  rw [kap X] at C
  refine api.1.trans B' (api.1.trans (api.2.1 _ _ fun s t => ?_) (api.1.trans C (api.1.symm A)))
  have hd : topM l n r (N * N) ∣ topM l n (r + 1) (N * N) :=
    Nat.mul_dvd_mul_right (pow_dvd_pow l (by omega)) _
  have D := sXiDist Ω ε X l n N M₀ _ w g lev _ hd lev'.eq _ _
    (bas_r l (r + n + 1) N (l * M₀) (Dvd.intro _ rfl) (by omega) H.cop x) (fun z => redMh l n r (N * N) z = t) (ws n (l * M₀) s)
  rw [dn_rU l _ N M₀ h H.cop, dn_rV l _ N M₀ h H.cop] at D
  convert D using 1
  have E := (sXiMul Ω ε X l n N (l * M₀) _ w g lev' _ _ ok' (fun _ => True)).2.2.2 (ws n (l * M₀) s)
  rw [E _ (fun z => redMh l n r (N * N) (Units.map (ZMod.castHom hd (ZMod _)).toMonoidHom z)) t, GlobalTheory.KA.push]
  simp only [E _ (redMh l n (r + 1) (N * N))]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext z
  have : redLh l r (redMh l n (r + 1) (N * N) z) =
      redMh l n r (N * N) (Units.map (ZMod.castHom hd (ZMod _)).toMonoidHom z) := by
    apply Units.ext
    have e1 := DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow l (Nat.le_succ r))
      (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right (r + 1) n)) (N * N) : _ ∣ topM l n (r + 1) (N * N))) z.val
    have e2 := DFunLike.congr_fun (ZMod.castHom_comp
      (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N) : _ ∣ topM l n r (N * N)) hd) z.val
    exact e1.trans e2.symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, this]

end
