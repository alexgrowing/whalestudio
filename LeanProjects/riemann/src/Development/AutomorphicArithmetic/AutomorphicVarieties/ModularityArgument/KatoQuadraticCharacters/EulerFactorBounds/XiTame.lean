import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem tm_val {Q r : ℕ} [NeZero Q] (h : r ∣ Q) (c : ZMod Q) : (ZMod.castHom h (ZMod r) c).val = c.val % r := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

private theorem tm_cast {Q r : ℕ} [NeZero Q] (h : r ∣ Q) (c : ZMod Q) : ZMod.castHom h (ZMod r) c = (c.val : ZMod r) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem zmod_val_cast_compose {Q r k : ℕ} [NeZero Q] (h : r ∣ Q) (hk : k ∣ r) (c : ZMod Q) :
    ((ZMod.castHom h (ZMod r) c).val : ZMod k) = (c.val : ZMod k) := by
  rw [tm_val, ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hk]

private theorem tm_key {Q k r : ℕ} [NeZero Q] (hQ : Q = k * r) (h : r ∣ Q) (c : ZMod Q) :
    ((k * (ZMod.castHom h (ZMod r) c).val : ℕ) : ZMod Q) = k * c := by
  rw [tm_val]
  have : ((k * (c.val % r) : ℕ) : ZMod Q) = ((k * c.val : ℕ) : ZMod Q) := by
    rw [ZMod.natCast_eq_natCast_iff]
    generalize c.val = v
    rw [hQ]
    exact Nat.ModEq.mul_left' k (Nat.mod_modEq _ _)
  rw [this]; simp

private theorem tm_vec {Q k r : ℕ} [NeZero Q] [NeZero r] (hQ : Q = k * r) (h : r ∣ Q) (x : Fin 2 → ZMod r)
    (A : Matrix (Fin 2) (Fin 2) (ZMod Q)) :
    (fun i => ((k * (x i).val : ℕ) : ZMod Q)) ᵥ* A =
      fun i => ((k * ((x ᵥ* A.map (ZMod.castHom h (ZMod r))) i).val : ℕ) : ZMod Q) := by
  funext i
  have : (x ᵥ* A.map (ZMod.castHom h (ZMod r))) i =
      ZMod.castHom h (ZMod r) (((x 0).val : ZMod Q) * A 0 i + ((x 1).val : ZMod Q) * A 1 i) := by
    rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [this, tm_key hQ]
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Nat.cast_mul]
  ring

private theorem tm_inj {Q p M : ℕ} (hQ : Q = p * M) (hc : Nat.Coprime p M) (hp : p ∣ Q) (hM : M ∣ Q) (a b : ZMod Q)
    (h1 : ZMod.castHom hp (ZMod p) a = ZMod.castHom hp (ZMod p) b)
    (h2 : ZMod.castHom hM (ZMod M) a = ZMod.castHom hM (ZMod M) b) : a = b := by
  subst hQ
  apply (ZMod.chineseRemainder hc).injective
  have e1 : ∀ c, (ZMod.chineseRemainder hc c).1 = ZMod.castHom hp (ZMod p) c := fun c =>
    DFunLike.congr_fun (Subsingleton.elim ((RingHom.fst _ _).comp (ZMod.chineseRemainder hc).toRingHom) (ZMod.castHom hp (ZMod p))) c
  have e2 : ∀ c, (ZMod.chineseRemainder hc c).2 = ZMod.castHom hM (ZMod M) c := fun c =>
    DFunLike.congr_fun (Subsingleton.elim ((RingHom.snd _ _).comp (ZMod.chineseRemainder hc).toRingHom) (ZMod.castHom hM (ZMod M))) c
  ext
  · rw [e1, e1, h1]
  · rw [e2, e2, h2]

private theorem tm_surj {Q p M : ℕ} (hQ : Q = p * M) (hc : Nat.Coprime p M) (hp : p ∣ Q) (hM : M ∣ Q) (a : ZMod p) (b : ZMod M) :
    ∃ c : ZMod Q, ZMod.castHom hp (ZMod p) c = a ∧ ZMod.castHom hM (ZMod M) c = b := by
  subst hQ
  have e1 : ∀ c, (ZMod.chineseRemainder hc c).1 = ZMod.castHom hp (ZMod p) c := fun c =>
    DFunLike.congr_fun (Subsingleton.elim ((RingHom.fst _ _).comp (ZMod.chineseRemainder hc).toRingHom) (ZMod.castHom hp (ZMod p))) c
  have e2 : ∀ c, (ZMod.chineseRemainder hc c).2 = ZMod.castHom hM (ZMod M) c := fun c =>
    DFunLike.congr_fun (Subsingleton.elim ((RingHom.snd _ _).comp (ZMod.chineseRemainder hc).toRingHom) (ZMod.castHom hM (ZMod M))) c
  refine ⟨(ZMod.chineseRemainder hc).symm (a, b), ?_, ?_⟩
  · rw [← e1]; simp
  · rw [← e2]; simp

private theorem tm_unit {Q p M : ℕ} (hQ : Q = p * M) (hc : Nat.Coprime p M) (hp : p ∣ Q) (hM : M ∣ Q) (c : ZMod Q)
    (h1 : IsUnit (ZMod.castHom hp (ZMod p) c)) (h2 : IsUnit (ZMod.castHom hM (ZMod M) c)) : IsUnit c := by
  obtain ⟨a, ha⟩ := h1.exists_right_inv
  obtain ⟨b, hb⟩ := h2.exists_right_inv
  obtain ⟨d, hd1, hd2⟩ := tm_surj hQ hc hp hM a b
  refine IsUnit.of_mul_eq_one d (tm_inj hQ hc hp hM _ _ ?_ ?_)
  · rw [map_mul, hd1, ha, map_one]
  · rw [map_mul, hd2, hb, map_one]

private theorem gamma_zero_double_coset_reduce {N M₀ M M' p : ℕ} [NeZero N] [NeZero M'] (hM : M = N * M₀) (h : M ∣ M') (h0 : M₀ ∣ p * M₀)
    (m : Matrix (Fin 2) (Fin 2) (ZMod M')) :
    (cD N (p * M₀) m).map (ZMod.castHom h0 (ZMod M₀)) = cD N M₀ (m.map (ZMod.castHom h (ZMod M))) := by
  have hd : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [cD, Matrix.map_apply]; simp only [Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, map_natCast, zmod_val_cast_compose h hd]
  · simp only [cD, Matrix.map_apply]; simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_natCast, Nat.cast_mul, map_mul, zmod_val_cast_compose h hd]
  · simp only [cD, Matrix.map_apply]; simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_natCast, tm_val]
    rw [ZMod.natCast_eq_natCast_iff', hM, Nat.mod_mul_right_div_self, Nat.mod_mod]
  · simp only [cD, Matrix.map_apply]; simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_natCast, zmod_val_cast_compose h hd]

private theorem gamma_zero_double_coset_mod_prime {N M₀ M' p : ℕ} [Fact p.Prime] [NeZero M'] (hN : (N : ZMod p) ≠ 0) (h : p ∣ M') (h0 : p ∣ p * M₀)
    (m : Matrix (Fin 2) (Fin 2) (ZMod M')) (hm : ((m 1 0).val : ZMod N) = 0) :
    (cD N (p * M₀) m).map (ZMod.castHom h0 (ZMod p)) =
      !![ZMod.castHom h (ZMod p) (m 0 0), N * ZMod.castHom h (ZMod p) (m 0 1);
        (N : ZMod p)⁻¹ * ZMod.castHom h (ZMod p) (m 1 0), ZMod.castHom h (ZMod p) (m 1 1)] := by
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).1 hm
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [cD, Matrix.map_apply] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_natCast, Nat.cast_mul, map_mul] <;> rw [tm_cast h]
  rw [hk, Nat.mul_div_cancel_left _ hN0, Nat.cast_mul, inv_mul_cancel_left₀ hN]

private theorem tm_fib {N M₀ M M' p : ℕ} [Fact p.Prime] [NeZero M] [NeZero M'] (hN : N ∣ M) (hQ : M' = p * M) (hc : Nat.Coprime p M)
    (h : M ∣ M') (h0 : p ∣ p * M₀) (t t' : Fin 2 → ZMod p) (ht : t 0 * t' 1 - t 1 * t' 0 ≠ 0) (m : GL (Fin 2) (ZMod M))
    (hm : (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0).val : ZMod N) = 0) {A : Type} [AddCommMonoid A]
    (F : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) → A) :
    ∑ m' ∈ Finset.univ.filter (fun m' : GL (Fin 2) (ZMod M') => Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod M)) m' = m),
      F (t ᵥ* (cD N (p * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod M'))).map (ZMod.castHom h0 (ZMod p)),
        t' ᵥ* (cD N (p * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod M'))).map (ZMod.castHom h0 (ZMod p))) =
    ∑ tt ∈ Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) => tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0), F tt := by
  have hp : p ∣ M' := ⟨M, hQ⟩
  have hN0 : (N : ZMod p) ≠ 0 := fun e =>
    (Fact.out : p.Prime).one_lt.ne' (hc.eq_one_of_dvd (((ZMod.natCast_eq_zero_iff _ _).1 e).trans hN))
  have hent : ∀ m' : GL (Fin 2) (ZMod M'), Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod M)) m' = m → ∀ i j,
      ZMod.castHom h (ZMod M) ((m' : Matrix (Fin 2) (Fin 2) (ZMod M')) i j) = (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i j := by
    rintro m' rfl i j; rfl
  have hlow : ∀ m' : Matrix (Fin 2) (Fin 2) (ZMod M'), ZMod.castHom h (ZMod M) (m' 1 0) = (m : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0 →
      ((m' 1 0).val : ZMod N) = 0 := by
    intro m' e; rw [← zmod_val_cast_compose h hN, e, hm]
  have hT : IsUnit (Matrix.of ![t, t']) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two]
    exact Ne.isUnit (by simpa using ht)
  have r0 : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod p), (Matrix.of ![t, t'] * B) 0 = t ᵥ* B := fun B => rfl
  have r1 : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod p), (Matrix.of ![t, t'] * B) 1 = t' ᵥ* B := fun B => rfl
  refine Finset.sum_bij (fun m' _ => (t ᵥ* (cD N (p * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod M'))).map (ZMod.castHom h0 (ZMod p)),
        t' ᵥ* (cD N (p * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod M'))).map (ZMod.castHom h0 (ZMod p)))) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro m' hm'
    rw [Finset.mem_filter] at hm' ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hd : ZMod.castHom hp (ZMod p) (m' : Matrix (Fin 2) (Fin 2) (ZMod M')).det ≠ 0 :=
      (((Matrix.isUnit_iff_isUnit_det _).1 m'.isUnit).map _).ne_zero
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul] at hd
    rw [gamma_zero_double_coset_mod_prime hN0 hp h0 _ (hlow _ (hent m' hm'.2 1 0))]
    intro e
    apply mul_ne_zero ht hd
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at e
    rw [← e]; field_simp; ring
  · intro a ha b hb e
    rw [Finset.mem_filter] at ha hb
    have e2 : (cD N (p * M₀) (a : Matrix (Fin 2) (Fin 2) (ZMod M'))).map (ZMod.castHom h0 (ZMod p)) =
        (cD N (p * M₀) (b : Matrix (Fin 2) (Fin 2) (ZMod M'))).map (ZMod.castHom h0 (ZMod p)) := by
      apply hT.mul_left_cancel
      funext i
      fin_cases i
      · exact (r0 _).trans ((congrArg Prod.fst e).trans (r0 _).symm)
      · exact (r1 _).trans ((congrArg Prod.snd e).trans (r1 _).symm)
    rw [gamma_zero_double_coset_mod_prime hN0 hp h0 _ (hlow _ (hent a ha.2 1 0)), gamma_zero_double_coset_mod_prime hN0 hp h0 _ (hlow _ (hent b hb.2 1 0))] at e2
    ext i j
    refine tm_inj hQ hc hp h _ _ ?_ (by rw [hent a ha.2, hent b hb.2])
    have e3 := congrFun (congrFun e2 i) j
    fin_cases i <;> fin_cases j
    · exact e3
    · exact mul_left_cancel₀ hN0 e3
    · exact mul_left_cancel₀ (inv_ne_zero hN0) e3
    · exact e3
  · intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨U, hU⟩ := hT.exists_right_inv
    set B : Matrix (Fin 2) (Fin 2) (ZMod p) := U * Matrix.of ![s.1, s.2] with hB
    have hTB : Matrix.of ![t, t'] * B = Matrix.of ![s.1, s.2] := by rw [hB, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    have hBd : B.det ≠ 0 := by
      intro e
      have := congrArg Matrix.det hTB
      rw [Matrix.det_mul, e, mul_zero, Matrix.det_fin_two] at this
      exact hs.2 (by simpa using this.symm)
    choose c hc1 hc2 using fun i j => tm_surj hQ hc hp h
      ((!![B 0 0, (N : ZMod p)⁻¹ * B 0 1; N * B 1 0, B 1 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) i j) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) i j)
    have hu : IsUnit (Matrix.of c) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      refine tm_unit hQ hc hp h _ ?_ ?_
      · apply Ne.isUnit
        rw [Matrix.det_fin_two] at hBd ⊢
        simp only [map_sub, map_mul, Matrix.of_apply, hc1, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
        convert hBd using 1
        field_simp
      · have := (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
        rw [Matrix.det_fin_two] at this ⊢
        simpa only [map_sub, map_mul, Matrix.of_apply, hc2] using this
    have hBB : (cD N (p * M₀) (Matrix.of c)).map (ZMod.castHom h0 (ZMod p)) = B := by
      rw [gamma_zero_double_coset_mod_prime hN0 hp h0 _ (hlow (Matrix.of c) (hc2 1 0))]
      simp only [Matrix.of_apply, hc1, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_inv_cancel_left₀ hN0, inv_mul_cancel_left₀ hN0]
      exact (Matrix.eta_fin_two B).symm
    refine ⟨hu.unit, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext i j
      exact hc2 i j
    · rw [IsUnit.unit_spec, hBB, ← r0, ← r1, hTB]; rfl

private theorem tm_prod {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n N : ℕ) {ι : Type} (S : Finset ι) (f : ι → X.Kˣ) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (slD X N ((∏ i ∈ S, f i : X.Kˣ) : X.K))) =
      ∑ i ∈ S, AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (slD X N (f i : X.K))) := by
  obtain ⟨h1, h2, -⟩ := sCls Ω ε X l n
  have hs : ∀ g : X.Kˣ, slD X N (g : X.K) = (slU X (toGQ !![(N : ℤ), 0; 0, 1]) g : X.Kˣ) := fun g => rfl
  simp only [hs]
  rw [map_prod, ← map_sum]
  have key : Rep X l n (∏ i ∈ S, slU X (toGQ !![(N : ℤ), 0; 0, 1]) (f i))
      (∑ i ∈ S, clsK X l n (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (f i) : X.Kˣ)) := by
    induction S using Finset.induction_on with
    | empty => simpa using (h2 1 1 _ _ (h1 1) (h1 1)).2
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (h2 _ _ _ _ (h1 _) ih).1
  exact (h1 _).trans key.symm

private theorem tm_wt {M M' : ℕ} [NeZero M'] (l : ℕ) [Fact l.Prime] (n : ℕ) (hl : l ^ n ∣ M) (h : M ∣ M') (c : ZMod M') :
    ((c.val : ℤ_[l])) ≡ ((ZMod.castHom h (ZMod M) c).val : ℤ_[l]) [SMOD (Ideal.span {(l : ℤ_[l]) ^ n})] := by
  rw [SModEq.sub_mem, Ideal.mem_span_singleton, tm_val]
  obtain ⟨k, hk⟩ := hl
  refine ⟨k * (c.val / M : ℕ), ?_⟩
  conv_lhs => enter [1]; rw [← Nat.mod_add_div c.val M]
  generalize c.val % M = a
  generalize c.val / M = b
  rw [hk]; push_cast; ring

theorem sXiTame : SXiTame := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL p M' _ _ _ h hM' hc x y t t' ht P a u
  have hQ : M' = p * M := by rw [hM', hL.eq]; ring
  have hN : N ∣ M := ⟨M₀, hL.eq⟩
  have hln : l ^ n ∣ M := hL.dl.trans ⟨N, by rw [hL.eq, mul_comm]⟩
  have hl : l ∣ M := (dvd_pow_self l (Nat.one_le_iff_ne_zero.1 hL.pos)).trans hln
  have h0 : p ∣ p * M₀ := dvd_mul_right _ _
  have h1 : M₀ ∣ p * M₀ := dvd_mul_left _ _
  have hw := (sApi Ω ε X l n).2.2.2.2.1
  have hdet : ∀ m' : GL (Fin 2) (ZMod M'), Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod M)) m') =
      Units.map (ZMod.castHom h (ZMod M)).toMonoidHom (Matrix.GeneralLinearGroup.det m') := by
    intro m'; ext1
    exact (RingHom.map_det _ _).symm
  have hcnd : ∀ m' : GL (Fin 2) (ZMod M'), Cnd l N g (Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod M)) m' : GL (Fin 2) (ZMod M)).1 ↔
      Cnd l N g m'.1 := by
    intro m'
    have e : ∀ i j, (Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod M)) m' : GL (Fin 2) (ZMod M)).1 i j =
      ZMod.castHom h (ZMod M) (m'.1 i j) := fun _ _ => rfl
    simp only [Cnd, e, zmod_val_cast_compose h hN, zmod_val_cast_compose h hl]
  rw [map_sub, sub_eq_zero]
  unfold Xi
  rw [map_sum, map_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod M)))
    (t := Finset.univ.filter (fun m : GL (Fin 2) (ZMod M) =>
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)))]
  swap
  · intro m' hm'
    rw [Finset.mem_filter] at hm' ⊢
    exact ⟨Finset.mem_univ _, (hcnd m').2 hm'.2.1, hdet m' ▸ hm'.2.2⟩
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [map_smul, pushB, tm_prod, ← tm_fib hN hQ hc h h0 t t' ht m hm.2.1.1, Finset.smul_sum]
  refine Finset.sum_congr ?_ fun m' hm' => ?_
  · ext m'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun e => e.2, fun e => ⟨?_, e⟩⟩
    subst e
    exact ⟨(hcnd m').1 hm.2.1, hdet m' ▸ hm.2.2⟩
  rw [Finset.mem_filter] at hm'
  obtain ⟨-, rfl⟩ := hm'
  have hv : ∀ (z : Row M₀) (s : Fin 2 → ZMod p), (up p M₀ z + tp p M₀ s) ᵥ* cD N (p * M₀) m'.1 =
      up p M₀ (z ᵥ* cD N M₀ (Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod M)) m' : GL (Fin 2) (ZMod M)).1) +
        tp p M₀ (s ᵥ* (cD N (p * M₀) m'.1).map (ZMod.castHom h0 (ZMod p))) := by
    intro z s
    rw [Matrix.add_vecMul]
    congr 1
    · have := tm_vec rfl h1 z (cD N (p * M₀) m'.1)
      rw [gamma_zero_double_coset_reduce hL.eq h h1] at this
      exact this
    · exact tm_vec (mul_comm _ _) h0 s (cD N (p * M₀) m'.1)
  rw [hv, hv, ← map_smul, ← sub_eq_zero, ← map_sub]
  apply hw
  rw [← Ideal.mem_span_singleton, ← SModEq.sub_mem]
  rw [hdet, ← map_inv]
  exact (tm_wt l n hln h _).mul ((((tm_wt l n hln h _).mul SModEq.rfl).add ((tm_wt l n hln h _).mul SModEq.rfl)).pow w)

end UpperTheory.V.Z.Kato.Nb
