import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem term {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n N : ℕ) (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (f : X.Kˣ) (c : ℕ) (k k' : ℤ_[l]) (h : (l : ℤ_[l]) ^ n ∣ k * c - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n (k • clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
      X.kmap l (X.gal s) (k' • clsK X l n (slD X N (f : X.K)))) = 0 := by
  obtain ⟨hRep, -, hPow, hUniq, hMap, -, -⟩ := sCls Ω ε X l n
  obtain ⟨hGalSl, -⟩ := sSlD Ω ε X N hN
  have hApi := (sApi Ω ε X l n).2.2.2.2.1
  have hmul : ∀ a b : X.K, slD X N (a * b) = slD X N a * slD X N b := by
    intro a b
    simp [slD]
  have h1 : slD X N 1 = 1 := by simp [slD]
  have hpow : ∀ (a : X.K) (m : ℕ), slD X N (a ^ m) = slD X N a ^ m := by
    intro a m
    simp [slD]
  let U : X.Kˣ → X.Kˣ := fun u =>
    ⟨slD X N u, slD X N ↑u⁻¹, by rw [← hmul]; simp [h1], by rw [← hmul]; simp [h1]⟩
  have hA := hRep (U (galU X s f ^ c))
  have hB := hPow _ _ c (hMap (X.gal s) _ _ (hRep (U f)))
  have heq : (Units.map (X.gal s : X.K →* X.K) (U f)) ^ c = U (galU X s f ^ c) := by
    ext
    simp only [U, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [hpow, hGalSl]
    rfl
  rw [heq] at hB
  have hc : Cgr (l ^ n) (U (galU X s f ^ c)) (U (galU X s f ^ c)) := by
    first | rfl | exact ⟨1, by simp⟩ | simp [Cgr]
  have hz := hUniq _ _ _ _ hA hB hc
  rw [map_smul]
  have hsplit : k • clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
      k' • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K))) =
      k • (clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
        (c : ℤ_[l]) • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K)))) +
      ((k * c) • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K))) -
        k' • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K)))) := by
    rw [smul_sub, smul_smul]
    abel
  rw [hsplit, map_add, map_smul, hApi (k * c) k' _ h, add_zero]
  convert smul_zero k using 2

private theorem dvd_iff (l : ℕ) [Fact l.Prime] (n : ℕ) (k k' : ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ k - k' ↔ PadicInt.toZModPow n k = PadicInt.toZModPow n k' := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

private theorem val_cast {M M' : ℕ} [NeZero M] (h : M' ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod M') = ZMod.castHom h (ZMod M') z := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private noncomputable def dg {M : ℕ} (d : (ZMod M)ˣ) : GL (Fin 2) (ZMod M) :=
  ⟨!![1, 0; 0, (d : ZMod M)], !![1, 0; 0, ((d⁻¹ : (ZMod M)ˣ) : ZMod M)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

theorem UpperTheory.V.Z.Kato.Nb.sXiTw :
    UpperTheory.V.Z.Kato.Nb.SXiTw := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y P a s
  have hM0 : M₀ ∣ M := hL.eq ▸ Dvd.intro_left N rfl
  have hlM : l ^ n ∣ M := hL.dl.trans hM0
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨-, -, -, -, -, -, -, hcyc⟩ := sSlD Ω ε X N hN
  have hone : ∀ (K : ℕ) [NeZero K], cycM K (1 : Gal(Ω/ℚ)) = 1 := by
    intro K _
    have h := (hcyc K 1).2.1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hinv : ∀ (K : ℕ) [NeZero K], cycM K s⁻¹ = (cycM K s)⁻¹ := by
    intro K _
    rw [eq_inv_iff_mul_eq_one, ← (hcyc K s⁻¹).2.1 s, inv_mul_cancel, hone]
  set d := cycM M s with hd
  have hcd : ZMod.castHom hM0 (ZMod M₀) ((d⁻¹ : (ZMod M)ˣ) : ZMod M) = cyc M₀ s⁻¹ := by
    rw [(hcyc M₀ s⁻¹).1, ← ((hcyc M s⁻¹).2.2.2.2 M₀ hM0), hinv M]
    rfl
  have hgr : ∀ (z : Row M₀) (m : GL (Fin 2) (ZMod M)),
      gr M₀ s⁻¹ (z ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) =
        z ᵥ* cD N M₀ ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro z m
    ext i
    fin_cases i
    · simp [gr, cD, dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    · simp [gr, cD, dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, val_cast hM0, ← hcd]
      rw [ZMod.cast_mul hM0, ZMod.cast_mul hM0]
      ring
  unfold Xi UpperTheory.Kd.K4.CgF
  intro u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_filter, Finset.sum_filter, map_sum, map_sub, sub_eq_zero]
  conv_rhs => rw [← Fintype.sum_equiv (Equiv.mulRight (dg d⁻¹)) _ _ (fun _ => rfl)]
  rw [← sub_eq_zero, ← map_sub, ← Finset.sum_sub_distrib, map_sum]
  apply Finset.sum_eq_zero
  intro m _
  simp only [Equiv.coe_mulRight]
  have hdet : Matrix.GeneralLinearGroup.det (m * dg d⁻¹) = Matrix.GeneralLinearGroup.det m * d⁻¹ := by
    rw [map_mul]
    congr 1
    ext
    simp [dg, Matrix.det_fin_two, Matrix.GeneralLinearGroup.val_det_apply]
  have hent : ∀ i, ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0 =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0 ∧
      ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1 =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1 * ((d⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    intro i
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have hC : Cnd l N g ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) ↔
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    unfold Cnd
    rw [(hent 1).1, (hent 0).1]
  have hP : Matrix.GeneralLinearGroup.det m * d⁻¹ * d = Matrix.GeneralLinearGroup.det m := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  simp only [hdet, hP]
  by_cases h : Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)
  · rw [if_pos h, if_pos ⟨hC.2 h.1, h.2⟩]
    unfold tw
    rw [hgr x m, hgr y m]
    refine term X l n N hN s _ _ _ _ ?_
    rw [dvd_iff]
    simp only [map_sub, map_mul, map_pow, map_add, map_natCast, (hent 0).1, (hent 0).2]
    have hdl : Units.map (ZMod.castHom hlM (ZMod (l ^ n)) : ZMod M →* ZMod (l ^ n)) d = cycM (l ^ n) s :=
      (hcyc M s).2.2.2.2 (l ^ n) hlM
    have hχ : PadicInt.toZModPow n (((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]ˣ) : ℤ_[l]) =
        ZMod.castHom hlM (ZMod (l ^ n)) (d : ZMod M) := by
      rw [(dvd_iff l n _ _).1 (sCycZ Ω l n s).2, map_natCast, ZMod.natCast_zmod_val, ← hdl]
      rfl
    have hc : (((cyc (l ^ n) s).val : ℕ) : ZMod (l ^ n)) = ZMod.castHom hlM (ZMod (l ^ n)) (d : ZMod M) := by
      rw [ZMod.natCast_zmod_val, (hcyc (l ^ n) s).1, ← hdl]
      rfl
    simp only [hc, hχ, val_cast hlM, Units.val_mul, mul_inv_rev, inv_inv, map_mul]
    clear hcyc hgr hcd hC hP hdl hone hinv hent hdet h
    set φ := ZMod.castHom hlM (ZMod (l ^ n))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, map_mul, hχ]
    have hdd : φ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) * φ (d : ZMod M) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have key : φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * φ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) *
        (φ (d : ZMod M) * PadicInt.toZModPow n (u 1)) =
        φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1) := by
      linear_combination (φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1)) * hdd
    rw [key]
    ring
  · rw [if_neg h, if_neg (fun h' => h ⟨hC.1 h'.1, h'.2⟩), map_zero, sub_zero, map_zero]
