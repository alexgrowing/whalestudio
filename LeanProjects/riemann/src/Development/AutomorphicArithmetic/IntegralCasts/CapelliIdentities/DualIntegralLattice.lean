import Mathlib

theorem UpperTheory.Reformulated.B.DualIntegralLattice.aux2 :
    ∀ (E : Type) [inst : Field E] [inst_1 : NumberField E], (Algebra.traceForm ℚ E).Nondegenerate := by
  intro E _ _
  exact traceForm_nondegenerate ℚ E

noncomputable def UpperTheory.Reformulated.B.DualIntegralLattice.dualInt :
    (E : Type) →
      [inst : Field E] → [inst_1 : NumberField E] → Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E) → E :=
    fun (E : Type) [Field E] [NumberField E] (k : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E)) ↦
      ((Algebra.traceForm ℚ E).dualBasis (UpperTheory.Reformulated.B.DualIntegralLattice.aux2 E) (NumberField.integralBasis E) :
          Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E) → E)
        k

private theorem key1 {S : Type} [CommRing S] [IsDomain S] [CharZero S] {ι : Type} [Fintype ι]
    {p R N : ℕ} (hp : p.Prime) (hR : 1 ≤ R) (c : S ≃+* S) (b w : ι → S) (T : S →+ ℤ) (d : ℤ)
    (hd : ¬ (p : ℤ) ∣ d)
    (hdual : ∀ a : S, d • a = ∑ k, T (a * w k) • b k)
    (e : (Fin N → S) →+ (Fin N → S) →+ ZMod (p ^ R))
    (hadj : ∀ (a : S) (x y : Fin N → S), e (a • x) y = e x (c a • y))
    (hnd : ∀ x, e x = 0 → ∃ x', x = p ^ R • x')
    (x : Fin N → S)
    (hx : ∀ j, ∃ z : S, ∑ i, x i *
      (∑ k, ((e (Pi.single i (b k)) (Pi.single j 1)).val : S) * w k) = (p : S) * z) :
    ∃ x' : Fin N → S, x = p • x' := by
  classical
  haveI : NeZero (p ^ R) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have star : ∀ (i j : Fin N) (a : S), (d : ZMod (p ^ R)) * e (Pi.single i a) (Pi.single j 1) =
      ((T (a * ∑ k, ((e (Pi.single i (b k)) (Pi.single j 1)).val : S) * w k) : ℤ) : ZMod (p ^ R)) := by
    intro i j a
    let g : S →+ ZMod (p ^ R) := (e.flip (Pi.single j 1)).comp (AddMonoidHom.single (fun _ => S) i)
    have hg : ∀ a, g a = e (Pi.single i a) (Pi.single j 1) := fun _ => rfl
    simp only [← hg]
    have h1 : (d : ZMod (p ^ R)) * g a = g (d • a) := by
      rw [map_zsmul, zsmul_eq_mul]
    rw [h1, hdual, map_sum, Finset.mul_sum, map_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h2 : a * (((g (b k)).val : S) * w k) = ((g (b k)).val : ℕ) • (a * w k) := by
      rw [nsmul_eq_mul]; ring
    rw [h2, map_nsmul, map_zsmul, nsmul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_comm]
  obtain ⟨W, hW⟩ : ∃ W : Fin N → Fin N → S, ∀ i j, W i j =
      ∑ k, ((e (Pi.single i (b k)) (Pi.single j 1)).val : S) * w k := ⟨_, fun _ _ => rfl⟩
  simp only [← hW] at star hx
  have expand : ∀ y : Fin N → S, (d : ZMod (p ^ R)) * e x y =
      ((T (∑ j, c.symm (y j) * ∑ i, x i * W i j) : ℤ) : ZMod (p ^ R)) := by
    intro y
    have hxs : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
    have hys : y = ∑ j, Pi.single j (y j) := (Finset.univ_sum_single y).symm
    have term : ∀ i j, (d : ZMod (p ^ R)) * e (Pi.single i (x i)) (Pi.single j (y j)) =
        ((T (c.symm (y j) * (x i * W i j)) : ℤ) : ZMod (p ^ R)) := by
      intro i j
      have h1 : (Pi.single j (y j) : Fin N → S) = c (c.symm (y j)) • Pi.single j 1 := by
        rw [c.apply_symm_apply, ← Pi.single_smul, smul_eq_mul, mul_one]
      have h2 : c.symm (y j) • (Pi.single i (x i) : Fin N → S) =
          Pi.single i (c.symm (y j) * x i) := by
        rw [← Pi.single_smul, smul_eq_mul]
      rw [h1, ← hadj, h2, star, mul_assoc]
    conv_lhs => rw [hxs, map_sum, AddMonoidHom.finset_sum_apply, hys]
    simp only [map_sum, Finset.mul_sum, Int.cast_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact term i j
  choose z hz using hx
  have hpR : ((p : ZMod (p ^ R))) ^ R = 0 := by
    exact_mod_cast ZMod.natCast_self (p ^ R)
  have h3 : ∀ y, ((p : ZMod (p ^ R)) ^ (R - 1) * d) * e x y = 0 := by
    intro y
    rw [mul_assoc, expand]
    simp only [hz]
    have h4 : ∑ j, c.symm (y j) * ((p : S) * z j) = p • ∑ j, c.symm (y j) * z j := by
      rw [nsmul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h4, map_nsmul, nsmul_eq_mul]
    push_cast
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hR, hpR, zero_mul]
  have h4 : e (((p : ℤ) ^ (R - 1) * d) • x) = 0 := by
    refine AddMonoidHom.ext fun y => ?_
    have h5 : e (((p : ℤ) ^ (R - 1) * d) • x) y = ((p : ℤ) ^ (R - 1) * d) • e x y :=
      map_zsmul (e.flip y) _ x
    rw [h5, zsmul_eq_mul]
    push_cast
    exact h3 y
  obtain ⟨x', hx'⟩ := hnd _ h4
  have hp0 : (p : S) ^ (R - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have h5 : ∀ i, (d : S) * x i = p * x' i := by
    intro i
    have h6 := congrFun hx' i
    simp only [Pi.smul_apply, zsmul_eq_mul, nsmul_eq_mul] at h6
    push_cast at h6
    apply mul_left_cancel₀ hp0
    rw [← mul_assoc, h6, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hR]
  have hcop : IsCoprime d (p : ℤ) :=
    (((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).mpr hd).symm
  obtain ⟨u, v, huv⟩ := hcop
  have huv' : (u : S) * d + v * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → S) huv
  refine ⟨fun i => (u : S) * x' i + (v : S) * x i, funext fun i => ?_⟩
  simp only [Pi.smul_apply, nsmul_eq_mul]
  linear_combination (-(x i)) * huv' + (u : S) * h5 i

private theorem key2 {S : Type} [CommRing S] {N p : ℕ} [Finite (S ⧸ Ideal.span {(p : S)})]
    (W : Matrix (Fin N) (Fin N) S)
    (hW : ∀ x : Fin N → S, (∀ j, ∃ z : S, ∑ i, x i * W i j = (p : S) * z) →
      ∃ x' : Fin N → S, x = p • x') :
    ∃ u z : S, W.det * u = 1 + (p : S) * z := by
  classical
  let I : Ideal S := Ideal.span {(p : S)}
  let π : S →+* S ⧸ I := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hker : ∀ s : S, π s = 0 → ∃ z, s = (p : S) * z := by
    intro s hs
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hs)
    exact ⟨a, by rw [← ha, mul_comm]⟩
  have hp0 : π (p : S) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let Wb : Matrix (Fin N) (Fin N) (S ⧸ I) := W.map π
  have inj : Function.Injective (fun v : Fin N → S ⧸ I => Matrix.vecMul v Wb) := by
    intro v1 v2 h
    have h0 : Matrix.vecMul (v1 - v2) Wb = 0 := by
      rw [Matrix.sub_vecMul]; exact sub_eq_zero.mpr h
    choose x hx using fun i => hπ ((v1 - v2) i)
    obtain ⟨x', hx'⟩ := hW x (fun j => by
      refine hker _ ?_
      have := congrFun h0 j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [map_sum, ← this]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hx]; rfl)
    refine sub_eq_zero.mp (funext fun i => ?_)
    rw [← hx, hx']
    simp [hp0]
  have surj := Finite.injective_iff_surjective.mp inj
  choose G hG using fun j : Fin N => surj (Pi.single j 1)
  have hGW : (Matrix.of G) * Wb = 1 := by
    ext i j
    have := congrFun (hG i) j
    simp only [Matrix.vecMul, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp [eq_comm]
  have hdet : (Matrix.of G).det * π W.det = 1 := by
    have h1 : π W.det = Wb.det := RingHom.map_det π W
    rw [h1, ← Matrix.det_mul, hGW, Matrix.det_one]
  obtain ⟨u, hu⟩ := hπ (Matrix.of G).det
  obtain ⟨z, hz⟩ := hker (W.det * u - 1) (by
    rw [map_sub, map_mul, hu, map_one, mul_comm, hdet, sub_self])
  exact ⟨u, z, by linear_combination hz⟩

private theorem key3 {S O : Type} [CommRing S] [CommRing O] [IsLocalRing O] {N p : ℕ}
    (τ : S →+* O) (hp : ¬ IsUnit (p : O)) (W : Matrix (Fin N) (Fin N) S)
    (h : ∃ u z : S, W.det * u = 1 + (p : S) * z) : IsUnit (W.map τ).det := by
  obtain ⟨u, z, h⟩ := h
  have h1 : (W.map τ).det * τ u = 1 + (p : O) * τ z := by
    have h2 : τ W.det = (W.map τ).det := RingHom.map_det τ W
    rw [← h2, ← map_mul, h]
    simp
  have h3 : IsUnit (1 + (p : O) * τ z) := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-((p : O) * τ z)) with h4 | h4
    · exact absurd (isUnit_of_mul_isUnit_left (IsUnit.neg_iff _ |>.mp h4)) hp
    · simpa using h4
  rw [← h1] at h3
  exact isUnit_of_mul_isUnit_left h3

open NumberField in
private theorem key4 (E : Type) [Field E] [NumberField E] :
    ∃ (T : 𝓞 E →+ ℤ) (w : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E),
      (∀ k, ((w k : 𝓞 E) : E) = (discr E : E) * UpperTheory.Reformulated.B.DualIntegralLattice.dualInt E k) ∧
      ∀ a : 𝓞 E, discr E • a = ∑ k, T (a * w k) • RingOfIntegers.basis E k := by
  classical
  let b := RingOfIntegers.basis E
  let T : 𝓞 E →ₗ[ℤ] ℤ := Algebra.trace ℤ (𝓞 E)
  let Q := Algebra.traceMatrix ℤ b
  have hQ : Q.det = discr E := (discr_eq_discr E b).symm ▸ rfl
  let w : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E := fun k => ∑ l, Q.adjugate k l • b l
  have hQ' : ∀ l m, T (b l * b m) = Q l m := fun l m => by
    simp [Q, T, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hTw : ∀ m k, T (b m * w k) = if k = m then discr E else 0 := by
    intro m k
    have h1 : T (b m * w k) = (Q.adjugate * Q) k m := by
      simp only [w, Finset.mul_sum, map_sum, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_smul_comm, map_zsmul, mul_comm (b m), hQ', smul_eq_mul]
    rw [h1, Matrix.adjugate_mul, hQ, Matrix.smul_apply, Matrix.one_apply]
    simp
  have hint : ∀ a : 𝓞 E, Algebra.trace ℚ E (a : E) = (T a : ℚ) := by
    intro a
    have := Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E) a
    rw [Algebra.intTrace_eq_trace] at this
    simpa using this.symm
  refine ⟨T.toAddMonoidHom, w, ?_, ?_⟩
  · intro k
    apply (((Algebra.traceForm ℚ E).dualBasis (UpperTheory.Reformulated.B.DualIntegralLattice.aux2 E)
      (integralBasis E)).repr).injective
    refine Finsupp.ext fun i => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, LinearMap.BilinForm.dualBasis_repr_apply]
    have hR : (Algebra.traceForm ℚ E) ((discr E : E) * UpperTheory.Reformulated.B.DualIntegralLattice.dualInt E k)
        (integralBasis E i) = (discr E : ℚ) * if i = k then 1 else 0 := by
      have h1 : (discr E : E) * UpperTheory.Reformulated.B.DualIntegralLattice.dualInt E k =
          (discr E : ℚ) • UpperTheory.Reformulated.B.DualIntegralLattice.dualInt E k := by
        rw [Algebra.smul_def]; simp
      rw [h1, map_smul, LinearMap.smul_apply, smul_eq_mul]
      congr 1
      exact LinearMap.BilinForm.apply_dualBasis_left _ _ _ _
    rw [hR, Algebra.traceForm_apply, integralBasis_apply, mul_comm]
    have h2 : algebraMap (𝓞 E) E (RingOfIntegers.basis E i) * ((w k : 𝓞 E) : E) =
        ((b i * w k : 𝓞 E) : E) := by simp [b]
    rw [h2, hint, hTw]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik, Ne.symm hik]
  · intro a
    have hTa : ∀ k, T (a * w k) = b.repr a k * discr E := by
      intro k
      conv_lhs => rw [← b.sum_repr a]
      rw [Finset.sum_mul, map_sum]
      simp only [smul_mul_assoc, map_zsmul, hTw, smul_eq_mul]
      simp
    change discr E • a = ∑ k, T (a * w k) • b k
    simp only [hTa]
    conv_lhs => rw [← b.sum_repr a]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, mul_comm]

theorem UpperTheory.Reformulated.B.DualIntegralLattice.main :
    ∀ (E : Type) [inst : Field E] [inst_1 : NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact (Nat.Prime p)],
      (1 : ℕ) ≤ R →
        ¬(↑p : ℤ) ∣ NumberField.discr E →
          ∀ (e : (Fin N → NumberField.RingOfIntegers E) →+ (Fin N → NumberField.RingOfIntegers E) →+ ZMod (p ^ R)),
            (∀ (a : NumberField.RingOfIntegers E) (x y : Fin N → NumberField.RingOfIntegers E),
                ((e : (Fin N → NumberField.RingOfIntegers E) → (Fin N → NumberField.RingOfIntegers E) →+ ZMod (p ^ R))
                        (a • x) :
                      (Fin N → NumberField.RingOfIntegers E) → ZMod (p ^ R))
                    y =
                  ((e : (Fin N → NumberField.RingOfIntegers E) → (Fin N → NumberField.RingOfIntegers E) →+ ZMod (p ^ R)) x :
                      (Fin N → NumberField.RingOfIntegers E) → ZMod (p ^ R))
                    ((NumberField.RingOfIntegers.mapRingEquiv cc :
                          NumberField.RingOfIntegers E → NumberField.RingOfIntegers E)
                        a •
                      y)) →
              (∀ (x : Fin N → NumberField.RingOfIntegers E),
                  (e : (Fin N → NumberField.RingOfIntegers E) → (Fin N → NumberField.RingOfIntegers E) →+ ZMod (p ^ R)) x =
                      (0 : (Fin N → NumberField.RingOfIntegers E) →+ ZMod (p ^ R)) →
                    ∃ (x' : Fin N → NumberField.RingOfIntegers E), x = p ^ R • x') →
                ∀ (O Ω : Type) [inst_3 : CommRing O] [IsDomain O] [IsLocalRing O] [inst_6 : Field Ω] [inst_7 : Algebra O Ω],
                  Function.Injective (⇑(Algebra.algebraMap O Ω) : O → Ω) →
                    ¬IsUnit (↑p : O) →
                      ∀ (σ : E →+* Ω),
                        (∀ (a : NumberField.RingOfIntegers E),
                            ∃ (o : O), (Algebra.algebraMap O Ω : O → Ω) o = (σ : E → Ω) (↑a : E)) →
                          ∃ (C : Matrix (Fin N) (Fin N) Ω),
                            (∀ (i j : Fin N), C i j ∈ (Algebra.algebraMap O Ω).range) ∧
                              ((Matrix.of : (Fin N → Fin N → Ω) → Matrix (Fin N) (Fin N) Ω) fun (i j : Fin N) ↦
                                    ∑ k : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E),
                                      (σ : E → Ω) (UpperTheory.Reformulated.B.DualIntegralLattice.dualInt E k) *
                                        (↑(((e :
                                                      (Fin N → NumberField.RingOfIntegers E) →
                                                        (Fin N → NumberField.RingOfIntegers E) →+ ZMod (p ^ R))
                                                    (Pi.single i
                                                      ((NumberField.RingOfIntegers.basis E :
                                                          Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E) →
                                                            NumberField.RingOfIntegers E)
                                                        k)) :
                                                  (Fin N → NumberField.RingOfIntegers E) → ZMod (p ^ R))
                                                (Pi.single j (1 : NumberField.RingOfIntegers E))).val :
                                          Ω)) *
                                  C =
                                (1 : Matrix (Fin N) (Fin N) Ω) := by
  intro E _ _ cc p R N hfact hR hd e hadj hnd O Ω _ _ _ _ _ hinj hpu σ hσ
  classical
  have hp : p.Prime := hfact.out
  obtain ⟨T, w, hw, hdual⟩ := key4 E
  let W : Matrix (Fin N) (Fin N) (NumberField.RingOfIntegers E) := Matrix.of fun i j =>
    ∑ k, ((e (Pi.single i (NumberField.RingOfIntegers.basis E k)) (Pi.single j 1)).val :
      NumberField.RingOfIntegers E) * w k
  haveI : Finite (NumberField.RingOfIntegers E ⧸
      Ideal.span {((p : ℕ) : NumberField.RingOfIntegers E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simp [hp.ne_zero])
  have hkey := key2 (p := p) W (fun x hx =>
    key1 hp hR (NumberField.RingOfIntegers.mapRingEquiv cc) _ w T _ hd hdual e hadj hnd x hx)
  choose t ht using hσ
  let τ : NumberField.RingOfIntegers E →+* O :=
    { toFun := t
      map_one' := hinj (by rw [ht]; simp)
      map_zero' := hinj (by rw [ht]; simp)
      map_mul' := fun a b => hinj (by rw [ht, map_mul, ht, ht]; simp)
      map_add' := fun a b => hinj (by rw [ht, map_add, ht, ht]; simp) }
  have hdet := key3 τ hpu W hkey
  let Wo := W.map τ
  have hinv : Wo * Wo⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hfin : ∀ M : Matrix (Fin N) (Fin N) Ω,
      (∀ i j, ((NumberField.discr E : ℤ) : Ω) * M i j = algebraMap O Ω (Wo i j)) →
      M * (((NumberField.discr E : ℤ) : Ω) • (Wo⁻¹).map (algebraMap O Ω)) = 1 := by
    intro M hM
    have h1 : ((NumberField.discr E : ℤ) : Ω) • M = Wo.map (algebraMap O Ω) := by
      ext i j
      simpa using hM i j
    rw [Matrix.mul_smul, ← Matrix.smul_mul, h1, ← Matrix.map_mul, hinv]
    simp
  refine ⟨((NumberField.discr E : ℤ) : Ω) • (Wo⁻¹).map (algebraMap O Ω), fun i j =>
    ⟨((NumberField.discr E : ℤ) : O) * Wo⁻¹ i j, by simp⟩, hfin _ fun i j => ?_⟩
  have h2 : algebraMap O Ω (Wo i j) = σ ((W i j : NumberField.RingOfIntegers E) : E) := ht _
  rw [h2]
  simp only [W, Matrix.of_apply, map_sum, map_mul, hw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_natCast, map_mul, map_intCast]
  ring
