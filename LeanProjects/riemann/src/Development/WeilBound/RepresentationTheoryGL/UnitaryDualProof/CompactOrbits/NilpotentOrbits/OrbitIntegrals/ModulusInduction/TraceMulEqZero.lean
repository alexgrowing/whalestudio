import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem qZ_add (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x + y) = qZ Z x + qZ Z y := by
  funext i; simp [qZ, mul_add, trace_add]

theorem qZ_sub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x - y) = qZ Z x - qZ Z y := by
  funext i; simp [qZ, mul_sub, trace_sub]

theorem qZ_smul (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (r : k) (x : Matrix (Fin n) (Fin n) k) :
    qZ Z (r • x) = r • qZ Z x := by
  funext i
  simp only [qZ, Pi.smul_apply, Matrix.mul_smul, trace_smul]

theorem piZ_congr (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {x y : Matrix (Fin n) (Fin n) k}
    (h : qZ Z x = qZ Z y) : piZ Z x = piZ Z y := by
  unfold piZ; rw [h]

theorem piZ_mem (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) : piZ Z x ∈ Z := by
  unfold piZ
  split
  · rename_i h; exact h.choose_spec.1
  · exact Z.zero_mem

theorem qZ_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (h : GL (Fin n) k) (hh : h ∈ Gz Z)
    (x : Matrix (Fin n) (Fin n) k) : qZ Z (h.val * x * h⁻¹.val) = qZ Z x := by
  funext i
  simp only [qZ]
  have hb := hh _ ((Module.finBasis k Z) i).2
  have e1 : (((Module.finBasis k Z) i : Z) : Matrix (Fin n) (Fin n) k) * (h.val * x * h⁻¹.val)
      = h.val * ((((Module.finBasis k Z) i : Z) : Matrix (Fin n) (Fin n) k) * x) * h⁻¹.val := by
    simp only [← mul_assoc, hb]
  rw [e1, trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem conj_of_mem (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (h : GL (Fin n) k) (hh : h ∈ Gz Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) : h.val * c * h⁻¹.val = c := by
  rw [← hh c hc, mul_assoc, Units.mul_inv, mul_one]

theorem sig_act (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (h : GL (Fin n) k) (hh : h ∈ Gz Z)
    (q : Sp k n) : sig Z t (act h q) = act h (sig Z t q) := by
  have h1 : piZ Z (h.val * q.1 * h⁻¹.val) = piZ Z q.1 := piZ_congr Z (qZ_conj Z h hh q.1)
  have h2 : h.val * piZ Z q.1 * h⁻¹.val = piZ Z q.1 := conj_of_mem Z h hh (piZ_mem Z q.1)
  simp only [sig, act]
  refine Prod.ext ?_ rfl
  show piZ Z (h.val * q.1 * h⁻¹.val) + (t : k) • (h.val * q.1 * h⁻¹.val - piZ Z (h.val * q.1 * h⁻¹.val))
    = h.val * (piZ Z q.1 + (t : k) • (q.1 - piZ Z q.1)) * h⁻¹.val
  rw [h1, mul_add, add_mul, h2, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, h2]

theorem reg_in (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) : ∃ g ∈ Z, c * g * c = c := by
  obtain ⟨hcomm, hred⟩ := hZ
  haveI := hred
  have hint : IsIntegral k c := Algebra.IsIntegral.isIntegral c
  have hp0 : minpoly k c ≠ 0 := minpoly.ne_zero hint
  obtain ⟨q, hpq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly k c) hp0 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h0
    apply hnd
    rw [map_zero, sub_zero, Polynomial.X_dvd_iff]
    exact h0
  have haZ : Polynomial.aeval c q.divX ∈ Z :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hc) (Polynomial.aeval_mem_adjoin_singleton k c)
  have hev : q.coeff 0 • c ^ Polynomial.rootMultiplicity 0 (minpoly k c)
      + c ^ Polynomial.rootMultiplicity 0 (minpoly k c) * c * Polynomial.aeval c q.divX = 0 := by
    have h1 := minpoly.aeval k c
    rw [hpq, ← Polynomial.X_mul_divX_add q] at h1
    simp only [map_mul, map_pow, map_sub, map_add, Polynomial.aeval_X, Polynomial.aeval_C, map_zero,
      sub_zero] at h1
    rw [mul_add, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, ← mul_assoc] at h1
    rw [add_comm]
    exact h1
  generalize Polynomial.rootMultiplicity 0 (minpoly k c) = m at hev
  generalize Polynomial.aeval c q.divX = a at hev haZ
  generalize q.coeff 0 = s at hev hq0
  have h2 : c ^ m * c * a = -(s • c ^ m) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hev
  have hgZ : (-(s⁻¹) • a) ∈ Z := Z.smul_mem haZ _
  have hmu : c ^ m * (1 - c * (-(s⁻¹) • a)) = 0 := by
    rw [mul_sub, mul_one, Matrix.mul_smul, Matrix.mul_smul, ← mul_assoc, h2, smul_neg, neg_smul,
      neg_neg, smul_smul, inv_mul_cancel₀ hq0, one_smul, sub_self]
  generalize -(s⁻¹) • a = g at hgZ hmu
  have hcg : Commute c g := hcomm c hc g hgZ
  have hcomm' : Commute c (1 - c * g) := (Commute.one_right c).sub_right ((Commute.refl c).mul_right hcg)
  have hpow : (c * (1 - c * g)) ^ (m + 1) = 0 := by
    rw [hcomm'.mul_pow, pow_succ', pow_succ', mul_assoc, ← mul_assoc (c ^ m), hmu, zero_mul, mul_zero]
  have hdZ : c * (1 - c * g) ∈ Z := Z.mul_mem hc (Z.sub_mem Z.one_mem (Z.mul_mem hc hgZ))
  have hnil : IsNilpotent (⟨c * (1 - c * g), hdZ⟩ : Z) :=
    ⟨m + 1, Subtype.ext (by simpa using hpow)⟩
  have hd0 : c * (1 - c * g) = 0 := congrArg Subtype.val hnil.eq_zero
  refine ⟨g, hgZ, ?_⟩
  rw [mul_sub, mul_one, sub_eq_zero] at hd0
  have hcg' : c * g = g * c := hcg
  rw [mul_assoc, ← hcg']
  exact hd0.symm

theorem idem_zero [CharZero k] (e : Matrix (Fin n) (Fin n) k) (he : e * e = e) (ht : trace e = 0) : e = 0 := by
  have hf : IsIdempotentElem (Matrix.toLin' e) := by
    show Matrix.toLin' e * Matrix.toLin' e = Matrix.toLin' e
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  have ht' : LinearMap.trace k _ (Matrix.toLin' e) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    exact ht
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hf ht'
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

theorem trace_mul_eq_zero (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {c : Matrix (Fin n) (Fin n) k}
    (hq : qZ Z c = 0) {b : Matrix (Fin n) (Fin n) k} (hb : b ∈ Z) : trace (b * c) = 0 := by
  have hsum := (Module.finBasis k Z).sum_repr ⟨b, hb⟩
  have hb' : b = ∑ i, ((Module.finBasis k Z).repr ⟨b, hb⟩ i) •
      (((Module.finBasis k Z) i : Z) : Matrix (Fin n) (Fin n) k) := by
    have h1 := congrArg Subtype.val hsum
    push_cast at h1
    exact h1.symm
  rw [hb', Finset.sum_mul, trace_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.smul_mul, trace_smul]
  have h2 := congrFun hq i
  simp only [qZ, Pi.zero_apply] at h2
  rw [h2, smul_zero]

theorem qZ_inj [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (hq : qZ Z c = 0) : c = 0 := by
  obtain ⟨g, hg, hcgc⟩ := reg_in Z hZ hc
  have hgc : g * c = c * g := hZ.1 g hg c hc
  have hidem : (c * g) * (c * g) = c * g := by
    rw [← mul_assoc, hcgc]
  have htr : trace (c * g) = 0 := by
    rw [trace_mul_comm]
    exact trace_mul_eq_zero Z hq hg
  have he0 := idem_zero (c * g) hidem htr
  rw [← hcgc, he0, zero_mul]

theorem exists_qZ [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (x : Matrix (Fin n) (Fin n) k) : ∃ c ∈ Z, qZ Z c = qZ Z x := by
  let φ : Z →ₗ[k] (Fin (Module.finrank k Z) → k) :=
    { toFun := fun c => qZ Z c.1
      map_add' := fun a b => qZ_add Z a.1 b.1
      map_smul' := fun r a => qZ_smul Z r a.1 }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact Subtype.ext (qZ_inj Z hZ a.2 ha)
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨a, ha⟩ := hsurj (qZ Z x)
  exact ⟨a.1, a.2, ha⟩

theorem piZ_spec [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (x : Matrix (Fin n) (Fin n) k) : qZ Z (piZ Z x) = qZ Z x := by
  unfold piZ
  rw [dif_pos (exists_qZ Z hZ x)]
  exact (exists_qZ Z hZ x).choose_spec.2

theorem piZ_eq [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    {x c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (h : qZ Z c = qZ Z x) : piZ Z x = c := by
  have := qZ_inj Z hZ (Z.sub_mem (piZ_mem Z x) hc) (by rw [qZ_sub, piZ_spec Z hZ, h, sub_self])
  exact sub_eq_zero.mp this

def piL [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k where
  toFun := piZ Z
  map_add' x y := by
    refine piZ_eq Z hZ (Z.add_mem (piZ_mem Z x) (piZ_mem Z y)) ?_
    rw [qZ_add, qZ_add, piZ_spec Z hZ, piZ_spec Z hZ]
  map_smul' r x := by
    refine piZ_eq Z hZ (Z.smul_mem (piZ_mem Z x) r) ?_
    rw [qZ_smul, qZ_smul, piZ_spec Z hZ]; rfl

theorem continuous_piZ [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    Continuous (piZ Z (n := n)) := by
  have hrep : ∀ x : Matrix (Fin n) (Fin n) k,
      piZ Z x = ∑ i, ∑ j, x i j • piZ Z (Matrix.single i j (1 : k)) := by
    intro x
    have h := congrArg (piL Z hZ) (Matrix.matrix_eq_sum_single x)
    have hs : ∀ i j, Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : k) := by
      intro i j
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    simp only [hs, map_sum, map_smul] at h
    exact h
  have hfun : piZ Z (n := n) = fun x => ∑ i, ∑ j, x i j • piZ Z (Matrix.single i j (1 : k)) := funext hrep
  rw [hfun]
  fun_prop

theorem sig_inv_sig [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ)
    (q : Sp k n) : sig Z t⁻¹ (sig Z t q) = q := by
  obtain ⟨x, v⟩ := q
  have hP : piZ Z (piZ Z x + (t : k) • (x - piZ Z x)) = piZ Z x := by
    refine piZ_eq Z hZ (piZ_mem Z x) ?_
    rw [qZ_add, qZ_smul, qZ_sub, piZ_spec Z hZ, sub_self, smul_zero, add_zero]
  simp only [sig]
  refine Prod.ext ?_ rfl
  show piZ Z (piZ Z x + (t : k) • (x - piZ Z x)) + ((t⁻¹ : kˣ) : k) • (piZ Z x + (t : k) • (x - piZ Z x) - piZ Z (piZ Z x + (t : k) • (x - piZ Z x))) = x
  rw [hP, add_sub_cancel_left, smul_smul, Units.inv_mul, one_smul, add_sub_cancel]

theorem continuous_sig [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) :
    Continuous (sig Z t) := by
  have hc := continuous_piZ Z hZ
  unfold sig
  fun_prop

end PositivityTheory.RgUd.T.Nil.Orb.BStep
