import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
import Development.AbelianVarietyTheory.Definitions.Foundations.FrobLiftWittClosure

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem nl_det {K : Type} [Field K] {n : ℕ} (w v : Fin n → K) (hw : Function.Injective w)
    (L : Matrix (Fin n) (Fin n) K) (h : ∀ k j : Fin n, v k * w k ^ (j : ℕ) = ∑ i, L i j * w k ^ (i : ℕ)) :
    L.det = ∏ k, v k := by
  have hV : (Matrix.vandermonde w).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hw
  have hmul : Matrix.vandermonde w * L = Matrix.diagonal v * Matrix.vandermonde w := by
    ext k j
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.vandermonde_apply, h k j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.vandermonde_apply]
    ring
  have key := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at key
  exact mul_left_cancel₀ hV (key.trans (mul_comm _ _))

private theorem nl_dec {S : Type} [CommRing S] [Nontrivial S] (n : ℕ) (hn : 0 < n) (F : Polynomial S) :
    ∃ G : Fin n → Polynomial S, F = ∑ i, Polynomial.expand S n (G i) * (Polynomial.X - 1) ^ (i : ℕ) := by
  classical
  let P : Polynomial S → Prop := fun F => ∃ G : Fin n → Polynomial S,
    F = ∑ i, Polynomial.expand S n (G i) * (Polynomial.X - 1) ^ (i : ℕ)
  suffices hall : ∀ F, P F from hall F
  have h0 : P 0 := ⟨0, by simp⟩
  have hadd : ∀ F₁ F₂, P F₁ → P F₂ → P (F₁ + F₂) := by
    rintro F₁ F₂ ⟨G₁, rfl⟩ ⟨G₂, rfl⟩
    exact ⟨G₁ + G₂, by simp [add_mul, Finset.sum_add_distrib]⟩
  have hmul : ∀ H F, P F → P (Polynomial.expand S n H * F) := by
    rintro H F ⟨G, rfl⟩
    exact ⟨fun i => H * G i, by simp [Finset.mul_sum, mul_assoc]⟩
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → Polynomial S), (∀ j ∈ s, P (f j)) → P (∑ j ∈ s, f j) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hbase : ∀ j, j < n → P ((Polynomial.X - 1) ^ j) := by
    intro j hj
    refine ⟨Pi.single ⟨j, hj⟩ 1, ?_⟩
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  have hXr : ∀ r, r < n → P (Polynomial.X ^ r) := by
    intro r hr
    have e : (Polynomial.X : Polynomial S) ^ r = ((Polynomial.X - 1) + 1) ^ r := by ring
    rw [e, add_pow]
    refine hsum _ _ fun j hj => ?_
    have hj' : j < n := by
      have := Finset.mem_range.mp hj
      omega
    have e2 : (Polynomial.X - 1 : Polynomial S) ^ j * 1 ^ (r - j) * (r.choose j : Polynomial S)
        = Polynomial.expand S n (Polynomial.C (r.choose j : S)) * (Polynomial.X - 1) ^ j := by
      simp [mul_comm]
    rw [e2]
    exact hmul _ _ (hbase j hj')
  intro F
  induction F using Polynomial.induction_on' with
  | add p q hp hq => exact hadd _ _ hp hq
  | monomial k c =>
    have e : Polynomial.monomial k c
        = Polynomial.expand S n (Polynomial.C c * Polynomial.X ^ (k / n)) * Polynomial.X ^ (k % n) := by
      rw [map_mul, Polynomial.expand_C, map_pow, Polynomial.expand_X, ← pow_mul, mul_assoc, ← pow_add,
        Nat.div_add_mod, Polynomial.C_mul_X_pow_eq_monomial]
    rw [e]
    exact hmul _ _ (hXr _ (Nat.mod_lt _ hn))

private theorem nl_card (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1).card = l := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hl0 : l ≠ 0 := hl.out.ne_zero
  haveI : NeZero (l ^ (k + 1 + 1)) := ⟨pow_ne_zero _ hl0⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl0⟩
  have hdvd : l ^ (k + 1) ∣ l ^ (k + 1 + 1) := pow_dvd_pow l (Nat.le_succ _)
  have hsurj : Function.Surjective (red l (k + 1)) := ZMod.unitsMap_surjective hdvd
  have hc := (red l (k + 1)).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (k + 1)))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (k + 1 + 1)))ˣ),
    ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ hl.out, Nat.totient_prime_pow_succ hl.out] at hc
  have hker : Nat.card (red l (k + 1)).ker
      = (Finset.univ.filter fun x : (ZMod (l ^ (k + 1 + 1)))ˣ => red l (k + 1) x = 1).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => MonoidHom.mem_ker)
  rw [← hker]
  have hpos : 0 < l ^ k * (l - 1) :=
    Nat.mul_pos (pow_pos hl.out.pos k) (by have := hl.out.two_le; omega)
  have e : l ^ (k + 1) * (l - 1) = l * (l ^ k * (l - 1)) := by ring
  rw [e] at hc
  exact Nat.eq_of_mul_eq_mul_right hpos hc

private theorem nl_nrm {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : 1 ≤ m)
    [IsAdicComplete (Ideal.span {(p : R)}) R] (hu : (p : R) ∈ nonunits R) (h : PowerSeries R)
    (c : Matrix (Fin p) (Fin p) (PowerSeries R))
    (hc : ∀ j : Fin p, h * PowerSeries.X ^ (j : ℕ) = ∑ i, phi p hp.out.pos (c i j) * PowerSeries.X ^ (i : ℕ)) :
    nrm p m hm (ev R p (m + 1) h) = ev R p m c.det := by
  classical
  have hb : ∀ j : Fin p, (Model.basis p hu j : Model.Up R p) = (PowerSeries.X ^ (j : ℕ) : PowerSeries R) := by
    intro j
    rw [Model.basis, Module.Basis.mk_apply]
  have hn : normOp p h = c.det := by
    have key := Algebra.norm_eq_matrix_det (Model.basis p hu) (show Model.Up R p from h)
    refine key.trans ?_
    congr 1
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have e : (show Model.Up R p from h) * Model.basis p hu j = ∑ i', c i' j • Model.basis p hu i' := by
      rw [hb j]
      refine (hc j).trans ?_
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hb i']
      rfl
    rw [e, map_sum]
    simp [Finsupp.single_apply]
  rw [Model.nrm_ev p m hm hu h, hn]

theorem UpperTheory.Kd.C7.pNormLev :
    UpperTheory.Kd.C7.SNormLev := by
  intro l hl hl2 Ω _ _ _ A hA jj Φ ζ hζ m hm P Q hPQ
  classical
  have hlp : l.Prime := hl.out
  have hl0 : 0 < l := hlp.pos
  haveI : IsAdicComplete (Ideal.span {(l : Φ.R)}) Φ.R := Φ.fl.complete
  have hu : (l : Φ.R) ∈ nonunits Φ.R := Φ.fl.prime.not_unit
  let ψ : Polynomial (R0 A) →+* PowerSeries Φ.R :=
    (Polynomial.eval₂RingHom PowerSeries.C (1 + PowerSeries.X)).comp (Polynomial.mapRingHom Φ.i0)
  have hψ : ∀ F, Φ.ser F = ψ F := fun F => rfl
  have hψX : ψ (Polynomial.X - 1) = PowerSeries.X := by simp [ψ]
  have hψexp : ∀ F, ψ (Polynomial.expand (R0 A) l F) = phi l hl0 (ψ F) := by
    intro F
    simp only [ψ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_eval₂RingHom]
    rw [Polynomial.map_expand, phi_eval₂]
  have hdec : ∀ jx : Fin l, ∃ G : Fin l → Polynomial (R0 A),
      P * (Polynomial.X - 1) ^ (jx : ℕ) = ∑ i, Polynomial.expand (R0 A) l (G i) * (Polynomial.X - 1) ^ (i : ℕ) :=
    fun jx => nl_dec l hl0 _
  choose G hG using hdec
  let M : Matrix (Fin l) (Fin l) (Polynomial (R0 A)) := Matrix.of fun i jx => G jx i
  have hc : ∀ jx : Fin l, Φ.ser P * PowerSeries.X ^ (jx : ℕ)
      = ∑ i, phi l hl0 ((ψ.mapMatrix M) i jx) * PowerSeries.X ^ (i : ℕ) := by
    intro jx
    have := congrArg ψ (hG jx)
    rw [map_mul, map_pow, hψX, map_sum] at this
    rw [hψ, this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hψX, hψexp]
    rfl
  have hnorm := nl_nrm l m hm hu (Φ.ser P) (ψ.mapMatrix M) hc
  rw [hnorm, ← RingHom.map_det, ← hψ]
  have hcard : Fintype.card {x : (ZMod (l ^ (m + 1)))ˣ // red l m x = 1} = l := by
    rw [Fintype.card_subtype]
    exact nl_card l m hm
  let e : Fin l ≃ {x : (ZMod (l ^ (m + 1)))ˣ // red l m x = 1} := (Fintype.equivFinOfCardEq hcard).symm
  let w : Fin l → Ω := fun k => ζ (m + 1) ^ (((e k : (ZMod (l ^ (m + 1)))ˣ) : ZMod (l ^ (m + 1))).val)
  have hprim := (hζ (m + 1)).1
  haveI : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hlp.ne_zero⟩
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hlp.ne_zero⟩
  have hmodpow : ∀ a : ℕ, ζ (m + 1) ^ a = ζ (m + 1) ^ (a % l ^ (m + 1)) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a (l ^ (m + 1)), pow_add, pow_mul, hprim.pow_eq_one, one_pow, mul_one]
  have hwpow : ∀ k, w k ^ l = ζ m := by
    intro k
    have hx := (e k).2
    have h0 : (((e k : (ZMod (l ^ (m + 1)))ˣ) : ZMod (l ^ (m + 1))).cast : ZMod (l ^ m)) = 1 :=
      congrArg Units.val hx
    rw [ZMod.cast_eq_val] at h0
    have h1 : (((e k : (ZMod (l ^ (m + 1)))ˣ) : ZMod (l ^ (m + 1))).val : ZMod (l ^ m)) = ((1 : ℕ) : ZMod (l ^ m)) := by
      rw [Nat.cast_one]
      exact h0
    have hmod := ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1).mul_right' l
    rw [← pow_succ, one_mul] at hmod
    show (ζ (m + 1) ^ _) ^ l = ζ m
    rw [← pow_mul, ← (hζ m).2, hmodpow (_ * l), hmodpow l]
    exact congrArg (fun t => ζ (m + 1) ^ t) hmod
  have hwinj : Function.Injective fun k => w k - 1 := by
    intro a b hab
    have h2 : w a = w b := by simpa using hab
    have h3 := hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
    exact e.injective (Subtype.ext (Units.ext (ZMod.val_injective _ h3)))
  have hev : ∀ (F : Polynomial (R0 A)) (z : Ω), pv (Polynomial.expand (R0 A) l F) z = pv F (z ^ l) := by
    intro F z
    simp only [pv]
    rw [← Polynomial.eval_map, ← Polynomial.eval_map, Polynomial.map_expand, Polynomial.expand_eval]
  have hrow : ∀ k (jx : Fin l), pv P (w k) * (w k - 1) ^ (jx : ℕ)
      = ∑ i, pv (G jx i) (ζ m) * (w k - 1) ^ (i : ℕ) := by
    intro k jx
    have := congrArg (Polynomial.eval₂ (R0 A).subtype (w k)) (hG jx)
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_one, Polynomial.eval₂_finset_sum] at this
    rw [show pv P (w k) = Polynomial.eval₂ (R0 A).subtype (w k) P from rfl, this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hwpow k, ← hev]
    rfl
  have hdetL := nl_det (fun k => w k - 1) (fun k => pv P (w k)) hwinj
      (Matrix.of fun i jx => pv (G jx i) (ζ m)) (fun k jx => hrow k jx)
  have hpvdet : pv M.det (ζ m) = (Matrix.of fun i jx => pv (G jx i) (ζ m)).det :=
    RingHom.map_det (Polynomial.eval₂RingHom (R0 A).subtype (ζ m)) M
  have hprod : ∏ k, pv P (w k) = pv Q (ζ m) := by
    rw [← hPQ, Finset.prod_subtype (p := fun x => red l m x = 1) _ (fun x => by simp)]
    convert e.prod_comp (fun x => pv P (ζ (m + 1) ^ ((x : (ZMod (l ^ (m + 1)))ˣ) : ZMod (l ^ (m + 1))).val))
  have hzero : pv (M.det - Q) (ζ m) = 0 := by
    have hs : pv (M.det - Q) (ζ m) = pv M.det (ζ m) - pv Q (ζ m) := Polynomial.eval₂_sub _
    rw [hs, hpvdet, hdetL, hprod, sub_self]
  have key := (pWD l hl2 Ω A hA jj Φ ζ hζ m hm (M.det - Q)).1 hzero
  rw [hψ, map_sub, ← hψ, ← hψ, map_sub] at key
  exact sub_eq_zero.mp key
