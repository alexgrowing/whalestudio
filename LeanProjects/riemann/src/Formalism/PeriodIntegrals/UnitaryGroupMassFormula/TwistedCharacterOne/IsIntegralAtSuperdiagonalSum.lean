import Formalism.PeriodIntegrals.TwChrOne

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwChrOne.Pf

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

lemma mk_ne {s : 𝓞 E} (hs : s ∉ P.asIdeal) : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
  rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]

lemma nm_mul {s s' : 𝓞 E} (hs : s ∉ P.asIdeal) (hs' : s' ∉ P.asIdeal) : s * s' ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs hs'

lemma one_nm : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

lemma reduction_spec {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  let _ := Ideal.Quotient.field P.asIdeal
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ (mk_ne P hs), mul_one]⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc⟩ := hex.choose_spec
  have hx : s * r' = s' * r := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_mul, ← h, ← h']
    ring
  apply mul_left_cancel₀ (mk_ne P hs')
  calc Ideal.Quotient.mk P.asIdeal s' * (Ideal.Quotient.mk P.asIdeal s * hex.choose)
      = Ideal.Quotient.mk P.asIdeal s * (Ideal.Quotient.mk P.asIdeal s' * hex.choose) := by ring
    _ = Ideal.Quotient.mk P.asIdeal (s * r') := by rw [hc, map_mul]
    _ = Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r := by rw [hx, map_mul]

lemma redP_eq {a : E} {r s : 𝓞 E} {x : 𝓞 E ⧸ P.asIdeal} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r)
    (hx : Ideal.Quotient.mk P.asIdeal s * x = Ideal.Quotient.mk P.asIdeal r) : redP P a = x := by
  have : P.asIdeal.IsPrime := P.isPrime
  exact mul_left_cancel₀ (mk_ne P hs) ((reduction_spec P hs h).trans hx.symm)

lemma reduction_eq_zero {a : E} {p r s : 𝓞 E} (hp : p ∈ P.asIdeal) (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E p * algebraMap (𝓞 E) E r) : redP P a = 0 :=
  redP_eq P (r := p * r) hs (by rw [map_mul]; exact h)
    (by rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mul_mem_right _ _ hp)

def intS : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨r, s, hs, h⟩ := ha
    obtain ⟨r', s', hs', h'⟩ := hb
    refine ⟨r * r', s * s', nm_mul P hs hs', ?_⟩
    rw [map_mul, map_mul, ← h, ← h']
    ring
  one_mem' := ⟨1, 1, one_nm P, by simp⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨r, s, hs, h⟩ := ha
    obtain ⟨r', s', hs', h'⟩ := hb
    refine ⟨s' * r + s * r', s * s', nm_mul P hs hs', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
    ring
  zero_mem' := ⟨0, 1, one_nm P, by simp⟩
  neg_mem' := by
    intro a ha
    obtain ⟨r, s, hs, h⟩ := ha
    exact ⟨-r, s, hs, by rw [map_neg, ← h]; ring⟩

lemma mem_intS {a : E} : a ∈ intS P ↔ IntAt P a := Iff.rfl

def redH : intS P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := redP_eq P (r := 1) (s := 1) (one_nm P) (by simp) (by simp)
  map_mul' a b := by
    obtain ⟨r, s, hs, h⟩ := a.2
    obtain ⟨r', s', hs', h'⟩ := b.2
    show redP P (a.1 * b.1) = redP P a.1 * redP P b.1
    refine redP_eq P (r := r * r') (s := s * s') (nm_mul P hs hs') ?_ ?_
    · rw [map_mul, map_mul, ← h, ← h']
      ring
    · rw [map_mul, map_mul, ← reduction_spec P hs h, ← reduction_spec P hs' h']
      ring
  map_zero' := redP_eq P (r := 0) (s := 1) (one_nm P) (by simp) (by simp)
  map_add' a b := by
    obtain ⟨r, s, hs, h⟩ := a.2
    obtain ⟨r', s', hs', h'⟩ := b.2
    show redP P (a.1 + b.1) = redP P a.1 + redP P b.1
    refine redP_eq P (r := s' * r + s * r') (s := s * s') (nm_mul P hs hs') ?_ ?_
    · rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
      ring
    · rw [map_add, map_mul, map_mul, map_mul, ← reduction_spec P hs h, ← reduction_spec P hs' h']
      ring

lemma reduction_one₂ : redP P (1 : E) = 1 := (redH P).map_one

lemma reduction_zero : redP P (0 : E) = 0 := (redH P).map_zero

lemma reduction_mul {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a * b) = redP P a * redP P b :=
  (redH P).map_mul ⟨a, ha⟩ ⟨b, hb⟩

lemma reduction_sum₂ {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  have h1 : ((∑ i ∈ s, (⟨f i, hf i⟩ : intS P) : intS P) : E) = ∑ i ∈ s, f i := by simp
  rw [← h1]
  exact map_sum (redH P) (fun i => (⟨f i, hf i⟩ : intS P)) s

lemma reduction_det {m : ℕ} (M : Matrix (Fin m) (Fin m) E) (hM : ∀ s t, IntAt P (M s t)) :
    redP P M.det = (M.map (redP P)).det := by
  have h1 : M.det = (intS P).subtype (Matrix.of fun s t => (⟨M s t, hM s t⟩ : intS P)).det := by
    rw [RingHom.map_det]
    rfl
  rw [h1]
  exact RingHom.map_det (redH P) _

variable {n : ℕ}

lemma int_of_mem_stdAt {x : Sp E n} (hx : x ∈ stdAt E n P) (i : Fin n) : IntAt P (x i) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 hsx) i (Set.mem_univ _))
  exact ⟨y, s, hs, by rw [hy, Pi.smul_apply, Algebra.smul_def]⟩

lemma mem_stdAt_of {x : Sp E n} (hx : ∀ i, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = x i) :
    x ∈ stdAt E n P := by
  refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
  rw [one_smul]
  exact Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 (hx i)

lemma eN_mem (j : ℕ) : Loc.eN E n j ∈ stdAt E n P := by
  refine mem_stdAt_of P fun i => ?_
  unfold Loc.eN
  split_ifs
  · exact ⟨1, map_one _⟩
  · exact ⟨0, map_zero _⟩

lemma ent_int {r : Sp E n ≃ₗ[E] Sp E n} (hr : r ∈ stabL E n (stdAt E n P)) (j : ℕ) (i : Fin n) :
    IntAt P (r (Loc.eN E n j) i) :=
  int_of_mem_stdAt P ((hr _).2 (eN_mem P j)) i

lemma apply_eq_sum (f : Sp E n ≃ₗ[E] Sp E n) (v : Sp E n) (i : Fin n) :
    f v i = ∑ m, v m * f (Loc.eN E n m.1) i := by
  have hv : v = ∑ m : Fin n, v m • Loc.eN E n m.1 := by
    funext j
    simp [Loc.eN, Finset.sum_apply, Fin.val_inj]
  conv_lhs => rw [hv]
  simp [map_sum, Finset.sum_apply]

variable {kj N c : ℕ}

lemma mem_parL {q : ℕ} {x : Sp E (N + c)} :
    x ∈ LocE.parL P q kj N c ↔
      (fun l : Fin (N + c) => ((q : E) ^ (if kj ≤ l.1 ∧ l.1 < N then (1 : ℤ) else 0))⁻¹ * x l) ∈
        stdAt E (N + c) P := Iff.rfl

private lemma intAt_inv_absNorm_mul_apply_of_mem_JQ {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)}
    (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c)
    (i : Fin (N + c)) (hi1 : kj ≤ i.1) (hi2 : i.1 < N) (j : Fin (N + c)) (hj : ¬(kj ≤ j.1 ∧ j.1 < N)) :
    IntAt P (((Ideal.absNorm P.asIdeal : ℕ) : E)⁻¹ * r (Loc.eN E (N + c) j.1) i) := by
  have hej : Loc.eN E (N + c) j.1 ∈ LocE.parL P (Ideal.absNorm P.asIdeal) kj N c := by
    rw [mem_parL]
    refine mem_stdAt_of P fun l => ?_
    by_cases hl : kj ≤ l.1 ∧ l.1 < N
    · have hlj : l.1 ≠ j.1 := fun h => hj (h ▸ hl)
      exact ⟨0, by simp [Loc.eN, hlj]⟩
    · refine ⟨if l.1 = j.1 then 1 else 0, ?_⟩
      simp only [Loc.eN, if_neg hl, zpow_zero, inv_one, one_mul]
      split_ifs <;> simp
  have h1 := (Subgroup.mem_inf.1 hr).2 _ |>.2 hej
  rw [mem_parL] at h1
  have h2 := int_of_mem_stdAt P h1 i
  simpa only [if_pos (And.intro hi1 hi2), zpow_one] using h2

private lemma redP_eq_zero_of_intAt_inv_absNorm_mul {a : E} (h : IntAt P (((Ideal.absNorm P.asIdeal : ℕ) : E)⁻¹ * a)) :
    redP P a = 0 := by
  obtain ⟨r', s, hs, hrs⟩ := h
  have hq : ((Ideal.absNorm P.asIdeal : ℕ) : E) ≠ 0 :=
    Nat.cast_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot)
  refine reduction_eq_zero P (p := ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)) (Ideal.absNorm_mem _) hs (r := r') ?_
  rw [map_natCast, ← hrs, mul_left_comm, ← mul_assoc ((Ideal.absNorm P.asIdeal : ℕ) : E), mul_inv_cancel₀ hq, one_mul]

lemma red_DA {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)}
    (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c)
    (i : Fin (N + c)) (hi1 : kj ≤ i.1) (hi2 : i.1 < N) (j : Fin (N + c)) (hj : ¬(kj ≤ j.1 ∧ j.1 < N)) :
    redP P (r (Loc.eN E (N + c) j.1) i) = 0 :=
  redP_eq_zero_of_intAt_inv_absNorm_mul P (intAt_inv_absNorm_mul_apply_of_mem_JQ P hr i hi1 hi2 j hj)

def Ment (kj N c : ℕ) (f : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Matrix (Fin (N - kj)) (Fin (N - kj)) E :=
  Matrix.of fun s t => Loc.atN (f (Loc.eN E (N + c) (kj + t.1))) (kj + s.1)

def Mb (kj N c : ℕ) (f : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) :
    Matrix (Fin (N - kj)) (Fin (N - kj)) (𝓞 E ⧸ P.asIdeal) :=
  (Ment kj N c f).map (redP P)

def dI (kj N c : ℕ) (t : Fin (N - kj)) : Fin (N + c) := ⟨kj + t.1, by have := t.2; omega⟩

lemma dI_inj : Function.Injective (dI kj N c) := by
  intro s t h
  simpa [dI, Fin.ext_iff] using h

lemma atN_dI (v : Sp E (N + c)) (s : Fin (N - kj)) : Loc.atN v (kj + s.1) = v (dI kj N c s) := by
  unfold Loc.atN
  rw [dif_pos (by have := s.2; omega)]
  rfl

lemma Mb_mul_of {r g h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)}
    (hDA : ∀ i : Fin (N + c), kj ≤ i.1 → i.1 < N → ∀ j : Fin (N + c), ¬(kj ≤ j.1 ∧ j.1 < N) →
      redP P (r (Loc.eN E (N + c) j.1) i) = 0)
    (hrI : ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i))
    (hgI : ∀ (j : ℕ) i, IntAt P (g (Loc.eN E (N + c) j) i))
    (hh : ∀ t : Fin (N - kj), h (Loc.eN E (N + c) (kj + t.1)) = r (g (Loc.eN E (N + c) (kj + t.1)))) :
    Mb P kj N c h = Mb P kj N c r * Mb P kj N c g := by
  ext s t
  have key : ∀ m : Fin (N + c), ¬(kj ≤ m.1 ∧ m.1 < N) →
      redP P (r (Loc.eN E (N + c) m.1) (dI kj N c s)) = 0 :=
    fun m hm => hDA (dI kj N c s) (show kj ≤ kj + s.1 by omega) (show kj + s.1 < N by have := s.2; omega) m hm
  simp only [Mb, Ment, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, atN_dI]
  conv_lhs => rw [hh t, apply_eq_sum r, reduction_sum₂ P _ _ fun m => (intS P).mul_mem (hgI _ m) (hrI _ _)]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨dI kj N c, dI_inj⟩)) ?_, Finset.sum_map]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [reduction_mul P (hgI _ _) (hrI _ _)]
    exact mul_comm _ _
  · intro m _ hm
    have hD : ¬(kj ≤ m.1 ∧ m.1 < N) := by
      rintro ⟨h1, h2⟩
      exact hm (Finset.mem_map.2 ⟨⟨m.1 - kj, by omega⟩, Finset.mem_univ _,
        Fin.ext (show kj + (m.1 - kj) = m.1 by omega)⟩)
    rw [reduction_mul P (hgI _ _) (hrI _ _), key m hD, mul_zero]

lemma Mb_one : Mb P kj N c (1 : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) = 1 := by
  ext s t
  simp only [Mb, Ment, Matrix.map_apply, Matrix.of_apply, atN_dI]
  by_cases hst : s = t
  · subst hst
    simp [Loc.eN, dI, reduction_one₂]
  · have hv : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
    rw [Matrix.one_apply_ne hst]
    simp [Loc.eN, dI, hv, reduction_zero]

lemma redP_det_Ment {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hrI : ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i)) :
    redP P (Ment kj N c r).det = (Mb P kj N c r).det :=
  reduction_det P _ fun s t => by
    show IntAt P (Loc.atN _ (kj + s.1))
    rw [atN_dI]
    exact hrI _ _

lemma hDA_of {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) :
    ∀ i : Fin (N + c), kj ≤ i.1 → i.1 < N → ∀ j : Fin (N + c), ¬(kj ≤ j.1 ∧ j.1 < N) →
      redP P (r (Loc.eN E (N + c) j.1) i) = 0 :=
  fun i hi1 hi2 j hj => redP_eq_zero_of_intAt_inv_absNorm_mul P (intAt_inv_absNorm_mul_apply_of_mem_JQ P hr i hi1 hi2 j hj)

lemma hI_of {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) :
    ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i) :=
  fun j i => ent_int P (Subgroup.mem_inf.1 hr).1 j i

lemma isUnit_Mb {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) :
    IsUnit (Mb P kj N c r).det := by
  have hr' : r⁻¹ ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c := inv_mem hr
  have hm := Mb_mul_of P (h := 1) (r := r) (g := r⁻¹) (hDA_of P hr) (hI_of P hr) (hI_of P hr')
    (fun t => by show _ = (r * r⁻¹) _; rw [mul_inv_cancel])
  rw [Mb_one] at hm
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_one, Matrix.det_mul] at hd
  exact isUnit_iff_exists_inv.2 ⟨_, hd.symm⟩

lemma isIntegralAt_superdiagonalSum {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hrI : ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i)) :
    IntAt P (Loc.n1Arg r) := by
  rw [← mem_intS]
  unfold Loc.n1Arg
  refine (intS P).sum_mem fun i _ => ?_
  unfold Loc.atN
  split_ifs
  · exact (mem_intS P).2 (hrI _ _)
  · exact (intS P).zero_mem

lemma inX_eN {j : ℕ} (hj : j < N) : Loc.inX E N c (Loc.eN E N j) = Loc.eN E (N + c) j := by
  funext l
  simp only [Loc.inX, LinearMap.pi_apply]
  by_cases hl : l.1 < N
  · rw [dif_pos hl]
    rfl
  · rw [dif_neg hl, LinearMap.zero_apply]
    unfold Loc.eN
    rw [if_neg (by omega)]

variable {K : Type} [Field K]

lemma unitV_mul (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b d : E} (ha : IsUnit (redP P a)) (hb : IsUnit (redP P b))
    (hd : redP P d = redP P a * redP P b) :
    LocE.unitV ξ d = LocE.unitV ξ a * LocE.unitV ξ b := by
  have hd' : IsUnit (redP P d) := hd ▸ ha.mul hb
  unfold LocE.unitV
  rw [dif_pos hd', dif_pos ha, dif_pos hb]
  have hu : hd'.unit = ha.unit * hb.unit := Units.ext (by simp [hd])
  rw [hu, map_mul, Units.val_mul]

end PI.TwChrOne.Pf
