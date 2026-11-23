import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IsUnitRedP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.UniformContinuityGaloisGroup

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section F

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by
  unfold fIdx
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) (hk : k₀ ≤ n)
    (h : fIdx k₀ c n p = fIdx k₀ c n p') : p = p' := by
  unfold fIdx at h
  split_ifs at h <;> omega

theorem fIdx_notD {k₀ c n kj p : ℕ} (hk : k₀ ≤ kj) (hp : p < kj + c) :
    ¬(kj ≤ fIdx k₀ c n p ∧ fIdx k₀ c n p < n) := by
  unfold fIdx
  split_ifs <;> omega

theorem fIdx_D {k₀ c n kj p : ℕ} (hk : k₀ ≤ kj) (hp1 : kj + c ≤ p) (hp2 : p < n + c) :
    kj ≤ fIdx k₀ c n p ∧ fIdx k₀ c n p < n := by
  unfold fIdx
  split_ifs <;> omega

end F

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem mem_stdAt' {n : ℕ} (v : Sp E n) : v ∈ stdAt E n P ↔ ∀ l, IntAt P (v l) := by
  exact PI.TwNormLat.W.mem_stdAt P v

theorem eN_mem' (n j : ℕ) : eN E n j ∈ stdAt E n P := by
  rw [mem_stdAt']
  intro l
  unfold eN
  split_ifs
  · exact ia_one (P := P)
  · exact ia_zero (P := P)

theorem jq_int {q kj n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (j : ℕ)
    (l : Fin (n + c)) : IntAt P (g (eN E (n + c) j) l) := by
  have h1 : ∀ x, g x ∈ stdAt E (n + c) P ↔ x ∈ stdAt E (n + c) P := (Subgroup.mem_inf.mp hg).1
  exact (mem_stdAt' _).mp ((h1 _).mpr (eN_mem' _ _)) l

theorem mem_parL' {q kj n c : ℕ} (x : Sp E (n + c)) :
    x ∈ parL P q kj n c ↔ ∀ l : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * x l) := by
  unfold parL sclLat
  rw [Submodule.mem_comap, mem_stdAt']
  simp only [LinearMap.coe_restrictScalars, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.coe_proj,
    Function.eval, smul_eq_mul]

theorem jq_DA {q kj n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (j : ℕ)
    (hj : ¬(kj ≤ j ∧ j < n)) (l : Fin (n + c)) (hl : kj ≤ l.1 ∧ l.1 < n) :
    IntAt P (g (eN E (n + c) j) l / (q : E)) := by
  have h2 : ∀ x, g x ∈ parL P q kj n c ↔ x ∈ parL P q kj n c := (Subgroup.mem_inf.mp hg).2
  have hej : eN E (n + c) j ∈ parL P q kj n c := by
    rw [mem_parL']
    intro l'
    unfold eN
    by_cases hl' : l'.1 = j
    · rw [if_neg (by rw [hl']; exact hj), if_pos hl']
      simpa using ia_one (P := P)
    · rw [if_neg hl', mul_zero]
      exact ia_zero (P := P)
  have h3 := (mem_parL' _).mp ((h2 _).mpr hej) l
  rw [if_pos hl, zpow_one] at h3
  rwa [div_eq_inv_mul]

theorem apply_sum' {N : ℕ} (f : Sp E N ≃ₗ[E] Sp E N) (v : Sp E N) (i : Fin N) :
    f v i = ∑ m : Fin N, v m * f (eN E N m.1) i := by
  have hv : v = ∑ m : Fin N, v m • eN E N m.1 := by
    funext l
    simp [eN, Finset.sum_apply, Fin.val_inj]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [Finset.sum_apply, map_smul]

theorem atN_of_lt {N : ℕ} (v : Fin N → E) {i : ℕ} (hi : i < N) : atN v i = v ⟨i, hi⟩ := by
  unfold atN
  rw [dif_pos hi]

theorem row_tr {N' n c k₀ : ℕ} (hk : k₀ ≤ n) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (y : HomE E N' (n + c))
    (s p : ℕ) (hp : p < n + c) :
    atN ((g.toLinearMap ∘ₗ y) (eN E N' s)) (fIdx k₀ c n p) =
      ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        atN (y (eN E N' s)) (fIdx k₀ c n p'') := by
  have himg : (Finset.range (n + c)).image (fIdx k₀ c n) = Finset.range (n + c) := by
    apply Finset.eq_of_subset_of_card_le
    · intro m hm
      obtain ⟨p'', hp'', rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (fIdx_lt hk (Finset.mem_range.mp hp''))
    · rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      exact fIdx_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hk hab
  have hsum : ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        atN (y (eN E N' s)) (fIdx k₀ c n p'') =
      ∑ m ∈ Finset.range (n + c), atN (g (eN E (n + c) m)) (fIdx k₀ c n p) * atN (y (eN E N' s)) m := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a ha b hb hab => fIdx_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hk hab)]
  have hA : ∀ {M : ℕ} (v : Fin M → E) (m : Fin M), atN v m.1 = v m := fun v m => by
    rw [atN_of_lt v m.isLt]
  have hB : ∀ (v : Fin (n + c) → E), atN v (fIdx k₀ c n p) = v ⟨_, fIdx_lt hk hp⟩ := fun v => atN_of_lt v _
  rw [hsum, Finset.sum_range (fun m => atN (g (eN E (n + c) m)) (fIdx k₀ c n p) * atN (y (eN E N' s)) m)]
  simp only [hA, hB, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [apply_sum' g]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mul_comm]

theorem reduction_absNorm_mul_eq_zero {z : E} (hz : IntAt P z) : redP P ((qOf P : E) * z) = 0 := by
  obtain ⟨r, s, hs, hsz⟩ := hz
  refine PI.TwChrOne.Pf.reduction_eq_zero P (p := (Ideal.absNorm P.asIdeal : 𝓞 E)) (r := r) (s := s)
    (Ideal.absNorm_mem P.asIdeal) hs ?_
  rw [← hsz, map_natCast]
  unfold qOf
  ring

theorem reduction_eq_zero_of_integral_inv_mul {z : E} (hp : (Ideal.absNorm P.asIdeal).Prime) (hz : IntAt P (z / (qOf P : E))) :
    redP P z = 0 := by
  have hq := NTA.q_ne (P := P) hp
  have e : z = (qOf P : E) * (z / (qOf P : E)) := by field_simp
  rw [e]
  exact reduction_absNorm_mul_eq_zero hz

theorem reduction_det' {m : ℕ} (M : Matrix (Fin m) (Fin m) E) (hM : ∀ s t, IntAt P (M s t)) :
    redP P M.det = (M.map (redP P)).det := by
  exact PI.TwChrOne.Pf.reduction_det P M hM

theorem redP_sum' {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  exact PI.TwChrOne.Pf.reduction_sum₂ P s f hf

theorem block_entry_zero_zero {N' N : ℕ} (q k₀ c' n' c n : ℕ) (x : HomE E N' N) (p p' : ℕ) :
    entB q k₀ c' n' c n 0 0 x p p' = atN (x (eN E N' (fIdx k₀ c' n' p'))) (fIdx k₀ c n p) := by
  simp [entB, scE]

section Law

variable (P)

def CondQ (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) : Prop :=
  (∀ p p', p < n + c → p' < n' + c' → IntAt P (entB q k₀ c' n' c n 0 0 x p p')) ∧
  (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (entB q k₀ c' n' c n 0 0 x p p' / (q : E)))

def AYm (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun s t : Fin r => entB q k₀ c' n' c n 0 0 x s.1 t.1

variable {P}

def GA (k₀ r c n : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun s p : Fin r => atN (g (eN E (n + c) (fIdx k₀ c n p.1))) (fIdx k₀ c n s.1)

open Classical in
theorem phi_eq (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) :
    PhiQ q ξ k₀ r c' n' c n x =
      if CondQ P q k₀ r c' n' c n x then unitV ξ (AYm q k₀ r c' n' c n x).det else 0 := by
  unfold PhiQ CondQ AYm
  split_ifs with ha hb hb <;> first | rfl | exact absurd ha hb | exact absurd hb ha

theorem redP_zero' : redP P (0 : E) = 0 := by
  exact PI.TwChrOne.Pf.reduction_zero P

theorem reduction_add' {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a + b) = redP P a + redP P b := by
  have h := redP_sum' (P := P) (Finset.univ : Finset (Fin 2)) ![a, b] (by intro i; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

theorem reduction_sum' {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [redP_zero']
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      reduction_add' (hf i (Finset.mem_insert_self i s))
        (ia_sum (P := P) s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5

theorem ent_comp (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)) (p p' : ℕ) (hp : p < n + c) :
    entB q k₀ c' n' c n 0 0 (g.toLinearMap ∘ₗ y) p p' =
      ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        entB q k₀ c' n' c n 0 0 y p'' p' := by
  rw [block_entry_zero_zero, row_tr (le_trans h2 h3) g y _ p hp]
  refine Finset.sum_congr rfl (fun p'' _ => ?_)
  rw [block_entry_zero_zero]

theorem gm_int {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (p p'' : ℕ) (hp : p < n + c) :
    IntAt P (atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p)) := by
  unfold atN
  split_ifs with hlt
  · exact jq_int hg _ _
  · exact ia_zero (P := P)

theorem supp_comp {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) {y : HomE E (n' + c') (n + c)}
    (hy : CondQ P q k₀ r c' n' c n y) : CondQ P q k₀ r c' n' c n (g.toLinearMap ∘ₗ y) := by
  obtain ⟨hyA, hyB⟩ := hy
  refine ⟨fun p p' hp hp' => ?_, fun p p' hrp hp hp' => ?_⟩
  · rw [ent_comp hqq h1 h2 h3 h4 h5 g y p p' hp]
    exact ia_sum (P := P) _ _ (fun p'' hp'' => ia_mul (P := P)
      (gm_int hqq h1 h2 h3 h4 h5 hg p p'' hp) (hyA p'' p' (Finset.mem_range.mp hp'') hp'))
  · rw [ent_comp hqq h1 h2 h3 h4 h5 g y p p' hp, Finset.sum_div]
    refine ia_sum (P := P) _ _ (fun p'' hp'' => ?_)
    have hp''' := Finset.mem_range.mp hp''
    by_cases hr : r ≤ p''
    · rw [mul_div_assoc]
      exact ia_mul (P := P) (gm_int hqq h1 h2 h3 h4 h5 hg p p'' hp) (hyB p'' p' hr hp''' hp')
    · push_neg at hr
      rw [mul_div_right_comm]
      refine ia_mul (P := P) ?_ (hyA p'' p' hp''' (by omega))
      rw [atN_of_lt _ (fIdx_lt (le_trans h2 h3) hp)]
      have hD := fIdx_D (k₀ := k₀) (c := c) (n := n) (kj := kj) h2 (by omega) hp
      have hnD := fIdx_notD (k₀ := k₀) (c := c) (n := n) (kj := kj) (p := p'') h2 (by omega)
      exact jq_DA hg _ hnD ⟨_, fIdx_lt (le_trans h2 h3) hp⟩ hD

theorem val_comp (hp : (Ideal.absNorm P.asIdeal).Prime) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c)
    {y : HomE E (n' + c') (n + c)} (hy : CondQ P q k₀ r c' n' c n y) :
    (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y)).map (redP P) =
      (GA k₀ r c n g).map (redP P) * (AYm q k₀ r c' n' c n y).map (redP P) := by
  subst hqq
  obtain ⟨hyA, hyB⟩ := hy
  ext s t
  have hs : s.1 < n + c := by have := s.isLt; omega
  have ht : t.1 < n' + c' := by have := t.isLt; omega
  simp only [Matrix.map_apply, Matrix.mul_apply, AYm, GA, Matrix.of_apply]
  rw [ent_comp rfl h1 h2 h3 h4 h5 g y s.1 t.1 hs,
    reduction_sum' _ _ (fun p'' hp'' => ia_mul (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 p'' hs)
      (hyA p'' t.1 (Finset.mem_range.mp hp'') ht)),
    ← Finset.sum_range_add_sum_Ico _ (show r ≤ n + c by omega)]
  have hzero : ∑ p'' ∈ Finset.Ico r (n + c), redP P (atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n s.1) *
      entB (qOf P) k₀ c' n' c n 0 0 y p'' t.1) = 0 := by
    refine Finset.sum_eq_zero (fun p'' hp'' => ?_)
    obtain ⟨h6, h7⟩ := Finset.mem_Ico.mp hp''
    rw [reduction_mul' (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 p'' hs) (hyA p'' t.1 h7 ht),
      reduction_eq_zero_of_integral_inv_mul hp (hyB p'' t.1 h6 h7 t.isLt), mul_zero]
  rw [hzero, add_zero, Finset.sum_range]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [reduction_mul' (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 x.1 hs) (hyA x.1 t.1 (by have := x.isLt; omega) ht)]

theorem det_comp (hp : (Ideal.absNorm P.asIdeal).Prime) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c)
    {y : HomE E (n' + c') (n + c)} (hy : CondQ P q k₀ r c' n' c n y) :
    redP P (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y)).det =
      redP P (GA k₀ r c n g).det * redP P (AYm q k₀ r c' n' c n y).det := by
  have hgy := supp_comp hqq h1 h2 h3 h4 h5 hg hy
  rw [reduction_det' (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y))
      (fun s t => hgy.1 s.1 t.1 (by have := s.isLt; omega) (by have := t.isLt; omega)),
    val_comp hqq h1 h2 h3 h4 h5 hp hg hy, Matrix.det_mul,
    reduction_det' (GA k₀ r c n g) (fun s t => gm_int hqq h1 h2 h3 h4 h5 hg s.1 t.1 (by have := s.isLt; omega)),
    reduction_det' (AYm q k₀ r c' n' c n y)
      (fun s t => hy.1 s.1 t.1 (by have := s.isLt; omega) (by have := t.isLt; omega))]

end Law

private theorem unitV_eq_mul_of_redP_eq_mul (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b d : E} (ha : IsUnit (redP P a))
    (hd : redP P d = redP P a * redP P b) : unitV ξ d = unitV ξ a * unitV ξ b := by
  by_cases hb : IsUnit (redP P b)
  · have hd' : IsUnit (redP P d) := by rw [hd]; exact ha.mul hb
    unfold unitV
    rw [dif_pos hd', dif_pos ha, dif_pos hb, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp [hd]
  · have hd' : ¬ IsUnit (redP P d) := by
      rw [hd]
      intro h
      exact hb (isUnit_of_mul_isUnit_right h)
    unfold unitV
    rw [dif_neg hd', dif_neg hb, mul_zero]

theorem jacobian_transformation_law : JLawP := by
  intro E K _ _ _ _ P hp hq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 κ hκ
  classical
  have hk : k₀ ≤ n := le_trans h2 h3
  have hg : κ.symm ∈ JQ P (qOf P) kj n c := (JQ P (qOf P) kj n c).inv_mem hκ
  have hcomp : ∀ y : HomE E (n' + c') (n + c), κ.toLinearMap ∘ₗ (κ.symm.toLinearMap ∘ₗ y) = y := by
    intro y
    ext x i
    simp

  obtain ⟨M0, hM0⟩ : ∃ M0 : Matrix (Fin (n + c)) (Fin (n' + c')) E, M0 = fun i j =>
      if ∃ t, t < r ∧ i.1 = fIdx k₀ c n t ∧ j.1 = fIdx k₀ c' n' t then 1 else 0 := ⟨_, rfl⟩
  have hent0 : ∀ p p', p < n + c → p' < n' + c' →
      entB (qOf P) k₀ c' n' c n 0 0 (Matrix.toLin' M0) p p' = if p' < r ∧ p = p' then 1 else 0 := by
    intro p p' hp hp'
    have hfp := fIdx_lt hk hp
    have hfp' := fIdx_lt (c := c') h5 hp'
    rw [block_entry_zero_zero, atN_of_lt _ hfp, Matrix.toLin'_apply]
    rw [show (Matrix.mulVec M0 (eN E (n' + c') (fIdx k₀ c' n' p'))) ⟨fIdx k₀ c n p, hfp⟩ =
        M0 ⟨fIdx k₀ c n p, hfp⟩ ⟨fIdx k₀ c' n' p', hfp'⟩ by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single ⟨fIdx k₀ c' n' p', hfp'⟩]
      · simp [eN]
      · intro b _ hb
        simp only [eN]
        rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h]
    rw [hM0]
    beta_reduce
    by_cases hc : p' < r ∧ p = p'
    · rw [if_pos hc, if_pos ⟨p', hc.1, by show fIdx k₀ c n p = fIdx k₀ c n p'; rw [hc.2], rfl⟩]
    · rw [if_neg hc, if_neg]
      rintro ⟨t, ht, e1, e2⟩
      have i1 := fIdx_inj hp (by omega : t < n + c) hk e1
      have i2 := fIdx_inj hp' (by omega : t < n' + c') h5 e2
      exact hc ⟨by omega, by omega⟩
  have hy0 : CondQ P (qOf P) k₀ r c' n' c n (Matrix.toLin' M0) := by
    refine ⟨fun p p' hp hp' => ?_, fun p p' hrp hp hp' => ?_⟩
    · rw [hent0 p p' hp hp']
      split_ifs
      · exact ia_one (P := P)
      · exact ia_zero (P := P)
    · rw [hent0 p p' hp (by omega), if_neg (by omega), zero_div]
      exact ia_zero (P := P)
  have hA0 : AYm (qOf P) k₀ r c' n' c n (Matrix.toLin' M0) = 1 := by
    ext s t
    simp only [AYm, Matrix.of_apply, Matrix.one_apply]
    rw [hent0 _ _ (by have := s.isLt; omega) (by have := t.isLt; omega)]
    by_cases hst : s = t
    · subst hst
      simp
    · rw [if_neg, if_neg hst]
      rintro ⟨-, h⟩
      exact hst (Fin.ext h)
  have hr1 : redP P (1 : E) = 1 := PI.TwChrOne.Pf.reduction_one₂ P

  have hd1 := det_comp rfl h1 h2 h3 h4 h5 hp hg hy0
  have hd2 := det_comp rfl h1 h2 h3 h4 h5 hp hκ (supp_comp rfl h1 h2 h3 h4 h5 hg hy0)
  rw [hcomp, hd1, hA0, Matrix.det_one, hr1, mul_one] at hd2
  have hGA : IsUnit (redP P (GA k₀ r c n κ.symm).det) :=
    ⟨⟨_, _, by rw [mul_comm]; exact hd2.symm, hd2.symm⟩, rfl⟩
  refine ⟨unitV ξ (GA k₀ r c n κ.symm).det, ?_, fun y => ?_⟩
  · unfold unitV
    rw [dif_pos hGA]
    exact Units.ne_zero _
  rw [phi_eq, phi_eq]
  by_cases hy : CondQ P (qOf P) k₀ r c' n' c n y
  · have hgy := supp_comp rfl h1 h2 h3 h4 h5 hg hy
    rw [if_pos hgy, if_pos hy]
    exact unitV_eq_mul_of_redP_eq_mul ξ hGA (det_comp rfl h1 h2 h3 h4 h5 hp hg hy)
  · have hgy : ¬ CondQ P (qOf P) k₀ r c' n' c n (κ.symm.toLinearMap ∘ₗ y) := by
      intro h'
      apply hy
      have h6 := supp_comp rfl h1 h2 h3 h4 h5 hκ h'
      rwa [hcomp y] at h6
    rw [if_neg hgy, if_neg hy, mul_zero]

end PI.TwistedEisensteinNonvanishing.W
