import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet

open MvPolynomial Formalism.L2.Pj

variable {R : Type} [CommRing R]

abbrev zz {κ : Type} (m : ℕ) (j : κ) : Jet R κ m := Ideal.Quotient.mk _ (X j)

variable (R) in

def Ij (κ : Type) (m : ℕ) : Ideal (Jet R κ m) := Ideal.span (Set.range (zz (R := R) (κ := κ) m))

theorem Ij_eq_map (κ : Type) (m : ℕ) :
    Ij R κ m = (orig R κ).map (Ideal.Quotient.mk (orig R κ ^ (m + 1))) := by
  unfold Ij orig
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem Ij_pow_eq_bot (κ : Type) (m : ℕ) : Ij R κ m ^ (m + 1) = ⊥ := by
  rw [Ij_eq_map, ← Ideal.map_pow, Ideal.map_quotient_self]

theorem eq_zero_of_mem_pow {κ : Type} {m k : ℕ} (hk : m + 1 ≤ k) {p : Jet R κ m} (hp : p ∈ Ij R κ m ^ k) :
    p = 0 := by
  have h := Ideal.pow_le_pow_right hk hp
  rw [Ij_pow_eq_bot] at h
  exact (Submodule.mem_bot _).1 h

theorem jetMap_alt_alt {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R) (hφ : ∀ i, φ i ∈ orig R κ') (j : κ) :
    jetMap (m := m) φ hφ (zz m j) = Ideal.Quotient.mk _ (φ j) := by
  simp only [jetMap, liftJet, Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  simp

theorem mem_pow_of_trunc_eq_zero {κ : Type} {m : ℕ} (p : Jet R κ (m + 1))
    (h : (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) p = 0) : p ∈ Ij R κ (m + 1) ^ (m + 1) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
  have hP : P ∈ orig R κ ^ (m + 1) := by
    have e : (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) (Ideal.Quotient.mk _ P) =
        Ideal.Quotient.mk _ P := by
      first
      | rfl
      | simp [jetTrunc]
    rw [e, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  rw [Ij_eq_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hP

theorem augmentation_jet_variable {κ : Type} (m : ℕ) (j : κ) : (jetAug : Jet R κ m →ₐ[R] R) (zz m j) = 0 := by
  simp [jetAug, liftJet, zz]

theorem jet_ext' {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] {f g : Jet R κ m →ₐ[R] A}
    (h : ∀ j, f (zz m j) = g (zz m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j

theorem sub_aug_mem {κ : Type} {m : ℕ} (p : Jet R κ m) :
    p - algebraMap R _ ((jetAug : Jet R κ m →ₐ[R] R) p) ∈ Ij R κ m := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
  induction P using MvPolynomial.induction_on
  next a =>
    have e : (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (C a) : Jet R κ m) = algebraMap R _ a := rfl
    rw [e, AlgHom.commutes]
    simp
  next q r hq hr =>
    have h := Ideal.add_mem _ hq hr
    convert h using 1
    simp only [map_add]
    abel
  next q j _ =>
    have hz : (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (X j) : Jet R κ m) ∈ Ij R κ m :=
      Ideal.subset_span ⟨j, rfl⟩
    have h0 : (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (X j)) = 0 :=
      augmentation_jet_variable m j
    rw [map_mul, map_mul, h0, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ hz

theorem map_pow_mem {κ κ' : Type} {m m' : ℕ} (f : Jet R κ m →ₐ[R] Jet R κ' m')
    (hf : ∀ j, f (zz m j) ∈ Ij R κ' m') (k : ℕ) {p : Jet R κ m} (hp : p ∈ Ij R κ m ^ k) :
    f p ∈ Ij R κ' m' ^ k := by
  have h1 : Ideal.map f (Ij R κ m) ≤ Ij R κ' m' := by
    rw [Ij, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hf j
  have h2 : Ideal.map f (Ij R κ m ^ k) ≤ Ij R κ' m' ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 k
  exact h2 (Ideal.mem_map_of_mem f hp)

section Scale

abbrev sc {κ : Type} (m : ℕ) (c : R) : Jet R κ m →ₐ[R] Jet R κ m := jetScale (fun _ => c)

theorem scale_jet_variable {κ : Type} (m : ℕ) (c : R) (j : κ) : sc m c (zz m j) = c • zz m j := by
  simp only [sc, jetScale]
  rw [jetMap_alt_alt, map_mul, Algebra.smul_def]
  rfl

theorem aug_sc {κ : Type} (m : ℕ) (c : R) (p : Jet R κ m) :
    (jetAug : Jet R κ m →ₐ[R] R) (sc m c p) = (jetAug : Jet R κ m →ₐ[R] R) p := by
  have h : (jetAug : Jet R κ m →ₐ[R] R).comp (sc m c) = jetAug := by
    apply jet_ext'
    intro j
    rw [AlgHom.comp_apply, scale_jet_variable, map_smul, augmentation_jet_variable, smul_zero]
  exact congrArg (fun g : Jet R κ m →ₐ[R] R => g p) h

theorem sc_sub_mem {κ : Type} (m : ℕ) (c : R) (p : Jet R κ m) : sc m c p - p ∈ Ij R κ m := by
  have h1 := sub_aug_mem (sc m c p)
  have h2 := sub_aug_mem p
  rw [aug_sc] at h1
  have h3 := Ideal.sub_mem _ h1 h2
  rwa [sub_sub_sub_cancel_right] at h3

theorem sc_one_mem {κ : Type} (m : ℕ) (c : R) {b : Jet R κ m} (hb : b ∈ Ij R κ m) :
    sc m c b - c • b ∈ Ij R κ m ^ 2 := by
  have hb' : b ∈ Submodule.span (Jet R κ m) (Set.range (zz (R := R) (κ := κ) m)) := hb
  clear hb
  induction hb' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [scale_jet_variable, sub_self]
    exact Ideal.zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    have h := Ideal.add_mem _ hx hy
    convert h using 1
    rw [map_add, smul_add]
    abel
  | smul a x hx' hx =>
    have e1 : sc m c (a • x) - c • (a • x) =
        sc m c a * (sc m c x - c • x) + (sc m c a - a) * (c • x) := by
      simp only [smul_eq_mul, map_mul, Algebra.smul_def]
      ring
    rw [e1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) ?_
    rw [pow_two (Ij R κ m)]
    exact Ideal.mul_mem_mul (sc_sub_mem m c a) (Submodule.smul_of_tower_mem _ c hx')

theorem sc_pow_mem {κ : Type} (m : ℕ) (c : R) :
    ∀ (k : ℕ) {p : Jet R κ m}, p ∈ Ij R κ m ^ k → sc m c p - c ^ k • p ∈ Ij R κ m ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro p _
    simpa using sc_sub_mem m c p
  | succ k ih =>
    intro p hp
    rw [pow_succ (Ij R κ m) k] at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro a ha b hb
      have hsb : sc m c b ∈ Ij R κ m := by
        have h := Ideal.add_mem _ (sc_sub_mem m c b) hb
        simpa using h
      have e : sc m c (a * b) - c ^ (k + 1) • (a * b) =
          (sc m c a - c ^ k • a) * sc m c b + (c ^ k • a) * (sc m c b - c • b) := by
        simp only [map_mul, Algebra.smul_def, map_pow]
        ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ (Ij R κ m) (k + 1)]
        exact Ideal.mul_mem_mul (ih ha) hsb
      · have h2 := sc_one_mem m c hb
        have h3 : c ^ k • a ∈ Ij R κ m ^ k := Submodule.smul_of_tower_mem _ _ ha
        rw [show k + 1 + 1 = k + 2 by ring, pow_add (Ij R κ m) k 2]
        exact Ideal.mul_mem_mul h3 h2
    · intro x y hx hy
      have h := Ideal.add_mem _ hx hy
      convert h using 1
      rw [map_add, smul_add]
      abel

end Scale

section Kill

variable {n : ℕ}

def killS (i : Fin 2) (v : Fin 2 × Fin n) : MvPolynomial (Fin 2 × Fin n) R := if v.1 = i then 0 else X v

theorem killS_mem (i : Fin 2) (v : Fin 2 × Fin n) : killS (R := R) i v ∈ orig R (Fin 2 × Fin n) := by
  unfold killS
  split_ifs
  · exact Ideal.zero_mem _
  · exact X_mem_orig v

def kill (m : ℕ) (i : Fin 2) : Jet R (Fin 2 × Fin n) m →ₐ[R] Jet R (Fin 2 × Fin n) m :=
  jetMap (killS i) (killS_mem i)

def Kp (m : ℕ) (i : Fin 2) : Ideal (Jet R (Fin 2 × Fin n) m) :=
  Ideal.span (Set.range fun j : Fin n => zz (R := R) m (i, j))

theorem kill_alt_alt (m : ℕ) (i : Fin 2) (v : Fin 2 × Fin n) :
    kill (R := R) m i (zz m v) = if v.1 = i then 0 else zz m v := by
  rw [kill, jetMap_alt_alt, killS]
  split_ifs <;> simp [zz]

theorem poly_sub_kill_mem (i : Fin 2) (P : MvPolynomial (Fin 2 × Fin n) R) :
    P - aeval (killS i) P ∈ Ideal.span (Set.range fun j : Fin n => (X (i, j) : MvPolynomial (Fin 2 × Fin n) R)) := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp
  next p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  next p v hp =>
    rw [map_mul, aeval_X]
    have e : p * X v - aeval (killS i) p * killS i v =
        (p - aeval (killS i) p) * X v + aeval (killS i) p * (X v - killS i v) := by ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    rcases v with ⟨a, b⟩
    unfold killS
    split_ifs with hv
    · have ha : a = i := hv
      subst ha
      rw [sub_zero]
      exact Ideal.subset_span ⟨b, rfl⟩
    · rw [sub_self]
      exact Ideal.zero_mem _

theorem sub_kill_mem (m : ℕ) (i : Fin 2) (e : Jet R (Fin 2 × Fin n) m) : e - kill m i e ∈ Kp m i := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective e
  have h1 : kill m i (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (aeval (killS i) P) := by
    simp only [kill, jetMap, liftJet, Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
  rw [h1, ← map_sub]
  have h2 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (orig R (Fin 2 × Fin n) ^ (m + 1)))
    (poly_sub_kill_mem i P)
  rw [Ideal.map_span, ← Set.range_comp] at h2
  exact h2

theorem mem_mul_of_kill (m : ℕ) (e : Jet R (Fin 2 × Fin n) m) (h0 : kill m 0 e = 0) (h1 : kill m 1 e = 0) :
    e ∈ Kp m 0 * Kp m 1 := by
  have key : ∀ x ∈ Kp (R := R) (n := n) m 0, x - kill m 1 x ∈ Kp m 0 * Kp m 1 := by
    intro x hx
    have hx' : x ∈ Submodule.span (Jet R (Fin 2 × Fin n) m)
        (Set.range fun j : Fin n => zz (R := R) m ((0 : Fin 2), j)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [kill_alt_alt, if_neg (by simp), sub_self]
      exact Ideal.zero_mem _
    | zero => simp
    | add y z _ _ hy hz =>
      have h := Ideal.add_mem _ hy hz
      convert h using 1
      rw [map_add]
      abel
    | smul a y hy' hy =>
      have e1 : a • y - kill m 1 (a • y) = y * (a - kill m 1 a) + kill m 1 a * (y - kill m 1 y) := by
        rw [smul_eq_mul, map_mul]
        ring
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_mul hy' (sub_kill_mem m 1 a)) (Ideal.mul_mem_left _ _ hy)
  have he0 : e ∈ Kp m 0 := by simpa [h0] using sub_kill_mem m 0 e
  simpa [h1] using key e he0

end Kill

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
