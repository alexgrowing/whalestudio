import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.WittE

section Form

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {σ : E →+* E}

def IsIsom (B : V →ₛₗ[σ] V →ₗ[E] E) (γ : V →ₗ[E] V) : Prop :=
  ∀ z w, B (γ z) (γ w) = B z w

theorem IsIsom.comp {B : V →ₛₗ[σ] V →ₗ[E] E} {γ δ : V →ₗ[E] V} (hγ : IsIsom B γ)
    (hδ : IsIsom B δ) : IsIsom B (γ ∘ₗ δ) := fun z w => by
  simp only [LinearMap.comp_apply, hγ _ _, hδ _ _]

theorem exists_quasiRefl (B : V →ₛₗ[σ] V →ₗ[E] E) (hσ : ∀ x, σ (σ x) = x)
    (hB : ∀ x y, σ (B x y) = B y x) (x y : V) (hxy : B x x = B y y) (h0 : B (x - y) x ≠ 0) :
    ∃ γ : V →ₗ[E] V, IsIsom B γ ∧ γ x = y ∧ ∀ z, B (x - y) z = 0 → γ z = z := by
  set v := x - y with hv
  set a := B v x with ha
  have hsa : σ a = B x v := hB _ _
  have hsa0 : σ a ≠ 0 := (map_ne_zero σ).2 h0
  have hvv : B v v = a + σ a := by
    rw [hsa, ha, hv]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]
    ring
  have hγ : ∀ z, (LinearMap.id - (a⁻¹ • B v).smulRight v : V →ₗ[E] V) z
      = z - (a⁻¹ * B v z) • v := by
    intro z
    simp
  refine ⟨LinearMap.id - (a⁻¹ • B v).smulRight v, ?_, ?_, ?_⟩
  · intro z w
    have hzv : B z v = σ (B v z) := (hB v z).symm
    rw [hγ, hγ]
    simp only [map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, map_mul, map_inv₀, hvv, hzv, RingHom.id_apply]
    field_simp
    ring
  · rw [hγ, ← ha, inv_mul_cancel₀ h0, one_smul, hv, sub_sub_cancel]
  · intro z hz
    rw [hγ, hz]
    simp

theorem exists_isom_of_eq (B : V →ₛₗ[σ] V →ₗ[E] E) (hσ : ∀ x, σ (σ x) = x)
    (hB : ∀ x y, σ (B x y) = B y x) (h2 : (2 : E) ≠ 0) (x y : V) (hxy : B x x = B y y)
    (hq : B x x ≠ 0) :
    ∃ γ : V →ₗ[E] V, IsIsom B γ ∧ γ x = y ∧ ∀ z, B x z = 0 → B y z = 0 → γ z = z := by
  by_cases h0 : B (x - y) x = 0
  · have h1 : B (x - -y) x ≠ 0 := by
      intro h1
      apply hq
      simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply] at h0 h1
      have h3 : 2 * B x x = 0 := by linear_combination h0 + h1
      exact (mul_eq_zero.1 h3).resolve_left h2
    have h4 : B (-y - y) (-y) ≠ 0 := by
      have h5 : B (-y - y) (-y) = 2 * B y y := by
        simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply]
        ring
      rw [h5, ← hxy]
      exact mul_ne_zero h2 hq
    obtain ⟨γ₁, i1, e1, f1⟩ := exists_quasiRefl B hσ hB x (-y) (by simpa using hxy) h1
    obtain ⟨γ₂, i2, e2, f2⟩ := exists_quasiRefl B hσ hB (-y) y (by simp) h4
    refine ⟨γ₂ ∘ₗ γ₁, i2.comp i1, ?_, ?_⟩
    · simp [e1, e2]
    · intro z hx hy
      have g1 : γ₁ z = z := f1 z (by simp [hx, hy])
      have g2 : γ₂ z = z := f2 z (by simp [hy])
      simp [g1, g2]
  · obtain ⟨γ, i, e, f⟩ := exists_quasiRefl B hσ hB x y hxy h0
    exact ⟨γ, i, e, fun z hx hy => f z (by simp [hx, hy])⟩

def lin {n : ℕ} (X : Fin n → V) (c : Fin n → E) : V := ∑ a, c a • X a

theorem form_lin_left (B : V →ₛₗ[σ] V →ₗ[E] E) {n : ℕ} (X : Fin n → V) (c : Fin n → E) (z : V) :
    B (lin X c) z = ∑ a, σ (c a) * B (X a) z := by
  simp [lin, map_sum, LinearMap.sum_apply]

theorem form_lin_right (B : V →ₛₗ[σ] V →ₗ[E] E) {n : ℕ} (X : Fin n → V) (c : Fin n → E) (z : V) :
    B z (lin X c) = ∑ a, c a * B z (X a) := by
  simp [lin, map_sum]

theorem lin_single {n : ℕ} (X : Fin n → V) (a : Fin n) : lin X (Pi.single a (1 : E)) = X a := by
  simp [lin, Pi.single_apply, ite_smul]

theorem lin_add {n : ℕ} (X : Fin n → V) (c d : Fin n → E) : lin X (c + d) = lin X c + lin X d := by
  simp [lin, add_smul, Finset.sum_add_distrib]

theorem lin_smul {n : ℕ} (X : Fin n → V) (t : E) (c : Fin n → E) : lin X (t • c) = t • lin X c := by
  simp [lin, Finset.smul_sum, mul_smul]

theorem lin_sub {n : ℕ} (X : Fin n → V) (c d : Fin n → E) : lin X (c - d) = lin X c - lin X d := by
  simp [lin, sub_smul, Finset.sum_sub_distrib]

theorem lin_mem_span {n : ℕ} (X : Fin n → V) (c : Fin n → E) :
    lin X c ∈ Submodule.span E (Set.range X) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem (Submodule.span E (Set.range X)) _ (Submodule.subset_span ⟨a, rfl⟩)

theorem exists_norm_ne_zero (B : V →ₛₗ[σ] V →ₗ[E] E) (hB : ∀ x y, σ (B x y) = B y x)
    (h2 : (2 : E) ≠ 0) {n : ℕ} (X : Fin n → V) (hX : ¬ ∀ a b, B (X a) (X b) = 0) :
    ∃ c : Fin n → E, B (lin X c) (lin X c) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hX
  intro a b
  by_contra hs
  have hu : B (X a) (X a) = 0 := by simpa [lin_single] using hc (Pi.single a (1 : E))
  have hv : B (X b) (X b) = 0 := by simpa [lin_single] using hc (Pi.single b (1 : E))
  set s := B (X a) (X b) with hsdef
  have hba : B (X b) (X a) = σ s := (hB _ _).symm
  have h := hc (Pi.single a (1 : E) + s⁻¹ • Pi.single b (1 : E))
  rw [lin_add, lin_smul, lin_single, lin_single] at h
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, hu, hv, hba, ← hsdef, map_inv₀, RingHom.id_apply] at h
  have hσs : σ s ≠ 0 := (map_ne_zero σ).2 hs
  simp only [mul_zero, add_zero, zero_add, inv_mul_cancel₀ hs, inv_mul_cancel₀ hσs] at h
  exact h2 (by linear_combination h)

end Form

section Induct

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {σ : E →+* E}

theorem exists_isom_tuple (B : V →ₛₗ[σ] V →ₗ[E] E) (hσ : ∀ x, σ (σ x) = x)
    (hB : ∀ x y, σ (B x y) = B y x) (h2 : (2 : E) ≠ 0) {n : ℕ} (k : ℕ) :
    ∀ X Y : Fin n → V, Module.finrank E (Submodule.span E (Set.range X)) = k →
      (∀ a b, B (X a) (X b) = B (Y a) (Y b)) →
      (∀ c : Fin n → E, (∀ a, B (X a) (lin X c) = 0) → lin X c = 0 ∧ lin Y c = 0) →
      ∃ γ : V →ₗ[E] V, IsIsom B γ ∧ ∀ a, γ (X a) = Y a := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro X Y hk hG hN
  by_cases hX : ∀ a b, B (X a) (X b) = 0
  · refine ⟨LinearMap.id, fun _ _ => rfl, fun a => ?_⟩
    have h := hN (Pi.single a (1 : E)) (fun b => by rw [lin_single]; exact hX b a)
    rw [lin_single, lin_single] at h
    simp [h.1, h.2]
  obtain ⟨c, hc⟩ := exists_norm_ne_zero B hB h2 X hX
  set x := lin X c with hx
  set y := lin Y c with hy
  have hXY : ∀ a, B x (X a) = B y (Y a) := by
    intro a
    rw [hx, hy, form_lin_left, form_lin_left]
    simp only [hG]
  have hxy : B x x = B y y := by
    calc B x x = ∑ a, c a * B x (X a) := form_lin_right B X c x
      _ = ∑ a, c a * B y (Y a) := by simp only [hXY]
      _ = B y y := (form_lin_right B Y c y).symm
  have hXY' : ∀ a, B (X a) x = B (Y a) y := by
    intro a
    rw [← hB x, ← hB y, hXY]
  set q := B x x with hq
  set t : Fin n → E := fun a => B x (X a) with ht
  set X' : Fin n → V := fun a => X a - (t a / q) • x with hX'
  set Y' : Fin n → V := fun a => Y a - (t a / q) • y with hY'
  have hty : ∀ a, B y (Y a) = t a := fun a => (hXY a).symm
  have hyy : B y y = q := hxy.symm
  have hx0 : ∀ a, B x (X' a) = 0 := by
    intro a
    have e : B x (X a) = t a := rfl
    simp only [hX', map_sub, map_smul, smul_eq_mul, e, ← hq]
    rw [div_mul_cancel₀ _ hc, sub_self]
  have hy0 : ∀ a, B y (Y' a) = 0 := by
    intro a
    simp only [hY', map_sub, map_smul, smul_eq_mul, hty, hyy]
    rw [div_mul_cancel₀ _ hc, sub_self]
  have hG' : ∀ a b, B (X' a) (X' b) = B (Y' a) (Y' b) := by
    intro a b
    simp only [hX', hY', map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hG a b, hXY' a, hty, hyy]
    rw [← hq, show B x (X b) = t b from rfl]
  have hspan : Submodule.span E (Set.range X') < Submodule.span E (Set.range X) := by
    have hxm : x ∈ Submodule.span E (Set.range X) := lin_mem_span X c
    refine lt_of_le_of_ne ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩) (Submodule.smul_mem _ _ hxm)
    · intro he
      rw [← he] at hxm
      have hz : ∀ w ∈ Submodule.span E (Set.range X'), B x w = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw => obtain ⟨a, rfl⟩ := hw; exact hx0 a
        | zero => simp
        | add u v _ _ hu hv => simp [hu, hv]
        | smul s u _ hu => simp [hu]
      exact hc (hz x hxm)
  have hlt : Module.finrank E (Submodule.span E (Set.range X')) < k := by
    rw [← hk]
    exact Submodule.finrank_lt_finrank_of_lt hspan
  have hlinX : ∀ d : Fin n → E, lin X' d = lin X (d - ((∑ a, d a * t a) / q) • c) := by
    intro d
    rw [lin_sub, lin_smul, ← hx]
    simp only [lin, hX', smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul]
    congr 2
    simp only [Finset.sum_div, mul_div_assoc]
  have hlinY : ∀ d : Fin n → E, lin Y' d = lin Y (d - ((∑ a, d a * t a) / q) • c) := by
    intro d
    rw [lin_sub, lin_smul, ← hy]
    simp only [lin, hY', smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul]
    congr 2
    simp only [Finset.sum_div, mul_div_assoc]
  have hN' : ∀ d : Fin n → E, (∀ a, B (X' a) (lin X' d) = 0) → lin X' d = 0 ∧ lin Y' d = 0 := by
    intro d hd
    rw [hlinX, hlinY]
    apply hN
    intro a
    have h0 : B x (lin X' d) = 0 := by
      rw [form_lin_right]
      simp [hx0]
    have h1 := hd a
    have e : X' a = X a - (t a / q) • x := rfl
    rw [e] at h1
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [← hlinX]
    rw [h0, mul_zero, sub_zero] at h1
    exact h1
  obtain ⟨γ₁, i1, e1⟩ := ih _ hlt X' Y' rfl hG' hN'
  have hx1 : B (γ₁ x) (γ₁ x) = B y y := by rw [i1]; exact hxy
  obtain ⟨γ₂, i2, e2, f2⟩ := exists_isom_of_eq B hσ hB h2 (γ₁ x) y hx1
    (by rw [i1]; exact hc)
  refine ⟨γ₂ ∘ₗ γ₁, i2.comp i1, fun a => ?_⟩
  have hXa : X a = X' a + (t a / q) • x := by simp [hX']
  have hYa : Y a = Y' a + (t a / q) • y := by simp [hY']
  have hf : γ₂ (Y' a) = Y' a := f2 _ (by rw [← e1 a, i1]; exact hx0 a) (hy0 a)
  rw [LinearMap.comp_apply, hXa, map_add, map_smul, e1, map_add, map_smul, hf, e2, ← hYa]

end Induct

section Concrete

variable {E : Type} [Field E]

def formB (s : E →+* E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    (Fin M → E) →ₛₗ[s] (Fin M → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ s (RingHom.id E) (fun x y => hform s J x y)
    (fun x x' y => by
      simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc])
    (fun x y y' => by
      simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

theorem formB_apply (s : E →+* E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    formB s J x y = hform s J x y := rfl

theorem formB_conj (s : E →+* E) (hs : ∀ x, s (s x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin M → E) :
    s (formB s J x y) = formB s J y x := by
  simp only [formB_apply, hform, map_sum, map_mul, hs, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cT_mul_mul_apply (s : E →+* E) {M : ℕ} (J g : Matrix (Fin M) (Fin M) E) (i j : Fin M) :
    (cT s g * J * g) i j = hform s J (fun k => g k i) (fun k => g k j) := by
  simp only [Matrix.mul_apply, cT, hform, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_mem_UJ (s : E →+* E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (γ : (Fin M → E) →ₗ[E] (Fin M → E)) (hγ : IsIsom (formB s J) γ) :
    ∃ g ∈ UJ s J, ∀ z, (g : Matrix (Fin M) (Fin M) E) *ᵥ z = γ z := by
  set m := LinearMap.toMatrix' γ with hm
  have hmv : ∀ z, m *ᵥ z = γ z := fun z => LinearMap.toMatrix'_mulVec γ z
  have hu : cT s m * J * m = J := by
    ext i j
    have hcol : ∀ i, (fun k => m k i) = γ (Pi.single i 1) := by
      intro i
      rw [← hmv]
      ext k
      simp
    rw [cT_mul_mul_apply, hcol, hcol, ← formB_apply, hγ, formB_apply]
    simp [hform, Pi.single_apply]
  have hdet : m.det ≠ 0 := by
    intro h0
    apply hJ
    have := congrArg Matrix.det hu
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero m hdet, ?_, hmv⟩
  exact hu

end Concrete

theorem witt_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X Y : Fin n → Fin M → E), gramE σ J X = gramE σ J Y → (gramE σ J X).det ≠ 0 → ∃ g ∈ UJ (σ : E →+* E) J, ∀ a, (g : Matrix (Fin M) (Fin M) E) *ᵥ X a = Y a := by
  intro F E _ _ _ _ _ σ hcm M J hJ n X Y hG hdet
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    apply τ.injective
    have h := hcm.2.2.2
    simp only [RingHom.coe_coe]
    rw [h, h, star_star]
  have hB : ∀ x y, (σ : E →+* E) (formB (σ : E →+* E) J x y) = formB (σ : E →+* E) J y x :=
    formB_conj _ hσ J hJ.1
  have hgram : ∀ (Z : Fin n → Fin M → E) a b,
      formB (σ : E →+* E) J (Z a) (Z b) = gramE σ J Z a b := fun _ _ _ => rfl
  have hker : ∀ c : Fin n → E, (∀ a, formB (σ : E →+* E) J (X a) (lin X c) = 0) →
      lin X c = 0 ∧ lin Y c = 0 := by
    intro c hc
    have h0 : c = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      ext a
      have := hc a
      rw [form_lin_right] at this
      simp only [hgram] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    subst h0
    simp [lin]
  obtain ⟨γ, hγ, hXY⟩ := exists_isom_tuple (formB (σ : E →+* E) J) hσ hB two_ne_zero _ X Y rfl
    (fun a b => by rw [hgram, hgram, hG]) hker
  obtain ⟨g, hg, hgz⟩ := exists_mem_UJ _ J hJ.2 γ hγ
  exact ⟨g, hg, fun a => by rw [hgz, hXY]⟩

end GlobalTheory.CompanionTheory.SW.WittE
