import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.UnitaryTransvection

def tv (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  1 + μ • Matrix.vecMulVec w (fun i => D.host.conj (w i))

theorem tv_mulVec (D : D7) {n : ℕ} (μ : D.host.E) (w v : Fin n → D.host.E) :
    (tv D μ w).mulVec v = v + (μ * hE D v w) • w := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  congr 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hE,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cT_tv (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E) :
    cT D (tv D μ w) = tv D (D.host.conj μ) w := by
  ext i j
  simp only [cT, tv, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_add, map_mul, conj_conj, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp only [if_true, map_one]; ring
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]; ring

theorem tv_unitary (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E)
    (h : μ + D.host.conj μ + μ * D.host.conj μ * hE D w w = 0) : tv D μ w * cT D (tv D μ w) = 1 := by
  rw [cT_tv]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, Matrix.one_mulVec,
    hE_add_left, hE_smul_left, add_assoc, ← add_smul]
  have : D.host.conj μ * hE D v w + μ * (hE D v w + D.host.conj μ * hE D v w * hE D w w) = 0 := by
    linear_combination hE D v w * h
  rw [this, zero_smul, add_zero]

theorem smul_mem_int {D : D7} {n : ℕ} (N : Lat D n) {c : D.host.E} (hc : IntE D c) {v : Fin n → D.host.E}
    (hv : v ∈ N) : c • v ∈ N := by
  obtain ⟨a, rfl⟩ := hc
  rw [algebraMap_smul]
  exact N.smul_mem a hv

theorem intE_nat (D : D7) (m : ℕ) : IntE D (m : D.host.E) := ⟨m, map_natCast _ m⟩

theorem gen {D : D7} {n : ℕ} (s : Matrix (Fin n) (Fin n) D.host.E) (c : D.host.E) (M N : Lat D n)
    (z : Fin n → D.host.E) (hM : ∀ y ∈ M, c • s.mulVec y ∈ N) (hz : c • s.mulVec z ∈ N) :
    ∀ v ∈ M ⊔ Submodule.span (𝓞 D.host.E) {z}, c • s.mulVec v ∈ N := by
  intro v hv
  obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ht
  rw [Matrix.mulVec_add, smul_add]
  refine N.add_mem (hM y hy) ?_
  rw [← algebraMap_smul D.host.E a z, Matrix.mulVec_smul, smul_comm]
  exact smul_mem_int N ⟨a, rfl⟩ hz

theorem step {D : D7} {n : ℕ} (M N : Lat D n) (hMN : M ≤ N) (w y : Fin n → D.host.E) (μ : D.host.E) (m : ℕ)
    (hw : ((m : D.host.E) * μ) • w ∈ M) (hy : y ∈ N) (hi : IntE D (hE D y w)) :
    ((m * m : ℕ) : D.host.E) • (tv D μ w).mulVec y ∈ N := by
  rw [tv_mulVec, smul_add, smul_smul]
  refine N.add_mem (smul_mem_int N (intE_nat D _) hy) ?_
  have : ((m * m : ℕ) : D.host.E) * (μ * hE D y w) = ((m : D.host.E) * hE D y w) * ((m : D.host.E) * μ) := by
    push_cast; ring
  rw [this, mul_smul]
  exact smul_mem_int N (mul_mem (intE_nat D m) hi) (hMN hw)

theorem transvection : ∀ (D : D7) (n q : ℕ) (P : Ideal (𝓞 D.host.E)), (∀ a ∈ P, sgO D a ∈ P) → ∀ (M : Lat D n) (b x : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) → (∀ y ∈ M, IntE D (hE D y (b + x))) → IntE D (hE D (b + x) (b + x)) → lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x) (b + x) = 0 → Nat.Coprime m q → (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) → (∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x)) = (p : D.host.E)) → ∃ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (M ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
  intro D n q P hP M b x lam m hbx hM hww hl hmq ⟨p, hp, hpl⟩ ⟨p', hp', hpl'⟩
  have hPw : ∀ a ∈ P, (a : D.host.E) • (b + x) ∈ M := by
    intro a ha
    have : a • (b + x) ∈ M := by
      rw [smul_add]; exact M.add_mem (hbx a ha).1 (hbx a ha).2
    rw [← algebraMap_smul D.host.E a (b + x)] at this
    exact this
  have hcl : (m : D.host.E) * D.host.conj lam = ((sgO D p : 𝓞 D.host.E) : D.host.E) := by
    rw [sgO_coe, ← hpl, map_mul, map_natCast]
  have h1 : ((m : D.host.E) * lam) • (b + x) ∈ M := by rw [hpl]; exact hPw p hp
  have h2 : ((m : D.host.E) * D.host.conj lam) • (b + x) ∈ M := by rw [hcl]; exact hPw _ (hP p hp)
  have h3 : ((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x) ∈ M := by rw [hpl']; exact hPw p' hp'
  have hmem : ∀ z : Fin n → D.host.E, z ∈ M ⊔ Submodule.span (𝓞 D.host.E) {z} := fun z =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  have hco : Nat.Coprime (m * m) q := Nat.Coprime.mul_left hmq hmq
  refine ⟨tv D lam (b + x), tv_unitary D lam _ hl, ⟨m * m, hco, ?_, ?_⟩, ⟨m * m, hco, ?_, ?_⟩⟩
  · exact gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h1 (Submodule.mem_sup_left hy) (hM y hy))
      (step M _ le_sup_left _ _ _ m h1 (hmem _) hww)
  · rw [cT_tv]
    exact gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h2 (Submodule.mem_sup_left hy) (hM y hy))
      (step M _ le_sup_left _ _ _ m h2 (hmem _) hww)
  · refine gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h1 (Submodule.mem_sup_left hy) (hM y hy)) ?_
    rw [tv_mulVec]
    have : ((m * m : ℕ) : D.host.E) • (b + (lam * hE D b (b + x)) • (b + x)) =
        (m : D.host.E) • (((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x)) -
          ((m * m : ℕ) : D.host.E) • x := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      push_cast; ring
    rw [this]
    exact Submodule.sub_mem _ (smul_mem_int _ (intE_nat D m) (Submodule.mem_sup_left h3))
      (smul_mem_int _ (intE_nat D _) (hmem x))
  · rw [cT_tv]
    refine gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h2 (Submodule.mem_sup_left hy) (hM y hy)) ?_
    rw [tv_mulVec]
    have hx : hE D x (b + x) = hE D (b + x) (b + x) - hE D b (b + x) := by
      rw [hE_add_left]; ring
    have : ((m * m : ℕ) : D.host.E) • (x + (D.host.conj lam * hE D x (b + x)) • (b + x)) =
        ((m : D.host.E) + ((m : D.host.E) * D.host.conj lam) * hE D (b + x) (b + x)) •
          (((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x)) -
          ((m * m : ℕ) : D.host.E) • b := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [hx]
      push_cast
      linear_combination (-((m : D.host.E) * m * hE D b (b + x) * (b i + x i))) * hl
    rw [this]
    refine Submodule.sub_mem _ (smul_mem_int _ ?_ (Submodule.mem_sup_left h3))
      (smul_mem_int _ (intE_nat D _) (hmem b))
    rw [hcl]
    exact add_mem (intE_nat D m) (mul_mem ⟨sgO D p, rfl⟩ hww)

end GlobalTheory.UnitaryTransvection
