import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnOfDisj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsKill

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

private theorem pow_mul_int (l : ℕ) [Fact l.Prime] (q : ℚ_[l]) :
    ∃ (s : ℕ) (c : ℤ_[l]), ((l ^ s : ℕ) : ℚ_[l]) * q = (c : ℚ_[l]) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt ‖q‖ hl
  have hpos : (0 : ℝ) < (l : ℝ) ^ s := by positivity
  refine ⟨s, ⟨((l ^ s : ℕ) : ℚ_[l]) * q, ?_⟩, rfl⟩
  rw [norm_mul]
  push_cast
  rw [norm_pow, Padic.norm_p, inv_pow, inv_mul_le_one₀ hpos]
  exact hs.le

private theorem exists_int {l : ℕ} [Fact l.Prime] {H : Type*} [AddCommGroup H] [Module ℤ_[l] H]
    (a : ℚ_[l] ⊗[ℤ_[l]] H) : ∃ (s : ℕ) (h : H), (l ^ s : ℕ) • a = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul q x =>
    obtain ⟨s, c, hc⟩ := pow_mul_int l q
    refine ⟨s, c • x, ?_⟩
    have hq : ((l ^ s : ℕ) : ℚ_[l]) • q = c • (1 : ℚ_[l]) := by
      rw [smul_eq_mul, hc, Algebra.smul_def, mul_one]
      rfl
    rw [← Nat.cast_smul_eq_nsmul ℚ_[l], TensorProduct.smul_tmul', hq, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨s, h, e⟩ := ha
    obtain ⟨t, k, f⟩ := hb
    refine ⟨s + t, (l ^ t : ℕ) • h + (l ^ s : ℕ) • k, ?_⟩
    have e1 : (l ^ (s + t) : ℕ) • a = (l ^ t : ℕ) • (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h := by
      rw [← e, smul_smul, pow_add, mul_comm]
    have e2 : (l ^ (s + t) : ℕ) • b = (l ^ s : ℕ) • (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] k := by
      rw [← f, smul_smul, pow_add]
    have t1 : ∀ (c : ℕ) (x : H), c • (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (c • x) :=
      fun c x => (map_nsmul (TensorProduct.mk ℤ_[l] ℚ_[l] H 1) c x).symm
    rw [smul_add, e1, e2, TensorProduct.tmul_add, t1, t1]

private theorem exists_kill {l : ℕ} [Fact l.Prime] {H : Type*} [AddCommGroup H] [Module ℤ_[l] H]
    (h : H) (e : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h = 0) : ∃ b : ℕ, (l ^ b : ℕ) • h = 0 :=
  _root_.UpperTheory.Reformulated.B.Qk55.exists_kill h e

private theorem exists_ub {α : Type*} [Fintype α] (f : α → ℕ) : ∃ s, ∀ a, f a ≤ s :=
  ⟨Finset.univ.sup f, fun a => Finset.le_sup (Finset.mem_univ a)⟩

private theorem pullV_toV {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M N : Model l K}
    (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (x : N.T n) :
    Model.pullV u hu n (N.toV n x) = M.toV n (Model.pullT u hu n x) := by
  simp only [Model.pullV, Model.toV, Model.pullT, GlobalTheory.EtC.pullHQ]
  exact LinearMap.baseChange_tmul _ _ _

private theorem toV_nsmul {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n c : ℕ)
    (x : M.T n) : M.toV n (c • x) = c • M.toV n x :=
  map_nsmul (TensorProduct.mk ℤ_[l] ℚ_[l] (GlobalTheory.EtC.Hl l M.spc n 0) 1) c x

private theorem toV_sub {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ)
    (x y : M.T n) : M.toV n (x - y) = M.toV n x - M.toV n y :=
  map_sub (TensorProduct.mk ℤ_[l] ℚ_[l] (GlobalTheory.EtC.Hl l M.spc n 0) 1) x y

private theorem toV_sum {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ)
    {α : Type*} (t : Finset α) (f : α → M.T n) : M.toV n (∑ a ∈ t, f a) = ∑ a ∈ t, M.toV n (f a) :=
  map_sum (TensorProduct.mk ℤ_[l] ℚ_[l] (GlobalTheory.EtC.Hl l M.spc n 0) 1) f t

theorem UpperTheory.hecke_correspondence_product :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M W : Model l K) (π : W.X ⟶ M.X) (hπ : π ≫ M.p = W.p) (j n : ℕ)
        (T : Fin (n + 1) → Corr l M.X) (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p)
        (A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j)) (_ : ∀ i, IsHk M (T i) (hr i) j (A i))
        (z : ∀ i, Fin (T i).d → (W.X ⟶ (T i).Z)) (hz : ∀ i a, z i a ≫ (T i).p = π)
        (_ : ∀ i (X : Scheme.{0}) (y : X ⟶ W.X), IsUnit (l : Γ(X, ⊤)) → SplitOn (T i).p (y ≫ π) fun a => y ≫ z i a)
        {ι : Type} [Fintype ι] (v : ι → M.T j),
        ∃ (s b : ℕ) (w : Fin (n + 1) → ι → M.T j), (∀ i k, M.toV j (w i k) = (l ^ s : ℕ) • A i (M.toV j (v k))) ∧
          ∀ i k, (l ^ b : ℕ) • Model.pullT π hπ j (w i k) = (l ^ (s + b) : ℕ) •
            ∑ a, Model.pullT (z i a ≫ (T i).r) (by rw [Category.assoc, hr, ← Category.assoc, hz, hπ]) j (v k) := by
  intro l _ K M W π hπ j n T hr A hA z hz hsp ι _ v
  have h1 : ∀ (i : Fin (n + 1)) (k : ι), ∃ (s : ℕ) (h : M.T j), (l ^ s : ℕ) • A i (M.toV j (v k)) = M.toV j h :=
    fun i k => exists_int (H := GlobalTheory.EtC.Hl l M.spc j 0) (A i (M.toV j (v k)))
  choose s' h hs' using h1
  obtain ⟨s, hs⟩ := exists_ub (fun p : Fin (n + 1) × ι => s' p.1 p.2)
  have hle : ∀ i k, s' i k ≤ s := fun i k => hs (i, k)
  let w : Fin (n + 1) → ι → M.T j := fun i k => (l ^ (s - s' i k) : ℕ) • h i k
  have hw : ∀ i k, M.toV j (w i k) = (l ^ s : ℕ) • A i (M.toV j (v k)) := by
    intro i k
    have e : (l ^ s : ℕ) = l ^ (s - s' i k) * l ^ s' i k := by rw [← pow_add, Nat.sub_add_cancel (hle i k)]
    rw [e, mul_smul, hs', toV_nsmul]
  let d : ∀ i k, W.T j := fun i k => Model.pullT π hπ j (w i k) - (l ^ s : ℕ) •
    ∑ a, Model.pullT (z i a ≫ (T i).r) (by rw [Category.assoc, hr, ← Category.assoc, hz, hπ]) j (v k)
  have hd : ∀ i k, W.toV j (d i k) = 0 := by
    intro i k
    simp only [d]
    rw [toV_sub, toV_nsmul, toV_sum, ← pullV_toV, hw, map_nsmul, hA i W π hπ (z i) (hz i) (hsp i)]
    simp only [pullV_toV, sub_self]
  have h2 : ∀ i k, ∃ b : ℕ, (l ^ b : ℕ) • d i k = 0 := fun i k =>
    exists_kill (H := GlobalTheory.EtC.Hl l W.spc j 0) (d i k) (hd i k)
  choose b' hb' using h2
  obtain ⟨b, hb⟩ := exists_ub (fun p : Fin (n + 1) × ι => b' p.1 p.2)
  refine ⟨s, b, w, hw, fun i k => ?_⟩
  have e : (l ^ b : ℕ) = l ^ (b - b' i k) * l ^ b' i k := by rw [← pow_add, Nat.sub_add_cancel (hb (i, k))]
  have hz0 : (l ^ b : ℕ) • d i k = 0 := by rw [e, mul_smul, hb', smul_zero]
  simp only [d] at hz0
  rw [smul_sub, sub_eq_zero] at hz0
  rw [hz0, smul_smul, pow_add, mul_comm]
