import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.StarMemAp

noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WF

variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

theorem ap_smul (a : Ap I p) (v : Fin I.n → I.E) : a • v = (a : I.E) • v := rfl

theorem osmul (o : 𝓞 I.E) (v : Fin I.n → I.E) : o • v = (o : I.E) • v :=
  (algebraMap_smul I.E o v).symm

theorem hG_L {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) :
    hG I x y ∈ (algebraMap (𝓞 I.E) I.E).range := by
  unfold hG
  exact (I.L_dual y).mp hy x hx

theorem natsmul_mem_L {s : ℕ} {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by
  have h1 : ((s : 𝓞 I.E) : I.E) = (s : I.E) := by simp
  rw [← h1, ← osmul]
  exact I.L.smul_mem _ hx

theorem mem_LA_iff (hp : p.Prime) {x : Fin I.n → I.E} :
    x ∈ LA I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • x ∈ I.L := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
    | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
      have : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
        push_cast; module
      rw [this]
      exact I.L.add_mem (natsmul_mem_L hsx) (natsmul_mem_L hty)
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨s0, hs0, a0, ha0⟩ := a.2
      refine ⟨s0 * s, Nat.Coprime.mul_left hs0 hs, ?_⟩
      have : ((s0 * s : ℕ) : I.E) • (a • x) = a0 • ((s : I.E) • x) := by
        rw [ap_smul, osmul, ← ha0]; push_cast; module
      rw [this]
      exact I.L.smul_mem _ hsx
  · rintro ⟨s, hs, hsx⟩
    have hsA : ((s : I.E))⁻¹ ∈ Ap I p := inv_mem_Ap hp hs
    have hs0 : (s : I.E) ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs)
      exact_mod_cast this
    have : x = (⟨_, hsA⟩ : Ap I p) • ((s : I.E) • x) := by
      rw [ap_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

theorem L_le_LA {x : Fin I.n → I.E} (hx : x ∈ I.L) : x ∈ LA I p := Submodule.subset_span hx

theorem hG_LA (hp : p.Prime) {x y : Fin I.n → I.E} (hx : x ∈ LA I p) (hy : y ∈ LA I p) :
    hG I x y ∈ Ap I p := by
  obtain ⟨s, hs, hsx⟩ := (mem_LA_iff hp).1 hx
  obtain ⟨t, ht, hty⟩ := (mem_LA_iff hp).1 hy
  obtain ⟨o, ho⟩ := hG_L hsx hty
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, o, ?_⟩
  rw [hG_smul_left, hG_smul_right, star_natCast] at ho
  rw [show ((o : 𝓞 I.E) : I.E) = algebraMap (𝓞 I.E) I.E o from rfl, ho]; push_cast; ring

theorem dual_LA (hp : p.Prime) {x : Fin I.n → I.E} (hx : ∀ y ∈ I.L, hG I y x ∈ Ap I p) : x ∈ LA I p := by
  classical
  obtain ⟨T, hT⟩ := I.L_fg
  have hden : ∀ t ∈ T, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * hG I t x = (a : I.E) := by
    intro t ht
    exact hx t (hT ▸ Submodule.subset_span ht)
  choose! s hs a ha using hden
  let S : ℕ := ∏ t ∈ T, s t
  have hS : Nat.Coprime S p := Nat.Coprime.prod_left fun t ht => hs t ht
  have key : ∀ y ∈ I.L, hG I y ((S : I.E) • x) ∈ (algebraMap (𝓞 I.E) I.E).range := by
    intro y hy
    rw [← hT] at hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      have hdvd : s t ∣ S := Finset.dvd_prod_of_mem s ht
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : 𝓞 I.E) * a t, ?_⟩
      rw [hG_smul_right, hc]; push_cast
      rw [mul_comm ((s t : ℕ) : I.E), mul_assoc, ha t ht]
    | zero => exact ⟨0, by simp [hG_zero_left]⟩
    | add y z _ _ hy hz =>
      obtain ⟨o1, h1⟩ := hy; obtain ⟨o2, h2⟩ := hz
      exact ⟨o1 + o2, by rw [hG_add_left, ← h1, ← h2]; simp⟩
    | smul o y _ hy =>
      obtain ⟨o1, h1⟩ := hy
      refine ⟨PI.ScRefExists.TH.sg I o * o1, ?_⟩
      rw [osmul, hG_smul_left, ← h1]; simp [PI.ScRefExists.TH.sg_coe]
  have hSx : (S : I.E) • x ∈ I.L := (I.L_dual _).2 key
  exact (mem_LA_iff hp).2 ⟨S, hS, hSx⟩

theorem mem_LA_of_nsmul (hp : p.Prime) {M : ℕ} (hM : Nat.Coprime M p) {x : Fin I.n → I.E}
    (hx : M • x ∈ I.L) : x ∈ LA I p := by
  refine (mem_LA_iff hp).2 ⟨M, hM, ?_⟩
  rwa [← Nat.cast_smul_eq_nsmul I.E] at hx

def proj {r : ℕ} (e f : Fin r → Fin I.n → I.E) (y : Fin I.n → I.E) : Fin I.n → I.E :=
  ∑ a, (hG I (f a) y • e a + hG I (e a) y • f a)

theorem hG_e_proj {r : ℕ} {e f : Fin r → Fin I.n → I.E} (he : ∀ a b, hG I (e a) (e b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) (b : Fin r) (y : Fin I.n → I.E) :
    hG I (e b) (proj e f y) = hG I (e b) y := by
  have hr : ∀ (x : Fin I.n → I.E) (c : Fin r → I.E) (w : Fin r → Fin I.n → I.E),
      hG I x (∑ a, c a • w a) = ∑ a, c a * hG I x (w a) := by
    intro x c w
    unfold hG Formalism.UG.hform
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hadd2 : ∀ x u w : Fin I.n → I.E, hG I x (u + w) = hG I x u + hG I x w := by
    intro x u w
    unfold hG Formalism.UG.hform
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  unfold proj
  rw [Finset.sum_add_distrib, hadd2, hr, hr]
  simp only [he, hef]
  simp

theorem hG_f_proj {r : ℕ} {e f : Fin r → Fin I.n → I.E} (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) (b : Fin r) (y : Fin I.n → I.E) :
    hG I (f b) (proj e f y) = hG I (f b) y := by
  have hr : ∀ (x : Fin I.n → I.E) (c : Fin r → I.E) (w : Fin r → Fin I.n → I.E),
      hG I x (∑ a, c a • w a) = ∑ a, c a * hG I x (w a) := by
    intro x c w
    unfold hG Formalism.UG.hform
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hadd2 : ∀ x u w : Fin I.n → I.E, hG I x (u + w) = hG I x u + hG I x w := by
    intro x u w
    unfold hG Formalism.UG.hform
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hJ : ∀ i j, starRingEnd I.E (I.J i j) = I.J j i := by
    intro i j
    have := congrFun (congrFun I.J_herm j) i
    simpa [Formalism.UG.cT] using this
  have hsym : ∀ x y, hG I y x = starRingEnd I.E (hG I x y) := by
    intro x y
    unfold hG Formalism.UG.hform
    simp only [map_sum, map_mul, starRingEnd_self_apply, hJ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1 : ∀ a, hG I (f b) (e a) = if a = b then 1 else 0 := by
    intro a
    rw [hsym (e a) (f b), hef]
    split_ifs <;> simp
  unfold proj
  rw [Finset.sum_add_distrib, hadd2, hr, hr]
  simp only [hf, h1]
  simp

theorem proj_mem (hp : p.Prime) {r : ℕ} {e f : Fin r → Fin I.n → I.E}
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p) :
    proj e f y ∈ LA I p := by
  unfold proj
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · have h1 := Submodule.smul_mem (LA I p) (⟨hG I (f a) y, hG_LA hp (hfA a) hy⟩ : Ap I p) (heA a)
    rwa [ap_smul] at h1
  · have h1 := Submodule.smul_mem (LA I p) (⟨hG I (e a) y, hG_LA hp (heA a) hy⟩ : Ap I p) (hfA a)
    rwa [ap_smul] at h1

theorem proj_span {r : ℕ} (e f : Fin r → Fin I.n → I.E) (hp : p.Prime)
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p)
    (S : Set (Fin I.n → I.E)) (hS : Set.range e ∪ Set.range f ⊆ S) :
    proj e f y ∈ Submodule.span (Ap I p) S := by
  unfold proj
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · have h1 := Submodule.smul_mem (Submodule.span (Ap I p) S)
      (⟨hG I (f a) y, hG_LA hp (hfA a) hy⟩ : Ap I p)
      (Submodule.subset_span (hS (Or.inl ⟨a, rfl⟩)))
    rwa [ap_smul] at h1
  · have h1 := Submodule.smul_mem (Submodule.span (Ap I p) S)
      (⟨hG I (e a) y, hG_LA hp (heA a) hy⟩ : Ap I p)
      (Submodule.subset_span (hS (Or.inr ⟨a, rfl⟩)))
    rwa [ap_smul] at h1

end PI.ScRefExists.WF
