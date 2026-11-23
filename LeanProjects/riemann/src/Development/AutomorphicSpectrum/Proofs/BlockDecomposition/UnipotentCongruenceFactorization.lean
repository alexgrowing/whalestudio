import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1

open GlobalTheory.SplitWeil ValuativeRel

section Core

variable {k : Type} [Field k]

def rowM (n : ℕ) (a : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + Matrix.of fun r c => if r = Fin.last n then a c else 0

theorem rowM_apply (n : ℕ) (a : Fin (n + 1) → k) (r c : Fin (n + 1)) :
    rowM n a r c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c + if r = Fin.last n then a c else 0 := rfl

theorem rowM_mul (n : ℕ) (a b : Fin (n + 1) → k) :
    rowM n a * rowM n b = rowM n (a + b + a (Fin.last n) • b) := by
  ext r c
  have e : rowM n a * rowM n b = 1 + (Matrix.of fun r c => if r = Fin.last n then a c else 0) +
      (Matrix.of fun r c => if r = Fin.last n then b c else 0) +
      (Matrix.of fun r c => if r = Fin.last n then a c else 0) *
        (Matrix.of fun r c => if r = Fin.last n then b c else 0) := by
    unfold rowM
    noncomm_ring
  rw [e]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, rowM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hr : r = Fin.last n
  · subst hr
    simp [Finset.sum_ite_eq', ite_mul]
    ring
  · simp [hr]

def rowGL (n : ℕ) (a : Fin (n + 1) → k) (hu : 1 + a (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k where
  val := rowM n a
  inv := rowM n (-(1 + a (Fin.last n))⁻¹ • a)
  val_inv := by
    rw [rowM_mul]
    have : a + -(1 + a (Fin.last n))⁻¹ • a + a (Fin.last n) • -(1 + a (Fin.last n))⁻¹ • a = 0 := by
      ext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      field_simp
      ring
    rw [this]
    ext r c
    simp [rowM_apply]
  inv_val := by
    rw [rowM_mul]
    have : -(1 + a (Fin.last n))⁻¹ • a + a + (-(1 + a (Fin.last n))⁻¹ • a) (Fin.last n) • a = 0 := by
      ext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      field_simp
      ring
    rw [this]
    ext r c
    simp [rowM_apply]

theorem rowGL_inv_val (n : ℕ) (a : Fin (n + 1) → k) (hu : 1 + a (Fin.last n) ≠ 0) :
    (((rowGL n a hu)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      rowM n (-(1 + a (Fin.last n))⁻¹ • a) := rfl

end Core

section Core2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rowM_near (s : kˣ) (n : ℕ) (a : Fin (n + 1) → k) (ha : ∀ c, a c ∈ cball s) :
    GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (rowM n a) := by
  intro r c
  rw [rowM_apply, add_sub_cancel_left]
  split_ifs
  · exact ha c
  · exact (ballSub s).zero_mem

theorem rowGL_mem (s : kˣ) (hs : valuation k (s : k) ≤ 1) (n : ℕ) (a : Fin (n + 1) → k)
    (hu : 1 + a (Fin.last n) ≠ 0) (hv : valuation k (1 + a (Fin.last n)) = 1) (ha : ∀ c, a c ∈ cball s) :
    rowGL n a hu ∈ congGL k s hs (n + 1) := by
  refine ⟨rowM_near s n a ha, ?_⟩
  rw [rowGL_inv_val]
  refine rowM_near s n _ fun c => ?_
  show valuation k ((-(1 + a (Fin.last n))⁻¹ • a) c) ≤ valuation k (s : k)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, Valuation.map_neg, map_inv₀, hv, inv_one, one_mul]
  exact ha c

theorem core (s : kˣ) (hs : valuation k (s : k) ≤ 1) (hs1 : valuation k (s : k) < 1) {n i : ℕ} (hi : i < n)
    (A B M : GL (Fin (n + 1)) k) (hM : M ∈ Mir k n) (hMAB : M = A * B) (hB : B ∈ congGL k s hs (n + 1))
    (hA : ∀ r c : Fin (n + 1), i < r.val → c.val ≤ i → (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c = 0) :
    ∃ a x : GL (Fin (n + 1)) k, a ∈ Mir k n ∧ x ∈ Mir k n ∧ x ∈ congGL k s hs (n + 1) ∧ M = a * x ∧
      ∀ r c : Fin (n + 1), i < r.val → c.val ≤ i → (a : Matrix (Fin (n + 1)) (Fin (n + 1)) k) r c = 0 := by
  classical
  set Bi : Matrix (Fin (n + 1)) (Fin (n + 1)) k := ((B⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) with hBi
  let a : Fin (n + 1) → k := fun c => Bi (Fin.last n) c - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c
  have ha : ∀ c, a c ∈ cball s := fun c => hB.2 (Fin.last n) c
  have hv : valuation k (1 + a (Fin.last n)) = 1 :=
    Valuation.map_one_add_of_lt _ (lt_of_le_of_lt (ha _) hs1)
  have hu : 1 + a (Fin.last n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv

  have hAB : A = M * B⁻¹ := by rw [hMAB]; group
  have hlast : ∀ c, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c = Bi (Fin.last n) c := by
    intro c
    have hl := (mem_Mir_iff k M).1 hM
    rw [hAB, Units.val_mul, Matrix.mul_apply, hl]
    simp [eLast, Pi.single_apply, hBi]
  have ha0 : ∀ c : Fin (n + 1), c.val ≤ i → a c = 0 := by
    intro c hc
    have h1 : Bi (Fin.last n) c = 0 := by
      rw [← hlast c]
      exact hA _ c (by simpa using hi) hc
    have h2 : Fin.last n ≠ c := by
      intro e
      rw [← e] at hc
      simp at hc
      omega
    simp [a, h1, Matrix.one_apply_ne h2]
  let R := rowGL n a hu
  have hRlast : ∀ c, (R : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) c = Bi (Fin.last n) c := by
    intro c
    show rowM n a _ _ = _
    rw [rowM_apply]
    simp [a]
  have hR : R ∈ congGL k s hs (n + 1) := rowGL_mem s hs n a hu hv ha
  have hx : R * B ∈ Mir k n := by
    rw [mem_Mir_iff]
    funext c
    have e : (Bi * (B : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = 1 := by
      rw [hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 := congrFun (congrFun e (Fin.last n)) c
    rw [Matrix.mul_apply] at e2
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [hRlast]
    rw [e2]
    simp [eLast, Pi.single_apply, Matrix.one_apply, eq_comm]
  refine ⟨A * R⁻¹, R * B, ?_, hx, (congGL k s hs (n + 1)).mul_mem hR hB, ?_, ?_⟩
  · have : A * R⁻¹ = M * (R * B)⁻¹ := by rw [hMAB]; group
    rw [this]
    exact (Mir k n).mul_mem hM ((Mir k n).inv_mem hx)
  · rw [hMAB]; group
  · intro r c hr hc
    have e : ((R⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = rowM n (-(1 + a (Fin.last n))⁻¹ • a) := rfl
    have e1 : ∀ l, rowM n (-(1 + a (Fin.last n))⁻¹ • a) l c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) l c := by
      intro l
      rw [rowM_apply]
      simp [ha0 c hc]
    rw [Units.val_mul, e, Matrix.mul_apply]
    simp only [e1]
    simp [Matrix.one_apply, hA r c hr hc]

end Core2

theorem near_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : kˣ) {n : ℕ} (g : Mir k n)
    (hg : NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) :
    NearOne s ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro a b
  have h := hg (Fin.castSucc a) (Fin.castSucc b)
  have e : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (1 : Matrix (Fin n) (Fin n) k) a b := by
    simp [Matrix.one_apply]
  rw [e] at h
  exact h

theorem mirProj_mem_cong {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : kˣ) (hs : valuation k (s : k) ≤ 1) {n : ℕ} (g : Mir k n) (hg : g ∈ congM k s hs n) :
    mirabolicProjection k n g ∈ congGL k s hs n := by
  refine ⟨near_block s g hg.1, ?_⟩
  rw [← map_inv]
  exact near_block s g⁻¹ hg.2

theorem mirProj_sEmb {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (m : Mir k n) : mirabolicProjection k (n + 1) (sEmb k n m) = (m : GL (Fin (n + 1)) k) := by
  apply Units.ext
  ext a b
  show glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) = _
  simp [glEmbMat]

theorem mirProj_dEmb {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (d : Fin (t + 1) → k) : mirabolicProjection k ((i + 1) + t + 1) (dEmb k i t d) = 1 :=
  GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirProj_eq_one_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩)

theorem mem_mirabolicParabolic_mul_cong : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (hs1 : ValuativeRel.valuation k (s : k) < 1)
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (κ : Mir k ((i + 1) + t + 1)) (hκ : κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1))
    (e : dEmb k i t d * sEmb k ((i + 1) + t) m = h * κ),
  ∃ a ∈ MirabolicParabolic k (i + 1) t, ∃ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t), m = a * x := by
  intro k _ _ _ _ i t s hs hs1 d m h hh κ hκ e
  have e1 := congrArg (mirabolicProjection k ((i + 1) + t + 1)) e
  rw [map_mul, map_mul, mirProj_dEmb, mirProj_sEmb, one_mul] at e1
  have hA : ∀ r c : Fin ((i + 1) + t + 1), i < r.val → c.val ≤ i →
      ((mirabolicProjection k ((i + 1) + t + 1) h : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) r c = 0 := by
    intro r c hr hc
    have := GlobalTheory.CompanionTheory.BZPhiPG.Grp.hpg_entry h hh (Fin.castSucc r) (by simpa using hr)
      (by have := r.isLt; simp; omega) ⟨c.val, by omega⟩
    exact this
  obtain ⟨a, x, ha, hx, hxc, hax, hent⟩ := core s hs hs1 (n := (i + 1) + t) (i := i) (by omega) _ _
    (m : GL (Fin ((i + 1) + t + 1)) k) m.2 e1 (mirProj_mem_cong s hs κ hκ) hA
  refine ⟨⟨a, ha⟩, (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k (i + 1) t _).2 ?_, ⟨x, hx⟩, hxc, Subtype.ext hax⟩
  intro b c
  apply hent
  · rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]
    omega
  · rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
    have := c.isLt
    omega

end GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1

end
