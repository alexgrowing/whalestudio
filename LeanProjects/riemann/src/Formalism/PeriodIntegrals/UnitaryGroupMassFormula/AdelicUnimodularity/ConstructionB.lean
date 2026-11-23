import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.KCountable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatVec

noncomputable section

namespace PI.WAU.B

open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct

theorem cover_of {G : Type} [Group G] (K : Set G) (P : G → Prop) {C : Type} [Countable C]
    (f : G → C) (hf : ∀ x y, P x → P y → f x = f y → y⁻¹ * x ∈ K) :
    ∃ s : Set G, s.Countable ∧ ∀ x, P x → ∃ y ∈ s, y⁻¹ * x ∈ K := by
  classical
  refine ⟨Set.range fun c : {c : C // ∃ x, P x ∧ f x = c} => c.2.choose, Set.countable_range _,
    fun x hx => ?_⟩
  let c : {c : C // ∃ x, P x ∧ f x = c} := ⟨f x, x, hx, rfl⟩
  obtain ⟨hP, hfc⟩ := c.2.choose_spec
  exact ⟨c.2.choose, ⟨c, rfl⟩, hf x _ hx hP hfc.symm⟩

theorem nsmul_cancel {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {N : ℕ}
    (hN : 0 < N) {v w : V} (h : N • v = N • w) : v = w := by
  have h' : (N : K) • v = (N : K) • w := by
    rw [Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul K]
    exact h
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hN.ne') h'

section

variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)

theorem fmat_inv_mul (y : I.Gf) : I.fmat y⁻¹ * I.fmat y = 1 := by
  rw [show I.fmat y⁻¹ * I.fmat y = I.fmat (y⁻¹ * y) from rfl, inv_mul_cancel]
  rfl

theorem fmat_mul_inv (y : I.Gf) : I.fmat y * I.fmat y⁻¹ = 1 := by
  rw [show I.fmat y * I.fmat y⁻¹ = I.fmat (y * y⁻¹) from rfl, mul_inv_cancel]
  rfl

def PN (N : ℕ) (x : I.Gf) : Prop :=
  0 < N ∧ ∀ j, N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf ∧
    N • (I.fmat x⁻¹ *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf

def fN (N : ℕ) (x : I.Gf) : Fin k → Fin k → Bad I.F (N * N) → I.F := by
  classical
  exact fun j => if h : N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m then
    fun i => cls (N * N) (h.choose i) else fun _ _ => 0

theorem half (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y)
    (j : Fin k) : (I.fmat y⁻¹ * I.fmat x) *ᵥ ivec (F := I.F) (m j) ∈ I.Lf := by
  classical
  obtain ⟨hN, hxj⟩ := hx
  obtain ⟨_, hyj⟩ := hy
  have hTx : N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m :=
    lam_sub_alt hm hgen (hxj j).1
  have hTy : N • (I.fmat y *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m :=
    lam_sub_alt hm hgen (hyj j).1
  have hej := congrFun he j
  simp only [fN, dif_pos hTx, dif_pos hTy] at hej
  obtain ⟨haI, haE⟩ := hTx.choose_spec
  obtain ⟨ha'I, ha'E⟩ := hTy.choose_spec

  have hb : ∀ i, ∃ b : Af I.F, (∀ v, b v ∈ v.adicCompletionIntegers I.F) ∧
      hTx.choose i - hTy.choose i = ((N * N : ℕ) : Af I.F) * b := fun i =>
    cls_eq (Nat.mul_pos hN hN) (haI i) (ha'I i) (congrFun hej i)
  choose b hbI hbE using hb
  set w : Fin I.n → I.E ⊗[I.F] Af I.F := ∑ i, incA I.F I.E (b i) • ivec (F := I.F) (m i) with hwdef
  have hw : w ∈ I.Lf :=
    Submodule.sum_mem _ fun i _ => smulO_mem (incA_mem (hbI i)) (ivec_mem (hm i))
  have hdiff : N • (I.fmat x *ᵥ ivec (F := I.F) (m j) - I.fmat y *ᵥ ivec (F := I.F) (m j)) =
      N • (N • w) := by
    rw [smul_sub, haE, ha'E, ← Finset.sum_sub_distrib, hwdef, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, ← map_sub, hbE i, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul,
      smul_smul]
  have hd : I.fmat x *ᵥ ivec (F := I.F) (m j) - I.fmat y *ᵥ ivec (F := I.F) (m j) = N • w :=
    nsmul_cancel (K := I.F) hN hdiff
  have hxu : I.fmat x *ᵥ ivec (F := I.F) (m j) = I.fmat y *ᵥ ivec (F := I.F) (m j) + N • w := by
    rw [← hd]
    abel
  rw [← Matrix.mulVec_mulVec, hxu, Matrix.mulVec_add, Matrix.mulVec_mulVec, fmat_inv_mul I y,
    Matrix.one_mulVec]
  refine Submodule.add_mem _ (ivec_mem (hm j)) ?_
  have hP : ∀ i, (N • I.fmat y⁻¹) *ᵥ ivec (F := I.F) (m i) ∈ I.Lf := fun i => by
    rw [Matrix.smul_mulVec]
    exact (hyj i).2
  have h2 := mulVec_lam hm hgen (N • I.fmat y⁻¹) hP hw
  rwa [Matrix.smul_mulVec, ← Matrix.mulVec_smul] at h2

theorem step (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y) :
    y⁻¹ * x ∈ I.Kset := by
  show ∀ w, w ∈ I.Lf ↔
    (((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _) *ᵥ w ∈ I.Lf
  have hco : (((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _) =
      I.fmat y⁻¹ * I.fmat x := rfl
  intro w
  rw [hco]
  constructor
  · intro hw
    exact mulVec_lam hm hgen _ (half I m hm hgen hx hy he) hw
  · intro hw
    have h2 := mulVec_lam hm hgen _ (half I m hm hgen hy hx he.symm) hw
    have h1 : I.fmat x⁻¹ * I.fmat y * (I.fmat y⁻¹ * I.fmat x) = 1 := by
      rw [mul_assoc, ← mul_assoc (I.fmat y), fmat_mul_inv, one_mul, fmat_inv_mul]
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h2

theorem exists_PN (x : I.Gf) : ∃ N, PN I m N x := by
  classical
  have hA : ∀ j, ∃ N : ℕ, 0 < N ∧ N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf :=
    fun j => exists_nat_vec I.L_span _
  have hB : ∀ j, ∃ N : ℕ, 0 < N ∧ N • (I.fmat x⁻¹ *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf :=
    fun j => exists_nat_vec I.L_span _
  choose A hA0 hA using hA
  choose B hB0 hB using hB
  refine ⟨(∏ j, A j) * ∏ j, B j, ?_, fun j => ⟨?_, ?_⟩⟩
  · exact Nat.mul_pos (Finset.prod_pos fun j _ => hA0 j) (Finset.prod_pos fun j _ => hB0 j)
  · obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem A (Finset.mem_univ j)
    rw [hM, mul_assoc]
    exact nsmul_lam (hA j) _
  · obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem B (Finset.mem_univ j)
    rw [hM, show (∏ j, A j) * (B j * M) = B j * (M * ∏ j, A j) by ring]
    exact nsmul_lam (hB j) _

end

end PI.WAU.B

namespace PI.WAU

open PI.WAU.B

theorem compact_countable : KCountable := by
  intro I
  obtain ⟨k, m, hm, hgen⟩ := exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  have hcov : ∀ N : ℕ, ∃ s : Set I.Gf, s.Countable ∧
      ∀ x, PN I m N x → ∃ y ∈ s, y⁻¹ * x ∈ I.Kset := by
    intro N
    haveI : Countable (Bad I.F (N * N) → I.F) := countable_cls (N * N)
    exact cover_of I.Kset (PN I m N) (fN I m N) fun x y hx hy he => step I m hm hgen hx hy he
  choose s hs hsK using hcov
  refine ⟨⋃ N, s N, Set.countable_iUnion hs, fun x => ?_⟩
  obtain ⟨N, hN⟩ := exists_PN I m x
  obtain ⟨y, hy, hyK⟩ := hsK N x hN
  exact ⟨y, Set.mem_iUnion.mpr ⟨N, hy⟩, hyK⟩

end PI.WAU
