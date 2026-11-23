import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.KerDia.SharpPoly

theorem detShift_shW {N : ℕ} (lam : DomWeight N) (c : ℤ) (h : 0 < N) :
    (GlobalTheory.Mem.Col2.shW lam c).detShift = lam.detShift + c := by
  unfold DomWeight.detShift; rw [dif_pos h, dif_pos h]; rfl

theorem half_cast (R : Ranks) : ((((R.t + 1) / 2 : ℕ) : ℤ) : ℚ) = ((R.t : ℚ) + 1) / 2 := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h : (R.t + 1) / 2 = a + 1 := by omega
  rw [h, ha]; push_cast; ring

theorem wtN_last {R : Ranks} (P : HCParam R) (i : ℕ) (hi : i < R.m) :
    Examples₂.wtN P (R.N (i + 1) - 1) = -wG R (P.e ⟨i, hi⟩) (i + 1) := by
  have hN : R.N (i + 1) = R.k + i * (R.t + 1) + R.t + 1 := by unfold Ranks.N; ring
  have hq : Examples₂.blkN R (R.N (i + 1) - 1) = i := by
    unfold Examples₂.blkN
    rw [hN, show R.k + i * (R.t + 1) + R.t + 1 - 1 - R.k = R.t + (R.t + 1) * i by
      rw [Nat.mul_comm (R.t + 1) i]; omega]
    rw [Nat.add_mul_div_left _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (Nat.lt_succ_self _), Nat.zero_add]
  unfold Examples₂.wtN
  rw [dif_neg (by omega), dif_pos (by rw [hq]; exact hi)]
  simp only [hq]

theorem exp_nonneg {R : Ranks} {ι : Type} (hc : ι → HCParam R) (i : ℕ) (hi : i < R.m) (τ : ι) (s : ℤ)
    (hs : (s : ℚ) = sExp' R ((hc τ).e ⟨i, hi⟩) (i + 1)) : 0 ≤ (GlobalTheory.Mem.Col2.lamT hc i τ).detShift + s := by
  have hN := R.N_pos i
  have h1 : ((GlobalTheory.Mem.Col2.lamT hc i τ).detShift : ℚ) = Examples₂.wtN (hc τ) (R.N i - 1) - (i : ℚ) * (((R.t : ℚ) + 1) / 2) := by
    unfold GlobalTheory.Mem.Col2.lamT
    rw [detShift_shW _ _ hN]
    unfold DomWeight.detShift
    rw [dif_pos hN]
    rw [Int.cast_add, Int.cast_neg, Int.cast_mul, half_cast, Examples₂.lamOf_eq _ i hi.le, Examples₂.wtQ_eq_wtN]
    push_cast
    ring
  have h2 := wtN_last (hc τ) i hi
  have hle : R.N i ≤ R.N (i + 1) := by
    unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have hlt : R.N (i + 1) - 1 < R.N R.m := by
    have := Examples₂.N_mono (R := R) (j := i + 1) (by omega)
    have := R.N_pos (i + 1)
    omega
  have h3 := Examples₂.wtN_anti (hc τ) (show R.N i - 1 ≤ R.N (i + 1) - 1 by omega) hlt
  have h4 : (((GlobalTheory.Mem.Col2.lamT hc i τ).detShift + s : ℤ) : ℚ) ≥ 0 := by
    rw [Int.cast_add, h1, hs]
    rw [h2] at h3
    simp only [wG, sExp', Ranks.N] at h3 ⊢
    push_cast at h3 ⊢
    linarith
  exact_mod_cast h4

end GlobalTheory.KerDia.SharpPoly

namespace GlobalTheory.KerDia.SharpPoly

def detP {ι : Type} (n : ℕ) (τ : ι) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  (Matrix.of fun a b => (MvPolynomial.X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

theorem eval_detP {ι : Type} {n : ℕ} (y : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) :
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) (detP n τ) = (y τ).det := by
  unfold detP
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

end GlobalTheory.KerDia.SharpPoly

theorem GlobalTheory.KerDia.sharp_mem_range : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ x ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i), (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) := by
  intro B X I l u a i hi x hx
  obtain ⟨P, -, rfl⟩ := Submodule.mem_map.mp hx
  set n : Tau B.R → ℤ := fun τ => (lamT (B.hcW u) i τ).detShift + (I.chain l u a).sSharp i τ with hn
  have hn0 : ∀ τ, 0 ≤ n τ := fun τ =>
    GlobalTheory.KerDia.SharpPoly.exp_nonneg (B.hcW u) i hi τ _ ((I.chain l u a).sSharp_eq i hi τ)
  refine ⟨P * ∏ τ, GlobalTheory.KerDia.SharpPoly.detP (B.R.N i) τ ^ (n τ).toNat, ?_⟩
  funext y
  have hd : ∀ τ, (y.1 τ).det ≠ 0 := fun τ => (y.2 τ).ne_zero
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, ColumnChain.sharp, mulFun, Pi.one_apply, Matrix.one_mul,
    zpow_zero, Finset.prod_const_one, one_mul, map_mul, map_prod, map_pow, GlobalTheory.KerDia.SharpPoly.eval_detP]
  have key : ∀ τ, deFr y τ ^ (I.chain l u a).sSharp i τ * (y.1 τ).det ^ shiftOf (lamT (B.hcW u) i) τ =
      (y.1 τ).det ^ (n τ).toNat := by
    intro τ
    rw [deFr, ← zpow_add₀ (hd τ), ← zpow_natCast, Int.toNat_of_nonneg (hn0 τ), hn, shiftOf, add_comm]
  simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  rw [← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (key τ).symm
