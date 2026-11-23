import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.EvalIdFrameRowAct

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace FrameUnitLemmas

section Rel

variable {Kc : Type} [Field Kc] (Oc : Subring Kc) (π : Kc)

def Sim (x : Kc) (n : ℤ) : Prop := ∃ u : Kc, u ∈ Oc ∧ u⁻¹ ∈ Oc ∧ x = u * π ^ n

variable {Oc π}

theorem Sim.mem {x : Kc} (h : Sim Oc π x 0) : x ∈ Oc := by
  obtain ⟨u, hu, _, rfl⟩ := h
  rwa [zpow_zero, mul_one]

theorem Sim.congr {x : Kc} {n m : ℤ} (h : Sim Oc π x n) (e : n = m) : Sim Oc π x m := e ▸ h

theorem Sim.mul (hπ : π ≠ 0) {x y : Kc} {n m : ℤ} (hx : Sim Oc π x n) (hy : Sim Oc π y m) :
    Sim Oc π (x * y) (n + m) := by
  obtain ⟨u, hu, hu', rfl⟩ := hx
  obtain ⟨v, hv, hv', rfl⟩ := hy
  refine ⟨u * v, mul_mem hu hv, ?_, ?_⟩
  · rw [mul_inv]; exact mul_mem hu' hv'
  · rw [zpow_add₀ hπ]; ring

theorem Sim.inv {x : Kc} {n : ℤ} (hx : Sim Oc π x n) : Sim Oc π x⁻¹ (-n) := by
  obtain ⟨u, hu, hu', rfl⟩ := hx
  exact ⟨u⁻¹, hu', by rwa [inv_inv], by rw [mul_inv, zpow_neg]⟩

theorem Sim.pow {x : Kc} {n : ℤ} (hx : Sim Oc π x n) (k : ℕ) : Sim Oc π (x ^ k) (k * n) := by
  obtain ⟨u, hu, hu', rfl⟩ := hx
  refine ⟨u ^ k, pow_mem hu k, by rw [← inv_pow]; exact pow_mem hu' k, ?_⟩
  rw [mul_pow, ← zpow_natCast (π ^ n), ← zpow_mul, mul_comm n]

theorem Sim.zpow {x : Kc} {n : ℤ} (hx : Sim Oc π x n) (k : ℤ) : Sim Oc π (x ^ k) (k * n) := by
  cases k with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact hx.pow k
  | negSucc k =>
    rw [zpow_negSucc]
    exact (hx.pow (k + 1)).inv.congr (by rw [Int.negSucc_eq]; push_cast; ring)

theorem Sim.prod (hπ : π ≠ 0) {ι : Type} (S : Finset ι) (x : ι → Kc) (n : ι → ℤ)
    (h : ∀ i ∈ S, Sim Oc π (x i) (n i)) : Sim Oc π (∏ i ∈ S, x i) (∑ i ∈ S, n i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by rw [inv_one]; exact one_mem _, by simp⟩
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).mul hπ (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Sim.self_zpow (k : ℤ) : Sim Oc π (π ^ k) k :=
  ⟨1, one_mem _, by rw [inv_one]; exact one_mem _, (one_mul _).symm⟩

end Rel

theorem sum_min_colH {N : ℕ} (μ : Fin N → ℕ) (hμ : Antitone μ) (c : ℕ) (hc : ∀ t, μ t ≤ c) (i : ℕ) (hi : i ≤ N) :
    ∑ k : Fin c, min (colH μ k.val) i = ∑ t : Fin N, if t.val < i then μ t else 0 := by
  have h1 : ∀ k : Fin c, min (colH μ k.val) i = ∑ t : Fin N, if t.val < i ∧ k.val < μ t then 1 else 0 := by
    intro k
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun t : Fin N => t.val < i ∧ k.val < μ t) =
        Finset.univ.filter fun t : Fin N => t.val < min (colH μ k.val) i := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← BidetPairing.lt_colH_iff hμ k.val t, lt_min_iff, and_comm]
    rw [this, BidetPairing.card_fin_lt N _ (le_trans (min_le_right _ _) hi)]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with h
  · simp only [h, true_and]
    rw [← Finset.card_filter, BidetPairing.card_fin_lt c _ (hc t)]
  · simp [h]

theorem sum_Icc_eq_range (F : ℕ → ℤ) (i : ℕ) : ∑ a ∈ Finset.Icc 1 i, F a = ∑ t ∈ Finset.range i, F (t + 1) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem sum_fin_lt (F : ℕ → ℤ) (N i : ℕ) (hi : i ≤ N) :
    ∑ t : Fin N, (if t.val < i then F t.val else 0) = ∑ t ∈ Finset.range i, F t := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if t < i then F t else 0) N, ← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem place_arith {n' : ℕ} (P : Fin n' → Prop) [DecidablePred P] (w e0 e1 c e M la : Fin n' → ℤ) (n n1 i : ℤ)
    (hE : ∀ s, ¬ P s → e s = e0 s + w s ∧ e1 s = -w s ∧ M s = la s + i * w s)
    (hO : ∀ s, P s → c s = w s - e0 s ∧ e1 s = e0 s) :
    (∑ s ∈ Finset.univ.filter (fun s => ¬ P s), la s + i * ∑ s ∈ Finset.univ.filter (fun s => P s), w s) +
      ((∑ s ∈ Finset.univ.filter (fun s => ¬ P s), w s - ∑ s ∈ Finset.univ.filter (fun s => P s), w s) * (-n) +
        -((∑ s ∈ Finset.univ.filter (fun s => ¬ P s), w s - ∑ s ∈ Finset.univ.filter (fun s => P s), w s) * (-n1))) +
      ∑ s, -(e0 s) * n + -(∑ s, -(e1 s) * (n1 + -i)) +
      ∑ s, (if P s then -(c s) * n + c s * (n1 + -i) else e s * n + -(M s)) = 0 := by
  have key : ∀ s, ((if ¬ P s then la s else 0) + i * (if P s then w s else 0)) +
      (((if ¬ P s then w s else 0) - (if P s then w s else 0)) * (-n) +
        -(((if ¬ P s then w s else 0) - (if P s then w s else 0)) * (-n1))) +
      -(e0 s) * n + -(-(e1 s) * (n1 + -i)) +
      (if P s then -(c s) * n + c s * (n1 + -i) else e s * n + -(M s)) = 0 := by
    intro s
    by_cases h : P s
    · obtain ⟨h1, h2⟩ := hO s h
      simp only [h, not_true_eq_false, if_true, if_false]
      rw [h1, h2]; ring
    · obtain ⟨h1, h2, h3⟩ := hE s h
      simp only [h, not_false_eq_true, if_true, if_false]
      rw [h1, h2, h3]; ring
  rw [← Finset.sum_eq_zero (fun s (_ : s ∈ Finset.univ) => key s)]
  simp only [Finset.sum_filter, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  simp only [← Finset.sum_mul, Finset.sum_sub_distrib]

section Blocks

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem sig_int (v : X.Pl) (s : ℕ) (x : X.G.P.W v) :
    ∃ y : X.G.P.W v, (X.G.P.σ v ^ s) (algebraMap (X.G.P.W v) (X.G.P.Qq v) x) = algebraMap (X.G.P.W v) (X.G.P.Qq v) y := by
  induction s generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ s ih =>
    obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
    obtain ⟨z, hz⟩ := ih (x ^ p + (p : X.G.P.W v) * y)
    refine ⟨z, ?_⟩
    rw [pow_succ, RingAut.mul_apply, hy, hz]

theorem mF_det (j : ℕ) (b : BX X) (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    (mF X j b A).det = X.G.P.ι b.1 ((X.G.P.σ b.1 ^ b.2.val) A.det) := by
  unfold mF
  rw [Matrix.det_submatrix_equiv_self]
  exact (RingHom.map_det ((X.G.P.ι b.1).comp (X.G.P.σ b.1 ^ b.2.val : X.G.P.Qq b.1 ≃+* X.G.P.Qq b.1).toRingHom) A).symm

theorem det_DgX (K' : Type) [Field K'] (j : ℕ) (i0 : X.Pl → ℕ) (v : X.Pl) (h : i0 v ≤ NJ X (j + 1)) :
    (DgX X K' j i0 v).det = (p : K') ^ (-(i0 v : ℤ)) := by
  unfold DgX
  rw [Matrix.det_diagonal, Fin.prod_univ_eq_prod_range (fun i => if i < i0 v then ((p : K'))⁻¹ else 1) (NJ X (j + 1)),
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have : (Finset.range (NJ X (j + 1))).filter (fun i => i < i0 v) = Finset.range (i0 v) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range, zpow_neg, zpow_natCast, inv_pow]

theorem len_def (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup) : len X v j L = lenLat (X.G.P.W v) p (X.latAt v j L) := by
  cases j <;> rfl

theorem len_eq (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup) (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hL : X.latAt v j L = colSpan (X.G.P.W v) (g : Matrix _ _ (X.G.P.Qq v))) :
    len X v j L = -ordP (X.G.P.W v) p (g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det := by
  have hu : IsUnit (g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit g)
  have hS := X.G.P.setting v
  have := hS.frac_alt
  rw [len_def, hL, lenLat_colSpan hS.p_unif _ hu]

theorem nuv_lam (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (t : ℕ) (ht : t < X.G.P.m + 1) :
    X.nuv v (j + 1) s (t + 1) = lamI (X.G.P.lam0 v) s (t + 1) + X.w v (j + 1) s := by
  unfold Sys.nuv nu
  rw [if_pos ⟨by omega, by omega⟩]

theorem boxes (hS : XShape) (j : ℕ) (b : BX X) (i : ℕ) (hi : i ≤ X.G.P.m + 1) :
    ((∑ k : Fin (cX X j b), min (X.colHt b.1 (j + 1) b.2 k.val) i : ℕ) : ℤ) =
      ∑ a ∈ Finset.Icc 1 i, lamI (X.G.P.lam0 b.1) b.2 a + (i : ℤ) * X.w b.1 (j + 1) b.2 := by
  obtain ⟨_, _, h3, h4, _, h6, _⟩ := hS p X j b
  have hi' : i ≤ NJ X (j + 1) := by
    show i ≤ X.G.P.m + 1 + (j + 1) * (X.t + 1)
    omega
  have h := sum_min_colH (muX X j (NJ X (j + 1)) b) (h3 _) (cX X j b) (h4 _) i hi'
  simp only [h6] at h
  have h7 : ∀ t : Fin (NJ X (j + 1)), (((if t.val < i then muX X j (NJ X (j + 1)) b t else 0 : ℕ)) : ℤ) =
      if t.val < i then X.nuv b.1 (j + 1) b.2 (t.val + 1) else 0 := by
    intro t
    split_ifs
    · exact Int.toNat_of_nonneg (nuv_nonneg X b.1 j b.2 _)
    · rfl
  rw [h, Nat.cast_sum, Finset.sum_congr rfl fun t _ => h7 t,
    sum_fin_lt (fun t => X.nuv b.1 (j + 1) b.2 (t + 1)) _ _ hi', sum_Icc_eq_range,
    Finset.sum_congr rfl fun t ht => nuv_lam X j b.1 b.2 t (by have := Finset.mem_range.1 ht; omega),
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (Oc : Subring Kc)

theorem tw_int (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc) (b : BX X) (x : X.G.P.W b.1) :
    algebraMap X.G.Kf Kc (X.G.P.ι b.1 ((X.G.P.σ b.1 ^ b.2.val) (algebraMap (X.G.P.W b.1) (X.G.P.Qq b.1) x))) ∈ Oc := by
  obtain ⟨y, hy⟩ := sig_int X b.1 b.2.val x
  rw [hy, (X.G.P.setting b.1).ι_comp]
  exact hO _

theorem sim_tw (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc) (b : BX X)
    {x : X.G.P.Qq b.1} (hx : x ≠ 0) :
    Sim Oc (p : Kc) (algebraMap X.G.Kf Kc (X.G.P.ι b.1 ((X.G.P.σ b.1 ^ b.2.val) x))) (ordP (X.G.P.W b.1) p x) := by
  have hS := X.G.P.setting b.1
  have := hS.frac_alt
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hS.p_unif hx
  rw [ordP_eq hS.p_unif]
  refine ⟨_, tw_int X Kc Oc hO b u, ?_, ?_⟩
  · have e : (algebraMap (X.G.P.W b.1) (X.G.P.Qq b.1) (u : X.G.P.W b.1))⁻¹ =
        algebraMap (X.G.P.W b.1) (X.G.P.Qq b.1) ((u⁻¹ : (X.G.P.W b.1)ˣ) : X.G.P.W b.1) := by
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    rw [← map_inv₀, ← map_inv₀, ← map_inv₀, e]
    exact tw_int X Kc Oc hO b _
  · rw [map_mul, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_natCast, map_natCast, map_natCast]

theorem sim_mF (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc) (j : ℕ) (b : BX X)
    (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    Sim Oc (p : Kc) (algebraMap X.G.Kf Kc (mF X j b (g : Matrix _ _ (X.G.P.Qq b.1))).det)
      (ordP (X.G.P.W b.1) p (g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)).det) := by
  rw [mF_det]
  exact sim_tw X Kc Oc hO b ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit g)).ne_zero

end Blocks

end FrameUnitLemmas

open FrameUnitLemmas in

theorem xUnit_of (hS : XShape) : XUnit := by
  intro p _ X Kc _ _ Oc hO hp j L L'' g g' hL hL'' i0 hi0
  have hr : ∀ v, i0 v ≤ X.G.P.m + 1 := fun v => by
    have h1 := hi0 v
    have h2 := (X.std v).two_r
    omega
  have hN : ∀ v, i0 v ≤ NJ X (j + 1) := fun v => by
    have h1 := hr v
    show i0 v ≤ X.G.P.m + 1 + (j + 1) * (X.t + 1)
    omega
  have hg : ∀ b : BX X, Sim Oc (p : Kc) (algebraMap X.G.Kf Kc (mF X j b (g b.1 : Matrix _ _ (X.G.P.Qq b.1))).det)
      (ordP (X.G.P.W b.1) p (g b.1 : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)).det) :=
    fun b => sim_mF X Kc Oc hO j b (g b.1)
  have hg' : ∀ b : BX X, Sim Oc (p : Kc)
      (algebraMap X.G.Kf Kc (mF X (j + 1) b (g' b.1 : Matrix _ _ (X.G.P.Qq b.1)) * DgX X X.G.Kf j i0 b.1).det)
      (ordP (X.G.P.W b.1) p
        (g' b.1 : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq b.1)).det + -(i0 b.1 : ℤ)) := by
    intro b
    rw [Matrix.det_mul, map_mul, det_DgX X X.G.Kf j i0 b.1 (hN b.1), map_zpow₀, map_natCast]
    exact (sim_mF X Kc Oc hO (j + 1) b (g' b.1)).mul hp (Sim.self_zpow _)
  have hU : Sim Oc (p : Kc) (numericalIdentityScalar X Kc j (fun v => g v) (fun v => g' v) i0)
      (∑ b : BX X, if IsOddPos b.2 then
        -(cX X j b : ℤ) * ordP (X.G.P.W b.1) p
            (g b.1 : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)).det +
          (cX X j b : ℤ) * (ordP (X.G.P.W b.1) p
            (g' b.1 : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq b.1)).det + -(i0 b.1 : ℤ))
        else (eX X j b : ℤ) * ordP (X.G.P.W b.1) p
            (g b.1 : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)).det +
          -((∑ k : Fin (cX X j b), min (X.colHt b.1 (j + 1) b.2 k.val) (i0 b.1) : ℕ) : ℤ)) := by
    unfold numericalIdentityScalar
    refine Sim.prod hp _ _ _ fun b _ => ?_
    split_ifs with h
    · exact ((hg b).zpow _).mul hp ((hg' b).pow _)
    · exact ((hg b).pow _).mul hp (Sim.self_zpow _)
  have h1 : Sim Oc (p : Kc) (algebraMap X.G.Kf Kc
      (∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))))
      (∑ v : X.Pl, Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v)) := by
    simp only [map_prod, map_zpow₀, map_natCast]
    exact Sim.prod hp _ _ _ fun v _ => Sim.self_zpow _
  have h2 : Sim Oc (p : Kc) (algebraMap X.G.Kf Kc (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j L)))
      (∑ v : X.Pl, X.vm v (j + 1) * len X v j L) := by
    simp only [map_prod, map_zpow₀, map_natCast]
    exact Sim.prod hp _ _ _ fun v _ => Sim.self_zpow _
  have h3 : Sim Oc (p : Kc) (algebraMap X.G.Kf Kc (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L'')))
      (∑ v : X.Pl, X.vm v (j + 1) * len X v (j + 1) L'') := by
    simp only [map_prod, map_zpow₀, map_natCast]
    exact Sim.prod hp _ _ _ fun v _ => Sim.self_zpow _
  have h4 : Sim Oc (p : Kc) (algebraMap X.G.Kf Kc (sX X j (fun v => g v)))
      (∑ b : BX X, -(eJ X j b.1 b.2) * ordP (X.G.P.W b.1) p
        (g b.1 : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)).det) := by
    unfold sX
    simp only [map_prod, map_zpow₀]
    exact Sim.prod hp _ _ _ fun b _ => (hg b).zpow _
  have h5 : Sim Oc (p : Kc) (algebraMap X.G.Kf Kc
      (∏ b : BX X, (mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2))))
      (∑ b : BX X, -(eJ X (j + 1) b.1 b.2) * (ordP (X.G.P.W b.1) p
        (g' b.1 : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq b.1)).det + -(i0 b.1 : ℤ))) := by
    simp only [map_prod, map_zpow₀]
    exact Sim.prod hp _ _ _ fun b _ => (hg' b).zpow _
  rw [map_mul, map_mul, map_mul, map_mul, map_inv₀, map_inv₀]
  refine Sim.mem (π := (p : Kc)) (Sim.congr
    (((((h1.mul hp (h2.mul hp h3.inv)).mul hp h4).mul hp h5.inv)).mul hp hU) ?_)
  simp only [Fintype.sum_sigma, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [len_eq X v j L (g v) (hL v), len_eq X v (j + 1) L'' (g' v) (hL'' v)]
  rw [Finset.sum_neg_distrib]
  refine place_arith (fun s : Fin (X.G.P.n' v) => IsOddPos s) (X.w v (j + 1)) (eJ X j v) (eJ X (j + 1) v)
    (fun s => (cX X j ⟨v, s⟩ : ℤ)) (fun s => (eX X j ⟨v, s⟩ : ℤ))
    (fun s => ((∑ k : Fin (cX X j ⟨v, s⟩), min (X.colHt v (j + 1) s k.val) (i0 v) : ℕ) : ℤ))
    (fun s => ∑ a ∈ Finset.Icc 1 (i0 v), lamI (X.G.P.lam0 v) s a) _ _ (i0 v : ℤ) ?_ ?_
  · intro s hs
    obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := hS p X j ⟨v, s⟩
    exact ⟨(h9 hs).1, (h9 hs).2, boxes X hS j ⟨v, s⟩ (i0 v) (hr v)⟩
  · intro s hs
    obtain ⟨_, _, _, _, _, _, _, _, _, h10⟩ := hS p X j ⟨v, s⟩
    exact h10 hs

end Formalism.L2.PairingIndexBounds.Ent
