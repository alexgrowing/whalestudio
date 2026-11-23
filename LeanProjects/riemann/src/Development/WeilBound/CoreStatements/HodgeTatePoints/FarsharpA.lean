import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm

noncomputable section

open TensorProduct Coalgebra WithConv GlobalTheory.GroupLikeDerivation

namespace PositivityTheory.HtPt.Farsharp

section Norm

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
  {O : Type} [CommRing O] [Algebra O C] (hO : ∀ o : O, ‖algebraMap O C o‖ ≤ 1)
  {M : Type} [AddCommGroup M] [Module O M]

include hO in

theorem norm_le_of_mem_span (f : M →ₗ[O] C) {s : Set M} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m ∈ s, ‖f m‖ ≤ r) {m : M} (hm : m ∈ Submodule.span O s) : ‖f m‖ ≤ r := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using hr
  | add x y _ _ hx hy =>
    rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul o x _ hx =>
    rw [map_smul, Algebra.smul_def, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hO o)).trans hx

include hO in

theorem bddAbove_norm [Module.Finite O M] (f : M →ₗ[O] C) :
    BddAbove (Set.range fun m => ‖f m‖) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine ⟨∑ m ∈ s, ‖f m‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  refine norm_le_of_mem_span hO f (s := s) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun m hm => Finset.single_le_sum (f := fun m => ‖f m‖) (fun _ _ => norm_nonneg _) hm) ?_
  rw [hs]; trivial

def supN (f : WithConv (M →ₗ[O] C)) : ℝ := ⨆ m, ‖f.ofConv m‖

include hO in

theorem le_supN [Module.Finite O M] (f : WithConv (M →ₗ[O] C)) (m : M) :
    ‖f.ofConv m‖ ≤ supN f := le_ciSup (bddAbove_norm hO f.ofConv) m

omit [IsUltrametricDist C] in

theorem supN_le {f : WithConv (M →ₗ[O] C)} {r : ℝ} (h : ∀ m, ‖f.ofConv m‖ ≤ r) :
    supN f ≤ r := ciSup_le h

omit [IsUltrametricDist C] in

theorem supN_nonneg (f : WithConv (M →ₗ[O] C)) : 0 ≤ supN f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

omit [IsUltrametricDist C] in

theorem supN_smul (c : C) (f : WithConv (M →ₗ[O] C)) :
    supN (c • f) = ‖c‖ * supN f := by
  rw [supN, supN, Real.mul_iSup_of_nonneg (norm_nonneg c)]
  congr 1
  ext m
  rw [← norm_mul]
  rfl

include hO in

theorem supN_add_le [Module.Finite O M] (f g : WithConv (M →ₗ[O] C)) :
    supN (f + g) ≤ max (supN f) (supN g) :=
  supN_le fun m => (IsUltrametricDist.norm_add_le_max (f.ofConv m) (g.ofConv m)).trans
    (max_le_max (le_supN hO f m) (le_supN hO g m))

include hO in

theorem supN_mul_le [Module.Finite O M] [Coalgebra O M]
    (f g : WithConv (M →ₗ[O] C)) : supN (f * g) ≤ supN f * supN g := by
  refine supN_le fun m => ?_
  have h := (Coalgebra.Repr.arbitrary O m).convMul_apply f g
  rw [h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (supN_nonneg _) (supN_nonneg _)) fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_supN hO f _) (le_supN hO g _) (norm_nonneg _) (supN_nonneg _)

theorem supN_le_of_tmul {f : WithConv (M ⊗[O] M →ₗ[O] C)} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ a b, ‖f.ofConv (a ⊗ₜ b)‖ ≤ r) : supN f ≤ r := by
  refine supN_le fun t => ?_
  induction t with
  | zero => simpa using hr
  | tmul a b => exact h a b
  | add x y hx hy =>
    rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

include hO in

theorem supN_eq_mul [Module.Finite O M] (f g : WithConv (M →ₗ[O] C))
    (h : WithConv (M ⊗[O] M →ₗ[O] C))
    (hh : ∀ a b, h.ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b) :
    supN h = supN f * supN g := by
  apply le_antisymm
  · refine supN_le_of_tmul (mul_nonneg (supN_nonneg _) (supN_nonneg _)) fun a b => ?_
    rw [hh, norm_mul]
    exact mul_le_mul (le_supN hO f _) (le_supN hO g _) (norm_nonneg _) (supN_nonneg _)
  · rw [supN.eq_1 f, Real.iSup_mul_of_nonneg (supN_nonneg g)]
    refine ciSup_le fun a => ?_
    rw [supN.eq_1 g, Real.mul_iSup_of_nonneg (norm_nonneg _)]
    refine ciSup_le fun b => ?_
    rw [← norm_mul, ← hh]
    exact le_supN hO h _

include hO in

theorem exists_supN_pow_le [Module.Finite O M] [Coalgebra O M]
    [IsCocomm O M] {y : WithConv (M →ₗ[O] C)} (hy : IsIntegral O y) :
    ∃ K : ℝ, ∀ k : ℕ, supN (y ^ k) ≤ K := by
  obtain ⟨s, hs⟩ := hy.fg_adjoin_singleton
  refine ⟨∑ f ∈ s, supN f, fun k => supN_le fun m => ?_⟩
  have hk : y ^ k ∈ Submodule.span O (s : Set (WithConv (M →ₗ[O] C))) := by
    rw [hs]
    exact pow_mem (Algebra.self_mem_adjoin_singleton _ y) k
  let ev : WithConv (M →ₗ[O] C) →ₗ[O] C :=
    { toFun := fun f => f.ofConv m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact norm_le_of_mem_span hO ev (Finset.sum_nonneg fun _ _ => supN_nonneg _)
    (fun f hf => (le_supN hO f m).trans
      (Finset.single_le_sum (f := fun f => supN f) (fun _ _ => supN_nonneg _) hf)) hk

end Norm

theorem dvd_mul_of_norm (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (O : Type) [CommRing O] [Algebra O C] (hinj : Function.Injective (algebraMap O C))
    (hO : ∀ x : C, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O C).range)
    (hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range)
    (A : Type) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (q : O) (hq : q ≠ 0) (D : A →ₗ[O] O)
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := O) a * D b -
      Coalgebra.counit (R := O) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem O u → q ∣ D u)
    (c : O) (hc : ‖algebraMap O C c‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) (a : A) :
    q ∣ c * D a := by
  have hO' : ∀ o : O, ‖algebraMap O C o‖ ≤ 1 := fun o => (hO _).2 ⟨o, rfl⟩
  have hq' : algebraMap O C q ≠ 0 := fun h => hq (hinj (by rw [h, map_zero]))
  have hdvd : ∀ x : O, q ∣ x ↔ ‖(algebraMap O C q)⁻¹ * algebraMap O C x‖ ≤ 1 := fun x => by
    constructor
    · rintro ⟨z, rfl⟩
      rw [map_mul, inv_mul_cancel_left₀ hq']
      exact hO' z
    · intro h
      obtain ⟨z, hz⟩ := (hO _).1 h
      refine ⟨z, hinj ?_⟩
      rw [map_mul, hz, mul_inv_cancel_left₀ hq']
  set y : WithConv (A →ₗ[O] C) := (algebraMap O C q)⁻¹ • extendHom O C A (toConv D) with hy
  have hya : ∀ a, y.ofConv a = (algebraMap O C q)⁻¹ * algebraMap O C (D a) := fun _ => rfl
  have : IsScalarTower O C (WithConv (A →ₗ[O] C)) := ⟨fun o x f =>
    WithConv.ext (LinearMap.ext fun a => smul_assoc o x (f.ofConv a))⟩
  have hint : IsIntegral O y :=
    GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul_of_closed (B₀ := GlobalTheory.CartierDual O A) hinj hcl
      (extendHom O C A) (toConv D) q hq fun χ => by
        obtain ⟨u, h1, h2⟩ := exists_isGroupLikeElem χ
        rw [← h2]
        exact hu u h1
  have key := GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers C p hp _ _ supN supN (mulHom O C A)
    (inlHom O C A) (inrHom O C A) supN_smul supN_smul supN_nonneg
    supN_nonneg (supN_add_le hO') (supN_mul_le hO')
    (fun f => supN_le fun t => le_supN hO' f _)
    (fun f g => supN_eq_mul hO' f g _ fun a b => by rw [inlHom_mul_inrHom, extProd_tmul])
    y (exists_supN_pow_le hO' hint)
    (supN_le_of_tmul zero_le_one fun a b => by
      have h := (hdvd _).1 (hD a b)
      convert h using 2
      change y.ofConv (a * b) - (extProd y 1).ofConv (a ⊗ₜ b) - (extProd 1 y).ofConv (a ⊗ₜ b) = _
      rw [extProd_tmul, extProd_tmul, hya, hya, hya, LinearMap.convOne_apply,
        LinearMap.convOne_apply]
      simp only [map_sub, map_mul]
      ring)
    (algebraMap O C c) hc
  rw [hdvd]
  have h : (algebraMap O C q)⁻¹ * algebraMap O C (c * D a) = (algebraMap O C c • y).ofConv a := by
    change _ = algebraMap O C c * y.ofConv a
    rw [hya, map_mul]
    ring
  rw [h]
  exact (le_supN hO' _ a).trans key

def powAbs {C : Type} [Field C] (v : Valuation C NNReal) (s : ℝ) (hs : 0 < s) : AbsoluteValue C ℝ where
  toFun x := ((v x : NNReal) : ℝ) ^ s
  map_mul' x y := by
    rw [map_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  nonneg' x := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero (NNReal.coe_nonneg _) hs.ne']
    simp
  add_le' x y := by
    rcases le_max_iff.1 (v.map_add x y) with h | h
    · exact (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (NNReal.coe_nonneg _) _))
    · exact (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (NNReal.coe_nonneg _) _))

theorem dvd_mul_of_val (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    (hp : v (p : C) < 1)
    (A : Type) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (q : O) (hq : q ≠ 0) (D : A →ₗ[O] O)
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := O) a * D b -
      Coalgebra.counit (R := O) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem O u → q ∣ D u)
    (c : O) (hc : v (algebraMap O C c) ^ (p - 1) ≤ v (p : C)) (a : A) :
    q ∣ c * D a := by
  have hpp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hp0 : (0 : ℝ) < ((v (p : C) : NNReal) : ℝ) := by
    have : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
    exact NNReal.coe_pos.2 ((Valuation.pos_iff v).2 this)
  have hlog : Real.log ((v (p : C) : NNReal) : ℝ) < 0 := Real.log_neg hp0 (by exact_mod_cast hp)
  let s : ℝ := Real.log p / (-Real.log ((v (p : C) : NNReal) : ℝ))
  have hs : 0 < s := div_pos (Real.log_pos hp1) (neg_pos.2 hlog)
  letI : NormedField C := (powAbs v s hs).toNormedField
  have hn : ∀ x : C, ‖x‖ = ((v x : NNReal) : ℝ) ^ s := fun _ => rfl
  have hpn : ‖(p : C)‖ = (p : ℝ)⁻¹ := by
    rw [hn, Real.rpow_def_of_pos hp0]
    have : Real.log ((v (p : C) : NNReal) : ℝ) * s = -Real.log p := by
      have := hlog.ne
      simp only [s]
      field_simp
    rw [this, Real.exp_neg, Real.exp_log (by linarith)]
  letI : NontriviallyNormedField C :=
    { non_trivial := ⟨(p : C)⁻¹, by rw [norm_inv, hpn, inv_inv]; exact hp1⟩ }
  haveI : IsUltrametricDist C := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    fun x y => by
      rw [hn, hn, hn]
      rcases le_max_iff.1 (v.map_add x y) with h | h
      · exact le_max_of_le_left
          (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le)
      · exact le_max_of_le_right
          (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le)
  refine dvd_mul_of_norm C p hpn O hv.hom_inj (fun x => ?_)
    (fun z hz => hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 hz)) A q hq D hD hu c ?_ a
  · rw [hn]
    constructor
    · intro h
      refine hv.exists_of_le_one ?_
      by_contra h1
      exact absurd h (not_le.2 (Real.one_lt_rpow (by exact_mod_cast not_le.1 h1) hs))
    · rintro ⟨o, rfl⟩
      exact Real.rpow_le_one (NNReal.coe_nonneg _) (by exact_mod_cast hv.map_le_one o) hs.le
  · have h1 : ‖algebraMap O C c‖ ^ (p - 1) ≤ (p : ℝ)⁻¹ := by
      rw [← hpn, ← norm_pow, hn, hn, map_pow]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 hc) hs.le
    have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h3 : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
    have h4 := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) h1 (one_div_pos.2 h2).le
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), h3, mul_one_div_cancel h2.ne',
      Real.rpow_one, Real.inv_rpow (by linarith), ← Real.rpow_neg (by linarith)] at h4
    exact h4

end PositivityTheory.HtPt.Farsharp
