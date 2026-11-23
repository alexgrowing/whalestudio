import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamondStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondActionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCongStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct
open UpperTheory.V.Z.Kato.Joint

namespace UpperTheory.V.Z.Kato.Joint.ThetaOperator

variable {l : ℕ} [Fact l.Prime]

private theorem cg_trans {n : ℕ} {x y z : Qbar l} (h1 : Cg n x y) (h2 : Cg n y z) : Cg n x z := by
  unfold Cg at *
  have e : x - z = (x - y) + (y - z) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

private theorem cg_symm {n : ℕ} {x y : Qbar l} (h1 : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cg_lin {n : ℕ} {x y : Qbar l} (a c : Qbar l) (hc : ‖c‖ ≤ 1) (h1 : Cg n x y) :
    Cg n (a + c * x) (a + c * y) := by
  unfold Cg at *
  have e : a + c * x - (a + c * y) = c * (x - y) := by ring
  rw [e, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans h1

private theorem cg_j {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hj : ∀ x ∈ A, ‖j x‖ ≤ 1)
    {n : ℕ} {x y : Ω} (h : CgA A l n x y) : Cg n (j x) (j y) := by
  obtain ⟨z, hz, e⟩ := h
  unfold Cg
  rw [← map_sub, e, map_mul, map_pow, map_natCast, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hj z hz)

private theorem norm_appr_sub_le_norm_pow (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)‖ ≤ ‖((l : Qbar l)) ^ n‖ := by
  have e : ((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)
      = algebraMap ℚ_[l] (PadicAlgCl l) (((-(c - ((c.appr n : ℕ) : ℤ_[l])) : ℤ_[l]) : ℚ_[l])) := by
    simp
  have e2 : ((l : Qbar l)) ^ n = algebraMap ℚ_[l] (PadicAlgCl l) (((l : ℚ_[l])) ^ n) := by simp
  rw [e, e2, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends, PadicInt.padic_norm_e_of_padicInt, norm_neg]
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n c)
  refine h.trans (le_of_eq ?_)
  rw [Padic.norm_p_pow]

private theorem cg_appr (n : ℕ) (c : ℤ_[l]) (x : Qbar l) (hx : ‖x‖ ≤ 1) :
    Cg n (((c.appr n : ℕ) : Qbar l) * x) (((c : ℤ_[l]) : Qbar l) * x) := by
  unfold Cg
  rw [← sub_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_appr_sub_le_norm_pow n c) (norm_nonneg _)).trans
    (by rw [mul_comm]; exact mul_le_of_le_one_left (norm_nonneg _) hx)

private theorem appr_zero' (n : ℕ) : (0 : ℤ_[l]).appr n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [PadicInt.appr]; simp [ih]

private theorem diam_cg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (hS : Std A N w j) (n a : ℕ) (b : X.Fn l)
    (ha : a.Coprime N) (hb : InChi X N w χ b) (r : ℚ) :
    Cg n (j ((thN X A N l n 1 (X.diam N l a b)).coeff r))
      (((χ a : ℤ_[l]) : Qbar l) * j ((thN X A N l n 1 b).coeff r)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS
  obtain ⟨hbB, hdiam⟩ := hb
  have hB1 : X.diam N l 1 b ∈ X.B N l w := by
    rw [hdiam 1 (Nat.coprime_one_left N)]
    exact Submodule.smul_mem _ _ hbB
  have hBa : X.diam N l a b ∈ X.B N l w := by
    rw [hdiam a ha]
    exact Submodule.smul_mem _ _ hbB
  have hψ := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) b hbB).1
  have hθ := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) (X.diam N l a b) hBa).1
  have hD : ∀ s : ℚ, (thN X A N l n 1 b).coeff s ∈ A := by
    obtain ⟨f, -, -, -, hd⟩ := hψ
    exact hd.1
  have hlin := GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w (X.diam N l 1 b) (X.diam N l 1 b) hB1 hB1 (χ a) 0
    (thN X A N l n 1 b) (thN X A N l n 1 b) hψ hψ
  have e : X.act l (sgD N l 1) (X.diam N l a b) = χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b := by
    rw [zero_smul, add_zero, hdiam a ha, map_smul]
    rfl
  rw [e] at hθ
  have hmem : χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b ∈ X.B N l w :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hB1) (Submodule.smul_mem _ _ hB1)
  have hu := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w hw _ hmem _ _ hθ hlin r
  have h1 := cg_j hj hu
  rw [appr_zero'] at h1
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, Nat.cast_zero, zero_smul, add_zero,
    smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast] at h1
  exact cg_trans h1 (cg_appr n (χ a) _ (hj _ (hD r)))

end UpperTheory.V.Z.Kato.Joint.ThetaOperator

private theorem norm_natCast_pow_le_one {l : ℕ} [Fact l.Prime] (q k : ℕ) : ‖((q : Qbar l)) ^ k‖ ≤ 1 := by
  have e : ((q : Qbar l)) ^ k = algebraMap ℚ_[l] (PadicAlgCl l) (((q : ℤ) : ℚ_[l]) ^ k) := by simp
  rw [e, PadicAlgCl.norm_extends, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (Padic.norm_int_le_one _)

private theorem coeff_div_prime_eq_zero_of_not_dvd_of_isLat {Ω : Type} [Field Ω] (φ : HahnSeries ℚ Ω) (hL : IsLat 1 φ) {q i : ℕ}
    (hq : q.Prime) (hnd : ¬ q ∣ i) : φ.coeff ((i : ℚ) / q) = 0 := by
  by_contra h
  have hden := hL _ h
  rw [Nat.cast_one, one_mul] at hden
  have key : (((i : ℚ) / q).num : ℚ) = (i : ℚ) / q := Rat.coe_int_num_of_den_eq_one hden
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h2 : (i : ℚ) = q * ((i : ℚ) / q).num := by rw [key]; field_simp
  have h3 : (i : ℤ) = q * ((i : ℚ) / q).num := by exact_mod_cast h2
  exact hnd (Int.natCast_dvd_natCast.mp ⟨_, h3⟩)

open UpperTheory.V.Z.Kato.Joint.ThetaOperator in
theorem UpperTheory.V.Z.Kato.Joint.thOp :
    UpperTheory.V.Z.Kato.Joint.ThOp := by
  intro l _ Ω _ _ _ ε X A N w j χ hS n T b hT hb i
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hS' := hS
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS'
  have hψ : ∀ m, IsThB X A N l m (X.act l (sgD N l 1) b) (thN X A N l m 1 b) ∧ IsLat 1 (thN X A N l m 1 b) :=
    fun m => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl m w 1 hw (Nat.coprime_one_left N) b hb.1
  have hrel := GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw (Nat.coprime_one_left N) b hb.1
  cases T with
  | T q =>
    obtain ⟨hqp, hqNl⟩ := hT
    have hqN : q.Coprime N :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqNl)
    simp only [th, seqN, fop, Tower.op, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.EisM.To, GlobalTheory.EisM.Vo]
    have h1 := hrel.1 q hqp hqNl ((i : ℚ) / (1 : ℕ))
    rw [GlobalTheory.CyclotomicQExpansion.Api.hq_eq_uq_of_isAlgClosed hqp.pos (hψ n).2] at h1
    have h1' := cg_j hj h1
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, GlobalTheory.CyclotomicQExpansion.Api.coeff_uq hqp.pos,
      GlobalTheory.CyclotomicQExpansion.Api.coeff_vq hqp.pos, map_add, Nat.cast_one, div_one, Rat.den_natCast, if_true,
      one_mul, smul_eq_mul, nsmul_eq_mul, map_mul, map_pow, map_natCast] at h1'
    have hx : Cg n (j ((thN X A N l n q b).coeff ((i : ℚ) / q)))
        (((χ q : ℤ_[l]) : Qbar l) *
          (if q ∣ i then j ((thN X A N l n 1 b).coeff (((i / q : ℕ) : ℚ) / ((1 : ℕ) : ℚ))) else 0)) := by
      have ha := cg_j hj (hrel.2.2 q hqN ((i : ℚ) / q))
      have hc := cg_trans (cg_symm ha) (diam_cg X A N w j χ hS n q b hqN hb ((i : ℚ) / q))
      rw [one_mul] at hc
      split_ifs with hdiv
      · rwa [Nat.cast_one, div_one, Nat.cast_div hdiv (by exact_mod_cast hqp.ne_zero)]
      · rw [mul_zero]
        rwa [coeff_div_prime_eq_zero_of_not_dvd_of_isLat _ (hψ n).2 hqp hdiv, map_zero, mul_zero] at hc
    have key := cg_trans h1' (cg_lin _ _ (norm_natCast_pow_le_one q (w + 1)) hx)
    have hw2 : w + 2 - 1 = w + 1 := by omega
    simp only [Nat.cast_one, div_one, Nat.cast_mul, hw2]
    convert key using 2
    simp only [Nat.cast_one, div_one]
    ring
  | U =>
    show Cg n (j ((thN X A N l n 1 (X.heckeU l b)).coeff ((i : ℚ) / ((1 : ℕ) : ℚ))))
      (j ((thN X A N l n 1 b).coeff (((l * i : ℕ) : ℚ) / ((1 : ℕ) : ℚ))))
    have h2 := cg_j hj (hrel.2.1 ((i : ℚ) / (1 : ℕ)))
    simp only [GlobalTheory.CyclotomicQExpansion.Api.coeff_uq (Fact.out : l.Prime).pos, Nat.cast_one, div_one, Rat.den_natCast,
      if_true] at h2
    have h3 := cg_j hj (GlobalTheory.T.cgA_coeff_of_isThB_succ Ω ε X A N l hl2 hlN (by omega) hl n _ _ _ (hψ (n + 1)).1 (hψ n).1
      ((l : ℚ) * i))
    simp only [Nat.cast_one, div_one, Nat.cast_mul]
    exact cg_trans h2 h3
  | D d =>
    simp only [th, seqN, fop, Tower.op, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply,
      smul_eq_mul]
    exact diam_cg X A N w j χ hS n d b hT hb _

end
