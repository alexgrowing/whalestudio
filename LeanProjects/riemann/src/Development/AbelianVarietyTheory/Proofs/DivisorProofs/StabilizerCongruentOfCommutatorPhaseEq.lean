import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PtHomInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDualStatement
open scoped Pointwise nonZeroDivisors
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.PhaseCong

variable {D : D7}

def skewCoef (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {e | ∀ b ∈ D.host.𝔟, ∀ c ∈ D.host.conj • 𝔪, ∃ m ∈ 𝔪,
    algebraMap (𝓞 D.host.E) D.host.E m = e * algebraMap (𝓞 D.host.E) D.host.E b * algebraMap (𝓞 D.host.E) D.host.E c}
  zero_mem' := fun _ _ _ _ => ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro e f he hf b hb c hc
    obtain ⟨m, hm, h1⟩ := he b hb c hc
    obtain ⟨n, hn, h2⟩ := hf b hb c hc
    exact ⟨m + n, add_mem hm hn, by rw [map_add, h1, h2]; ring⟩
  smul_mem' := by
    rintro s e he b hb c hc
    obtain ⟨m, hm, h1⟩ := he b hb c hc
    exact ⟨s * m, Ideal.mul_mem_left _ _ hm, by rw [map_mul, h1, Algebra.smul_def]; ring⟩

theorem b_ne_zero (D : D7) :
    ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
    have h3 := D.host.𝔟_spec.2
    simp [h] at h3

theorem entries_of_homL {𝔪 : Ideal (𝓞 D.host.E)} {a d : ℕ} {A : Matrix (Fin d) (Fin a) D.host.E}
    (hA : A ∈ homL D (stdL D a) (skewLat D 𝔪 d)) (i : Fin d) (j : Fin a) :
    A i j ∈ ((((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    have hs : (Pi.single j 1 : Fin a → D.host.E) ∈ stdL D a := by
      simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
      intro k
      rw [Pi.single_apply]
      split_ifs
      exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]
    have := hA _ hs
    simp only [skewLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff] at this
    simpa using this i
  | zero => exact Submodule.zero_mem _
  | add A B _ _ hA hB => exact Submodule.add_mem _ hA hB
  | smul c A _ hA => exact Submodule.smul_mem _ c hA

theorem entries_of_YYl {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {A : Matrix (Fin d) (Fin a) D.host.E}
    (hA : A ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) (i : Fin d) (j : Fin a) : A i j ∈ skewCoef D 𝔪 := by
  have hne : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => h𝔪 (by
      have h' := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
      simpa using h')
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hB
    intro b hb c hc
    have h1 : t * algebraMap (𝓞 D.host.E) D.host.E b ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      (FractionalIdeal.mem_inv_iff (b_ne_zero D)).1 ht _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩)
    have h2 : A i j * algebraMap (𝓞 D.host.E) D.host.E c ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      (FractionalIdeal.mem_div_iff_of_ne_zero hne).1 (entries_of_homL hA i j) _
        ((FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩)
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    obtain ⟨m, hm, hm'⟩ := (FractionalIdeal.mem_coeIdeal _).1 h2
    refine ⟨o * m, Ideal.mul_mem_left _ _ hm, ?_⟩
    rw [map_mul, ho, hm', Matrix.smul_apply, smul_eq_mul]
    ring
  | zero => exact (skewCoef D 𝔪).zero_mem
  | add A B _ _ hA hB => exact (skewCoef D 𝔪).add_mem hA hB
  | smul c A _ hA =>
    rw [Matrix.smul_apply]
    exact (skewCoef D 𝔪).smul_mem c hA

theorem entries_of_mem {δ : ℂ} (hc : Crv D ⊤ δ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ}
    (z : Matrix (Fin d) (Fin a) D.host.E)
    (hz : pt D (tor0 D ⊤ δ) δ z ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) (i : Fin d) (j : Fin a) :
    z i j ∈ skewCoef D 𝔪 := by
  let S : AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) :=
    { carrier := {z | ∀ i j, z i j ∈ skewCoef D 𝔪}
      zero_mem' := fun _ _ => (skewCoef D 𝔪).zero_mem
      add_mem' := fun ha hb i j => (skewCoef D 𝔪).add_mem (ha i j) (hb i j)
      neg_mem' := fun ha i j => (skewCoef D 𝔪).neg_mem (ha i j) }
  have hle : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ≤ S.map (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
    have hint : IsIntegral ℤ ((c : D.host.K) : D.host.E) :=
      (RingOfIntegers.isIntegral_coe c).algebraMap (B := D.host.E)
    have := (skewCoef D 𝔪).smul_mem (⟨_, hint⟩ : 𝓞 D.host.E) (entries_of_YYl h𝔪 hA i j)
    rw [Matrix.smul_apply, smul_eq_mul]
    exact this
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hc).2.1
  obtain ⟨z', hz', e⟩ := hle hz
  have : z' = z := GlobalTheory.ThetaLatticePoints.ptHom_injective D ⊤ hδ a d e
  exact this ▸ hz' i j

theorem mem_of_int {𝔪 : Ideal (𝓞 D.host.E)} (h1 : IsCoprime 𝔪 (D.host.conj • 𝔪)) (h2 : IsCoprime 𝔪 D.host.𝔟)
    {e : D.host.E} (he : e ∈ skewCoef D 𝔪) (hi : IsIntegral ℤ e) :
    ∃ m ∈ 𝔪, algebraMap (𝓞 D.host.E) D.host.E m = e := by
  obtain ⟨μ, hμ, β, hβ, hμβ⟩ := Ideal.isCoprime_iff_exists.1 h2
  obtain ⟨μ', hμ', ν, hν, hμν⟩ := Ideal.isCoprime_iff_exists.1 h1
  obtain ⟨m, hm, hme⟩ := he β hβ ν hν
  let o : 𝓞 D.host.E := ⟨e, hi⟩
  have ho : algebraMap (𝓞 D.host.E) D.host.E o = e := rfl
  refine ⟨o * μ + o * β * μ' + m, add_mem (add_mem (Ideal.mul_mem_left _ _ hμ) (Ideal.mul_mem_left _ _ hμ')) hm, ?_⟩
  have ea : algebraMap (𝓞 D.host.E) D.host.E μ + algebraMap (𝓞 D.host.E) D.host.E β = 1 := by
    rw [← map_add, hμβ, map_one]
  have eb : algebraMap (𝓞 D.host.E) D.host.E μ' + algebraMap (𝓞 D.host.E) D.host.E ν = 1 := by
    rw [← map_add, hμν, map_one]
  rw [map_add, map_add, hme, map_mul, map_mul, map_mul, ho]
  linear_combination e * ea + e * algebraMap (𝓞 D.host.E) D.host.E β * eb

theorem im_int_of_kap_eq (T : Tor D) {N N' : ℕ} (u u' y : VC D N N')
    (h : Formalism.MainNotions.TaylorLogMetric.kap D T u y = Formalism.MainNotions.TaylorLogMetric.kap D T u' y) : ∃ m : ℤ, (Hf D T (u - u') y).im = m := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨-n, ?_⟩
  have e : Hf D T u y = Hf D T (u - u') y + Hf D T u' y := by rw [← VacMove.hf_add_left, sub_add_cancel]
  have e2 : (Hf D T u y).im = (Hf D T (u - u') y).im + (Hf D T u' y).im := by rw [e, Complex.add_im]
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h3 : ((Hf D T u y).im : ℂ) = (Hf D T u' y).im - n := by
    apply mul_left_cancel₀ hpi
    linear_combination -hn
  have h4 : (Hf D T u y).im = (Hf D T u' y).im - n := by exact_mod_cast h3
  push_cast
  linarith

end GlobalTheory.FunObj.StdDatum.PhaseCong

namespace GlobalTheory.FunObj.StdDatum.PhaseCong

variable {D : D7}

theorem alg1 {G : Type*} [AddCommGroup G] (p q u v : G) : p - q = (v - q) - (u - p) + (u - v) := by abel

theorem alg2 {G : Type*} [AddCommGroup G] (s t w : G) : w = s - t + w - s + t := by abel

theorem mem_OhE_of_hatId {𝔪 : Ideal (𝓞 D.host.E)} {y : AE D} (hy : y ∈ hatId D 𝔪) : y ∈ OhE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, -, s, hs, rfl⟩ := hy
    exact mul_mem ((GlobalTheory.HeckeVal.inc_mem_iff D _).2 (RingOfIntegers.isIntegral_coe b)) hs
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | neg _ _ h => exact neg_mem h

theorem hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

set_option maxHeartbeats 2000000 in

theorem cong_of_kap_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → ∀ {a d : ℕ}, a ≤ d → ∀ (r r' : GA D a), r ∈ intG D a → r' ∈ intG D a → ∀ x x' : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) → pt D (tor0 D ⊤ δ) δ x' ∈ (La0 D (tor0 D ⊤ δ) a d) → (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) → (∀ i j, (x'.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r'⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) → (∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) y = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x') y) → CongOne D 𝔪 (r⁻¹ * r') := by
  intro D δ hc 𝔪 h𝔪 hcop hb a d had r r' hr hr' x x' _ _ hx hx' hk
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D a), GlobalTheory.T.selfDualSkewIdealLattice_isSelfDual D 𝔪 d h𝔪, rfl⟩
  have hpt : pt D (tor0 D ⊤ δ) δ (x - x') = pt D (tor0 D ⊤ δ) δ x - pt D (tor0 D ⊤ δ) δ x' :=
    map_sub (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d) x x'
  have hmem : pt D (tor0 D ⊤ δ) δ (x - x') ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
    refine (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D h1 ⊤ δ hc a d _ kp).2.2.2.1 _ fun y hy => ?_
    rw [hpt]
    exact im_int_of_kap_eq _ _ _ y (hk y hy)
  have hz := entries_of_mem hc h𝔪 (x - x') hmem
  set B := (unitBlock D 0 a d).map (inc D) with hB
  set R := (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hRdef
  set R' := (((r'⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hR'def
  set P' := (((r' : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hP'def
  have hri := (mem_intG r).1 hr
  have hri' := (mem_intG r').1 hr'
  have hR : ∀ i j, R i j ∈ OhE D := fun i j => (hri i j).2
  have hR' : ∀ i j, R' i j ∈ OhE D := fun i j => (hri' i j).2
  have hP' : ∀ i j, P' i j ∈ OhE D := fun i j => (hri' i j).1
  have hBi : ∀ i k, B i k ∈ OhE D := fun i k => by
    simp only [hB, Matrix.map_apply, unitBlock, Matrix.of_apply]
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _

  have hrow : ∀ (i : Fin d) (j : Fin a), (B * (R - R')) i j ∈ hatId D 𝔪 := by
    intro i j
    have e : (B * (R - R')) i j = (x'.map (inc D) - B * R') i j - (x.map (inc D) - B * R) i j + inc D ((x - x') i j) := by
      simp only [Matrix.mul_sub, Matrix.sub_apply, Matrix.map_apply, map_sub]
      exact alg1 _ _ _ _
    have hint : (B * (R - R')) i j ∈ OhE D := by
      rw [Matrix.mul_apply]
      exact sum_mem fun k _ => mul_mem (hBi i k) (by rw [Matrix.sub_apply]; exact sub_mem (hR k j) (hR' k j))
    have hzi : inc D ((x - x') i j) ∈ OhE D := by
      have : inc D ((x - x') i j) = (B * (R - R')) i j - (x'.map (inc D) - B * R') i j + (x.map (inc D) - B * R) i j := by
        rw [e]; exact alg2 _ _ _
      rw [this]
      exact add_mem (sub_mem hint (mem_OhE_of_hatId (hx' i j))) (mem_OhE_of_hatId (hx i j))
    obtain ⟨m, hm, hme⟩ := mem_of_int hcop hb (hz i j) ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 hzi)
    have hzm : inc D ((x - x') i j) ∈ hatId D 𝔪 :=
      AddSubgroup.subset_closure ⟨m, hm, 1, one_mem _, by rw [mul_one, ← hme]⟩
    rw [e]
    exact add_mem (sub_mem (hx' i j) (hx i j)) hzm

  have hdiff : ∀ i j : Fin a, (R - R') i j ∈ hatId D 𝔪 := by
    intro i j
    have e : (B * (R - R')) ⟨i.1, lt_of_lt_of_le i.2 had⟩ j = (R - R') i j := by
      simp only [hB, Matrix.mul_apply, Matrix.map_apply, unitBlock, Matrix.of_apply, zero_add]
      simp [apply_ite (inc D), Fin.val_inj]
    rw [← e]
    exact hrow _ j
  have e1 : R' * P' = 1 := by
    simp only [hR'def, hP'def, Subgroup.coe_inv]
    exact Units.inv_mul _
  intro i j
  have e2 : (((r⁻¹ * r' : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) - 1 = (R - R') * P' := by
    rw [Matrix.sub_mul, e1]
    rfl
  rw [e2, Matrix.mul_apply]
  exact sum_mem fun k _ => by rw [mul_comm]; exact hatId_mul (hP' k j) (hdiff i k)

end GlobalTheory.FunObj.StdDatum.PhaseCong

end
