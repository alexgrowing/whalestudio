import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PairingRankOneMemInverseDifferent
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNatSmulMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_nat_eq_mul {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c : 𝓞 K, (m : 𝓞 K) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
    omega
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

theorem exists_nat_mul_mem {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : K) * e ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) e
  obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul (b : 𝓞 K) (nonZeroDivisors.ne_zero b.2)
  refine ⟨m, hm, a * c, ?_⟩
  have h1 : (m : K) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K c := by
    rw [← map_mul, ← hc, map_natCast]
  simp only at h
  rw [map_mul, h1, ← h]
  ring

lemma uniform_nat {ι : Type*} [Fintype ι] (P : ι → ℕ → Prop) (hP : ∀ i k m, P i k → P i (m * k))
    (h : ∀ i, ∃ k, 0 < k ∧ P i k) : ∃ k, 0 < k ∧ ∀ i, P i k := by
  classical
  choose k hk hPk using h
  refine ⟨∏ i, k i, Finset.prod_pos fun i _ => hk i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP i _ _ (hPk i)

lemma exists_nat_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) (x : Fin n → D.host.E) :
    ∃ N : ℕ, 0 < N ∧ (N : D.host.E) • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_nat_smul_mem hΛ x

lemma exists_nat_smul_single {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) :
    ∃ m : ℕ, 0 < m ∧ ∀ j, (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ := by
  refine uniform_nat (fun j m => (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ) (fun j k m h => ?_)
    (fun j => exists_nat_smul_mem hΛ _)
  rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
  exact Λ.nsmul_mem h m

lemma exists_nat_denom {n : ℕ} (v : Fin n → D.host.E) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  uniform_nat (fun j c => (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (fun j k m h => by push_cast; rw [mul_assoc]; exact mul_mem (natCast_mem _ m) h)
    (fun j => by obtain ⟨m, hm, h⟩ := exists_nat_mul_mem (v j); exact ⟨m, hm, h⟩)

theorem lattice_projective {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) : Module.Projective (𝓞 D.host.E) Λ := by
  have : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.2 hΛ.fg
  have : Module.Flat (𝓞 D.host.E) Λ := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    rw [Submodule.mem_bot]
    rw [Submonoid.smul_def] at ha
    exact (smul_eq_zero.1 ha).resolve_left (nonZeroDivisors.coe_ne_zero a)
  have : Module.FinitePresentation (𝓞 D.host.E) Λ := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem hF_eq_dot (S : HSp D) (x y : Fin S.rank → D.host.E) :
    hF S x y = (fun a => star (x a)) ⬝ᵥ (S.gram *ᵥ y) := by
  simp only [hF, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hF_swap (S : HSp D) (x y : Fin S.rank → D.host.E) : hF S x y = star (hF S y x) := by
  unfold hF
  simp only [star_sum, star_mul', star_star, star_gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

def repV (S : HSp D) (w : Fin S.rank → D.host.E) : Fin S.rank → D.host.E :=
  fun k => star ((w ᵥ* S.gram⁻¹) k)

theorem hF_repV (S : HSp D) (w v : Fin S.rank → D.host.E) : hF S (repV S w) v = w ⬝ᵥ v := by
  have h1 : S.gram⁻¹ * S.gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Formalism.MainNotions.S.Inh.tie_gram_det_ne S))
  have h2 : (fun a => star (repV S w a)) = w ᵥ* S.gram⁻¹ := by
    funext a; simp [repV]
  rw [hF_eq_dot, h2, dotProduct_mulVec, vecMul_vecMul, h1, vecMul_one]

set_option maxHeartbeats 1600000 in

theorem selfDual_basis (S : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hS : IsSelfDualC S ΛS) :
    ∃ (N : ℕ) (g s' : Fin N → Fin S.rank → D.host.E), (∀ i, g i ∈ ΛS) ∧ (∀ i, s' i ∈ ΛS) ∧
      ∀ v : Fin S.rank → D.host.E, ∑ i, hF S (s' i) v • g i = v := by
  classical
  have := lattice_projective hS.1
  have : Module.Finite (𝓞 D.host.E) ΛS := Module.Finite.iff_fg.2 hS.1.fg
  obtain ⟨N, f, hf⟩ := Module.Finite.exists_fin' (𝓞 D.host.E) ΛS
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  let gg : Fin N → ΛS := fun i => f (fun j => if i = j then 1 else 0)
  have hrep : ∀ x : ΛS, ∑ i, σ x i • gg i = x := by
    intro x
    have h1 : f (σ x) = x := LinearMap.congr_fun hσ x
    have h2 : f (σ x) = ∑ i, σ x i • gg i := by
      conv_lhs => rw [pi_eq_sum_univ (σ x)]
      rw [map_sum]
      simp only [map_smul, gg]
    rw [← h2, h1]
  let A := algebraMap (𝓞 D.host.E) D.host.E
  obtain ⟨m, hm, hmS⟩ := exists_nat_smul_single hS.1
  have hm0 : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  let em : Fin S.rank → ΛS := fun j => ⟨(m : D.host.E) • (Pi.single j 1 : Fin S.rank → D.host.E), hmS j⟩
  let w : Fin N → Fin S.rank → D.host.E := fun i j => A (σ (em j) i) / m
  have hw : ∀ i j, A (σ (em j) i) = m * w i j := by
    intro i j; simp only [w]; field_simp

  have hagree : ∀ (x : ΛS) (i : Fin N), A (σ x i) = w i ⬝ᵥ (x : Fin S.rank → D.host.E) := by
    intro x i
    obtain ⟨c, hc, hcx⟩ := exists_nat_denom (x : Fin S.rank → D.host.E)
    have hcx' : ∀ j, ∃ y, A y = (c : D.host.E) * (x : Fin S.rank → D.host.E) j := fun j => RingHom.mem_range.1 (hcx j)
    choose o ho using hcx'
    have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
    have hx : ((c * m : ℕ) : 𝓞 D.host.E) • x = ∑ j, o j • em j := by
      apply Subtype.ext
      funext k
      simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, em]
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp only [Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def]
      have := ho k
      simp only [A] at this
      rw [map_natCast, this]
      push_cast; ring
    have h3 := congrArg (fun y => A (σ y i)) hx
    simp only [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_natCast] at h3
    apply mul_left_cancel₀ (mul_ne_zero hc0 hm0)
    rw [dotProduct, Finset.mul_sum]
    have e1 : ((c * m : ℕ) : D.host.E) = (c : D.host.E) * m := by push_cast; ring
    rw [e1] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ho j, hw i j]; ring

  have hcol : ∀ j, ∑ i, w i j • (gg i : Fin S.rank → D.host.E) = Pi.single j 1 := by
    intro j
    have h := congrArg (fun y : ΛS => (y : Fin S.rank → D.host.E)) (hrep (em j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    have h' : ∑ i, A (σ (em j) i) • (gg i : Fin S.rank → D.host.E) = (m : D.host.E) • Pi.single j 1 :=
      (Finset.sum_congr rfl fun i _ => algebraMap_smul D.host.E _ _).trans h
    simp only [hw, mul_smul, ← Finset.smul_sum] at h'
    exact smul_right_injective _ hm0 h'
  refine ⟨N, fun i => (gg i : Fin S.rank → D.host.E), fun i => repV S (w i), fun i => (gg i).2, fun i => ?_, fun v => ?_⟩
  · refine (hS.2 (repV S (w i))).2 fun x hx => ⟨starO (σ ⟨x, hx⟩ i), ?_⟩
    rw [coe_starO]
    show star (A (σ ⟨x, hx⟩ i)) = hF S x (repV S (w i))
    rw [hF_swap, hF_repV, hagree]
  · simp only [hF_repV, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, (w i j * v j) • (gg i : Fin S.rank → D.host.E)
        = ∑ j, v j • ∑ i, w i j • (gg i : Fin S.rank → D.host.E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, mul_comm]
      _ = ∑ j, v j • (Pi.single j 1 : Fin S.rank → D.host.E) := by simp only [hcol]
      _ = v := by
          funext k
          simp [Finset.sum_apply, Pi.single_apply]

end Formalism.IndefR.Fin.PDA

end
