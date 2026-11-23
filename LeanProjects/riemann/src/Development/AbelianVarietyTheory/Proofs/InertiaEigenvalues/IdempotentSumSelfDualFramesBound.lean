import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.HalfAdjLattice

open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas.Lat

theorem sum_rank_one {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) {m n N : ℕ}
    (Gs Gi : Matrix (Fin n) (Fin n) R) (Gt : Matrix (Fin m) (Fin m) R)
    (hGi : (Gi.map σ)ᵀ = Gi) (hGt : (Gt.map σ)ᵀ = Gt) (h : Gi * Gs = 1) (M : Matrix (Fin m) (Fin n) R)
    (g s : Fin N → Fin m → R) (hb : ∑ k, vecMulVec (g k) (vecMul (fun a => σ (s k a)) Gt) = 1)
    (z w : R) (hM : (w * σ z) • M = M) :
    ∑ k, w • vecMulVec (g k) (vecMul (fun a => σ ((z • ((Gi * (M.map σ)ᵀ * Gt) *ᵥ s k)) a)) Gs) = M := by
  have hMM : ((M.map σ)ᵀ.map σ)ᵀ = M := by ext i j; simp [hσ]
  have hA : ((Gi * (M.map σ)ᵀ * Gt).map σ)ᵀ * Gs = Gt * M := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hGi, hGt, hMM,
      Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_one]
  have h1 : ∀ k, (fun a => σ ((z • ((Gi * (M.map σ)ᵀ * Gt) *ᵥ s k)) a)) =
      σ z • vecMul (fun a => σ (s k a)) ((Gi * (M.map σ)ᵀ * Gt).map σ)ᵀ := by
    intro k
    ext a
    generalize Gi * (M.map σ)ᵀ * Gt = A
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mulVec, vecMul, dotProduct, map_sum, transpose_apply, map_apply]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : ∀ k, w • vecMulVec (g k) (vecMul (fun a => σ ((z • ((Gi * (M.map σ)ᵀ * Gt) *ᵥ s k)) a)) Gs) =
      (w * σ z) • (vecMulVec (g k) (vecMul (fun a => σ (s k a)) Gt) * M) := by
    intro k
    rw [h1, smul_vecMul, vecMul_vecMul, hA, ← vecMul_vecMul, vecMulVec_mul]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun k _ => h2 k, ← Finset.smul_sum, ← Matrix.sum_mul, hb, Matrix.one_mul, hM]

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
    ∃ N : ℕ, 0 < N ∧ (N : D.host.E) • x ∈ Λ := by
  have hnat : ∀ (m : ℕ) {y : Fin n → D.host.E}, y ∈ Λ → (m : D.host.E) • y ∈ Λ := fun m y hy => by
    rw [Nat.cast_smul_eq_nsmul]; exact Λ.nsmul_mem hy m
  have hx : x ∈ Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) := by
    rw [hΛ.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N₁, hN₁, h₁⟩ := hy
    obtain ⟨N₂, hN₂, h₂⟩ := hz
    refine ⟨N₁ * N₂, Nat.mul_pos hN₁ hN₂, ?_⟩
    have : ((N₁ * N₂ : ℕ) : D.host.E) • (y + z) = (N₂ : D.host.E) • ((N₁ : D.host.E) • y) +
        (N₁ : D.host.E) • ((N₂ : D.host.E) • z) := by
      rw [smul_add, smul_smul, smul_smul]; push_cast; ring_nf
    rw [this]
    exact Λ.add_mem (hnat _ h₁) (hnat _ h₂)
  | smul c y _ hy =>
    obtain ⟨N, hN, h⟩ := hy
    obtain ⟨M, hM, o, ho⟩ := exists_nat_mul_mem c
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : D.host.E) • (c • y) = (o : 𝓞 D.host.E) • ((N : D.host.E) • y) := by
      rw [← algebraMap_smul D.host.E o, ho, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    rw [this]
    exact Λ.smul_mem _ h

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

theorem gram_conj (V : HSp D) : V.gramᴴ = V.gram := Matrix.ext fun i j => V.herm.eq _ _

theorem form_swap (S : HSp D) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star ((fun a => star (y a)) ⬝ᵥ (S.gram *ᵥ x)) := by
  have hg : ∀ k b, star (S.gram k b) = S.gram b k := fun k b => congrFun (congrFun (gram_conj S) b) k
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, hg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem form_rep (S : HSp D) (w v : Fin S.rank → D.host.E) :
    (fun a => star (star ((w ᵥ* S.gram⁻¹) a))) ⬝ᵥ (S.gram *ᵥ v) = w ⬝ᵥ v := by
  have h1 : S.gram⁻¹ * S.gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne S))
  have h2 : (fun a => star (star ((w ᵥ* S.gram⁻¹) a))) = w ᵥ* S.gram⁻¹ := by
    funext a; rw [star_star]
  rw [h2, dotProduct_mulVec, vecMul_vecMul, h1, vecMul_one]

theorem halfDifferent_ne_bot : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h] at h1
  simp only [Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

set_option maxHeartbeats 1600000 in

theorem exists_dual_families (S : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hS : IsSelfDualC S ΛS) :
    ∃ (N : ℕ) (g s' : Fin N → Fin S.rank → D.host.E), (∀ i, g i ∈ ΛS) ∧ (∀ i, s' i ∈ ΛS) ∧
      ∀ v : Fin S.rank → D.host.E, ∑ i, ((fun a => star (s' i a)) ⬝ᵥ (S.gram *ᵥ v)) • g i = v := by
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
  refine ⟨N, fun i => (gg i : Fin S.rank → D.host.E), fun i => (fun k => star ((w i ᵥ* S.gram⁻¹) k)), fun i => (gg i).2, fun i => ?_, fun v => ?_⟩
  · refine (hS.2 ((fun k => star ((w i ᵥ* S.gram⁻¹) k)))).2 fun x hx => ⟨⟨star (σ ⟨x, hx⟩ i : D.host.E), isIntegral_star' _⟩, ?_⟩
    show star (A (σ ⟨x, hx⟩ i)) = _
    rw [form_swap, form_rep, hagree]
  · simp only [form_rep]
    simp only [dotProduct, Finset.sum_smul]
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

theorem toEAf_int {x : AE D} (hx : finPart D x ∈ intAE D) : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  show Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D x) ∈ _
  generalize finPart D x = y at hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, o, rfl⟩ := hy
    have h : ((o : D.host.E) ⊗ₜ[D.host.F] a : EAf D) =
        ((o : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.comm_tmul, h]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨o, ⟨o, rfl⟩⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem natCast_mem_AA (k : ℕ) : ((k * Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
  rw [map_natCast] at h1
  have h2 : ((k * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h1
  have h3 : ((k * Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈
      (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, h2, map_natCast _ _⟩
  have hb : (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 halfDifferent_ne_bot
  have h4 : (1 : D.host.E) ∈ D.host.AA0 := by
    unfold Formalism.BasicNotions.Host.AA0
    rw [FractionalIdeal.mem_inv_iff hb]
    intro y hy
    rw [one_mul]
    exact FractionalIdeal.coeIdeal_le_one hy
  have h5 := FractionalIdeal.mul_mem_mul h3 h4
  rwa [mul_one] at h5

theorem idem_div_int {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ}
    (hn : ∀ PP ∈ P, (n : 𝓞 D.host.E) ∉ PP.asIdeal) : finPart D (e * incA D (n : D.host.E)⁻¹) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul, map_sum]
  refine AddSubgroup.sum_mem _ fun PP hPP => ?_
  have h0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hn PP hPP (h ▸ zero_mem _)
  have h1 := (hes PP hPP).2 n h0
  by_contra hc
  exact hn PP hPP (h1.2 hc)

theorem natCast_mul_idem_div {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ}
    (hn : ∀ PP ∈ P, (n : 𝓞 D.host.E) ∉ PP.asIdeal) : incA D (n : D.host.E) * (e * incA D (n : D.host.E)⁻¹) = e := by
  by_cases h0 : n = 0
  · obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    have hP : P = ∅ := Finset.eq_empty_of_forall_notMem fun PP hPP => hn PP hPP (by rw [h0]; simp)
    simp [hP]
  · rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 h0), map_one, mul_one]

theorem gram_map_conj (V : HSp D) : ((V.gram.map (eToEAf D)).map (sR D))ᵀ = V.gram.map (eToEAf D) := by
  ext i j
  simp only [transpose_apply, map_apply, sR_eTo]
  exact congrArg _ (congrFun (congrFun (gram_conj V) i) j)

theorem gramInv_map_conj (V : HSp D) : ((V.gram⁻¹.map (eToEAf D)).map (sR D))ᵀ = V.gram⁻¹.map (eToEAf D) := by
  have h : (V.gram⁻¹)ᴴ = V.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_conj]
  ext i j
  simp only [transpose_apply, map_apply, sR_eTo]
  exact congrArg _ (congrFun (congrFun h i) j)

theorem sR_sR (x : EAf D) : sR D (sR D x) = x := by
  rw [← toEAf_liftE x, ← toEAf_cA, ← toEAf_cA, cA_cA]

theorem mulVec_mem_hatL {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin m) (EAf D)} {β' : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') {A : Matrix (Fin m) (Fin n) (EAf D)}
    (hA : IsIntM ((β⁻¹).val * A * β'.val)) {v : Fin n → EAf D} (hv : v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ') :
    A *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [hβ]
  have hv' := (hβ' v).1 hv
  have e : (β⁻¹).val *ᵥ (A *ᵥ v) = ((β⁻¹).val * A * β'.val) *ᵥ ((β'⁻¹).val *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β'.val, Units.mul_inv, Matrix.mul_one]
  intro i
  rw [e]
  generalize (β⁻¹).val * A * β'.val = B at hA
  simp only [Matrix.mulVec, dotProduct] at hv' ⊢
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hv' k)

theorem mem_latO_of_adj_int : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ t : WO S T, IsHalf (cA D e) t → IsIntM (frMapAdj S T βS βT t) → t ∈ latO S T ΛS ΛT (fun _ => True) := by
  intro D S T ΛS ΛT βS βT _ hT hβS hβT P e he hP t ht hN
  have ha := natCast_mem_AA (D := D) (D.host.QS * D.host.q)
  generalize D.host.QS * D.host.q * Ideal.absNorm D.host.ccK = n at hP ha
  obtain ⟨N, g, s, hg, hs, hb⟩ := exists_dual_families T hT
  have hz := toEAf_int (idem_div_int he hP)
  have hze := natCast_mul_idem_div he hP
  generalize e * incA D (n : D.host.E)⁻¹ = z at hz hze
  set M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.map t (toEAf D) with hMdef
  have hA : (adjO S T t).map (toEAf D) =
      S.gram⁻¹.map (eToEAf D) * (M.map (sR D))ᵀ * T.gram.map (eToEAf D) := by
    unfold adjO
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    congr 1
    ext i j
    simp only [hMdef, map_apply, transpose_apply, toEAf_cA]
  have hN' : IsIntM ((βS⁻¹).val * (S.gram⁻¹.map (eToEAf D) * (M.map (sR D))ᵀ * T.gram.map (eToEAf D)) * βT.val) := by
    rw [← hA]; exact hN
  have hb' : ∑ k, vecMulVec (fun i => eToEAf D (g k i))
      (vecMul (fun a => sR D (eToEAf D (s k a))) (T.gram.map (eToEAf D))) = 1 := by
    ext i j
    have h1 := congrArg (eToEAf D) (congrFun (hb (Pi.single j 1)) i)
    rw [Finset.sum_apply, map_sum] at h1
    rw [Matrix.sum_apply]
    have h2 : eToEAf D ((Pi.single j 1 : Fin T.rank → D.host.E) i) = (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← h2, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_single_one]
    simp only [vecMulVec_apply, vecMul, dotProduct, map_apply, sR_eTo, Pi.smul_apply, smul_eq_mul, map_mul, map_sum,
      Matrix.col, transpose_apply]
    exact mul_comm _ _
  have hM : ((eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * sR D (toEAf D z)) • M = M := by
    have h1 : (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * sR D (toEAf D z) =
        toEAf D (cA D e) := by
      rw [← hze, ← Algebra.TensorProduct.one_def, mul_one, map_natCast, map_natCast, map_mul, map_natCast, map_mul,
        map_natCast, toEAf_cA]
    rw [h1]
    ext i j
    simp only [hMdef, Matrix.smul_apply, map_apply, smul_eq_mul]
    rw [← map_mul, ht i j]
  have hGi : S.gram⁻¹.map (eToEAf D) * S.gram.map (eToEAf D) = 1 := by
    have h := congrArg (fun X => Matrix.map X (toEAf D)) (gramInv_mul S)
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have key := sum_rank_one (sR D) sR_sR _ _ _ (gramInv_map_conj S) (gram_map_conj T) hGi M
    (fun k i => eToEAf D (g k i)) (fun k a => eToEAf D (s k a)) hb' _ _ hM
  have hdec : t = ∑ k, genE (S := S) (T := T)
      (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) (fun i => eToEAf D (g k i))
      (toEAf D z • ((S.gram⁻¹.map (eToEAf D) * (M.map (sR D))ᵀ * T.gram.map (eToEAf D)) *ᵥ fun a => eToEAf D (s k a))) := by
    ext i j
    have h1 := congrFun (congrFun key i) j
    rw [Matrix.sum_apply] at h1
    rw [Matrix.sum_apply]
    unfold genE
    simp only [map_apply]
    rw [← liftE_sum, h1]
    have h0 : infPart D (t i j) = 0 := by rw [← ht i j, map_mul, infPart_cA_idemSum he, zero_mul]
    refine (eq_lift_of_infPart _ h0).trans ?_
    unfold liftE
    congr 1
    exact ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply _).symm
  rw [hdec]
  refine AddSubgroup.sum_mem _ fun k _ => genE_mem ?_ ha (mem_hatL_of_mem (hg k)) ?_
  · intro v; rw [map_one]; exact one_mem _
  · exact Submodule.smul_mem _ (⟨_, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
      (mulVec_mem_hatL hβS hβT hN' (mem_hatL_of_mem (hs k)))

end GlobalTheory.HalfAdjLattice

end
