import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

open Matrix GlobalTheory.SmoothForms

namespace GlobalTheory.LeviHC.RelCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A}

def blockOf {m o : Type} (N : Matrix (m × o) (m × o) ℂ) (i : o) : Matrix m m ℂ := Matrix.of fun I K => N (I, i) (K, i)

theorem blockOf_add {m o : Type} (N N' : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (N + N') i = blockOf N i + blockOf N' i := rfl

theorem blockOf_sub {m o : Type} (N N' : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (N - N') i = blockOf N i - blockOf N' i := rfl

theorem blockOf_smul {m o : Type} (c : ℂ) (N : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (c • N) i = c • blockOf N i := rfl

variable {m o : Type} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

theorem blockOf_blockDiagonal (P : o → Matrix m m ℂ) (i : o) : blockOf (blockDiagonal P) i = P i := by
  ext I K; simp [blockOf]

theorem blockOf_bd_mul (P : o → Matrix m m ℂ) (N : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (blockDiagonal P * N) i = P i * blockOf N i := by
  ext I K
  simp [blockOf, Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply]

theorem blockOf_mul_bd (P : o → Matrix m m ℂ) (N : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (N * blockDiagonal P) i = blockOf N i * P i := by
  ext I K
  simp [blockOf, Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply]

variable (X) in

def phi (d : ℕ) {k : ℕ} (b : Fin k → A) :
    Matrix ((Fin d → Fin n) × Fin k) ((Fin d → Fin n) × Fin k) ℂ →ₗ[ℂ] A where
  toFun N := ∑ i, wordMap X d (blockOf N i) * b i
  map_add' N N' := by simp [blockOf_add, add_mul, Finset.sum_add_distrib]
  map_smul' c N := by simp [blockOf_smul, Finset.smul_sum, smul_mul_assoc]

theorem phi_apply (d : ℕ) {k : ℕ} (b : Fin k → A) (N) : phi X d b N = ∑ i, wordMap X d (blockOf N i) * b i := rfl

theorem phi_comm (hX : Formalism.REAL.GlRel X) (d : ℕ) {k : ℕ} (b : Fin k → A) (hb : ∀ i a c, X a c * b i = b i * X a c)
    (N : Matrix ((Fin d → Fin n) × Fin k) ((Fin d → Fin n) × Fin k) ℂ) (a c : Fin n) :
    X a c * phi X d b N - phi X d b N * X a c =
      phi X d b (blockDiagonal (fun _ => polar n d a c) * N - N * blockDiagonal (fun _ => polar n d a c)) := by
  simp only [phi_apply, blockOf_sub, blockOf_bd_mul, blockOf_mul_bd, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n X hX, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_mul, mul_assoc, mul_assoc, ← hb, ← mul_assoc, ← mul_assoc]

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC.RelCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A}

theorem filtB_ad (hX : Formalism.REAL.GlRel X) {B : Subalgebra ℂ A} (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j) (d : ℕ)
    (a c : Fin n) {y : A} (hy : y ∈ filt X d * Subalgebra.toSubmodule B) :
    X a c * y - y * X a c ∈ filt X d * Subalgebra.toSubmodule B := by
  refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) fun x y hx hy => ?_
  · have e : X a c * (u * v) - u * v * X a c = (X a c * u - u * X a c) * v := by
      rw [sub_mul, mul_assoc u v, ← hB v hv, ← mul_assoc, ← mul_assoc]
    rw [e]
    exact Submodule.mul_mem_mul (filt_ad hX d a c hu) hv
  · have e : X a c * (x + y) - (x + y) * X a c = (X a c * x - x * X a c) + (X a c * y - y * X a c) := by
      rw [mul_add, add_mul]; abel
    rw [e]; exact add_mem hx hy

theorem exists_sum {B : Subalgebra ℂ A} {d : ℕ} {u : A}
    (hu : u ∈ LinearMap.range (wordMap X d) * Subalgebra.toSubmodule B) :
    ∃ (k : ℕ) (M : Fin k → Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ) (b : Fin k → A),
      (∀ i, b i ∈ B) ∧ u = ∑ i, wordMap X d (M i) * b i := by
  refine Submodule.mul_induction_on hu (fun x hx v hv => ?_) fun x y hx hy => ?_
  · obtain ⟨M, rfl⟩ := hx
    exact ⟨1, fun _ => M, fun _ => v, fun _ => hv, by simp⟩
  · obtain ⟨k, M, b, hb, rfl⟩ := hx
    obtain ⟨k', M', b', hb', rfl⟩ := hy
    refine ⟨k + k', Fin.append M M', Fin.append b b', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hb i
      · simpa using hb' i
    · rw [Fin.sum_univ_add]; simp

theorem exists_filtB {B : Subalgebra ℂ A} (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j) {z : A}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) ⊔ B) :
    ∃ d, z ∈ filt X d * Subalgebra.toSubmodule B := by
  set S := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2)
  have hSB : ∀ s ∈ S, ∀ b ∈ B, b * s = s * b := by
    intro s hs b hb
    have : S ≤ Subalgebra.centralizer ℂ {b} := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩ g hg
      rw [Set.mem_singleton_iff.1 hg]
      exact (hB b hb p.1 p.2).symm
    exact this hs b rfl
  set W := Subalgebra.toSubmodule S * Subalgebra.toSubmodule B
  have mono : ∀ {P Q R U : Submodule ℂ A}, P ≤ Q → R ≤ U → P * R ≤ Q * U := fun h h' =>
    Submodule.mul_le.2 fun p hp r hr => Submodule.mul_mem_mul (h hp) (h' hr)
  have oS : (1 : A) ∈ Subalgebra.toSubmodule S := one_mem S
  have oB : (1 : A) ∈ Subalgebra.toSubmodule B := one_mem B
  have hmul : W * W ≤ W := by
    have h1 : Subalgebra.toSubmodule B * Subalgebra.toSubmodule S ≤ W :=
      Submodule.mul_le.2 fun b hb s hs => by rw [hSB s hs b hb]; exact Submodule.mul_mem_mul hs hb
    have h2 : Subalgebra.toSubmodule S * Subalgebra.toSubmodule S ≤ Subalgebra.toSubmodule S :=
      Submodule.mul_le.2 fun s hs t ht => show s * t ∈ S from mul_mem (show s ∈ S from hs) (show t ∈ S from ht)
    have h3 : Subalgebra.toSubmodule B * Subalgebra.toSubmodule B ≤ Subalgebra.toSubmodule B :=
      Submodule.mul_le.2 fun s hs t ht => show s * t ∈ B from mul_mem (show s ∈ B from hs) (show t ∈ B from ht)
    calc W * W = Subalgebra.toSubmodule S * (Subalgebra.toSubmodule B * Subalgebra.toSubmodule S) *
          Subalgebra.toSubmodule B := by simp only [W, mul_assoc]
      _ ≤ Subalgebra.toSubmodule S * W * Subalgebra.toSubmodule B := mono (mono le_rfl h1) le_rfl
      _ = (Subalgebra.toSubmodule S * Subalgebra.toSubmodule S) *
          (Subalgebra.toSubmodule B * Subalgebra.toSubmodule B) := by simp only [W, mul_assoc]
      _ ≤ W := mono h2 h3
  let T : Subalgebra ℂ A := Submodule.toSubalgebra W
    (by simpa using Submodule.mul_mem_mul oS oB)
    (fun x y hx hy => hmul (Submodule.mul_mem_mul hx hy))
  have hT : S ⊔ B ≤ T := by
    refine sup_le (fun s hs => ?_) fun b hb => ?_
    · show s ∈ W
      simpa using Submodule.mul_mem_mul (show s ∈ Subalgebra.toSubmodule S from hs) oB
    · show b ∈ W
      simpa using Submodule.mul_mem_mul oS (show b ∈ Subalgebra.toSubmodule B from hb)
  have hW : W ≤ ⨆ d, filt X d * Subalgebra.toSubmodule B := Submodule.mul_le.2 fun s hs b hb => by
    obtain ⟨d, hd⟩ := exists_filt (E := X) hs
    exact Submodule.mem_iSup_of_mem d (Submodule.mul_mem_mul hd hb)
  have hz' : z ∈ ⨆ d, filt X d * Subalgebra.toSubmodule B := hW (hT hz)
  refine (Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun d d' h => ?_)).1 hz'
  exact Submodule.mul_le.2 fun u hu v hv => Submodule.mul_mem_mul (filt_mono h hu) hv

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC.RelCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A}

theorem central_of_filtB (hX : Formalism.REAL.GlRel X) (B : Subalgebra ℂ A) (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j)
    (d : ℕ) : ∀ z ∈ filt X d * Subalgebra.toSubmodule B, (∀ a c, X a c * z = z * X a c) →
      z ∈ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B := by
  induction d with
  | zero =>
    intro z hz _
    have h0 : filt X 0 ≤ ⊥ := iSup₂_le fun k hk => absurd hk (Nat.not_lt_zero k)
    have : filt X 0 * Subalgebra.toSubmodule B ≤ ⊥ :=
      Submodule.mul_le.2 fun u hu v _ => by rw [(Submodule.mem_bot ℂ).1 (h0 hu), zero_mul]; exact zero_mem _
    rw [(Submodule.mem_bot ℂ).1 (this hz)]
    exact zero_mem _
  | succ d ih =>
    intro z hz hc
    have hz' : z ∈ LinearMap.range (wordMap X d) * Subalgebra.toSubmodule B ⊔ filt X d * Subalgebra.toSubmodule B := by
      rw [← Submodule.sup_mul]
      exact (Submodule.mul_le.2 fun u hu v hv => Submodule.mul_mem_mul (filt_succ d hu) hv) hz
    obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hz'
    obtain ⟨k, M, b, hb, rfl⟩ := exists_sum hu
    have hbX : ∀ i a c, X a c * b i = b i * X a c := fun i a c => hB _ (hb i) a c
    set FB := filt X d * Subalgebra.toSubmodule B
    have hM : phi X d b (blockDiagonal M) = ∑ i, wordMap X d (M i) * b i := by
      simp [phi_apply, blockOf_blockDiagonal]
    obtain ⟨M₀, h1, h2⟩ := GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _
      (Set.range fun p : Fin n × Fin n => blockDiagonal fun _ : Fin k => polar n d p.1 p.2)
      (FB.comap (phi X d b))
      (by
        rintro _ ⟨p, rfl⟩
        exact ⟨(p.2, p.1), by rw [blockDiagonal_conjTranspose]; simp [polar_conjTranspose]⟩)
      (by
        rintro _ ⟨p, rfl⟩ N hN
        rw [Submodule.mem_comap, ← phi_comm hX d b hbX]
        exact filtB_ad hX hB d _ _ hN)
      (blockDiagonal M)
      (by
        rintro _ ⟨p, rfl⟩
        rw [Submodule.mem_comap, ← phi_comm hX d b hbX, hM]
        have h3 := neg_mem (filtB_ad hX hB d p.1 p.2 hy)
        have h4 := hc p.1 p.2
        rw [mul_add, add_mul] at h4
        convert h3 using 1
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h4, add_comm])
    have h4 : Submodule.span ℂ (Set.range (permMat n d)) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (gelfA X))) ⊔ filt X d).comap (wordMap X d) := by
      rw [Submodule.span_le]
      rintro _ ⟨π, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter A n X hX d π
      exact Submodule.mem_sup.2 ⟨c, hc1, _, hc2, by abel⟩
    have h5 : ∀ i, blockOf M₀ i ∈ Submodule.span ℂ (Set.range (permMat n d)) := fun i => by
      refine GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d _ fun T hT => ?_
      have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) ≤
          Subalgebra.centralizer ℂ {blockOf M₀ i} := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨p, rfl⟩ g hg
        rw [Set.mem_singleton_iff.1 hg]
        have := congrArg (fun N => blockOf N i) (h2 _ ⟨p, rfl⟩)
        simp only [blockOf_bd_mul, blockOf_mul_bd] at this
        exact this.symm
      exact this (GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT) _ rfl
    have h6 : ∀ i, ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA X)), ∃ f ∈ filt X d,
        wordMap X d (blockOf M₀ i) = c + f := fun i => by
      obtain ⟨c, hc1, f, hf, e⟩ := Submodule.mem_sup.1 (h4 (h5 i))
      exact ⟨c, hc1, f, hf, e.symm⟩
    choose c hc1 f hf hcf using h6
    have h7 : ∑ i, wordMap X d (M i) * b i + y - ∑ i, c i * b i ∈ FB := by
      have e : ∑ i, wordMap X d (M i) * b i + y - ∑ i, c i * b i =
          phi X d b (blockDiagonal M - M₀) + ∑ i, f i * b i + y := by
        rw [map_sub, hM, phi_apply]
        simp only [hcf, add_mul, Finset.sum_add_distrib]
        abel
      rw [e]
      refine add_mem (add_mem h1 (sum_mem fun i _ => Submodule.mul_mem_mul (hf i) (hb i))) hy
    have hcX : ∀ a a', X a a' * ∑ i, c i * b i = (∑ i, c i * b i) * X a a' := fun a a' => by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, gelf_adjoin_comm hX (hc1 i), mul_assoc, hbX, mul_assoc]
    have h8 := ih _ h7 fun a a' => by rw [mul_sub, sub_mul, hc, hcX]
    have h9 : ∑ i, c i * b i ∈ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B :=
      sum_mem fun i _ => mul_mem (le_sup_left (a := Algebra.adjoin ℂ (Set.range (gelfA X))) (hc1 i))
        (le_sup_right (b := B) (hb i))
    simpa using add_mem h8 h9

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC

theorem relativeCentre : RelativeCentre := by
  intro A _ _ n X hX B hB z hz hc
  obtain ⟨d, hd⟩ := RelCentre.exists_filtB hB hz
  exact RelCentre.central_of_filtB hX B hB d z hd hc

end GlobalTheory.LeviHC
