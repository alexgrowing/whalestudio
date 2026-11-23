import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFactor

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.HeightBound

section Alg

variable {K : Type} [Field K] {n r : ℕ}

theorem exists_factor (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) :
    ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) K) (N : Matrix (Fin r) (Fin n) K), N * M = 1 ∧ M * N = e :=
  _root_.UpperTheory.Reformulated.B.ExistsFactor.exists_factor e he

variable {R : Type*} [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

theorem comm_aeval (γ : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) R)
    (hX : X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X) (h : K[X]) :
    X * (aeval γ h).map (algebraMap K R) = (aeval γ h).map (algebraMap K R) * X := by
  have e1 : (aeval γ h).map (algebraMap K R) =
      aeval (γ.map (algebraMap K R)) h := by
    have := Polynomial.aeval_algHom_apply ((Algebra.ofId K R).mapMatrix (m := Fin n)) γ h
    exact this.symm
  rw [e1]
  have h1 : Algebra.adjoin K {γ.map (algebraMap K R)} ≤ Subalgebra.centralizer K {X} := by
    refine Algebra.adjoin_le ?_
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact hX
  have h2 := h1 (Polynomial.aeval_mem_adjoin_singleton K (γ.map (algebraMap K R)) (p := h))
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact h2 X rfl

def Ph (h : Fin n → K[X]) (γ : Matrix (Fin n) (Fin n) K) (z : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  ∑ j, z j • (aeval γ (h j)).map (algebraMap K R)

def Qm (h : Fin n → K[X]) (γ : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) (Fin r) K)
    (N : Matrix (Fin r) (Fin n) K) (z : Fin n → R) : Matrix (Fin r) (Fin r) R :=
  N.map (algebraMap K R) * Ph h γ z * M.map (algebraMap K R)

def detPoly (h : Fin n → K[X]) (γ : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) (Fin r) K)
    (N : Matrix (Fin r) (Fin n) K) : MvPolynomial (Fin n) K :=
  (Qm h γ M N (MvPolynomial.X : Fin n → MvPolynomial (Fin n) K)).det

theorem Ph_map (h : Fin n → K[X]) (γ : Matrix (Fin n) (Fin n) K) (f : R →ₐ[K] R') (z : Fin n → R) :
    (Ph h γ z).map f = Ph h γ (f ∘ z) := by
  ext a b
  simp [Ph, Matrix.sum_apply, map_sum, Matrix.map_apply]

theorem Qm_map (h : Fin n → K[X]) (γ : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) (Fin r) K)
    (N : Matrix (Fin r) (Fin n) K) (f : R →ₐ[K] R') (z : Fin n → R) :
    (Qm h γ M N z).map f = Qm h γ M N (f ∘ z) := by
  have hm : ∀ {a b : Type} (A : Matrix a b K),
      (A.map (algebraMap K R)).map f = A.map (algebraMap K R') := by
    intro a b A
    ext i j
    simp
  unfold Qm
  rw [← Ph_map, ← hm N, ← hm M]
  exact (Matrix.map_mul (f := (f : R →+* R'))).trans (by rw [Matrix.map_mul (f := (f : R →+* R'))]; rfl)

theorem aeval_detPoly (h : Fin n → K[X]) (γ : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) (Fin r) K)
    (N : Matrix (Fin r) (Fin n) K) (y : Fin n → R) :
    MvPolynomial.aeval y (detPoly h γ M N) = (Qm h γ M N y).det := by
  have hy : (MvPolynomial.aeval y : MvPolynomial (Fin n) K →ₐ[K] R) ∘ MvPolynomial.X = y := by
    funext p
    simp
  rw [detPoly, AlgHom.map_det]
  have := Qm_map h γ M N (MvPolynomial.aeval y) (MvPolynomial.X : Fin n → MvPolynomial (Fin n) K)
  rw [hy] at this
  rw [← this]
  rfl

theorem Ph_smul (h : Fin n → K[X]) (γ : Matrix (Fin n) (Fin n) K) (t : R) (z : Fin n → R) :
    Ph h γ (t • z) = t • Ph h γ z := by
  simp [Ph, Finset.smul_sum, smul_smul]

theorem aeval_detPoly_smul (h : Fin n → K[X]) (γ : Matrix (Fin n) (Fin n) K)
    (M : Matrix (Fin n) (Fin r) K) (N : Matrix (Fin r) (Fin n) K) (t : R) (y : Fin n → R) :
    MvPolynomial.aeval (t • y) (detPoly h γ M N) = t ^ r * MvPolynomial.aeval y (detPoly h γ M N) := by
  rw [aeval_detPoly, aeval_detPoly]
  have : Qm h γ M N (t • y) = t • Qm h γ M N y := by
    simp [Qm, Ph_smul]
  rw [this, Matrix.det_smul, Fintype.card_fin]

variable {v : Fin n → K} {h : Fin n → K[X]} {γ : Matrix (Fin n) (Fin n) K}

theorem vecMul_map_single (hs : ∀ j, (Pi.single j 1 : Fin n → K) = v ᵥ* aeval γ (h j)) (j : Fin n) :
    (algebraMap K R ∘ v) ᵥ* (aeval γ (h j)).map (algebraMap K R) = Pi.single j 1 := by
  funext i
  have := RingHom.map_vecMul (algebraMap K R) (aeval γ (h j)) v i
  rw [← this, ← hs j]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Pi.single_apply, hij]

theorem vecMul_Ph (hs : ∀ j, (Pi.single j 1 : Fin n → K) = v ᵥ* aeval γ (h j)) (z : Fin n → R) :
    (algebraMap K R ∘ v) ᵥ* Ph h γ z = z := by
  have h1 : ∀ (s : Finset (Fin n)) (A : Fin n → Matrix (Fin n) (Fin n) R) (w : Fin n → R),
      w ᵥ* ∑ j ∈ s, A j = ∑ j ∈ s, w ᵥ* A j := by
    intro s A w
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.vecMul_add, ih]
  rw [Ph, h1]
  simp only [Matrix.vecMul_smul, vecMul_map_single hs]
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem Ph_comm (z : Fin n → R) :
    Ph h γ z * γ.map (algebraMap K R) = γ.map (algebraMap K R) * Ph h γ z := by
  have hγ : ∀ j, (aeval γ (h j)).map (algebraMap K R) * γ.map (algebraMap K R) =
      γ.map (algebraMap K R) * (aeval γ (h j)).map (algebraMap K R) := by
    intro j
    rw [← Matrix.map_mul, ← Matrix.map_mul, pol_comm γ _ _ ⟨h j, rfl⟩ ⟨Polynomial.X, (aeval_X _).symm⟩]
  simp only [Ph, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, hγ]

theorem eq_zero_of_vecMul (hs : ∀ j, (Pi.single j 1 : Fin n → K) = v ᵥ* aeval γ (h j))
    (X : Matrix (Fin n) (Fin n) R) (hX : X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X)
    (h0 : (algebraMap K R ∘ v) ᵥ* X = 0) : X = 0 := by
  ext i j
  have h1 : (Pi.single i 1 : Fin n → R) ᵥ* X = 0 := by
    rw [← vecMul_map_single hs i, Matrix.vecMul_vecMul, ← comm_aeval γ X hX, ← Matrix.vecMul_vecMul, h0,
      Matrix.zero_vecMul]
  have h2 := congrFun h1 j
  simpa using h2

theorem Ph_vecMul (hs : ∀ j, (Pi.single j 1 : Fin n → K) = v ᵥ* aeval γ (h j))
    (A : Matrix (Fin n) (Fin n) R) (hA : A * γ.map (algebraMap K R) = γ.map (algebraMap K R) * A)
    (z : Fin n → R) : Ph h γ (z ᵥ* A) = Ph h γ z * A := by
  rw [← sub_eq_zero]
  refine eq_zero_of_vecMul hs _ ?_ ?_
  · rw [sub_mul, mul_sub, Ph_comm, mul_assoc, hA, ← mul_assoc, ← mul_assoc, Ph_comm]
  · rw [Matrix.vecMul_sub, vecMul_Ph hs, ← Matrix.vecMul_vecMul, vecMul_Ph hs, sub_self]

end Alg

section Comp

variable {K : Type} [Field K] {n r : ℕ}
variable {R : Type*} [CommRing R] [Algebra K R]
variable {v : Fin n → K} {h : Fin n → K[X]} {γ e : Matrix (Fin n) (Fin n) K}
variable {M : Matrix (Fin n) (Fin r) K} {N : Matrix (Fin r) (Fin n) K}

theorem Qm_vecMul (hs : ∀ j, (Pi.single j 1 : Fin n → K) = v ᵥ* aeval γ (h j))
    (hp : IsPol γ e) (hNM : N * M = 1) (hMN : M * N = e)
    (A : Matrix (Fin n) (Fin n) R) (hA : A * γ.map (algebraMap K R) = γ.map (algebraMap K R) * A)
    (z : Fin n → R) :
    Qm h γ M N (z ᵥ* A) = Qm h γ M N z * (N.map (algebraMap K R) * A * M.map (algebraMap K R)) := by
  obtain ⟨f, hf⟩ := hp
  have hMNR : M.map (algebraMap K R) * N.map (algebraMap K R) = e.map (algebraMap K R) := by
    rw [← hMN, Matrix.map_mul]
  have hNMR : N.map (algebraMap K R) * M.map (algebraMap K R) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAe : A * e.map (algebraMap K R) = e.map (algebraMap K R) * A := by
    rw [hf]
    exact comm_aeval γ A hA f
  have hAM : A * M.map (algebraMap K R) =
      M.map (algebraMap K R) * (N.map (algebraMap K R) * A * M.map (algebraMap K R)) := by
    calc A * M.map (algebraMap K R)
        = A * (M.map (algebraMap K R) * (N.map (algebraMap K R) * M.map (algebraMap K R))) := by
          rw [hNMR, Matrix.mul_one]
      _ = (A * e.map (algebraMap K R)) * M.map (algebraMap K R) := by
          rw [← hMNR]; simp only [Matrix.mul_assoc]
      _ = e.map (algebraMap K R) * A * M.map (algebraMap K R) := by rw [hAe]
      _ = _ := by rw [← hMNR]; simp only [Matrix.mul_assoc]
  simp only [Qm]
  rw [Ph_vecMul hs A hA]
  calc N.map (algebraMap K R) * (Ph h γ z * A) * M.map (algebraMap K R)
      = N.map (algebraMap K R) * Ph h γ z * (A * M.map (algebraMap K R)) := by
        simp only [Matrix.mul_assoc]
    _ = N.map (algebraMap K R) * Ph h γ z *
          (M.map (algebraMap K R) * (N.map (algebraMap K R) * A * M.map (algebraMap K R))) := by
        rw [hAM]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem det_compress (hNM : N * M = 1) (hMN : M * N = e) (A : Matrix (Fin n) (Fin n) R) :
    (N.map (algebraMap K R) * A * M.map (algebraMap K R)).det =
      (1 + e.map (algebraMap K R) * (A - 1)).det := by
  have hMNR : M.map (algebraMap K R) * N.map (algebraMap K R) = e.map (algebraMap K R) := by
    rw [← hMN, Matrix.map_mul]
  have hNMR : N.map (algebraMap K R) * M.map (algebraMap K R) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : e.map (algebraMap K R) * (A - 1) =
      M.map (algebraMap K R) * (N.map (algebraMap K R) * (A - 1)) := by
    rw [← hMNR, Matrix.mul_assoc]
  have h2 : N.map (algebraMap K R) * (A - 1) * M.map (algebraMap K R) =
      N.map (algebraMap K R) * A * M.map (algebraMap K R) - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hNMR]
  rw [h1, Matrix.det_one_add_mul_comm, h2, add_sub_cancel]

theorem det_Qm_ne_zero (hs : ∀ j, (Pi.single j 1 : Fin n → K) = v ᵥ* aeval γ (h j))
    (he : IsPrim γ e) (hNM : N * M = 1) (hMN : M * N = e) (x : Fin n → K) (hx : x ᵥ* e ≠ 0) :
    (Qm h γ M N x).det ≠ 0 := by
  have hB : Ph h γ x = aeval γ (∑ j, Polynomial.C (x j) * h j) := by
    simp [Ph, map_sum, Algebra.smul_def, Polynomial.aeval_C]
  have hv : v ᵥ* Ph h γ x = x := by
    have := vecMul_Ph (R := K) hs x
    simpa using this
  set p : K[X] := ∑ j, Polynomial.C (x j) * h j with hp
  have hne : aeval γ p * e ≠ 0 := by
    intro h0
    apply hx
    rw [← hv, Matrix.vecMul_vecMul, hB, h0, Matrix.vecMul_zero]
  obtain ⟨p', hp'⟩ := he.inv p hne
  have hc : e * aeval γ p = aeval γ p * e := pol_comm γ _ _ he.pol ⟨p, rfl⟩
  have hQ : Qm h γ M N x = N * aeval γ p * M := by
    simp [Qm, hB]
  have h1 : (N * aeval γ p' * M) * (N * aeval γ p * M) = 1 := by
    calc (N * aeval γ p' * M) * (N * aeval γ p * M)
        = N * aeval γ p' * (M * N) * aeval γ p * M := by simp only [Matrix.mul_assoc]
      _ = N * (aeval γ p' * (e * aeval γ p)) * M := by rw [hMN]; simp only [Matrix.mul_assoc]
      _ = N * e * M := by rw [hc, hp']
      _ = N * M * (N * M) := by rw [← hMN]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hNM, Matrix.mul_one]
  rw [hQ]
  intro h0
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h2
  exact zero_ne_one h2

end Comp

section Main

open scoped NumberField.AdeleRing

theorem exists_pos_le_height :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), (∀ y : Fin n → K, ∃ h : K[X], y = v ᵥ* aeval γ h) → ∀ e : Matrix (Fin n) (Fin n) K, IsPrim γ e → ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ g : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n, g.val * γ.map (algebraMap K (AdeleRing (𝓞 K) K)) = γ.map (algebraMap K (AdeleRing (𝓞 K) K)) * g.val → ∀ s : (AdeleRing (𝓞 K) K)ˣ, (s : AdeleRing (𝓞 K) K) = (1 + e.map (algebraMap K (AdeleRing (𝓞 K) K)) * (g.val - 1)).det → c ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) → ∀ x : Fin n → K, x ᵥ* e ≠ 0 → ε ≤ GroundTheory.Automorphic.Reduction.height g x := by
  intro K _ _ n γ v hcyc e he c hc
  choose h hs using fun j : Fin n => hcyc (Pi.single j 1)
  obtain ⟨r, M, N, hNM, hMN⟩ := exists_factor e he.idem
  have hr : 0 < r := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    subst h0
    apply he.ne
    rw [← hMN]
    ext i j
    simp [Matrix.mul_apply]
  obtain ⟨C, hC, hCb⟩ := GroundTheory.Automorphic.Anisotropic.exists_adelicNorm_aeval_le (K := K) (d := r) (m := 1) hr
    (fun _ => detPoly h γ M N)
    (fun w t y k => aeval_detPoly_smul h γ M N t y)
    (fun w t y k => aeval_detPoly_smul h γ M N t y)
  refine ⟨min 1 (c / C), lt_min one_pos (div_pos hc hC), fun g hg s hsdet hcs x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (Matrix.zero_vecMul _)
  set y := GroundTheory.Automorphic.Reduction.ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy
  let z : Fin 1 → K := fun _ => (Qm h γ M N x).det
  have hz : z ≠ 0 := fun h0 => det_Qm_ne_zero hs he hNM hMN x hx (congrFun h0 0)
  have hrat : (Qm h γ M N (GroundTheory.Automorphic.Reduction.ratVec x)).det = algebraMap K 𝔸[K] (Qm h γ M N x).det := by
    have h1 := Qm_map h γ M N (Algebra.ofId K 𝔸[K]) x
    have h2 : (Algebra.ofId K 𝔸[K]) ∘ x = GroundTheory.Automorphic.Reduction.ratVec x := rfl
    rw [h2] at h1
    rw [← h1]
    exact (AlgHom.map_det (Algebra.ofId K 𝔸[K]) _).symm
  have hval : (fun _ : Fin 1 => MvPolynomial.aeval y (detPoly h γ M N)) =
      (s : 𝔸[K]) • GroundTheory.Automorphic.Reduction.ratVec z := by
    funext i
    rw [aeval_detPoly, hy, Qm_vecMul hs he.pol hNM hMN _ hg, Matrix.det_mul, det_compress hNM hMN, ← hsdet, hrat,
      mul_comm]
    rfl
  have hyf := GroundTheory.Automorphic.Reduction.hasFiniteContent_height g hx0
  have hzf := GroundTheory.Automorphic.Reduction.hasFiniteContent_ratVec hz
  have hfz : GroundTheory.Automorphic.Reduction.HasFiniteContent
      (fun _ : Fin 1 => MvPolynomial.aeval y (detPoly h γ M N)) := by
    rw [hval]
    exact hzf.smul s
  have h1 : c ≤ GroundTheory.Automorphic.Reduction.adelicNorm
      (fun _ : Fin 1 => MvPolynomial.aeval y (detPoly h γ M N)) := by
    rw [hval, GroundTheory.Automorphic.Reduction.adelicNorm_smul hzf]
    have := GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec hz
    nlinarith [hcs, hc]
  have h2 : c ≤ C * GroundTheory.Automorphic.Reduction.height g x ^ r := h1.trans (hCb y hyf hfz)
  have h0 : 0 ≤ GroundTheory.Automorphic.Reduction.height g x := GroundTheory.Automorphic.Reduction.height_nonneg g x
  by_cases h1' : 1 ≤ GroundTheory.Automorphic.Reduction.height g x
  · exact (min_le_left _ _).trans h1'
  · replace h1' := not_le.1 h1'
    have hpow : GroundTheory.Automorphic.Reduction.height g x ^ r ≤ GroundTheory.Automorphic.Reduction.height g x :=
      pow_le_of_le_one h0 h1'.le hr.ne'
    have h3 : c ≤ C * GroundTheory.Automorphic.Reduction.height g x :=
      h2.trans (mul_le_mul_of_nonneg_left hpow hC.le)
    refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ hC, mul_comm]
    exact h3

end Main

end GlobalTheory.CompanionTheory.TorusCh.HeightBound

end
