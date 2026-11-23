import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Formalism.LocalToGlobal.InertKernelTheory.DefsIntTens
import Formalism.LocalToGlobal.GlobalTheory.GL3.ThirdClauseIntegralCombination
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerJet
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2

noncomputable section

namespace Formalism.L2.KerInert.IntTens

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

section Part1

variable {D : D7} {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)

theorem mem_stdL_iff {k : ℕ} (x : Fin k → D.host.E) :
    x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D k ↔ ∀ i, x i ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi]

def entB (I : Fin n') (J : Fin n) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin m') (Fin m) D.host.E where
  toFun A := Matrix.of fun u v => A (eR.symm (I, u)) (eC.symm (J, v))
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

def sglB (I : Fin n') (J : Fin n) :
    Matrix (Fin m') (Fin m) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun a c => if (eR a).1 = I ∧ (eC c).1 = J then A (eR a).2 (eC c).2 else 0
  map_add' _ _ := by ext; simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' _ _ := by ext; simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem entB_apply (I : Fin n') (J : Fin n) (A : Matrix (Fin N') (Fin N) D.host.E) (u : Fin m') (v : Fin m) :
    entB (D := D) eR eC I J A u v = A (eR.symm (I, u)) (eC.symm (J, v)) := rfl

theorem sglB_apply (I : Fin n') (J : Fin n) (A : Matrix (Fin m') (Fin m) D.host.E) (a : Fin N') (c : Fin N) :
    sglB (D := D) eR eC I J A a c = if (eR a).1 = I ∧ (eC c).1 = J then A (eR a).2 (eC c).2 else 0 := rfl

theorem entB_smulE (I : Fin n') (J : Fin n) (x : D.host.E) (A : Matrix (Fin N') (Fin N) D.host.E) :
    entB (D := D) eR eC I J (x • A) = x • entB eR eC I J A := by
  ext; simp [entB_apply]

theorem sglB_smulE (I : Fin n') (J : Fin n) (x : D.host.E) (A : Matrix (Fin m') (Fin m) D.host.E) :
    sglB (D := D) eR eC I J (x • A) = x • sglB eR eC I J A := by
  ext a c; simp only [sglB_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem one_mem_zero : (0 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.zero_mem _

theorem entB_homL (I : Fin n') (J : Fin n) (A : Matrix (Fin N') (Fin N) D.host.E)
    (hA : A ∈ homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) :
    entB (D := D) eR eC I J A ∈ homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m') := by
  classical
  unfold homL at hA ⊢
  refine (Submodule.span_le.2 ?_ : _ ≤ (homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m')).comap
    (entB (D := D) eR eC I J)) hA
  intro B hB
  refine Submodule.subset_span ?_
  intro x hx
  rw [mem_stdL_iff] at hx ⊢
  intro u
  set y : Fin N → D.host.E := fun c => if (eC c).1 = J then x (eC c).2 else 0 with hy
  have hy1 : y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
    rw [mem_stdL_iff]; intro c; simp only [hy]; split_ifs
    · exact hx _
    · exact Submodule.zero_mem _
  have h := (mem_stdL_iff _).1 (hB y hy1) (eR.symm (I, u))
  convert h using 1
  simp only [Matrix.mulVec, dotProduct, entB_apply, hy]
  rw [← Equiv.sum_comp eC.symm, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single J]
  · simp
  · intro J' _ hJ; simp [hJ]
  · simp

theorem sglB_homL (I : Fin n') (J : Fin n) (A : Matrix (Fin m') (Fin m) D.host.E)
    (hA : A ∈ homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m')) :
    sglB (D := D) eR eC I J A ∈ homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') := by
  classical
  unfold homL at hA ⊢
  refine (Submodule.span_le.2 ?_ : _ ≤ (homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')).comap
    (sglB (D := D) eR eC I J)) hA
  intro B hB
  refine Submodule.subset_span ?_
  intro x hx
  rw [mem_stdL_iff] at hx ⊢
  intro a
  set x' : Fin m → D.host.E := fun v => x (eC.symm (J, v)) with hx'
  have hx1 : x' ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D m := by
    rw [mem_stdL_iff]; intro v; exact hx _
  have h := (mem_stdL_iff _).1 (hB x' hx1) (eR a).2
  by_cases hI : (eR a).1 = I
  · convert h using 1
    simp only [Matrix.mulVec, dotProduct, sglB_apply, hx', hI, true_and]
    rw [← Equiv.sum_comp eC.symm, Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply]
    rw [Finset.sum_eq_single J]
    · simp
    · intro J' _ hJ; simp [hJ]
    · simp
  · convert Submodule.zero_mem (1 : Submodule (𝓞 D.host.E) D.host.E) using 1
    simp [Matrix.mulVec, dotProduct, sglB_apply, hI]

end Part1

section Part2

variable {D : D7} {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)

theorem entB_YY (I : Fin n') (J : Fin n) (A : Matrix (Fin N') (Fin N) D.host.E)
    (hA : A ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) :
    entB (D := D) eR eC I J A ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m') := by
  unfold YYl at hA ⊢
  refine (Submodule.span_le.2 ?_ : _ ≤ (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m')).comap
    (entB (D := D) eR eC I J)) hA
  rintro B ⟨a, ha, A', hA', rfl⟩
  refine Submodule.subset_span ⟨a, ha, entB eR eC I J A', entB_homL eR eC I J A' hA', ?_⟩
  exact entB_smulE eR eC I J a A'

theorem sglB_YY (I : Fin n') (J : Fin n) (A : Matrix (Fin m') (Fin m) D.host.E)
    (hA : A ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m')) :
    sglB (D := D) eR eC I J A ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') := by
  unfold YYl at hA ⊢
  refine (Submodule.span_le.2 ?_ : _ ≤ (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')).comap
    (sglB (D := D) eR eC I J)) hA
  rintro B ⟨a, ha, A', hA', rfl⟩
  refine Submodule.subset_span ⟨a, ha, sglB eR eC I J A', sglB_homL eR eC I J A' hA', ?_⟩
  exact sglB_smulE eR eC I J a A'

theorem sum_sglB_entB (y : Matrix (Fin N') (Fin N) D.host.E) :
    ∑ I, ∑ J, sglB (D := D) eR eC I J (entB eR eC I J y) = y := by
  classical
  ext a c
  simp only [Matrix.sum_apply, sglB_apply, entB_apply]
  rw [Finset.sum_eq_single (eR a).1, Finset.sum_eq_single (eC c).1]
  · simp
  · intro J _ hJ; simp [Ne.symm hJ]
  · simp
  · intro I _ hI; refine Finset.sum_eq_zero fun J _ => ?_; simp [Ne.symm hI]
  · simp

theorem mem_YY_iff (y : Matrix (Fin N') (Fin N) D.host.E) :
    y ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') ↔
      ∀ I J, entB (D := D) eR eC I J y ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m') := by
  constructor
  · intro hy I J; exact entB_YY eR eC I J y hy
  · intro h
    rw [← sum_sglB_entB eR eC y]
    exact Submodule.sum_mem _ fun I _ => Submodule.sum_mem _ fun J _ => sglB_YY eR eC I J _ (h I J)

def prjB (I : Fin n') (J : Fin n) : VC D N N' →+ VC D m m' where
  toFun z := fun τ u v => z τ (eR.symm (I, u)) (eC.symm (J, v))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem prjB_apply (I : Fin n') (J : Fin n) (z : VC D N N') (τ : D.what₂.Tau) (u : Fin m') (v : Fin m) :
    prjB (D := D) eR eC I J z τ u v = z τ (eR.symm (I, u)) (eC.symm (J, v)) := rfl

theorem prjB_La (T : Tor D) (I : Fin n') (J : Fin n) (x : VC D N N')
    (hx : x ∈ La D T (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) :
    prjB (D := D) eR eC I J x ∈ La D T (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m') := by
  unfold La at hx ⊢
  refine ((AddSubgroup.closure_le _).2 ?_ : _ ≤ (La D T (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m')).comap
    (prjB (D := D) eR eC I J)) hx
  rintro z ⟨w, hw, A, hA, rfl⟩
  refine AddSubgroup.subset_closure ⟨w, hw, entB eR eC I J A, entB_YY eR eC I J A hA, ?_⟩
  funext τ u v
  simp [prjB_apply, embV, entB_apply]

theorem torsB (T : Tor D) (p : ℕ) (I : Fin n') (J : Fin n) (s : VC D N N')
    (hs : TorsPrime D p (La D T (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s) :
    TorsPrime D p (La D T (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m')) (prjB (D := D) eR eC I J s) := by
  obtain ⟨k, hk, hkp, hks⟩ := hs
  refine ⟨k, hk, hkp, ?_⟩
  rw [← map_nsmul]
  exact prjB_La eR eC T I J _ hks

theorem tors_zero (p : ℕ) {a b : ℕ} (La' : AddSubgroup (VC D a b)) : TorsPrime D p La' 0 :=
  ⟨1, one_pos, Nat.coprime_one_left _, by simp⟩

def eIdx (n' n r : ℕ) : (Fin n' × Fin n) × Fin r ≃ Fin (n' * n * r) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def bB {r : ℕ} (b : Fin r → Matrix (Fin m') (Fin m) D.host.E) (q : Fin (n' * n * r)) :
    Matrix (Fin N') (Fin N) D.host.E :=
  sglB eR eC ((eIdx n' n r).symm q).1.1 ((eIdx n' n r).symm q).1.2 (b ((eIdx n' n r).symm q).2)

theorem bB_eIdx {r : ℕ} (b : Fin r → Matrix (Fin m') (Fin m) D.host.E) (I : Fin n') (J : Fin n) (k : Fin r) :
    bB (D := D) eR eC b (eIdx n' n r ((I, J), k)) = sglB eR eC I J (b k) := by
  simp [bB]

theorem sum_sglB (I : Fin n') (J : Fin n) (A : Matrix (Fin m') (Fin m) D.host.E) :
    ∑ a, ∑ c, sglB (D := D) eR eC I J A a c = ∑ u, ∑ v, A u v := by
  classical
  rw [← eR.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single I]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [← eC.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single J]
    · simp [sglB_apply]
    · intro J' _ hJ; refine Finset.sum_eq_zero fun v _ => ?_; simp [sglB_apply, hJ]
    · simp
  · intro I' _ hI; refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun c _ => ?_; simp [sglB_apply, hI]
  · simp

theorem sglB_mul_conj (I J I' J') (A A' : Matrix (Fin m') (Fin m) D.host.E) (a : Fin N') (c : Fin N) :
    sglB (D := D) eR eC I J A a c * D.host.conj (sglB (D := D) eR eC I' J' A' a c) =
      if I = I' ∧ J = J' then sglB (D := D) eR eC I J (Matrix.of fun u v => A u v * D.host.conj (A' u v)) a c
      else 0 := by
  simp only [sglB_apply, Matrix.of_apply]
  split_ifs <;> simp_all

theorem hYY_sglB (I J I' J') (A A' : Matrix (Fin m') (Fin m) D.host.E) :
    hYY D (sglB (D := D) eR eC I J A) (sglB (D := D) eR eC I' J' A') = if I = I' ∧ J = J' then hYY D A A' else 0 := by
  unfold hYY
  simp_rw [sglB_mul_conj]
  split_ifs with h
  · rw [sum_sglB]; rfl
  · simp

theorem orth_bB {r : ℕ} (b : Fin r → Matrix (Fin m') (Fin m) D.host.E) (hb : Orthonormal D b) :
    Orthonormal D (bB (D := D) (n' := n') (n := n) eR eC b) := by
  intro q q'
  obtain ⟨⟨⟨I, J⟩, k⟩, rfl⟩ := (eIdx n' n r).surjective q
  obtain ⟨⟨⟨I', J'⟩, k'⟩, rfl⟩ := (eIdx n' n r).surjective q'
  rw [bB_eIdx, bB_eIdx, hYY_sglB, hb]
  simp only [(eIdx n' n r).injective.eq_iff, Prod.mk.injEq]
  by_cases hI : I = I' <;> by_cases hJ : J = J' <;> by_cases hk : k = k' <;> simp [hI, hJ, hk]

end Part2

section Part3

variable {D : D7} {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)

theorem entB_Ksmul (I : Fin n') (J : Fin n) (g : D.host.K) (A : Matrix (Fin N') (Fin N) D.host.E) :
    entB (D := D) eR eC I J (g • A) = g • entB eR eC I J A := by
  ext; simp [entB_apply]

theorem entB_sglB (I J I' J') (A : Matrix (Fin m') (Fin m) D.host.E) :
    entB (D := D) eR eC I J (sglB eR eC I' J' A) = if I' = I ∧ J' = J then A else 0 := by
  ext u v
  simp only [entB_apply, sglB_apply, Equiv.apply_symm_apply]
  split_ifs <;> simp_all

theorem linInd_bB {r : ℕ} (b : Fin r → Matrix (Fin m') (Fin m) D.host.E) (hb : LinearIndependent D.host.K b) :
    LinearIndependent D.host.K (bB (D := D) (n' := n') (n := n) eR eC b) := by
  classical
  rw [Fintype.linearIndependent_iff] at hb ⊢
  intro g hg q
  obtain ⟨⟨⟨I, J⟩, k⟩, rfl⟩ := (eIdx n' n r).surjective q
  have h1 := congrArg (entB (D := D) eR eC I J) hg
  rw [map_sum, map_zero] at h1
  simp_rw [entB_Ksmul] at h1
  have h2 : ∑ k, g (eIdx n' n r ((I, J), k)) • b k =
      ∑ q, g q • entB (D := D) eR eC I J (bB (D := D) eR eC b q) := by
    rw [← (eIdx n' n r).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (I, J)]
    · simp [bB_eIdx, entB_sglB]
    · rintro ⟨I', J'⟩ _ hne
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [bB_eIdx, entB_sglB, if_neg]
      · simp
      · rintro ⟨h1, h2⟩; exact hne (by simp [h1, h2])
    · simp
  exact hb _ (h2.trans h1) k

theorem mem_bB {r : ℕ} (p : ℕ) (b : Fin r → Matrix (Fin m') (Fin m) D.host.E)
    (hb : ∀ k, ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • b k ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m'))
    (q : Fin (n' * n * r)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • bB (D := D) eR eC b q ∈
      YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') := by
  obtain ⟨⟨⟨I, J⟩, k⟩, rfl⟩ := (eIdx n' n r).surjective q
  obtain ⟨s, hs, hsb⟩ := hb k
  refine ⟨s, hs, ?_⟩
  rw [bB_eIdx, ← sglB_smulE]
  exact sglB_YY eR eC I J _ hsb

theorem span_bB {r : ℕ} (p : ℕ) (b : Fin r → Matrix (Fin m') (Fin m) D.host.E)
    (hb : ∀ y ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m'), ∃ s : ℕ, Nat.Coprime s p ∧
      ∃ c : Fin r → 𝓞 D.host.K, (s : D.host.E) • y = ∑ i, (((c i : D.host.K) : D.host.E)) • b i) :
    ∀ y ∈ YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N'), ∃ s : ℕ, Nat.Coprime s p ∧
      ∃ c : Fin (n' * n * r) → 𝓞 D.host.K,
        (s : D.host.E) • y = ∑ i, (((c i : D.host.K) : D.host.E)) • bB (D := D) eR eC b i := by
  classical
  intro y hy
  have hyB := (mem_YY_iff eR eC y).1 hy
  choose s hs c hc using fun I J => hb _ (hyB I J)
  set S : ℕ := ∏ I, ∏ J, s I J with hS
  have hdvd : ∀ I J, s I J ∣ S := fun I J =>
    (Finset.dvd_prod_of_mem (fun J => s I J) (Finset.mem_univ J)).trans
      (Finset.dvd_prod_of_mem (fun I => ∏ J, s I J) (Finset.mem_univ I))
  refine ⟨S, Nat.Coprime.prod_left fun I _ => Nat.Coprime.prod_left fun J _ => hs I J,
    fun q => (((S / s ((eIdx n' n r).symm q).1.1 ((eIdx n' n r).symm q).1.2 : ℕ) : 𝓞 D.host.K)) *
      c ((eIdx n' n r).symm q).1.1 ((eIdx n' n r).symm q).1.2 ((eIdx n' n r).symm q).2, ?_⟩
  ext a c'
  have h1 := congrArg (fun M => M (eR a).2 (eC c').2) (hc (eR a).1 (eC c').1)
  simp only [Matrix.smul_apply, entB_apply, Matrix.sum_apply, smul_eq_mul, Prod.mk.eta,
    Equiv.symm_apply_apply] at h1
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [← (eIdx n' n r).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single ((eR a).1, (eC c').1)]
  · simp only [Equiv.symm_apply_apply, bB_eIdx, sglB_apply, and_self, if_true]
    have e1 : ∀ k, (((((S / s (eR a).1 (eC c').1 : ℕ) : 𝓞 D.host.K) * c (eR a).1 (eC c').1 k : 𝓞 D.host.K) :
        D.host.K) : D.host.E) * b k (eR a).2 (eC c').2 =
        ((S / s (eR a).1 (eC c').1 : ℕ) : D.host.E) * ((((c (eR a).1 (eC c').1 k : 𝓞 D.host.K) : D.host.K) :
          D.host.E) * b k (eR a).2 (eC c').2) := by
      intro k; push_cast; ring
    simp_rw [e1]
    rw [← Finset.mul_sum, ← h1, ← mul_assoc]
    congr 1
    rw [← Nat.cast_mul, Nat.div_mul_cancel (hdvd _ _)]
  · rintro ⟨I', J'⟩ _ hne
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [Equiv.symm_apply_apply, bB_eIdx, sglB_apply]
    rw [if_neg, mul_zero]
    rintro ⟨h1, h2⟩; exact hne (by simp [h1, h2])
  · simp

theorem locBasis_bB {r : ℕ} (p : ℕ) (b : Fin r → Matrix (Fin m') (Fin m) D.host.E)
    (hb : LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D m) (Formalism.MainNotions.StandardLatticesGL3.stdL D m')) b) :
    LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N'))
      (bB (D := D) (n' := n') (n := n) eR eC b) :=
  ⟨linInd_bB eR eC b hb.1, mem_bB eR eC p b hb.2.1, span_bB eR eC p b hb.2.2⟩

end Part3

section Part4

variable {D : D7} {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)

theorem sum_blocks {M : Type*} [AddCommMonoid M] (f : Fin N' → Fin N → M) :
    ∑ a, ∑ c, f a c = ∑ I, ∑ J, ∑ u, ∑ v, f (eR.symm (I, u)) (eC.symm (J, v)) := by
  rw [← eR.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun I _ => ?_
  have h : ∀ u, ∑ c, f (eR.symm (I, u)) c = ∑ J, ∑ v, f (eR.symm (I, u)) (eC.symm (J, v)) := fun u => by
    rw [← eC.symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [h]
  exact Finset.sum_comm

theorem prod_blocks {M : Type*} [CommMonoid M] (f : Fin N' → Fin N → M) :
    ∏ a, ∏ c, f a c = ∏ I, ∏ J, ∏ u, ∏ v, f (eR.symm (I, u)) (eC.symm (J, v)) := by
  rw [← eR.symm.prod_comp, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun I _ => ?_
  have h : ∀ u, ∏ c, f (eR.symm (I, u)) c = ∏ J, ∏ v, f (eR.symm (I, u)) (eC.symm (J, v)) := fun u => by
    rw [← eC.symm.prod_comp, Fintype.prod_prod_type]
  simp_rw [h]
  exact Finset.prod_comm

theorem Hf_blocks (T : Tor D) (x y : VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.Hf D T x y = ∑ I, ∑ J, Formalism.MainNotions.TaylorLogMetric.Hf D T (prjB (D := D) eR eC I J x) (prjB (D := D) eR eC I J y) := by
  simp only [Formalism.MainNotions.TaylorLogMetric.Hf, prjB_apply, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_congr rfl fun τ _ => sum_blocks eR eC (fun a c => x τ a c * (starRingEnd ℂ) (y τ a c)),
    Finset.sum_comm]
  exact Finset.sum_congr rfl fun I _ => Finset.sum_comm

theorem U_tensPow (T : Tor D) (θ : (D.what₂.Tau → ℂ) → ℂ) (s z : VC D N N') :
    U D T s (tensPow θ N N') z =
      ∏ I, ∏ J, U D T (prjB (D := D) eR eC I J s) (tensPow θ m m') (prjB (D := D) eR eC I J z) := by
  unfold U
  simp_rw [Finset.prod_mul_distrib]
  congr 1
  · unfold tensPow
    rw [prod_blocks eR eC]
    rfl
  · simp_rw [← Complex.exp_sum]
    congr 1
    rw [Hf_blocks eR eC T z s, Hf_blocks eR eC T s s]
    simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]

end Part4

section Part5

section Gen

variable {σ τ : Type*} {p : ℕ} [Fact p.Prime]

theorem rename_psubst (f : σ → τ) [Filter.TendstoCofinite f] {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (g : PowerSeries ℂ_[p]) :
    MvPowerSeries.rename f (PowerSeries.subst a g) = PowerSeries.subst (MvPowerSeries.rename f a) g := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero ha).const
      (MvPowerSeries.HasSubst.X_comp f), MvPowerSeries.rename_eq_subst]

theorem rename_inv (f : σ → τ) [Filter.TendstoCofinite f] (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.rename f F⁻¹ = (MvPowerSeries.rename f F)⁻¹ := by
  by_cases h : MvPowerSeries.constantCoeff F = 0
  · rw [(MvPowerSeries.inv_eq_zero).2 h, map_zero, eq_comm, MvPowerSeries.inv_eq_zero,
      MvPowerSeries.constantCoeff_rename, h]
  · have h' : MvPowerSeries.constantCoeff (MvPowerSeries.rename f F) ≠ 0 := by
      rwa [MvPowerSeries.constantCoeff_rename]
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one h', ← map_mul, mul_comm, MvPowerSeries.mul_inv_cancel F h, map_one]

theorem integralMv_rename (f : σ → τ) [Filter.TendstoCofinite f] {F : MvPowerSeries σ ℂ_[p]}
    (hF : IntegralMv F) : IntegralMv (MvPowerSeries.rename f F) := fun n => by
  rw [MvPowerSeries.coeff_rename]
  exact isPadicIntegral_sum _ _ fun x _ => hF x

theorem integralMv_one : IntegralMv (1 : MvPowerSeries σ ℂ_[p]) := fun n => by
  classical
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · unfold IsIntP; simp
  · unfold IsIntP; simp

theorem integralMv_prod {ι : Type*} (s : Finset ι) (F : ι → MvPowerSeries σ ℂ_[p])
    (h : ∀ i ∈ s, IntegralMv (F i)) : IntegralMv (∏ i ∈ s, F i) :=
  Finset.prod_induction _ IntegralMv (fun _ _ => integralMv_mul) integralMv_one h

end Gen

variable {D : D7} {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
variable {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])

theorem lamC_zero : lamC lam 0 = 0 := by
  unfold lamC
  rw [dif_pos (zero_mem _)]
  exact map_zero lam

def idxK (r : ℕ) (I : Fin n') (J : Fin n) (k : Fin r) : Fin (n' * n * r) := eIdx n' n r ((I, J), k)

theorem atLogA_blk {r : ℕ} (b : Fin r → Matrix (Fin m') (Fin m) D.host.E) (I : Fin n') (J : Fin n)
    (k : D.what₂.Tau × Fin m' × Fin m) :
    atLogA lam Λ C wq (bB (D := D) eR eC b) (blkIdx D eR eC I J k) =
      MvPowerSeries.rename (idxK r I J) (atLogA lam Λ C wq b k) := by
  classical
  simp only [atLogA, map_sum, map_mul, AlgHom.commutes]
  rw [← (eIdx n' n r).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (I, J)]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    rw [rename_psubst _ (MvPowerSeries.constantCoeff_X k'), MvPowerSeries.rename_X]
    simp [bB_eIdx, sglB_apply, blkIdx, idxK]
  · rintro ⟨I', J'⟩ _ hne
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [bB_eIdx, sglB_apply, if_neg]
    · simp [lamC_zero]
    · simp only [blkIdx, Equiv.apply_symm_apply]
      rintro ⟨h1, h2⟩; exact hne (by simp [h1, h2])
  · simp

theorem atLog_rename {r : ℕ} (b : Fin r → Matrix (Fin m') (Fin m) D.host.E) (I : Fin n') (J : Fin n)
    (F : MvPowerSeries (D.what₂.Tau × Fin m' × Fin m) ℂ_[p]) :
    atLog D lam Λ C wq (bB (D := D) eR eC b) (MvPowerSeries.rename (blkIdx D eR eC I J) F) =
      MvPowerSeries.rename (idxK r I J) (atLog D lam Λ C wq b F) := by
  show MvPowerSeries.subst (atLogA lam Λ C wq (bB (D := D) eR eC b)) _ =
    MvPowerSeries.rename (idxK r I J) (MvPowerSeries.subst (atLogA lam Λ C wq b) F)
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) (atLogA_hasSubst lam Λ C wq _),
    MvPowerSeries.subst_comp_subst_apply (atLogA_hasSubst lam Λ C wq b) (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext k
  rw [Function.comp_apply, MvPowerSeries.subst_X (atLogA_hasSubst lam Λ C wq _), ← MvPowerSeries.rename_eq_subst]
  exact atLogA_blk eR eC lam Λ C wq b I J k

theorem ePh_blk (hp2 : p ≠ 2) (r : ℕ) :
    ePh lam Λ C wq (n' * n * r) = ∏ I : Fin n', ∏ J : Fin n, MvPowerSeries.rename (idxK r I J) (ePh lam Λ C wq r) := by
  unfold ePh
  rw [if_neg hp2, if_neg hp2, ← (eIdx n' n r).prod_comp, Fintype.prod_prod_type, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun I _ => Finset.prod_congr rfl fun J _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [rename_inv, rename_psubst _ (MvPowerSeries.constantCoeff_X k), MvPowerSeries.rename_X]
  rfl

end Part5

section LatticeGramTransferCondition
open Formalism.L2.Th1.H (taylorMv linSubst taylorMvMul taylorMvComp taylorMv_coeff)

section TB

variable {n : Type} [Fintype n] [DecidableEq n]

theorem taylorMv_one : taylorMv (fun _ : n → ℂ => (1 : ℂ)) = 1 := by
  classical
  ext ν
  by_cases h : ν = 0
  · subst h
    rw [taylorMv_coeff _ 0 0 (by simp), MvPowerSeries.coeff_one, if_pos rfl]
    have hc : ∀ f : Fin 0 → n, Formalism.L2.Th1.H.cntVec f = 0 := fun f => by
      ext i; simp [Formalism.L2.Th1.H.cntVec_apply]
    rw [Finset.filter_true_of_mem (fun f _ => hc f)]
    simp
  · rw [taylorMv_coeff _ ν.degree ν rfl, MvPowerSeries.coeff_one]
    have hd : ν.degree ≠ 0 := by
      rwa [Ne, Finsupp.degree_eq_zero_iff]
    rw [if_neg h, iteratedFDeriv_const_of_ne hd]
    simp

theorem analyticAt_finprod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E} {ι : Type*} (s : Finset ι)
    (H : ι → E → ℂ) (hH : ∀ i, AnalyticAt ℂ (H i) x) :
    AnalyticAt ℂ (fun w => ∏ i ∈ s, H i w) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : ℂ)) x)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hH a).mul ih

theorem taylorMv_finprod {ι : Type*} (s : Finset ι) (H : ι → (n → ℂ) → ℂ) (hH : ∀ i, AnalyticAt ℂ (H i) 0) :
    taylorMv (fun w => ∏ i ∈ s, H i w) = ∏ i ∈ s, taylorMv (H i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using taylorMv_one
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [taylorMvMul n (H a) (fun w => ∏ i ∈ s, H i w) (hH a)
      (analyticAt_finprod s H hH), ih]

end TB

variable {D : D7}

theorem taylorSer_eq_taylorMv [DecidableEq D.what₂.Tau] {a b : ℕ} (G : VC D a b → ℂ) (hG : AnalyticOnNhd ℂ G Set.univ) :
    taylorSer D G = taylorMv (fun z => G (Formalism.L2.AlgTh.flat D.what₂.Tau a b z)) := by
  ext α
  have h1 := Formalism.L2.AlgTh.taylor_jet_expansion D.what₂.Tau a b G hG α
  have h2 := Formalism.L2.Ker.derivAt0_eq_taylor D G α
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  show taylor D G α = _
  apply mul_left_cancel₀ hne
  rw [h2, ← h1]
  congr 1
  simp [Formalism.DworkPowerSeriesWeights.mfact, Finsupp.prod]

end LatticeGramTransferCondition

section Part7
open Formalism.L2.Th1.H (taylorMv linSubst taylorMvMul taylorMvComp taylorMv_coeff)

def blkCL (D : D7) {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
    (I : Fin n') (J : Fin n) : VC D N N' →L[ℂ] VC D m m' :=
  LinearMap.toContinuousLinearMap
    { toFun := blkPt D eR eC I J, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem taylor_product_blocks_factorization : TaylorProductOverBlocks := by
  intro D N N' n n' m m' eR eC G hG
  classical
  let M : Fin n' → Fin n → Matrix (D.what₂.Tau × Fin m' × Fin m) (D.what₂.Tau × Fin N' × Fin N) ℂ :=
    fun I J => Matrix.of fun k k' => if k' = blkIdx D eR eC I J k then 1 else 0
  have hM : ∀ I J (w : D.what₂.Tau × Fin N' × Fin N → ℂ), (M I J).mulVec w = fun k => w (blkIdx D eR eC I J k) := by
    intro I J w; funext k; simp [M, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_eq']
  have hflat : ∀ I J (w : D.what₂.Tau × Fin N' × Fin N → ℂ),
      Formalism.L2.AlgTh.flat D.what₂.Tau m m' ((M I J).mulVec w) =
        blkPt D eR eC I J (Formalism.L2.AlgTh.flat D.what₂.Tau N N' w) := by
    intro I J w; rw [hM]; rfl
  have hGf : ∀ I J, AnalyticOnNhd ℂ (fun z => G I J (Formalism.L2.AlgTh.flat D.what₂.Tau m m' z)) Set.univ := by
    intro I J z _
    exact (hG I J _ trivial).comp
      (((Formalism.L2.AlgTh.flat D.what₂.Tau m m').toContinuousLinearEquiv :
        (D.what₂.Tau × Fin m' × Fin m → ℂ) →L[ℂ] VC D m m').analyticAt z)
  have hGfM : ∀ I J, AnalyticAt ℂ (fun w => G I J (Formalism.L2.AlgTh.flat D.what₂.Tau m m' ((M I J).mulVec w))) 0 := by
    intro I J
    exact (hGf I J _ trivial).comp
      ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin (M I J))).analyticAt 0)
  have hbig : AnalyticOnNhd ℂ (fun z => ∏ I, ∏ J, G I J (blkPt D eR eC I J z)) Set.univ := by
    intro z _
    exact analyticAt_finprod _ _ fun I => analyticAt_finprod _ _ fun J =>
      (hG I J _ trivial).comp ((blkCL D eR eC I J).analyticAt z)
  rw [taylorSer_eq_taylorMv _ hbig]
  simp_rw [← hflat]
  rw [taylorMv_finprod Finset.univ (fun I w => ∏ J, G I J (Formalism.L2.AlgTh.flat D.what₂.Tau m m' ((M I J).mulVec w)))
    (fun I => analyticAt_finprod _ _ fun J => hGfM I J)]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [taylorMv_finprod Finset.univ _ (fun J => hGfM I J)]
  refine Finset.prod_congr rfl fun J _ => ?_
  rw [taylorMvComp _ _ (M I J) (fun z => G I J (Formalism.L2.AlgTh.flat D.what₂.Tau m m' z)) (hGf I J 0 trivial),
    ← taylorSer_eq_taylorMv _ (hG I J), linSubst, MvPowerSeries.rename_eq_subst]
  congr 1
  funext k
  simp [M, apply_ite MvPowerSeries.C, ite_mul, Finset.sum_ite_eq']

end Part7

section Part8

variable {D : D7} {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
variable {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem pSer_blk (hTB : TaylorProductOverBlocks) (G : Fin n' → Fin n → VC D m m' → ℂ) (hG : ∀ I J, AlgEnt D (G I J)) :
    pSer D lam (fun z => ∏ I, ∏ J, G I J (blkPt D eR eC I J z)) =
      ∏ I, ∏ J, MvPowerSeries.rename (blkIdx D eR eC I J) (pSer D lam (G I J)) := by
  have hT := hTB D N N' n n' m m' eR eC G (fun I J => (hG I J).1)
  let TQ : Fin n' → Fin n → MvPowerSeries (D.what₂.Tau × Fin m' × Fin m) Qbar :=
    fun I J β => ⟨taylor D (G I J) β, (hG I J).2 β⟩
  have h1 : ∀ I J, taylorSer D (G I J) = MvPowerSeries.map (algebraMap Qbar ℂ) (TQ I J) := by
    intro I J; ext β; rfl
  have h2 : ∀ I J, pSer D lam (G I J) = MvPowerSeries.map lam (TQ I J) := by
    intro I J; ext β
    show lamC lam (taylor D (G I J) β) = lam (TQ I J β)
    unfold lamC
    rw [dif_pos ((hG I J).2 β)]
  ext α
  change lamC lam (MvPowerSeries.coeff α (taylorSer D (fun z => ∏ I, ∏ J, G I J (blkPt D eR eC I J z)))) = _
  rw [hT]
  simp_rw [h1, h2, MvPowerSeries.rename_map, ← map_prod]
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
  unfold lamC
  split_ifs with h
  · rfl
  · exact absurd (SetLike.coe_mem _) h

theorem atLog_prod (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) {r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (F : Fin n' → Fin n → MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b (∏ I, ∏ J, F I J) = ∏ I, ∏ J, atLog D lam Λ C wq b (F I J) := by
  simp only [atLog_eq, map_prod]

def eTwo (k : ℕ) : Fin (k + k) ≃ Fin k × Fin 2 := (finCongr (by omega : k + k = k * 2)).trans finProdFinEquiv.symm

theorem tensFact_of (hTB : TaylorProductOverBlocks) : TensFact := by
  intro D cc δ B hcc hδ p _ hp5 hin lam H N N' hN hN' s hs
  obtain ⟨n, rfl⟩ := hN
  obtain ⟨n', rfl⟩ := hN'
  have hp2 : p ≠ 2 := by omega
  obtain ⟨r, b, hloc, hon, -⟩ := (H 0 (tors_zero p _)).2.1
  refine ⟨n' * n * r, bB (eTwo n') (eTwo n) b, locBasis_bB (eTwo n') (eTwo n) p b hloc,
    orth_bB (eTwo n') (eTwo n) b hon, fun C wq hC hW => ?_⟩
  have hfun : U D B.tor s (B.thZero (n + n) (n' + n')) = fun z => ∏ I, ∏ J,
      U D B.tor (prjB (eTwo n') (eTwo n) I J s) (B.thZero 2 2) (blkPt D (eTwo n') (eTwo n) I J z) :=
    funext (U_tensPow (eTwo n') (eTwo n) B.tor B.thMM s)
  have hH := fun I J => H _ (torsB (eTwo n') (eTwo n) B.tor p I J s hs)
  rw [hfun, pSer_blk (eTwo n') (eTwo n) lam hTB _ (fun I J => (hH I J).1), atLog_prod]
  simp_rw [atLog_rename]
  rw [ePh_blk lam _ C wq hp2 r]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib, ← map_mul]
  exact integralMv_prod _ _ fun I _ => integralMv_prod _ _ fun J _ =>
    integralMv_rename _ ((hH I J).2.2 C wq r b hC hW hloc hon)

end Part8

end Formalism.L2.KerInert.IntTens

namespace Formalism.L2.KerInert

theorem taylor_product_over_blocks : TaylorProductOverBlocks := IntTens.taylor_product_blocks_factorization

theorem tensor_matrix_units_fact : TensFact := IntTens.tensFact_of taylor_product_over_blocks

end Formalism.L2.KerInert
