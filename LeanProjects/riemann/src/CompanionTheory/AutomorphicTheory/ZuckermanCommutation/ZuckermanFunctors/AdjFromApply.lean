import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.MultOne

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem cMT_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * Bᵀ = 1) :
    (cM n)ᵀ * (1 : Matrix Unit Unit ℂ) = (A ⊗ₖ B) * (cM n)ᵀ := by
  ext ⟨i, j⟩ u
  rw [Matrix.mul_one]
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hij
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cM, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [← hij]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

private theorem hpk_apply_lemma (k r : ℕ) (i l : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r i l = if (l : ℕ) = (if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i) then
      (if (i : ℕ) = r + k then -1 else 1) else 0 := by
  have hi := i.2
  have hl := l.2
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | rfl | omega | norm_num

private theorem hpk_mul_self_lemma_2 (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [Matrix.mul_apply]
  simp only [hpk_apply_lemma]
  rw [Finset.sum_eq_single ⟨if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i, by split_ifs <;> omega⟩]
  · simp only [Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega | norm_num
  · intro l _ hl
    rw [if_neg (fun h => hl (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem isUnit_det_lemma_3 {k r : ℕ} {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ BranchingSupport.GG k r) : IsUnit g.det := by
  have hH : (Formalism.QuantumDeterminants.Hpk k r).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (hpk_mul_self_lemma_2 k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hg' : g.conjTranspose * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hH
  rw [← hg', Matrix.det_mul, h0, mul_zero]

theorem cMT_hom (hM : MatHom) (b : Bool) (B : URep k r) :
    IsHom (one B) ((vr k r b).tens (vr k r (!b)), B) (mAct (cM _)ᵀ) := by
  refine hM k r (triv k r) ((vr k r b).tens (vr k r (!b))) B (cM _)ᵀ (fun g hg => ?_)
  have hinv : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (isUnit_det_lemma_3 hg)
  have hAB : (vr k r b).ρ g * ((vr k r (!b)).ρ g)ᵀ = 1 := by
    cases b <;> simp [vr, BranchingSupport.dualM, hinv, ← Matrix.transpose_mul]
  exact cMT_mul hAB

def uR (ι : Type) [DecidableEq ι] : Matrix (ι × Unit) ι ℂ := fun p d => if p.1 = d then 1 else 0

theorem uR_int (F : FRep k r) (g : Mx k r) : uR F.ι * F.ρ g = (F.tens (triv k r)).ρ g * uR F.ι := by
  ext ⟨i, u⟩ d
  cases u
  simp [Matrix.mul_apply, uR, FRep.tens, triv, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem uMT_int (F : FRep k r) (g : Mx k r) : (uM F.ι)ᵀ * ((triv k r).tens F).ρ g = F.ρ g * (uM F.ι)ᵀ := by
  ext d ⟨u, e⟩
  cases u
  simp [Matrix.mul_apply, uM, FRep.tens, triv, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

section

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def adjTo (p : (Fin n → V) →ₗ[ℂ] (Unit → V')) : (Unit → V) →ₗ[ℂ] (Fin n → V') :=
  mAct (uM (Fin n))ᵀ ∘ₗ (on1 p ∘ₗ mAct (cM n)ᵀ)

def adjFrom (i : (Unit → V) →ₗ[ℂ] (Fin n → V')) : (Fin n → V) →ₗ[ℂ] (Unit → V') :=
  mAct (cM n) ∘ₗ (on2 i ∘ₗ mAct (uR (Fin n)))

theorem adjTo_apply (p : (Fin n → V) →ₗ[ℂ] (Unit → V')) (x : Unit → V) (d : Fin n) :
    adjTo p x d = p (Pi.single d (x ())) () := by
  simp [adjTo, mAct_apply, uM, cM, on1, Fintype.sum_prod_type]
  have e : (LinearMap.funLeft ℂ V fun c => (c, d)) ((mAct (cM n)ᵀ) x) = Pi.single d (x ()) := by
    funext c
    simp [LinearMap.funLeft_apply, mAct_apply, cM, Matrix.transpose_apply, Pi.single_apply]
  rw [e]

theorem adjFrom_apply (i : (Unit → V) →ₗ[ℂ] (Fin n → V')) (y : Fin n → V) (u : Unit) :
    adjFrom i y u = ∑ c, i (fun _ => y c) c := by
  simp [adjFrom, mAct_apply, uR, cM, on2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  have e : (LinearMap.funLeft ℂ V fun d => (c, d)) ((mAct (uR (Fin n))) y) = fun _ => y c := by
    funext u
    simp [LinearMap.funLeft_apply, mAct_apply, uR]
  rw [e]

def adjEquiv : ((Fin n → V) →ₗ[ℂ] (Unit → V')) ≃ₗ[ℂ] ((Unit → V) →ₗ[ℂ] (Fin n → V')) where
  toFun := adjTo
  invFun := adjFrom
  map_add' p q := LinearMap.ext fun x => funext fun d => by simp [adjTo_apply]
  map_smul' a p := LinearMap.ext fun x => funext fun d => by simp [adjTo_apply]
  left_inv p := LinearMap.ext fun y => funext fun u => by
    rw [adjFrom_apply]
    simp only [adjTo_apply]
    rw [← Finset.sum_apply, ← map_sum, Finset.univ_sum_single]
  right_inv i := LinearMap.ext fun x => funext fun d => by
    rw [adjTo_apply, adjFrom_apply, Finset.sum_eq_single d]
    · simp
    · intro c _ hc
      rw [Pi.single_eq_of_ne hc]
      exact congrFun (map_zero i) c
    · simp

end

theorem adj_of (hC : HomCat) (hM : MatHom) (hT : TensHom) : Adj := by
  intro k r b U U'
  refine ⟨adjEquiv, fun p => ⟨fun hp => ?_, fun hq => ?_⟩⟩
  · have h1 := cMT_hom hM b U
    have h2 := (hT k r (vr k r b) (triv k r) (vr k r (!b)) U U' p hp).1
    have h3 : IsHom ((triv k r).tens (vr k r (!b)), U') (vr k r (!b), U') (mAct (uM (vr k r (!b)).ι)ᵀ) :=
      hM k r _ _ U' _ (fun g _ => uMT_int (vr k r (!b)) g)
    exact (hC k r).comp _ _ _ _ _ ((hC k r).comp _ _ _ _ _ h1 h2) h3
  · have h1 : IsHom (vr k r b, U) ((vr k r b).tens (triv k r), U) (mAct (uR (vr k r b).ι)) :=
      hM k r _ _ U _ (fun g _ => uR_int (vr k r b) g)
    have h2 := (hT k r (triv k r) (vr k r (!b)) (vr k r b) U U' (adjEquiv p) hq).2
    have h3 := cM_hom hM b U'
    have h4 := (hC k r).comp _ _ _ _ _ ((hC k r).comp _ _ _ _ _ h1 h2) h3
    rw [← adjEquiv.left_inv p]
    exact h4

end CompanionTheory.Zuck

end
