import Formalism.WachLatticeTwists.SandwichH1Classes.SandwichH1Proofs.SandwichCompositeOnH1

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

variable {ℓ : ℕ} [Fact ℓ.Prime] (Tt : TateTr ℓ) {r : ℕ}

lemma Vi_apply (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (t q : Fin r) :
    Tt.Vi Vm w j t q = algebraMap ℤ_[ℓ] Tt.Om ((w ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * Vm q t := rfl

lemma gXI_coe (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (v : Fin r → Tt.Xm) (t : Fin r) :
    ((Tt.gXI Vm w j v t : Tt.Xm) : Tt.Oi) = ∑ q, Tt.Vi Vm w j t q • Tt.g0 (v q : Tt.Oi) := by
  show ((matAct (Tt.Vi Vm w j) Tt.gX v t : Tt.Xm) : Tt.Oi) = _
  rw [matAct_apply]
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]
  rfl

lemma gmI_apply (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (v : Fin r → Tt.Om) :
    Tt.gmI Vm w j v = fun t => ∑ q, Tt.Vi Vm w j t q * v q := by
  show matAct (Tt.Vi Vm w j) LinearMap.id v = _
  rw [matAct_apply]
  rfl

lemma gmI_smul (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (a : Tt.Om) (v : Fin r → Tt.Om) :
    Tt.gmI Vm w j (a • v) = a • Tt.gmI Vm w j v :=
  (matAct (Tt.Vi Vm w j) LinearMap.id).map_smul a v

lemma pr_zsmul (c : ℤ_[ℓ]) (y : Tt.Oi) : Tt.pr (c • y) = c • Tt.pr y := by
  rw [← algebraMap_smul Tt.Om c y, map_smul, algebraMap_smul]

lemma ht_kill {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V] (f : V →ₗ[ℤ_[ℓ]] V) (w : ℤ_[ℓ]ˣ)
    (U : Finset ℤ) (i u : ℤ) (hu : u ∈ U) (x : V) (hx : f x = ((w ^ (i - u) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x) :
    aeval f (HTpoly ℓ w U i) x = 0 := by
  unfold HTpoly
  rw [← Finset.prod_erase_mul U _ hu, map_mul, Module.End.mul_apply]
  have : aeval f (X - C (((w ^ (i - u) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) x = 0 := by
    rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, hx, sub_self]
  rw [this, map_zero]

theorem htW : StatHTW := by
  intro ℓ _ Tt r Vm w U htf ⟨N, B, B', u, hu, _, hB'B, hrel⟩ hinj i
  set al := algebraMap Tt.Om Tt.Oi with hal
  let Bm : Matrix (Fin r) (Fin r) Tt.Om := fun k t => Tt.pr (B k t)
  let Bm' : Matrix (Fin r) (Fin r) Tt.Om := fun k t => Tt.pr (B' k t)

  have R2 : ∀ k t, ∑ q, Vm q t * Bm k q = ((w ^ (-(u k)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • Bm k t := by
    intro k t
    have := congrArg Tt.pr (hrel k t)
    rw [map_sum, pr_zsmul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm (Tt.g0 (B k q)), ← Algebra.smul_def, map_smul, Tt.pr_comp_g_zero, smul_eq_mul]

  have hB : ∀ k t, B k t = al (Bm k t) := by
    intro k
    let v : Fin r → Tt.Xm := fun t => ⟨B k t - al (Bm k t), by
      show Tt.pr (B k t - al (Bm k t)) = 0
      rw [map_sub, Tt.pr_alg, sub_self]⟩
    have hv : Tt.gXI Vm w (u k) v = v := by
      funext t
      apply Subtype.ext
      rw [gXI_coe]
      show ∑ q, Tt.Vi Vm w (u k) t q • Tt.g0 (B k q - al (Bm k q)) = B k t - al (Bm k t)
      have e1 : ∀ q, Tt.Vi Vm w (u k) t q • Tt.g0 (B k q - al (Bm k q))
          = ((w ^ (u k) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (Tt.g0 (B k q) * al (Vm q t) - al (Vm q t * Bm k q)) := by
        intro q
        rw [Vi_apply, map_sub, AlgHom.commutes, Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_mul]
        ring
      rw [Finset.sum_congr rfl fun q _ => e1 q, ← Finset.smul_sum, Finset.sum_sub_distrib, hrel k t,
        ← map_sum, R2 k t]
      have e2 : al (((w ^ (-(u k)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • Bm k t)
          = ((w ^ (-(u k)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • al (Bm k t) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
      rw [e2, ← smul_sub, smul_smul, ← Units.val_mul, ← _root_.zpow_add]
      simp
    have h0 := hinj (u k) (hu k) v hv
    intro t
    have := congrArg (fun z : Tt.Xm => (z : Tt.Oi)) (congrFun h0 t)
    exact sub_eq_zero.mp this

  have h1 : Bm' * Bm = ((ℓ : Tt.Om) ^ N) • (1 : Matrix (Fin r) (Fin r) Tt.Om) := by
    ext k t
    have := congrArg Tt.pr (congrFun (congrFun hB'B k) t)
    rw [Matrix.mul_apply, map_sum] at this
    rw [Matrix.mul_apply]
    have e3 : ∀ q, Tt.pr (B' k q * B q t) = Bm' k q * Bm q t := by
      intro q
      rw [hB q t, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl fun q _ => e3 q] at this
    rw [this]
    have e4 : (((ℓ : Tt.Oi) ^ N) • (1 : Matrix (Fin r) (Fin r) Tt.Oi)) k t
        = al ((((ℓ : Tt.Om) ^ N) • (1 : Matrix (Fin r) (Fin r) Tt.Om)) k t) := by
      by_cases h : k = t <;> simp [Matrix.one_apply, h, hal]
    rw [e4, Tt.pr_alg]

  have heig : ∀ k, Tt.gmI Vm w i (Bm k) = ((w ^ (i - u k) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • Bm k := by
    intro k
    rw [gmI_apply]
    funext t
    have e5 : ∀ q, Tt.Vi Vm w i t q * Bm k q
        = algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (Vm q t * Bm k q) := by
      intro q
      rw [Vi_apply, mul_assoc]
    rw [Finset.sum_congr rfl fun q _ => e5 q, ← Finset.mul_sum, R2 k t, ← Algebra.smul_def, smul_smul,
      ← Units.val_mul, ← _root_.zpow_add, Pi.smul_apply, sub_eq_add_neg]

  apply LinearMap.ext
  intro v
  set P := aeval (Tt.gmI Vm w i) (HTpoly ℓ w U i) with hP
  have hdec : ((ℓ : ℤ_[ℓ]) ^ N) • v = ∑ k, (v ᵥ* Bm') k • Bm k := by
    rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, h1, Matrix.vecMul_smul, Matrix.vecMul_one]
    funext t
    simp [Algebra.smul_def]
  have hz : ((ℓ : ℤ_[ℓ]) ^ N) • P v = 0 := by
    rw [← map_smul, hdec, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    apply ht_kill _ w U i (u k) (hu k)
    rw [gmI_smul, heig k, smul_comm]
  have tf : ∀ (n : ℕ) (y : Fin r → Tt.Om), ((ℓ : ℤ_[ℓ]) ^ n) • y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      apply ih
      rw [pow_succ', mul_smul] at hy
      funext t
      exact htf _ (congrFun hy t)
  exact tf N _ hz

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
