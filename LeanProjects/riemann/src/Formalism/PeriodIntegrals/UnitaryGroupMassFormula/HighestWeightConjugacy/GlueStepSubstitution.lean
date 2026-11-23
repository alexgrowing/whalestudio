import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.ChangeOfDens

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open Classical in

def subT (τ : L →+* ℂ) : Vars L n → MvPolynomial (Bool × Fin n × Fin n) ℂ := fun p =>
  if p.1 = τ then MvPolynomial.X (true, p.2.1, p.2.2)
  else if p.1 = ComplexEmbedding.conjugate τ then MvPolynomial.X (false, p.2.1, p.2.2)
  else MvPolynomial.C (if p.2.1 = p.2.2 then 1 else 0)

theorem eval_subT (τ : L →+* ℂ) (g : GL (Fin n) ℂ) :
    (fun p => MvPolynomial.eval (gPt g) (subT τ p)) = evPt τ g := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  unfold subT evPt
  split_ifs <;> simp_all [gPt]

end

theorem glue_holds_var : GlueStep := by
  intro hd hg L _ _ _ n a τ lam mu h1 h2
  obtain ⟨ι, hι, hdι, b, P, hP, v, hv0, hv⟩ := h1
  obtain ⟨ι', hι', hdι', b', P', hP', u, hu0, hu⟩ := h2
  have ratM : ∀ (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n),
      evM P (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) = LinearMap.toMatrix b b (a.ρ (toGQ γ₀ hγ)) :=
    fun γ₀ hγ => by rw [hP _ γ₀ (toGQ_val γ₀ hγ)]; rfl
  have ratM' : ∀ (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n),
      evM P' (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) = LinearMap.toMatrix b' b' (a.ρ (toGQ γ₀ hγ)) :=
    fun γ₀ hγ => by rw [hP' _ γ₀ (toGQ_val γ₀ hγ)]; rfl
  have multP : ∀ y z, InV y → InV z → evM P (vmul y z) = evM P y * evM P z :=
    mult_of_dens hd P (fun γ₀ hγ δ₀ hδ => by
      rw [ratM _ (Subgroup.mul_mem _ hγ hδ), ratM γ₀ hγ, ratM δ₀ hδ, toGQ_mul, map_mul, LinearMap.toMatrix_mul])
  have changeP : ∀ y, InV y → evM P y = b.toMatrix b' * evM P' y * b'.toMatrix b :=
    change_of_dens hd P P' _ _ (fun γ₀ hγ => by
      rw [ratM γ₀ hγ, ratM' γ₀ hγ]
      exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' b b' _).symm)
  let R : GL (Fin n) ℂ → Matrix ι ι ℂ := fun g => evM P (evPt τ g)
  let Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ := fun i j => MvPolynomial.aeval (subT τ) (P i j)
  have hRQ : ∀ g i j, R g i j = MvPolynomial.eval (gPt g) (Q i j) := by
    intro g i j
    simp only [R, Q, evM, Matrix.of_apply, eval_aeval_eq, eval_subT]
  have hRmul : ∀ g h, R (g * h) = R g * R h := by
    intro g h
    simp only [R]
    rw [evPt_mul]
    exact multP _ _ (inV_evPt τ g) (inV_evPt τ h)
  let S : Set (Matrix ι ι ℂ) := {s | ∃ y, InV y ∧
    (∀ i j, y (τ, i, j) = (if i = j then 1 else 0) ∧ y (ComplexEmbedding.conjugate τ, i, j) = (if i = j then 1 else 0)) ∧
    s = evM P y}
  have hS : ∀ s ∈ S, ∀ g, s * R g = R g * s := by
    rintro s ⟨y, hy, hy1, rfl⟩ g
    simp only [R]
    rw [← multP _ _ hy (inV_evPt τ g), ← multP _ _ (inV_evPt τ g) hy, vmul_comm_evPt τ y hy1 g]
  have hspan : ∀ x : a.W, x ≠ 0 → Submodule.span ℂ
      {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) (b.equivFun x))} = ⊤ := by
    intro x hx
    rw [eq_top_iff, ← span_orbit a b x hx]
    apply Submodule.span_mono
    rintro w ⟨γ, rfl⟩
    obtain ⟨γ₀, hγ, rfl⟩ := toGQ_surj γ
    refine ⟨evM P (trivAt τ (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))),
      ⟨_, inV_trivAt τ _ (inV_ratPt γ₀ hγ), fun i j => ⟨trivAt_tau τ _ i j, trivAt_conj τ _ i j⟩, rfl⟩,
      Matrix.GeneralLinearGroup.map τ γ₀, ?_⟩
    rw [Matrix.mulVec_mulVec, ← ratM γ₀ hγ]
    simp only [R]
    rw [← multP _ _ (inV_trivAt τ _ (inV_ratPt γ₀ hγ)) (inV_evPt τ _), ← ratPt_split τ γ₀ hγ]
  let x' : a.W := b'.equivFun.symm u
  have hx' : x' ≠ 0 := by
    intro h
    apply hu0
    rw [← b'.equivFun.apply_symm_apply u]
    change b'.equivFun x' = 0
    rw [h, map_zero]
  have hxu : b.equivFun x' = Matrix.mulVec (b.toMatrix b') u := by
    have h3 := LinearMap.toMatrix_mulVec_repr b' b LinearMap.id x'
    rw [LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.id_apply] at h3
    rw [Module.Basis.equivFun_apply, ← h3]
    congr 1
    exact b'.equivFun.apply_symm_apply u
  have hv' : b.equivFun (b.equivFun.symm v) = v := b.equivFun.apply_symm_apply v
  have hvx : b.equivFun.symm v ≠ 0 := by
    intro h; apply hv0; rw [← hv', h, map_zero]
  have hũ0 : Matrix.mulVec (b.toMatrix b') u ≠ 0 := by
    rw [← hxu]; intro h; exact hx' (b.equivFun.injective (by rw [h, map_zero]))
  have huB : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id →
      Matrix.mulVec (R B) (Matrix.mulVec (b.toMatrix b') u) = (∏ i, B.val i i ^ mu i) • Matrix.mulVec (b.toMatrix b') u := by
    intro B hB
    have hc := changeP _ (inV_evPt τ B)
    simp only [R]
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_assoc, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
    have hu' := hu B hB
    change Matrix.mulVec (evM P' (evPt τ B)) u = _ at hu'
    rw [hu', Matrix.mulVec_smul]
  have spv := hspan _ hvx
  rw [hv'] at spv
  have spu := hspan _ hx'
  rw [hxu] at spu
  exact hg n ι R Q hRQ hRmul S hS v _ lam mu (fun B hB => hv B hB) huB spv spu hv0 hũ0

end PI.UnitaryGroupMassFormula.HwConjInf
