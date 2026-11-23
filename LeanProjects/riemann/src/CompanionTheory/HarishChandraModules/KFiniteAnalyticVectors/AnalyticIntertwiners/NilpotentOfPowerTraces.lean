import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial

open Matrix Topology Filter
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS Module.End

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem cpart_inK_A {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z * Jm ε = Jm ε * Z) :
    inK ε (S7.cpart1 ε Z) ∧ inK ε (S7.cpart2 ε Z) := by
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose_self
  have hZh : Zᴴ * Jm ε = Jm ε * Zᴴ := by
    have h := congrArg Matrix.conjTranspose hZ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hc : (Jm ε * Zᴴ * Jm ε) * Jm ε = Jm ε * (Jm ε * Zᴴ * Jm ε) := by
    simp only [Matrix.mul_assoc, hZh]
  refine ⟨⟨SmDerA.inG_cpart1 ε Z, ?_⟩, ⟨SmDerA.inG_cpart2 ε Z, ?_⟩⟩
  · unfold S7.cpart1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, hZ, hc]
  · unfold S7.cpart2
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hZ, hc]

theorem single_comm_A {a b : Fin n} (hab : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all

theorem dS_mem_of_inK_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {S : Submodule ℂ H}
    [FiniteDimensional ℂ S] (hK : Formalism.MainNotions.S.IsKStableOn ε σ S) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    {s : H} (hs : s ∈ S) (hsm : s ∈ smD ε σ) : dS σ Z s ∈ S := by
  have hd := hasDerivAt_dS hσ hZ.1 ((mem_smD_iff ε σ s).1 hsm)
  have ht := hd.tendsto_slope_zero
  have hcl : IsClosed (S : Set H) := Submodule.closed_of_finiteDimensional S
  refine hcl.mem_of_tendsto ht (Eventually.of_forall fun t => ?_)
  have hZt : inK ε (((t : ℝ) : ℂ) • Z) := by
    obtain ⟨h1, h2⟩ := hZ
    refine ⟨?_, ?_⟩
    · unfold inG at h1 ⊢
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal,
        ← smul_add, h1, smul_zero]
    · rw [Matrix.smul_mul, Matrix.mul_smul, h2]
  have h1 : σ (NormedSpace.exp (((0 + t : ℝ) : ℂ) • Z)) s ∈ S := by
    rw [zero_add]; exact hK _ (exp_mem_Kset hZt) s hs
  have h0 : σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) s = s := by
    rw [exp_zero_smul, hσ.1.1]; rfl
  simp only [zero_add] at h1
  show (t⁻¹ : ℝ) • (σ (NormedSpace.exp (((0 + t : ℝ) : ℂ) • Z)) s - σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) s) ∈ S
  rw [zero_add, h0]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ h1 hs)

theorem smE_mem_of_compact_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {S : Submodule ℂ H}
    [FiniteDimensional ℂ S] (hK : Formalism.MainNotions.S.IsKStableOn ε σ S) {a b : Fin n} (hab : ε a = ε b) (x : smD ε σ)
    (hx : (x : H) ∈ S) : ((smE ε σ a b x : smD ε σ) : H) ∈ S := by
  obtain ⟨h1, h2⟩ := cpart_inK_A (single_comm_A hab)
  rw [smE_apply hσ]
  exact Submodule.add_mem _ (dS_mem_of_inK_A hσ hK h1 hx x.2) (Submodule.smul_mem _ _ (dS_mem_of_inK_A hσ hK h2 hx x.2))

theorem exp_two_pi_A (a : Fin n) :
    NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ))) = 1 := by
  rw [show ((2 * Real.pi : ℝ) : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ)) =
      Matrix.diagonal (Pi.single a (2 * Real.pi * Complex.I)) by
    rw [smul_smul, Matrix.diagonal_single, Matrix.smul_single]
    simp]
  rw [Matrix.exp_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  by_cases h : i = a
  · subst h; simp [← Complex.exp_eq_exp_ℂ]
  · simp [h]

theorem inG_diag_A (a : Fin n) : inG ε (Complex.I • Matrix.single a a (1 : ℂ)) := by
  unfold inG
  have hc := single_comm_A (ε := ε) (a := a) (b := a) rfl
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_single, star_one, Matrix.smul_mul, Matrix.mul_smul, hc]
  simp

theorem eig_int_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (a : Fin n) {w : smD ε σ} (hw : w ≠ 0) {c : ℂ}
    (hc : smE ε σ a a w = c • w) : ∃ m : ℤ, c = m := by
  have hD := isDerivedOn_smE hσ
  set X : Matrix (Fin n) (Fin n) ℂ := Complex.I • Matrix.single a a (1 : ℂ)
  have hX : inG ε X := inG_diag_A a
  have hXw : actM (smE ε σ) X w = (Complex.I * c) • w := by
    rw [SmDerA.actM_smul, SmDerA.actM_single, LinearMap.smul_apply, hc, smul_smul]
  set f : ℝ → H := fun t => σ (NormedSpace.exp ((t : ℂ) • X)) (w : H)
  have hf : ∀ t, HasDerivAt f ((Complex.I * c) • f t) t := fun t => by
    have := hasDerivAt_orbit hσ hD hX w t
    rw [hXw, Submodule.coe_smul, map_smul] at this
    exact this
  set g : ℝ → H := fun t => Complex.exp (-(Complex.I * c) * t) • f t
  have hg : ∀ t, HasDerivAt g 0 t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(Complex.I * c) * t))
        (Complex.exp (-(Complex.I * c) * t) * (-(Complex.I * c))) t := by
      have := ((hasDerivAt_id (t : ℂ)).const_mul (-(Complex.I * c))).cexp
      have h2 := this.comp_ofReal (z := t)
      simpa using h2
    refine (h1.smul (hf t)).congr_deriv ?_
    rw [smul_smul, ← add_smul, mul_neg, add_neg_cancel, zero_smul]
  have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv)
    (2 * Real.pi) 0
  have h2pi : f (2 * Real.pi) = (w : H) := by
    show σ (NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • X)) (w : H) = (w : H)
    rw [exp_two_pi_A, hσ.1.1]; rfl
  have h0 : f 0 = (w : H) := by
    show σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) (w : H) = (w : H)
    rw [exp_zero_smul, hσ.1.1]; rfl
  simp only [g, h2pi, h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] at hconst
  have hw' : (w : H) ≠ 0 := fun h => hw (Subtype.ext h)
  have he : Complex.exp (-(Complex.I * c) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    by_contra hne
    have : (Complex.exp (-(Complex.I * c) * ((2 * Real.pi : ℝ) : ℂ)) - 1) • (w : H) = 0 := by
      rw [sub_smul, hconst, one_smul, sub_self]
    exact hw' ((smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne))
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 he
  refine ⟨-m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have : -(Complex.I * c) * ((2 * Real.pi : ℝ) : ℂ) = m * (2 * Real.pi * Complex.I) := hm
  push_cast at this ⊢
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hI)
  linear_combination (-1 : ℂ) * this

theorem integral_weights : IntWts := by
  intro n ε H _ _ _ σ hσ hirr v hv
  obtain ⟨S, hSf, hvS, hSK⟩ := hv
  have hU := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)
  have hE := (isDerivedOn_smE hσ).glRep
  let S₀ : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hS₀f : FiniteDimensional ℂ S₀ :=
    Module.Finite.of_injective (((smD ε σ).subtype.comp S₀.subtype).codRestrict S fun x => x.2)
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : H)) h)))
  have hst : ∀ a, ∀ x ∈ S₀, smE ε σ a a x ∈ S₀ := fun a x hx =>
    smE_mem_of_compact_A hσ hSK rfl x hx
  let T : Fin n → (S₀ →ₗ[ℂ] S₀) := fun a => (smE ε σ a a).restrict (hst a)
  have hT : ∀ a, (T a).IsSymmetric := fun a x y => by
    show ⟪((smE ε σ a a (x : smD ε σ) : smD ε σ)), (y : smD ε σ)⟫_ℂ = ⟪(x : smD ε σ), smE ε σ a a y⟫_ℂ
    rw [hU a a]; simp [adjSign]
  have hC : Pairwise (Function.onFun Commute T) := fun a b _ => by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show smE ε σ a a (smE ε σ b b x) = smE ε σ b b (smE ε σ a a x)
    have h := congrArg (fun f => f (x : smD ε σ)) (hE a a b b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    by_cases hab : a = b
    · subst hab; rfl
    · rw [if_neg hab, if_neg (Ne.symm hab), sub_self] at h
      exact sub_eq_zero.1 h
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  set G : Set (smD ε σ) := {w | w ∈ KF ε σ ∧ ∃ μ : Fin n → ℤ, ∀ a, smE ε σ a a w = (μ a : ℂ) • w}
  have hle : (⊤ : Submodule ℂ S₀) ≤ (Submodule.span ℂ G).comap S₀.subtype := by
    rw [← htop]
    refine iSup_le fun χ => fun x hx => ?_
    show (x : smD ε σ) ∈ Submodule.span ℂ G
    by_cases hx0 : x = 0
    · rw [hx0]; exact Submodule.zero_mem _
    refine Submodule.subset_span ⟨⟨S, hSf, x.2, hSK⟩, ?_⟩
    have hxa : ∀ a, smE ε σ a a x = χ a • (x : smD ε σ) := fun a => by
      have := (Submodule.mem_iInf _).1 hx a
      rw [Module.End.mem_eigenspace_iff] at this
      exact congrArg Subtype.val this
    have hx0' : (x : smD ε σ) ≠ 0 := fun h => hx0 (Subtype.ext h)
    choose μ hμ using fun a => eig_int_A hσ a hx0' (hxa a)
    exact ⟨μ, fun a => by rw [hxa a, hμ a]⟩
  exact hle (Submodule.mem_top (x := ⟨v, hvS⟩))

end CompanionTheory.D.gk.HC
