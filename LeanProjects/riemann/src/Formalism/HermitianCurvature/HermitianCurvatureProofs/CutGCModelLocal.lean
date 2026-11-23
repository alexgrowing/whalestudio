import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section loc

variable {r : ℕ} {TT : ℝ}

def LocOpQ (T : Module.End ℂ (MA.SmQ r TT)) : Prop :=
  ∀ (h₁ h₂ : MA.SmQ r TT) (c : Fin r → ℂ) (V : Set ℂ), IsOpen V →
    (∀ q : MA.Qp r TT, q.1.1 = c → q.1.2 ∈ V → (h₁ : MA.Qp r TT → ℂ) q = (h₂ : MA.Qp r TT → ℂ) q) →
    ∀ q : MA.Qp r TT, q.1.1 = c → q.1.2 ∈ V → (T h₁ : MA.Qp r TT → ℂ) q = (T h₂ : MA.Qp r TT → ℂ) q

theorem locOp_add {T S : Module.End ℂ (MA.SmQ r TT)} (hT : LocOpQ T) (hS : LocOpQ S) : LocOpQ (T + S) := by
  intro h₁ h₂ c V hV hag q hq hqV
  have e : ∀ h : MA.SmQ r TT, (((T + S) h : MA.SmQ r TT) : MA.Qp r TT → ℂ) q =
      (T h : MA.Qp r TT → ℂ) q + (S h : MA.Qp r TT → ℂ) q := fun h => rfl
  rw [e, e, hT h₁ h₂ c V hV hag q hq hqV, hS h₁ h₂ c V hV hag q hq hqV]

theorem locOp_mul {T S : Module.End ℂ (MA.SmQ r TT)} (hT : LocOpQ T) (hS : LocOpQ S) : LocOpQ (T * S) :=
  fun h₁ h₂ c V hV hag q hq hqV =>
    hT (S h₁) (S h₂) c V hV (fun q' hq' hqV' => hS h₁ h₂ c V hV hag q' hq' hqV') q hq hqV

theorem locOp_smul (z : ℂ) {T : Module.End ℂ (MA.SmQ r TT)} (hT : LocOpQ T) : LocOpQ (z • T) := by
  intro h₁ h₂ c V hV hag q hq hqV
  have e : ∀ h : MA.SmQ r TT, (((z • T) h : MA.SmQ r TT) : MA.Qp r TT → ℂ) q =
      z * (T h : MA.Qp r TT → ℂ) q := fun h => rfl
  rw [e, e, hT h₁ h₂ c V hV hag q hq hqV]

theorem locOp_zero : LocOpQ (0 : Module.End ℂ (MA.SmQ r TT)) :=
  fun _ _ _ _ _ _ _ _ _ => rfl

theorem locOp_one : LocOpQ (1 : Module.End ℂ (MA.SmQ r TT)) :=
  fun _ _ _ _ _ hag q hq hqV => hag q hq hqV

theorem locOp_sum {ι : Type} (s : Finset ι) (T : ι → Module.End ℂ (MA.SmQ r TT)) (hT : ∀ i ∈ s, LocOpQ (T i)) :
    LocOpQ (∑ i ∈ s, T i) := by
  classical
  revert hT
  refine Finset.induction_on s (fun _ => by simpa using locOp_zero) ?_
  intro i s hi ih hT
  rw [Finset.sum_insert hi]
  exact locOp_add (hT i (Finset.mem_insert_self i s)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem locOp_mulOp (f : MA.SmQ r TT) : LocOpQ ((MA.anQ r TT).mulOp f) := by
  intro h₁ h₂ c V hV hag q hq hqV
  show ((f * h₁ : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = ((f * h₂ : MA.SmQ r TT) : MA.Qp r TT → ℂ) q
  simp only [Subalgebra.coe_mul, Pi.mul_apply]
  rw [hag q hq hqV]

theorem dirE_zeta (v : M.Var r) (hv : ((ofLex v).1 : ℕ) = r) : MA.dirE v = ((0 : Fin r → ℂ), (1 : ℂ)) := by
  unfold MA.dirE
  rw [dif_neg (by omega)]

theorem fderiv_zeta_local {f₁ f₂ : MA.Qp r TT → ℂ} (hf₁ : f₁ ∈ MA.smSub r TT) (hf₂ : f₂ ∈ MA.smSub r TT)
    (c : Fin r → ℂ) (V : Set ℂ) (hV : IsOpen V)
    (hag : ∀ q : MA.Qp r TT, q.1.1 = c → q.1.2 ∈ V → f₁ q = f₂ q)
    (q : MA.Qp r TT) (hq : q.1.1 = c) (hqV : q.1.2 ∈ V) (w : ℂ) :
    fderiv ℝ (MA.ext f₁) q.1 ((0 : Fin r → ℂ), w) = fderiv ℝ (MA.ext f₂) q.1 ((0 : Fin r → ℂ), w) := by
  set γ : ℝ → MA.E r := fun t => q.1 + t • ((0 : Fin r → ℂ), w) with hγ
  have hγd : HasDerivAt γ ((0 : Fin r → ℂ), w) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const ((0 : Fin r → ℂ), w)).const_add q.1
    rw [one_smul] at h
    exact h
  have hγ0 : γ 0 = q.1 := by simp [hγ]
  have hq0 : γ 0 ∈ MA.Qset r TT := by rw [hγ0]; exact q.2
  have h1 : HasDerivAt (MA.ext f₁ ∘ γ) (fderiv ℝ (MA.ext f₁) (γ 0) ((0 : Fin r → ℂ), w)) 0 :=
    (MA.ext_smooth_diff hf₁ (γ 0) hq0).hasFDerivAt.comp_hasDerivAt 0 hγd
  have h2 : HasDerivAt (MA.ext f₂ ∘ γ) (fderiv ℝ (MA.ext f₂) (γ 0) ((0 : Fin r → ℂ), w)) 0 :=
    (MA.ext_smooth_diff hf₂ (γ 0) hq0).hasFDerivAt.comp_hasDerivAt 0 hγd

  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hQ : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ MA.Qset r TT :=
    hγc.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact (MA.Qset_open r TT).mem_nhds q.2)
  have hV' : ∀ᶠ t in 𝓝 (0 : ℝ), (γ t).2 ∈ V :=
    (continuous_snd.comp hγc).continuousAt.preimage_mem_nhds (by
      show V ∈ 𝓝 ((γ 0).2)
      rw [hγ0]; exact hV.mem_nhds hqV)
  have heq : MA.ext f₁ ∘ γ =ᶠ[𝓝 0] MA.ext f₂ ∘ γ := by
    filter_upwards [hQ, hV'] with t ht htV
    simp only [Function.comp_apply, MA.ext, dif_pos ht]
    refine hag ⟨γ t, ht⟩ ?_ htV
    show (q.1 + t • ((0 : Fin r → ℂ), w)).1 = c
    simp [hq]
  have := h1.unique (h2.congr_of_eventuallyEq heq)
  rwa [hγ0] at this

theorem locOp_euler (v : M.Var r) (hv : ((ofLex v).1 : ℕ) = r) : LocOpQ (MA.eulerQ (TT := TT) v) := by
  intro h₁ h₂ c V hV hag q hq hqV
  show MA.coordE v q.1 * MA.wirt v (MA.ext h₁.1) q.1 = MA.coordE v q.1 * MA.wirt v (MA.ext h₂.1) q.1
  unfold MA.wirt
  rw [dirE_zeta v hv]
  have hI : Complex.I • ((0 : Fin r → ℂ), (1 : ℂ)) = ((0 : Fin r → ℂ), Complex.I) := by
    ext <;> simp
  rw [hI, fderiv_zeta_local h₁.2 h₂.2 c V hV hag q hq hqV 1, fderiv_zeta_local h₁.2 h₂.2 c V hV hag q hq hqV Complex.I]

end loc

section ent

variable (P : M.Par)

def EntOK (A : MA.A P (MA.DQ P)) : Prop := ∀ π π', LocOpQ (A π π').1

theorem entOK_add {A B : MA.A P (MA.DQ P)} (hA : EntOK P A) (hB : EntOK P B) : EntOK P (A + B) :=
  fun π π' => locOp_add (hA π π') (hB π π')

theorem entOK_mul {A B : MA.A P (MA.DQ P)} (hA : EntOK P A) (hB : EntOK P B) : EntOK P (A * B) := by
  intro π π'
  rw [Matrix.mul_apply]
  have key : ∀ s : Finset (M.Ty P), LocOpQ (∑ j ∈ s, A π j * B j π').1 := by
    classical
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty]
      exact locOp_zero
    · intro j s hj ih
      rw [Finset.sum_insert hj]
      exact locOp_add (locOp_mul (hA π j) (hB j π')) ih
  exact key Finset.univ

theorem entOK_sum {ι : Type} (s : Finset ι) (A : ι → MA.A P (MA.DQ P)) (hA : ∀ i ∈ s, EntOK P (A i)) :
    EntOK P (∑ i ∈ s, A i) := by
  classical
  revert hA
  refine Finset.induction_on s (fun _ => by rw [Finset.sum_empty]; exact fun _ _ => locOp_zero) ?_
  intro i s hi ih hA
  rw [Finset.sum_insert hi]
  exact entOK_add P (hA i (Finset.mem_insert_self i s)) (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

theorem locOp_algebraMap (z : ℂ) : LocOpQ ((algebraMap ℂ (MA.DQ P).Pr z).1) := by
  rw [show (algebraMap ℂ (MA.DQ P).Pr z).1 = z • 1 by simp [Algebra.algebraMap_eq_smul_one]; rfl]
  exact locOp_smul z locOp_one

theorem entOK_algebraMap (z : ℂ) : EntOK P (algebraMap ℂ (MA.A P (MA.DQ P)) z) := by
  rw [Matrix.algebraMap_eq_diagonal]
  intro π π'
  by_cases h : π = π'
  · subst h
    rw [Matrix.diagonal_apply_eq]
    exact locOp_algebraMap P z
  · rw [Matrix.diagonal_apply_ne _ h]
    exact locOp_zero

theorem entOK_diag (x : M.Ty P → (MA.DQ P).Pr) (hx : ∀ π, LocOpQ (x π).1) : EntOK P (Matrix.diagonal x) := by
  intro π π'
  by_cases h : π = π'
  · subst h
    rw [Matrix.diagonal_apply_eq]
    exact hx π
  · rw [Matrix.diagonal_apply_ne _ h]
    exact locOp_zero

theorem entOK_sc (w : (MA.DQ P).Pr) (hw : LocOpQ w.1) : EntOK P (MA.sc P (MA.DQ P) w) := by
  intro π π'
  unfold MA.sc
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hw
  · exact locOp_zero

theorem entOK_fnP (f fb : (MA.DQ P).R) : EntOK P (MA.sc P (MA.DQ P) ((MA.DQ P).fnP f fb)) :=
  entOK_sc P _ (locOp_mulOp f)

theorem entOK_kap (φ : M.Ty P → ℂ) : EntOK P (MA.kap P (MA.DQ P) φ) := by
  intro π π'
  simp only [MA.kap, AlgHom.comp_apply, Matrix.diagonalAlgHom_apply, Matrix.diagonal_apply]
  split_ifs
  · exact locOp_algebraMap P _
  · exact locOp_zero

theorem entOK_SS (l : ℕ) : EntOK P (MA.SS P (MA.DQ P) l) := by
  intro π π'
  unfold MA.SS
  simp only [Matrix.of_apply]
  split_ifs
  · exact locOp_algebraMap P _
  · exact locOp_zero

theorem entOK_star_SS (l : ℕ) : EntOK P (star (MA.SS P (MA.DQ P) l)) := by
  intro π π'
  rw [Matrix.star_apply]
  unfold MA.SS
  simp only [Matrix.of_apply]
  split_ifs
  · rw [← algebraMap_star_comm]; exact locOp_algebraMap P _
  · rw [star_zero]; exact locOp_zero

theorem locOp_dz : LocOpQ (MA.DQ P).dzP.1 := by
  show LocOpQ ((MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) * (MA.DQ P).ev M.vz)
  exact locOp_mul (locOp_mulOp _) (locOp_euler M.vz (by simp [M.vz]))

theorem locOp_dzb : LocOpQ (MA.DQ P).dzbP.1 := by
  show LocOpQ ((MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) * (MA.DQ P).ev M.vzb)
  exact locOp_mul (locOp_mulOp _) (locOp_euler M.vzb (by simp [M.vzb]))

theorem locOp_fnP (f fb : (MA.DQ P).R) : LocOpQ ((MA.DQ P).fnP f fb).1 := locOp_mulOp f

theorem entOK_nab : EntOK P (MA.nabA P (MA.DQ P)) := by
  refine entOK_diag P _ fun π => ?_
  show LocOpQ ((MA.DQ P).dzP.1 + (M.aC P π : ℂ) • ((MA.DQ P).mulOp ((MA.DQ P).x M.vzb) *
    (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).gg P.TT))))
  exact locOp_add (locOp_dz P) (locOp_smul _ (locOp_mul (locOp_mulOp _) (locOp_mulOp _)))

theorem entOK_nabs : EntOK P (MA.nabsA P (MA.DQ P)) := by
  refine entOK_diag P _ fun π => ?_
  show LocOpQ (-(MA.DQ P).dzbP.1 + (M.aC P π : ℂ) • ((MA.DQ P).mulOp ((MA.DQ P).x M.vz) *
    (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).gg P.TT))))
  refine locOp_add ?_ (locOp_smul _ (locOp_mul (locOp_mulOp _) (locOp_mulOp _)))
  rw [show -(MA.DQ P).dzbP.1 = (-1 : ℂ) • (MA.DQ P).dzbP.1 by rw [neg_one_smul]]
  exact locOp_smul _ (locOp_dzb P)

theorem entOK_smulA (z : ℂ) {A : MA.A P (MA.DQ P)} (hA : EntOK P A) : EntOK P (z • A) := by
  intro π π'
  exact locOp_smul z (hA π π')

private theorem locOpQ_neg {r : ℕ} {TT : ℝ} {T : Module.End ℂ (MA.SmQ r TT)} (hT : LocOpQ T) :
    LocOpQ (-T) := by
  intro h₁ h₂ c V hV hag q hq hqV
  have e : ∀ h : MA.SmQ r TT, (((-T) h : MA.SmQ r TT) : MA.Qp r TT → ℂ) q =
      -(T h : MA.Qp r TT → ℂ) q := fun h => rfl
  rw [e, e, hT h₁ h₂ c V hV hag q hq hqV]

theorem entOK_neg {A : MA.A P (MA.DQ P)} (hA : EntOK P A) : EntOK P (-A) :=
  fun π π' => locOpQ_neg (hA π π')

theorem entOK_sub {A B : MA.A P (MA.DQ P)} (hA : EntOK P A) (hB : EntOK P B) : EntOK P (A - B) := by
  rw [sub_eq_add_neg]
  exact entOK_add P hA (entOK_neg P hB)

theorem entOK_QQr (Y : ℂ) (a b : Fin 2) : EntOK P (MA.QQr P (MA.DQ P) Y a b) := by
  have hz : EntOK P (MA.zA P (MA.DQ P)) := entOK_fnP P _ _
  have hzb : EntOK P (MA.zbA P (MA.DQ P)) := entOK_fnP P _ _
  have hgg : EntOK P (MA.ggA P (MA.DQ P)) := entOK_fnP P _ _
  have hggi : EntOK P (MA.ggiA P (MA.DQ P)) := entOK_fnP P _ _
  have hx : EntOK P (MA.xA P (MA.DQ P) Y) := entOK_kap P _
  have hl0 : EntOK P (MA.l0A P (MA.DQ P) Y) :=
    entOK_sub P (entOK_neg P (entOK_nab P)) (entOK_mul P (entOK_algebraMap P _) (entOK_mul P hzb hggi))
  have hm0 : EntOK P (MA.m0A P (MA.DQ P) Y) :=
    entOK_sub P (entOK_neg P (entOK_nabs P)) (entOK_mul P (entOK_algebraMap P _) (entOK_mul P hz hggi))
  have hS21 : EntOK P (MA.weightedSumBis P (MA.DQ P) Y) :=
    entOK_sum P _ _ fun l _ => entOK_mul P (entOK_SS P l) (entOK_kap P _)
  have hS12 : EntOK P (MA.S12 P (MA.DQ P) Y) :=
    entOK_sum P _ _ fun l _ => entOK_mul P (entOK_kap P _) (entOK_star_SS P l)
  have hS4 : EntOK P (MA.S4 P (MA.DQ P) Y) :=
    entOK_sum P _ _ fun l _ => entOK_sum P _ _ fun j _ =>
      entOK_mul P (entOK_mul P (entOK_star_SS P l) (entOK_SS P j)) (entOK_kap P _)
  fin_cases a <;> fin_cases b
  · show EntOK P (MA.t11 P (MA.DQ P) Y)
    unfold MA.t11
    exact entOK_add P (entOK_add P (entOK_add P (entOK_add P (entOK_mul P hggi (entOK_kap P _))
      (entOK_mul P (entOK_mul P (entOK_mul P hgg hx) hm0) hl0))
      (entOK_mul P (entOK_mul P (entOK_mul P hgg hm0) hggi) hS21)) (entOK_mul P hS12 hl0)) (entOK_mul P hggi hS4)
  · show EntOK P (MA.t12 P (MA.DQ P) Y)
    unfold MA.t12
    exact entOK_add P (entOK_mul P (entOK_mul P hgg hx) hm0) hS12
  · show EntOK P (MA.t21 P (MA.DQ P) Y)
    unfold MA.t21
    exact entOK_add P (entOK_mul P (entOK_mul P hgg hx) hl0) hS21
  · show EntOK P (MA.t22 P (MA.DQ P) Y)
    unfold MA.t22
    exact entOK_mul P hgg hx

end ent

theorem smq_sum_apply {r : ℕ} {TT : ℝ} {ι : Type} (s : Finset ι) (F : ι → MA.SmQ r TT) (q : MA.Qp r TT) :
    ((∑ i ∈ s, F i : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = ∑ i ∈ s, (F i : MA.Qp r TT → ℂ) q := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty]; rfl) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

theorem model_locality_holds : ModelLocal := by
  intro P f g c V hV hag Y a b ρ q hq hqV
  have hE := entOK_QQr P Y a b
  show ((∑ π', (MA.QQr P (MA.DQ P) Y a b ρ π').1 (f π') : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
    ((∑ π', (MA.QQr P (MA.DQ P) Y a b ρ π').1 (g π') : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q
  refine (smq_sum_apply (r := P.r) (TT := P.TT) Finset.univ
    (fun π' => (MA.QQr P (MA.DQ P) Y a b ρ π').1 (f π')) q).trans ?_
  refine Eq.trans ?_ (smq_sum_apply (r := P.r) (TT := P.TT) Finset.univ
    (fun π' => (MA.QQr P (MA.DQ P) Y a b ρ π').1 (g π')) q).symm
  exact Finset.sum_congr rfl fun π' _ =>
    hE ρ π' (f π') (g π') c V hV (fun q' hq' hq'V => hag π' q' hq' hq'V) q hq hqV

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
