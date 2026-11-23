import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.RadialDecompositionOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.TopDensNonnegOfKappa

open Matrix Finset
open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Kfp

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Skew

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem inner_pres (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {h : Mx k r} (hh : h ∈ UWset k r z)
    (v w : W) : ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ := by
  let Li : W →ₗᵢ[ℂ] W := ⟨(π h : W →ₗ[ℂ] W), hu h hh⟩
  exact Li.inner_map_map v w

theorem dOp_skew (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {X : Mx k r} (hX : InLieW k r z X) (v w : W) :
    ⟪dOp π X v, w⟫_ℂ = -⟪v, dOp π X w⟫_ℂ := by
  have hd := dOp_hasDeriv hπ hc hX
  have h1 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (dOp π X v) 0 :=
    ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have h2 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) w) (dOp π X w) 0 :=
    ((ContinuousLinearMap.apply ℂ W w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have hI := h1.inner ℂ h2
  have hconst : (fun t : ℝ => ⟪π (NormedSpace.exp ((t : ℂ) • X)) v, π (NormedSpace.exp ((t : ℂ) • X)) w⟫_ℂ) =
      fun _ => ⟪v, w⟫_ℂ := funext fun t => inner_pres hu (exp_uw hX t) v w
  rw [hconst] at hI
  have h0 := hI.unique (hasDerivAt_const (0 : ℝ) ⟪v, w⟫_ℂ)
  have hone : π (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := by
    simp [NormedSpace.exp_zero, hπ.1]
  rw [hone] at h0
  simp only [ContinuousLinearMap.one_apply] at h0
  linear_combination h0

theorem EB_adj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a b : Fin m) (v w : W) :
    ⟪EB π Bs a b v, w⟫_ℂ = ⟪v, EB π Bs b a w⟫_ℂ := by
  obtain ⟨l1, l2⟩ := frame_lie hB a b
  have hR : IsRepW k r z π := ⟨hπ, hc⟩
  have e1 : hpart1 (Hpk k r) (unitB (Hpk k r) Bs b a) =
      (((-1 : ℝ) : ℂ)) • hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) := by
    rw [Qx8.hpart1_unitB, Qx8.hpart1_unitB]
    push_cast
    module
  have e2 : hpart2 (Hpk k r) (unitB (Hpk k r) Bs b a) = hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) := by
    rw [Qx8.hpart2_unitB, Qx8.hpart2_unitB, add_comm (unitB (Hpk k r) Bs b a)]
  have hlin := (differential_operator_linear W k r z π hR _ _ l1 l1).2 (-1)
  show ⟪ecOp π (unitB (Hpk k r) Bs a b) v, w⟫_ℂ = ⟪v, ecOp π (unitB (Hpk k r) Bs b a) w⟫_ℂ
  unfold ecOp
  rw [e1, e2, hlin]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, dOp_skew hπ hc hu l1, dOp_skew hπ hc hu l2]
  simp only [Complex.conj_I, neg_smul, one_smul, ContinuousLinearMap.neg_apply, inner_neg_right]
  ring

end Skew

section SelfAdj

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem qdet_symm (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (w : ℝ) : (qdet (EB π Bs) (w : ℂ)).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  have hgl := (frame_general_linear W k r m z π Bs ⟨hπ, hc⟩ hB).1
  have hst : ∀ a b, star (EB π Bs a b) =
      (((((fun _ => (1 : ℤˣ)) : Fin m → ℤˣ) a * ((fun _ => (1 : ℤˣ)) : Fin m → ℤˣ) b : ℤˣ) : ℤ) :
        Module.End ℂ W) * EB π Bs b a := by
    intro a b
    simp only [mul_one, Units.val_one, Int.cast_one, one_mul]
    rw [LinearMap.star_eq_adjoint]
    symm
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    exact EB_adj hπ hc hu hB b a x y
  have h := star_quantum_minor (Module.End ℂ W) m m (EB π Bs) (fun _ => 1) hgl hst id id (w : ℂ)
  simp only [Finset.prod_const_one, mul_one, Units.val_one, Int.cast_one, one_mul, Complex.star_def,
    Complex.conj_ofReal] at h
  exact h

end SelfAdj

section Pos

theorem hs_pos {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Φ A : Wq →L[ℂ] Wp)
    (C : Module.End ℂ Wq) (hC : C.IsSymmetric) (p : Polynomial ℂ)
    (hp : ∀ μ, C.HasEigenvalue μ → 0 < p.eval μ) (hA : ∀ v, A v = Φ (Polynomial.aeval C p v)) :
    0 ≤ B.hsInner A Φ := by
  set T : Module.End ℂ Wq := (Φ.toLinearMap.adjoint ∘ₗ Φ.toLinearMap) * Polynomial.aeval C p with hT
  have hsum : ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ Wq),
      ∑ i, ⟪Φ (b i), A (b i)⟫_ℂ = LinearMap.trace ℂ Wq T := by
    intro ι _ b
    rw [LinearMap.trace_eq_sum_inner T b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA, hT, Module.End.mul_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    rfl
  have h1 : B.hsInner A Φ =
      ∑ i, ⟪Φ (stdOrthonormalBasis ℂ Wq i), A (stdOrthonormalBasis ℂ Wq i)⟫_ℂ := by
    simp only [B.hsInner, B.hsVec, PiLp.inner_apply]
  rw [h1, hsum, ← hsum (hC.eigenvectorBasis rfl)]
  refine Finset.sum_nonneg fun i _ => ?_
  have hev := hC.hasEigenvector_eigenvectorBasis rfl i
  rw [hA, Module.End.aeval_apply_of_hasEigenvector hev, map_smul, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  refine mul_nonneg (hp _ (Module.End.hasEigenvalue_of_hasEigenvector hev)).le ?_
  rw [← RCLike.ofReal_pow]
  exact RCLike.ofReal_nonneg.mpr (by positivity)

end Pos

section Alg

def fstAlg (V : Type) [AddCommGroup V] [Module ℂ V] : Pr V →ₐ[ℂ] Module.End ℂ V where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem kappa_aeval {P : M.Par} {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : NFData P 𝒜) (Y : ℂ)
    (p : Polynomial ℂ) (f : M.Ty P → ℂ) (hp : ∀ ρ, p.eval (M.xC P ρ Y) = f ρ) :
    d.κ f = Polynomial.aeval (d.x Y) p := by
  have hf : f = Polynomial.aeval (fun ρ => M.xC P ρ Y) p := by
    funext ρ
    rw [← hp ρ, ← Polynomial.coe_aeval_eq_eval]
    exact Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : M.Ty P => ℂ) ρ) (fun ρ => M.xC P ρ Y) p
  rw [hf, ← Polynomial.aeval_algHom_apply]
  rfl

theorem sep_real {P : M.Par} (hP : P.OK) :
    ∃ Y₀ : ℝ, Function.Injective (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) := by
  classical
  have gP : ∀ i ∈ Icc 1 (P.k - 1), P.lo i ≤ P.hi i := hP.gap
  have hne : ∀ σ σ' : M.Ty P, σ ≠ σ' → LieAlgebraWeightVectors.cb_xPoly P σ - LieAlgebraWeightVectors.cb_xPoly P σ' ≠ 0 := by
    intro σ σ' hss h0
    apply hss
    have hx : ∀ Y, M.xC P σ Y = M.xC P σ' Y := by
      intro Y
      rw [← LieAlgebraWeightVectors.cb_eval_xPoly, ← LieAlgebraWeightVectors.cb_eval_xPoly, sub_eq_zero.mp h0]
    have e := LieAlgebraWeightVectors.cb_eq_of_prod_eq (n := P.k - 1) (LieAlgebraWeightVectors.cb_rho_anti _ gP σ) (LieAlgebraWeightVectors.cb_rho_anti _ gP σ') hx
    exact LieAlgebraWeightVectors.cb_ty_ext _ (fun j => e _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩))
  obtain ⟨Y₀, hY⟩ := Infinite.exists_notMem_finset
    (((Finset.univ : Finset (M.Ty P × M.Ty P)).biUnion
      (fun q => if q.1 = q.2 then ∅ else (LieAlgebraWeightVectors.cb_xPoly P q.1 - LieAlgebraWeightVectors.cb_xPoly P q.2).roots.toFinset)).image
        Complex.re)
  refine ⟨Y₀, fun σ σ' h => ?_⟩
  by_contra hss
  apply hY
  rw [Finset.mem_image]
  refine ⟨(Y₀ : ℂ), ?_, Complex.ofReal_re Y₀⟩
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨(σ, σ'), ?_⟩
  rw [if_neg hss, Multiset.mem_toFinset, Polynomial.mem_roots (hne σ σ' hss), Polynomial.IsRoot.def,
    Polynomial.eval_sub, LieAlgebraWeightVectors.cb_eval_xPoly, LieAlgebraWeightVectors.cb_eval_xPoly, sub_eq_zero]
  exact h

theorem interp_exists {ι : Type} [Fintype ι] (node : ι → ℂ) (hinj : Function.Injective node) (f : ι → ℂ)
    (hf : ∀ i, 0 < f i) (E : Finset ℂ) :
    ∃ p : Polynomial ℂ, (∀ i, p.eval (node i) = f i) ∧ ∀ μ ∈ E, 0 < p.eval μ := by
  classical
  let s : Finset ℂ := Finset.univ.image node ∪ E
  let val : ℂ → ℂ := fun μ => if h : ∃ i, node i = μ then f h.choose else 1
  refine ⟨Lagrange.interpolate s id val, ?_, ?_⟩
  · intro i
    have hi : node i ∈ s := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    show Polynomial.eval (id (node i)) (Lagrange.interpolate s id val) = f i
    rw [Lagrange.eval_interpolate_at_node val (Set.injOn_id _) hi]
    have hex : ∃ j, node j = node i := ⟨i, rfl⟩
    simp only [val, id, dif_pos hex]
    rw [hinj hex.choose_spec]
  · intro μ hμ
    show 0 < Polynomial.eval (id μ) (Lagrange.interpolate s id val)
    rw [Lagrange.eval_interpolate_at_node val (Set.injOn_id _) (Finset.mem_union_right _ hμ)]
    simp only [val]
    split_ifs with h
    · exact hf _
    · exact one_pos

end Alg

section Act

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem aeval_act (T : Module.End ℂ (RadSp k r z z' π π')) (C : Module.End ℂ Wq) {c : Fin r → ℂ} {g : Mx k r}
    (hT : ∀ (Ψ : RadSp k r z z' π π') (v : Wq),
      ((T Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g v = (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g (C v))
    (p : Polynomial ℂ) : ∀ (Ψ : RadSp k r z z' π π') (v : Wq),
      ((Polynomial.aeval T p Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g v =
        (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g (Polynomial.aeval C p v) := by
  have hpow : ∀ (m : ℕ) (Ψ : RadSp k r z z' π π') (v : Wq),
      (((T ^ m) Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g v =
        (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g ((C ^ m) v) := by
    intro m
    induction m with
    | zero => intro Ψ v; simp
    | succ m ih =>
      intro Ψ v
      rw [pow_succ, Module.End.mul_apply, ih, hT, pow_succ', Module.End.mul_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro Ψ v
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, ContinuousLinearMap.add_apply,
      hp, hq, map_add, LinearMap.add_apply, map_add]
  | monomial m a =>
    intro Ψ v
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply,
      ContinuousLinearMap.smul_apply, hpow, map_smul]

variable [FiniteDimensional ℂ Wq]

theorem diagonal_transfer_action (X : ActualOps k r z z' π π') (hz : inWb k r z) (hz' : inWb k r z')
    (hπ'r : IsCRepOn (UWset k r z') π') (hπ'c : ContinuousOn π' (UWset k r z'))
    {c : Fin r → ℂ} {g : Mx k r} (hx : (c, g) ∈ DomR k r z z')
    (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (hBs : IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs)
    (Y : ℂ) (Ψ : RadSp k r z z' π π') (v : Wq) :
    (((X.fn 5 * X.t Y 1 1) Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g v =
      (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g (qdet (EB π' Bs) (Y + ((k : ℂ) - 2) / 2) v) := by
  obtain ⟨hc, hg, hG⟩ := hx
  have hGG : GGl k r z z' g ≠ 0 := hG.ne'
  rw [Module.End.mul_apply, X.fn_apply 5 _ (c, g) ⟨hc, hg, hG⟩, X.t_apply Y 1 1 Ψ (c, g) ⟨hc, hg, hG⟩]
  have hF := Qx5.slice_FF hz hz' Ψ.2 hc
  have h := LieAlgebraWeightVectors.top_level_pointwise_identity capelli_two_by_two right_type_action hz hz' (Qx5.Dp_dom k r z z')
    hπ'r hπ'c hF ⟨hg, hG⟩ hGG Bs hBs Y v
  have hq := (frame_general_linear Wq k r (k - 1) z' π' Bs ⟨hπ'r, hπ'c⟩ (LieAlgebraWeightVectors.frame_sub hBs (by simp))).2
  rw [ContinuousLinearMap.smul_apply]
  erw [h]
  rw [← hq, smul_smul]
  have : (fnVal k r z z' 5 g) * (GGl k r z z' g : ℂ) = 1 := by
    simp only [fnVal]
    exact inv_mul_cancel₀ (by exact_mod_cast hGG)
  rw [this, one_smul]

end Act

end Formalism.FourierDecayAlt.P5.Kfp

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD Formalism.FourierDecayAlt.P5.Kfp

theorem kappaFibrePos : KappaFibrePos := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hPl X d hL hS hR hQ f hf Φ c g
  obtain ⟨hP, hz, hz', hTz, hTz', hπ, hπ'⟩ := hPl
  by_cases hx : (c, g) ∈ DomR P.k P.r z z'
  swap
  · have h1 : (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 := Φ.2.1 (c, g) hx
    have h2 : (((d.κ f).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 :=
      ((d.κ f).1 Φ).2.1 (c, g) hx
    rw [h1, h2]
    simp [B.hsInner, B.hsVec]
  have hx' := hx
  obtain ⟨hc, hg, hG⟩ := hx'
  have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hP.T_pos
  have hT' : 0 < Tz P.k P.r z' := by rw [hTz']; exact hP.T'_pos
  obtain ⟨Bs, e', e, hB1, -, -, -, -, -, -, -, -⟩ := LieAlgebraWeightVectors.geom_package hz hz' hT hT' hg hG.ne'
  have hBz' : IsFrameOf P.k P.r [z'] Bs := LieAlgebraWeightVectors.frame_sub hB1 (by simp)
  have hπ'r := hπ'.2.1
  have hπ'c := hπ'.2.2.1
  have hu := hπ'.2.2.2.1
  obtain ⟨Y₀, hY₀⟩ := sep_real hP
  set w0 : ℝ := Y₀ + ((P.k : ℝ) - 2) / 2 with hw0
  set C : Module.End ℂ Wq := qdet (EB π' Bs) (w0 : ℂ) with hCdef
  have hC : C.IsSymmetric := qdet_symm hπ'r hπ'c hu hBz' w0
  obtain ⟨p, hpn, hpE⟩ := interp_exists (fun ρ => M.xC P ρ (Y₀ : ℂ)) hY₀ f hf (minpoly ℂ C).roots.toFinset
  have hκ : d.κ f = Polynomial.aeval (d.x (Y₀ : ℂ)) p := kappa_aeval d (Y₀ : ℂ) p f hpn
  have hx1 : fstAlg _ (d.x (Y₀ : ℂ)) = X.fn 5 * X.t (Y₀ : ℂ) 1 1 := by
    have h : d.x (Y₀ : ℂ) = d.L.GGi * X.QQ (Y₀ : ℂ) 1 1 := by
      rw [hQ]
      simp only [NFData.QQ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]
      rw [← mul_assoc, d.L.GGi_GG, one_mul]
    rw [h, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  have hfst : (d.κ f).1 = Polynomial.aeval (X.fn 5 * X.t (Y₀ : ℂ) 1 1) p := by
    rw [← hx1, Polynomial.aeval_algHom_apply, hκ]
    rfl
  have hact : ∀ (Ψ : RadSp P.k P.r z z' π π') (v : Wq),
      (((X.fn 5 * X.t (Y₀ : ℂ) 1 1) Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v =
        (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (C v) := by
    intro Ψ v
    rw [diagonal_transfer_action X hz hz' hπ'r hπ'c hx Bs hB1 (Y₀ : ℂ) Ψ v, hCdef, hw0]
    push_cast
    rfl
  refine hs_pos ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g)
    ((((d.κ f).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) C hC p ?_ ?_
  · intro μ hμ
    apply hpE
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (minpoly.ne_zero (Algebra.IsIntegral.isIntegral C))]
    exact Module.End.isRoot_of_hasEigenvalue hμ
  · intro v
    rw [hfst]
    exact aeval_act _ C hact p Φ v

end Formalism.FourierDecayAlt.P5
