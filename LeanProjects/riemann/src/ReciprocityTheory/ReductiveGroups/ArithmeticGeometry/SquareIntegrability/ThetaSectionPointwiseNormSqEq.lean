import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModeAddRealDirection

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem uMap_eq_uc (x : Vsp X.dim) : uMap I x = uc (IR I) x :=
  (isU_uMap I x).unique (isU_uc x)

theorem z_uc (hI : IsSplit P I) (k : Fin (dK (IR I))) (v : Vsp X.dim) :
    z (IR I) k (uc (IR I) v) = ((z (IR I) k v).im : ℂ) := by
  have hK := hK_of hI
  rw [uc, z_sum]
  simp only [z_rsmul, z_e hK, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem norm_uc_sq (hI : IsSplit P I) (v : Vsp X.dim) :
    ‖uc (IR I) v‖ ^ 2 = ∑ k, (z (IR I) k v).im ^ 2 := by
  have hK := hK_of hI
  rw [norm_sq_decomp hK, proj_two_of_mem hK (uc_mem _ v), norm_zero]
  simp only [z_uc hI, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_sq_alt (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem thetaSectionPointwiseNormSq_eq (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Vsp X.dim) :
    X.ptN2 1 s (fun _ => v) = ‖zmG I s v‖ ^ 2 *
      Real.exp (-(2 * Real.pi) * ‖uc (IR I) v‖ ^ 2 - Real.pi * ‖p2 (IR I) v‖ ^ 2) := by
  have hK := hK_of hI
  rw [PT.ptN2, HC_one, Hf_self_re, zmG, norm_mul, Complex.norm_exp, mul_pow, mul_assoc,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  have hA := norm_sq_decomp hK v
  simp only [norm_sq_alt, Finset.sum_add_distrib] at hA
  have hB : (-(Real.pi / 2 : ℂ) * S (IR I) v).re =
      -(Real.pi / 2) * (∑ k, (z (IR I) k v).re ^ 2 - ∑ k, (z (IR I) k v).im ^ 2) := by
    rw [S, ← Finset.sum_sub_distrib, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re, pow_two]
  rw [hB, norm_uc_sq hI v, hA]
  push_cast
  ring

theorem re_gaugeExp (hI : IsSplit P I) (γ v : Vsp X.dim) :
    (gaugeExp I γ v).re = 2 * Real.pi * ∑ k, (z (IR I) k γ).im * (z (IR I) k v).im +
      Real.pi * ∑ k, (z (IR I) k γ).im ^ 2 + Real.pi * (Hf (p2 (IR I) v) (p2 (IR I) γ)).re +
      Real.pi / 2 * ‖p2 (IR I) γ‖ ^ 2 := by
  rw [gaugeExp]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_sum, Complex.im_sum, Complex.mul_im,
    Complex.div_re, Hf_self_re]
  simp only [mul_zero, zero_mul, sub_zero, mul_one, zero_add, add_zero, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_ofNat]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  ring_nf

theorem norm_orthProj_add_sq (v γ : Vsp X.dim) :
    ‖p2 (IR I) v + p2 (IR I) γ‖ ^ 2 = ‖p2 (IR I) v‖ ^ 2 + 2 * (Hf (p2 (IR I) v) (p2 (IR I) γ)).re +
      ‖p2 (IR I) γ‖ ^ 2 := by
  rw [← Hf_self_re, ← Hf_self_re, ← Hf_self_re, Hf_add_l, Hf_add_r, Hf_add_r,
    Hf_swap (p2 (IR I) γ) (p2 (IR I) v)]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem mode_norm (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) {γ : Vsp X.dim} (hγ : γ ∈ X.L) (m : Fin (Module.finrank ℝ (IR I)) → ℤ)
    (hm : ∀ i, (Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im = m i) (v : Vsp X.dim) :
    ‖zmC hI s m v‖ * Real.exp (-Real.pi * ‖uc (IR I) v‖ ^ 2 - Real.pi / 2 * ‖p2 (IR I) v‖ ^ 2) =
      Real.sqrt ((YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (v + γ))) *
        Real.exp (-Real.pi * ‖uc (IR I) v + uc (IR I) γ‖ ^ 2) := by
  have hK := hK_of hI
  have h := zmC_add hI hs hγ m hm 0 v
  rw [zero_add] at h
  have heps : ‖(X.eps γ : ℂ)‖ = 1 := by rcases X.eps_pm γ hγ with h | h <;> simp [h]
  have hn : ‖zmC hI s 0 (v + γ)‖ = Real.exp (gaugeExp I γ v).re * ‖zmC hI s m v‖ := by
    rw [h, norm_mul, norm_mul, heps, one_mul, Complex.norm_exp]
  have hβ : zmB hI s (wmap (IR I) (v + γ)) = zmC hI s 0 (v + γ) := by
    simp only [zmB]; rw [jj_wmap' hK, ← zeroMode_proj_two hI hs]
  have hpt : Real.sqrt ((YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (v + γ))) =
      ‖zmC hI s 0 (v + γ)‖ * Real.exp (-(Real.pi / 2) * ‖p2 (IR I) (v + γ)‖ ^ 2) := by
    rw [GT.ptN2, hβ, norm_wmap hK, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [show Real.exp (-(((1 : ℕ) : ℝ) * Real.pi) * ‖p2 (IR I) (v + γ)‖ ^ 2) =
        Real.exp (-(Real.pi / 2) * ‖p2 (IR I) (v + γ)‖ ^ 2) ^ 2 by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
    exact Real.sqrt_sq (Real.exp_pos _).le
  rw [hpt, hn]
  have hu : ‖uc (IR I) v + uc (IR I) γ‖ ^ 2 =
      ∑ k, ((z (IR I) k v).im + (z (IR I) k γ).im) ^ 2 := by
    rw [← uc_add, norm_uc_sq hI (v + γ)]
    simp [z_add]
  have hsq : ∑ k, ((z (IR I) k v).im + (z (IR I) k γ).im) ^ 2 =
      ∑ k, (z (IR I) k v).im ^ 2 + 2 * ∑ k, (z (IR I) k γ).im * (z (IR I) k v).im +
        ∑ k, (z (IR I) k γ).im ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hp := norm_orthProj_add_sq (I := I) v γ
  rw [← proj_two_add] at hp
  have hv := norm_uc_sq hI v
  have hg := re_gaugeExp hI γ v
  have key : -Real.pi * ‖uc (IR I) v‖ ^ 2 - Real.pi / 2 * ‖p2 (IR I) v‖ ^ 2 =
      (gaugeExp I γ v).re + -(Real.pi / 2) * ‖p2 (IR I) (v + γ)‖ ^ 2 +
        -Real.pi * ‖uc (IR I) v + uc (IR I) γ‖ ^ 2 := by
    rw [hu, hsq, hp, hv, hg]; ring
  rw [key, Real.exp_add, Real.exp_add]
  ring

theorem dual_lift (hI : IsSplit P I) (m : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    ∃ γ ∈ X.L, ∀ i, (Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im = m i := by
  haveI := IK_discrete hI
  haveI : IsZLattice ℝ (IK I) := ⟨IK_span⟩
  haveI := ZLattice.module_free ℝ (IK I)
  set e := Fintype.equivFinOfCardEq (α := Module.Free.ChooseBasisIndex ℤ (IK I))
    (n := Module.finrank ℝ (IR I)) (by rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ])
  set bZ := (Module.Free.chooseBasis ℤ (IK I)).reindex e with hbZ
  have hIb : ∀ i, (Ib hI i : IR I) = ((bZ i : IK I) : IR I) := fun i => by
    simp [Ib, bZ, Module.Basis.ofZLatticeBasis_apply]
    rfl
  let ψ : IK I →ₗ[ℤ] ℤ := bZ.constr ℤ (fun i => m i)
  let N : Submodule ℤ X.L := I.comap X.L.subtype
  have hsat : ∀ (k : ℤ) (x : X.L), k ≠ 0 → k • x ∈ N → x ∈ N := fun k x hk h =>
    hI.sat x x.2 k hk (by simpa [N] using h)
  let j : N →ₗ[ℤ] IK I :=
    { toFun := fun x => ⟨⟨((x : X.L) : Vsp X.dim), mem_IR x.2⟩, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨Ψ, hΨ⟩ := Col.extend_hom N hsat (ψ.comp j)
  obtain ⟨γ, hγ, hγΨ⟩ := X.perfect Ψ.toAddMonoidHom
  refine ⟨γ, hγ, fun i => ?_⟩
  let y : X.L := ⟨((Ib hI i : IR I) : Vsp X.dim), hI.le (Ib_mem hI i)⟩
  have hyN : y ∈ N := Ib_mem hI i
  have h1 := hγΨ y
  have h2 : Ψ y = m i := by
    have := hΨ ⟨y, hyN⟩
    simp only at this
    rw [this, LinearMap.comp_apply]
    have hj : j ⟨y, hyN⟩ = bZ i := by
      apply Subtype.ext; apply Subtype.ext
      show ((Ib hI i : IR I) : Vsp X.dim) = (((bZ i : IK I) : IR I) : Vsp X.dim)
      rw [hIb]
    rw [hj]
    simp [ψ]
  rw [← h1]
  simp [h2]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
