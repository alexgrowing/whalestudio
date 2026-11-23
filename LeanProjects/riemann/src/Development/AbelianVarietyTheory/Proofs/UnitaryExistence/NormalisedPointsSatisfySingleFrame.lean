import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpMulThetaCharAutomorphy
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermEqOfNormalised
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.NormFrame

theorem eq_zero_of_eventually {g : ℕ} {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) {z : Fin g → ℂ}
    (hz : ∀ᶠ w in nhds z, θ w = 0) (w : Fin g → ℂ) : θ w = 0 := by
  have hl : Differentiable ℂ (fun t : ℂ => z + t • (w - z)) := by fun_prop
  have hd : Differentiable ℂ (fun t : ℂ => θ (z + t • (w - z))) := hθ.comp hl
  have ha : AnalyticOnNhd ℂ (fun t : ℂ => θ (z + t • (w - z))) Set.univ :=
    hd.differentiableOn.analyticOnNhd isOpen_univ
  have ht : Filter.Tendsto (fun t : ℂ => z + t • (w - z)) (nhds 0) (nhds z) := by
    simpa using hl.continuous.tendsto 0
  have h0 : (fun t : ℂ => θ (z + t • (w - z))) =ᶠ[nhds 0] 0 := ht.eventually hz
  have := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) h0
    (Set.mem_univ 1)
  simpa using this

theorem cancel_entire {g : ℕ} {θ f f' : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (hne : ∃ w, θ w ≠ 0)
    {O : Set (Fin g → ℂ)} (hO : IsOpen O) (hf : ContinuousOn f O) (hf' : ContinuousOn f' O)
    (h : ∀ z ∈ O, θ z * f z = θ z * f' z) : ∀ z ∈ O, f z = f' z := by
  intro z hz
  by_contra hc
  obtain ⟨w, hw⟩ := hne
  apply hw
  apply eq_zero_of_eventually hθ (z := z)
  have h1 : ∀ᶠ w in nhds z, f w ≠ f' w :=
    (((hf.continuousAt (hO.mem_nhds hz)).sub (hf'.continuousAt (hO.mem_nhds hz))).eventually_ne
      (sub_ne_zero.2 hc)).mono fun _ h => sub_ne_zero.1 h
  filter_upwards [h1, hO.mem_nhds hz] with w h1 h2
  by_contra h3
  exact h1 (mul_left_cancel₀ h3 (h w h2))

theorem norm_sq_scalar {g : ℕ} {κ d : ℂ} {P y : ℝ} (hy : 0 < y) (hd : d ≠ 0)
    (hκ : κ ^ 2 = (Real.sqrt (2 ^ g / P) : ℝ) * d) (hP : (P : ℂ) * (y : ℂ) = ((‖d‖ ^ 2 : ℝ) : ℂ)) :
    ‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * y))⁻¹ = 1 := by
  have hP' : P * y = ‖d‖ ^ 2 := by exact_mod_cast hP
  have hd' : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hP0 : 0 < P := by
    have : 0 < P * y := by rw [hP']; positivity
    exact (mul_pos_iff_of_pos_right hy).1 this
  have h1 : ‖κ‖ ^ 2 = Real.sqrt (2 ^ g / P) * ‖d‖ := by
    rw [← norm_pow, hκ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : Real.sqrt (2 ^ g * y) = Real.sqrt (2 ^ g / P) * ‖d‖ := by
    rw [← Real.sqrt_sq hd'.le, ← Real.sqrt_mul (by positivity), ← hP']
    congr 1
    field_simp
  rw [h1, ← h2]
  exact mul_inv_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne'

theorem period_bas {g : ℕ} {L : Type} [AddCommGroup L] (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] L)
    (P : L →+ (Fin g → ℂ)) (h τ : Matrix (Fin g) (Fin g) ℂ)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) (v : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas v) = (fun i => (v (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (v (Sum.inr i) : ℂ)) := by
  have hs : ∀ w : Fin g → ℤ, (fun i => (w i : ℂ)) = ∑ i, w i • (Pi.single i (1 : ℂ) : Fin g → ℂ) := by
    intro w
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ s, v s • (Pi.single s (1 : ℤ) : Fin g ⊕ Fin g → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hs fun i => v (Sum.inl i), hs fun i => v (Sum.inr i)]
  conv_lhs => rw [hv]
  simp only [map_sum, map_zsmul, map_add, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Fintype.sum_sum_type, (hn _).1, (hn _).2]

open MonoidalCategory CartesianMonoidalCategory MonObj in

theorem ex_add_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P)
    (a : (F.Di k).La) (z : Fin g → ℂ) : F.ex k P (z + P a) = F.ex k P z := by
  rw [F.ex_add k _ hP, (F.ex_ker k _ hP _).2 ⟨a, rfl⟩, _root_.mul_one]

set_option maxHeartbeats 1600000 in

theorem frameOK_of_isNormUn : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (un : (M.X k).dom → FrPt Xo c (CAt σ)), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T un → ∀ x, FrameOK e F M k x (un x) := by
  intro _ E _ _ _ H Dw l Xo c σ g e F r M k T un hG hM hX hN x
  obtain ⟨κ, hκ, hx, hu, hs⟩ := hN x
  set b := T.co.symm x.1 with hb
  have hbx : T.co b = x.1 := T.co.apply_symm_apply _
  have hbd : b ∈ T.co ⁻¹' (M.X k).dom := by
    rw [Set.mem_preimage, hbx]; exact x.2
  have hper := T.isPer _ hbd
  refine ⟨T.Pf (T.co b), fun a j => by rw [hbx]; exact T.per _ a j, hper, hx, hu, fun hunit => ?_⟩
  obtain ⟨Hm, hH1, hH2, hH3⟩ := hper.2.2.2.2
  obtain ⟨hdet, hsym, hpos, hn⟩ := T.norm b hbd
  obtain ⟨hHm, hHdet⟩ := GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ T.bas _ (T.h b) (T.ta b) Hm T.sympl hper hn
    ⟨hsym, hpos⟩ hH3
  have hud := GlobalTheory.UnitDet.det_eq_prod E H Dw l Xo c σ g e F r M hG hM hX k T.Pf T.per x.1 x.2 hunit Hm
    (by rw [← hbx]; exact hH3)
  rw [hud] at hHdet
  have hnorm := norm_sq_scalar (g := g) hpos.det_pos hdet.ne_zero hκ hHdet
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    simp at hnorm
  obtain ⟨q, hq⟩ : ∃ q : (Fin g → ℂ) → ℂ, ∀ z, q z = Real.pi / 2 * ((T.h b *ᵥ z) ⬝ᵥ
      ((((T.ta b).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (T.h b *ᵥ z))) := ⟨_, fun _ => rfl⟩
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => T.h b *ᵥ z) :=
    (Matrix.mulVecLin (T.h b)).toContinuousLinearMap.differentiable
  have hqd : Differentiable ℂ q := by
    rw [funext hq]
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hq0 : q 0 = 0 := by simp [hq]
  obtain ⟨hA1, hA2⟩ := GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy g (T.ta b) (T.h b) Hm T.c₁ T.c₂ q hsym hpos
    T.half₁ T.half₂ hHm hq
  have hlat : ∀ lam, lam ∈ (T.Pf (T.co b)).range ↔ ∃ m n : Fin g → ℤ,
      T.h b *ᵥ lam = (fun i => (m i : ℂ)) + T.ta b *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨v, rfl⟩ := T.bas.surjective a
      exact ⟨_, _, period_bas T.bas _ _ _ hn v⟩
    · rintro ⟨m, n, hmn⟩
      refine ⟨T.bas (Sum.elim m n), ?_⟩
      apply Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
      rw [hmn]
      exact period_bas T.bas _ _ _ hn _
  obtain ⟨Fd, hFd, hint⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g (T.ta b) (T.h b)
    T.c₁ T.c₂ _ hsym hpos hdet T.half₁ T.half₂ hlat
  obtain ⟨hθd, w0, hw0⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  have hχ : ∀ lam : Fin g → ℂ, ∃ χ : ℂ, lam ∈ (T.Pf (T.co b)).range → ‖χ‖ = 1 ∧ ∀ z,
      Complex.exp (q (z + lam)) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ (z + lam)) =
        χ * Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) *
          (Complex.exp (q z) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) := by
    intro lam
    by_cases hl : lam ∈ (T.Pf (T.co b)).range
    · obtain ⟨m, n, hmn⟩ := (hlat lam).1 hl
      obtain ⟨χ, hχ⟩ := hA2 lam m n hmn
      exact ⟨χ, fun _ => hχ⟩
    · exact ⟨1, fun h => absurd h hl⟩
  choose χl hχl using hχ
  have hfrd : ∀ j, DifferentiableOn ℂ (fun z => T.fr j (b, z) * Complex.exp (-q z))
      {z | ⊤ ≤ (F.ex k (T.Pf (T.co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
    intro j
    refine DifferentiableOn.mul ?_ (by fun_prop)
    exact (T.fr_hol j).comp (f := fun z => (b, z)) (by fun_prop) fun z hz => ⟨hbd, hz⟩
  have hval : ∀ j z (pt : Sp ℂ ⟶ Gx (un x).x),
      pt ≫ gxFst (un x).x = (F.ex k (T.Pf (T.co b)) z).left → pt ≫ gxSnd (un x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k (T.Pf (T.co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (un x).x).U (fun _ => j)) ((un x).s.f (fun _ => j)) =
        (κ * (Complex.exp (q z) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z))) *
          (T.fr j (b, z) * Complex.exp (-q z)) := by
    intro j z pt h1 h2 h3
    rw [hs j z pt h1 h2 h3, Complex.exp_neg]
    have := Complex.exp_ne_zero (q z)
    field_simp
  refine ⟨Hm, χl, fun j z => T.fr j (b, z) * Complex.exp (-q z),
    fun z => κ * (Complex.exp (q z) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)), Fd, hH1, hH2, hH3, hfrd,
    fun j z hz => mul_ne_zero (T.fr_ne j b z hbd hz) (Complex.exp_ne_zero _),
    fun j j' z hz => ?_, fun j hz => ?_, fun a j z => ⟨(hχl _ ⟨a, rfl⟩).1, ?_⟩, hval, hFd, ?_⟩
  · beta_reduce
    rw [T.fr_coc j j' b z hbd hz, mul_assoc]
  · beta_reduce
    rw [hq0, neg_zero, Complex.exp_zero, mul_one, T.fr_rig j b hbd hz, hx]
  · have hex : ∀ z, F.ex k (T.Pf (T.co b)) (z + T.Pf (T.co b) a) = F.ex k (T.Pf (T.co b)) z :=
      ex_add_period F k _ hper a
    have hO : IsOpen {z | ⊤ ≤ (F.ex k (T.Pf (T.co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h1 := ((F.hol k 0 Set.univ (fun _ => T.Pf (T.co b)) isOpen_univ
        ⟨fun _ _ => hper, fun _ => differentiableOn_const _⟩).2 (Xo.univ.t.PP.L.U j) 0).1
      have h2 := h1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
      convert h2 using 1
      ext z
      simp
    obtain ⟨s, hsec⟩ := T.fr_sec b hbd
    refine cancel_entire (θ := fun z => Complex.exp (q z) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z))
      (f := fun z => T.fr j (b, z) * Complex.exp (-q z))
      (f' := fun z => χl (T.Pf (T.co b) a) * Complex.exp (Real.pi * hermForm Hm z (T.Pf (T.co b) a) +
        Real.pi / 2 * hermForm Hm (T.Pf (T.co b) a) (T.Pf (T.co b) a)) *
        (T.fr j (b, z + T.Pf (T.co b) a) * Complex.exp (-q (z + T.Pf (T.co b) a))))
      ((hqd.cexp).mul (hθd.comp hlin)) ?_ hO (hfrd j).continuousOn ?_ ?_ z
    · obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet) w0
      exact ⟨w, mul_ne_zero (Complex.exp_ne_zero _) (by rw [hw]; exact hw0)⟩
    · refine ContinuousOn.mul (Continuous.continuousOn ?_) ?_
      · simp only [hermForm, dotProduct]
        fun_prop
      · refine (hfrd j).continuousOn.comp (f := fun z => z + T.Pf (T.co b) a) (by fun_prop) fun z hz => ?_
        rw [Set.mem_ofPred_eq, hex]
        exact hz
    · intro z hz
      have hw : (F.ex k (T.Pf (T.co b)) z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ F.u k (T.Pf (T.co b)) := by
        rw [Category.id_comp]
        exact Over.w (F.ex k (T.Pf (T.co b)) z)
      have h1 := hsec j z (pullback.lift _ _ hw) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hz
      have h2 := hsec j (z + T.Pf (T.co b) a) (pullback.lift _ _ hw) (by rw [hex]; exact pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _) (by rw [hex]; exact hz)
      have h3 := h1.symm.trans h2
      have h4 := (hχl _ ⟨a, rfl⟩).2 z
      have e1 : Complex.exp (q z) * Complex.exp (-q z) = 1 := by rw [← Complex.exp_add]; simp
      have e2 : Complex.exp (q (z + T.Pf (T.co b) a)) * Complex.exp (-q (z + T.Pf (T.co b) a)) = 1 := by
        rw [← Complex.exp_add]; simp
      linear_combination (thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z)) * e1 + h3 +
        (T.fr j (b, z + T.Pf (T.co b) a) * Complex.exp (-q (z + T.Pf (T.co b) a))) * h4 -
        (thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ (z + T.Pf (T.co b) a)) * T.fr j (b, z + T.Pf (T.co b) a)) * e2
  · rw [← hnorm, ← hint, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]
    congr 2
    ext z
    rw [← hA1 z, norm_mul, norm_mul]
    ring

end GlobalTheory.NormFrame
