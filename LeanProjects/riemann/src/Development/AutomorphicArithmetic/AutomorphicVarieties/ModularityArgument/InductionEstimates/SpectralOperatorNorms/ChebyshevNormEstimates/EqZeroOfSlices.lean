import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.BloIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecStr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdmCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TensInterp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.WhittakerHecke.LocGLEqLocalEmbeddingAndKGLEqIntegralGL
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem gl_ext {n : ℕ} {g g' : AdelicGLn.AdelicGL E n} (h1 : ∀ w, infAt w g = infAt w g') (h2 : ∀ v, finAt v g = finAt v g') :
    g = g' := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext E fun v => ?_))
  · exact congrArg (fun x : GL (Fin n) w.Completion => x.val i j) (h1 w)
  · exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (h2 v)

private theorem infAt_blk (w : InfinitePlace E) (a b : AdelicGLn.AdelicGL E 2) :
    infAt w (blk a b) = blk (infAt w a) (infAt w b) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> first | rfl | (simp [blk, infAt] <;> rfl)

private theorem finAt_blk (v : Pl E) (a b : AdelicGLn.AdelicGL E 2) :
    finAt v (blk a b) = blk (finAt v a) (finAt v b) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> first | rfl | simp [blk, finAt]

private theorem blk_one {R : Type} [CommRing R] : blk (1 : GL (Fin 2) R) (1 : GL (Fin 2) R) = 1 := by
  refine Units.ext ?_
  simp [blk]

private def LocAt (w : Pl E) {n : ℕ} (x : G1 E n) : Prop :=
  x ∈ KG E n ∧ (∀ w', infAt w' (x : AdelicGLn.AdelicGL E n) = 1) ∧ ∀ v, v ≠ w → finAt v (x : AdelicGLn.AdelicGL E n) = 1

private theorem infAt_finEmb' {n : ℕ} (w : InfinitePlace E) (x : AdelicGLn.FiniteAdelicGL E n) : infAt w (finEmb E n x) = 1 := by
  show (AdelicGLn.infiniteEquiv E n (AdelicGLn.prodEquiv E n (finEmb E n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

private theorem locAt_conj (w : Pl E) {n : ℕ} {x k : G1 E n} (hx : LocAt w x) (hk : k ∈ KG E n) : LocAt w (k⁻¹ * x * k) := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hi : ∀ w', infAt w' ((k⁻¹ : G1 E n) : AdelicGLn.AdelicGL E n) * infAt w' (k : AdelicGLn.AdelicGL E n) = 1 := fun w' => by
    rw [← infAt_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    simp [infAt, map_one]
  have hf : ∀ v, finAt v ((k⁻¹ : G1 E n) : AdelicGLn.AdelicGL E n) * finAt v (k : AdelicGLn.AdelicGL E n) = 1 := fun v => by
    rw [← finAt_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    simp [finAt, map_one]
  refine ⟨mul_mem (mul_mem (inv_mem hk) h1) hk, fun w' => ?_, fun v hv => ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, infAt_mul, infAt_mul, h2, mul_one, hi]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, finAt_mul, finAt_mul, h3 v hv, mul_one, hf]

private theorem zt_zero : zt E 0 = 1 := by
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
  rw [zt, this, map_one]

private theorem locAt_lv₁ (w : Pl E) {x : G1 E 2} (hx : LocAt w x) : LocAt w (lv x 1 0) := by
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨e, -, -, -, -, -, -, -, -, -, hK, -⟩ := blkLaws (K := E)
  have he : ((lv x 1 0 : G1 E (2 + 2)) : AdelicGLn.AdelicGL E (2 + 2)) = blk (x : AdelicGLn.AdelicGL E 2) 1 := by
    rw [e]
    simp [zt_zero]
  refine ⟨hK x h1 1 (one_mem _), fun w' => ?_, fun v hv => ?_⟩
  · rw [he, infAt_blk, h2]
    have : infAt w' (1 : AdelicGLn.AdelicGL E 2) = 1 := by simp [infAt, map_one]
    rw [this, blk_one]
  · rw [he, finAt_blk, h3 v hv]
    have : finAt v (1 : AdelicGLn.AdelicGL E 2) = 1 := by simp [finAt, map_one]
    rw [this, blk_one]

private theorem locAt_lv₂ (w : Pl E) {x : G1 E 2} (hx : LocAt w x) : LocAt w (lv 1 x 0) := by
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨e, -, -, -, -, -, -, -, -, -, hK, -⟩ := blkLaws (K := E)
  have he : ((lv 1 x 0 : G1 E (2 + 2)) : AdelicGLn.AdelicGL E (2 + 2)) = blk 1 (x : AdelicGLn.AdelicGL E 2) := by
    rw [e]
    simp [zt_zero]
  refine ⟨hK 1 (one_mem _) x h1, fun w' => ?_, fun v hv => ?_⟩
  · rw [he, infAt_blk, h2]
    have : infAt w' (1 : AdelicGLn.AdelicGL E 2) = 1 := by simp [infAt, map_one]
    rw [this, blk_one]
  · rw [he, finAt_blk, h3 v hv]
    have : finAt v (1 : AdelicGLn.AdelicGL E 2) = 1 := by simp [finAt, map_one]
    rw [this, blk_one]

private theorem locAt_eq (w : Pl E) {n : ℕ} {x : G1 E n} (hx : LocAt w x) :
    (x : AdelicGLn.AdelicGL E n) = finEmb E n (AdelicGLn.localEmbedding w (finAt w (x : AdelicGLn.AdelicGL E n))) := by
  obtain ⟨-, h1, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
  refine gl_ext (fun w' => ?_) fun v => ?_
  · rw [hx.2.1, infAt_finEmb']
  · by_cases hv : v = w
    · subst hv
      rw [h1]
    · rw [hx.2.2 v hv, h2 v hv]

private theorem locAt_int (w : Pl E) {n : ℕ} {x : G1 E n} (hx : LocAt w x) :
    finAt w (x : AdelicGLn.AdelicGL E n) ∈ GLnLocal.integralGL (w.adicCompletion E) n :=
  (Reduction.mem_maxCompact.1 hx.1).2 w

private theorem locAt_retract (w : Pl E) {n : ℕ} {u : GL (Fin n) (w.adicCompletion E)}
    (hu : u ∈ GLnLocal.integralGL (w.adicCompletion E) n) :
    LocAt w (retractOne (finEmb E n (AdelicGLn.localEmbedding w u))) := by
  obtain ⟨-, h1, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
  have hm : finEmb E n (AdelicGLn.localEmbedding w u) ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL E n)) := by
    refine Reduction.mem_maxCompact.2 ⟨fun w' => ?_, fun v => ?_⟩
    · rw [infAt_finEmb']
      exact one_mem _
    · by_cases hv : v = w
      · subst hv
        rw [h1]
        exact hu
      · rw [h2 v hv]
        exact one_mem _
  have hc : ((retractOne (finEmb E n (AdelicGLn.localEmbedding w u)) : G1 E n) : AdelicGLn.AdelicGL E n) =
      finEmb E n (AdelicGLn.localEmbedding w u) :=
    congrArg Subtype.val (retractOne_coe (⟨_, Reduction.maxCompact_le_normOneGL hm⟩ : normOneGL E n))
  refine ⟨?_, fun w' => ?_, fun v hv => ?_⟩
  · show ((retractOne (finEmb E n (AdelicGLn.localEmbedding w u)) : G1 E n) : AdelicGLn.AdelicGL E n) ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL E n))
    rw [hc]
    exact hm
  · rw [hc, infAt_finEmb']
  · rw [hc, h2 v hv]

private theorem fix_inv {n : ℕ} {D : TypeDat E n} {f : G1 E n → ℂ} {Kf : Subgroup (AdelicGLn.FiniteAdelicGL E n)} (hL : D.Level Kf) (hf : D.Fix f)
    {x : G1 E n} (hx : x ∈ D.U) (h1 : (AdelicGLn.prodEquiv E n x).1 = 1) (g : G1 E n) : f (g * x) = f g := by
  have h1' : (AdelicGLn.prodEquiv E n ((x⁻¹ : G1 E n) : AdelicGLn.AdelicGL E n)).1 = 1 := by
    rw [Subgroup.coe_inv, map_inv, Prod.fst_inv, h1, inv_one]
  have hp := D.inv x hx
  have e1 : ∫ k, D.e (x⁻¹ * k) * f (g * k) ∂D.ν = ∫ k, D.e k * f (g * x * k) ∂D.ν := by
    have := hp.integral_comp (MeasurableEquiv.mulLeft x).measurableEmbedding (fun k => D.e (x⁻¹ * k) * f (g * k))
    simpa [mul_assoc] using this.symm
  have e2 : ∫ k, D.e (x⁻¹ * k) * f (g * k) ∂D.ν = ∫ k, D.e k * f (g * k) ∂D.ν := by
    refine integral_congr_ae (D.supp.mono fun k hk => ?_)
    show D.e (x⁻¹ * k) * f (g * k) = D.e k * f (g * k)
    rw [hL.2.2 _ (inv_mem hx) h1' k hk]
  rw [← hf (g * x), ← e1, e2, hf g]

private theorem fix_loc {n : ℕ} {D : TypeDat E n} {f : G1 E n → ℂ} {Kf : Subgroup (AdelicGLn.FiniteAdelicGL E n)} (hL : D.Level Kf) (hf : D.Fix f)
    {w : Pl E} (hw : (GLnLocal.integralGL (w.adicCompletion E) n).map (AdelicGLn.localEmbedding w) ≤ Kf) {x : G1 E n} (hx : LocAt w x)
    (g : G1 E n) : f (g * x) = f g := by
  have e := congrArg (AdelicGLn.prodEquiv E n) (locAt_eq w hx)
  rw [AutomorphicForm.prodEquiv_finEmb] at e
  have h1 : (AdelicGLn.prodEquiv E n x).1 = 1 := by rw [e]
  have h2 : (AdelicGLn.prodEquiv E n x).2 ∈ Kf := by
    rw [e]
    exact hw (Subgroup.mem_map_of_mem _ (locAt_int w hx))
  exact fix_inv hL hf ((hL.1 x h1).2 h2) h1 g
private theorem blo_of [IsTotallyComplex E] {S : Set (Pl E)} {τ : Submodule ℂ (L2 (BW.mu1 E 2))} (hτ : CuspIrr (BW.mu1 E 2) τ)
    {m : (E →+* ℂ) → Multiset ℂ} {B : Pl E → Multiset ℂ} (hAt : At (BW.mu1 E 2) S τ m B) {φ : G1 E 2 → ℂ} (h0 : φ ≠ 0)
    (hφ : Rd τ φ) (hK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG E 2 => fun m => φ (m * k))))
    (hS : ∀ w ∉ S, ∀ x, LocAt w x → ∀ g, φ (g * x) = φ g) :
    ∃ b : BW.Blo S 2, BloIn b τ m B ∧ ∀ g : G1 E 2, b.f.1 (g : GlobalTheory.CuspRep.GA E 2) = φ g := by
  classical
  obtain ⟨-, Φ, hc, hΦ, hmem⟩ := cuspIrr_kFinite_rep_eq_centralCuspForm (BW.mu1 E 2) τ hτ φ hφ.cont hφ.rep hK
  have hV : IsSummand (BW.mu1 E 2) τ := ⟨hτ.le, hτ.closed, hτ.inv, hτ.ne, hτ.irr⟩
  obtain ⟨π, hπ, -⟩ := Dp.exCusp E 2 (BW.mu1 E 2) τ hV
  have hΦπ : UpperTheory.V.Cm.ofCusp E 2 Φ ∈ π.V := by
    rw [← UpperTheory.V.Cm.mem_carrier, hπ.carrier_eq]
    exact ⟨hc, hmem⟩
  have hret : ∀ g, Φ.1 g = φ (retractOne g) := fun g => by
    have e1 : g = (retractOne g : AdelicGLn.AdelicGL E 2) * centralSection E 2 (detModule E 2 g) := by
      rw [coe_retractOne, inv_mul_cancel_right]
    rw [← hΦ]
    conv_lhs => rw [e1, apply_mul_centralSection_of_mem hc]
  have hne : UpperTheory.V.Cm.ofCusp E 2 Φ ≠ 0 := fun e => h0 (funext fun g => by
    rw [← hΦ]
    exact congrArg (fun f : GlobalTheory.CuspRep.Sm E 2 => f.1 g) e)
  have hinf : ∀ σ, (m σ).card = 2 ∧ ∀ u : ℂ, ∀ ψ ∈ π.V, GlobalTheory.CuspRep.cap σ u ψ = ((m σ).map fun x => u + x).prod • ψ :=
    fun σ => (Dp.sInfIff E 2 _ π τ hπ σ (m σ)).1 (hAt.1 σ)
  have hΛ : ∀ σ, ∃ Λ : Fin 2 → ℂ, (Finset.univ.val.map fun i => Λ i) = m σ := fun σ => by
    obtain ⟨a, b, e⟩ := Multiset.card_eq_two.1 (hinf σ).1
    exact ⟨![a, b], by rw [e]; rfl⟩
  choose Λ hΛ using hΛ
  have hsat : ∀ w, ∃ B' : Multiset ℂˣ, w ∉ S → B w = B'.map (fun b : ℂˣ => (b : ℂ)) ∧ GlobalTheory.LFun.HasSatGL w (π.locRep w) B' := by
    intro w
    by_cases hw : w ∈ S
    · exact ⟨0, fun h => (h hw).elim⟩
    · obtain ⟨B', h⟩ := (Dp.sSatIff E 2 _ π τ hπ w (B w)).1 (hAt.2 w hw)
      exact ⟨B', fun _ => h⟩
  choose B' hB' using hsat
  refine ⟨⟨two_pos, UpperTheory.V.Cm.ofCusp E 2 Φ, hne, Φ.2, fun t g => ?_, ⟨τ, hV, hmem⟩, Λ, fun σ u => ?_, B', fun w hw => ?_⟩,
    ⟨?_, hΛ, fun w hw => (hB' w hw).1.symm⟩, hΦ⟩
  · show Φ.1 _ = Φ.1 _
    rw [hret, hret, BW.zt, retractOne_mul, retractOne_centralSection, one_mul]
  · rw [(hinf σ).2 u _ hΦπ, ← hΛ σ, Multiset.map_map]
    rfl
  · have hfix : (⟨_, hΦπ⟩ : π.V) ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w 2) := by
      refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (Subtype.ext (funext fun g => ?_))
      show Φ.1 (g * GlobalTheory.CuspRep.finGL E 2 (GlobalTheory.CuspRep.locGL E 2 w k)) = Φ.1 g
      rw [hret, hret, retractOne_mul, ← UpperTheory.V.Fb.finEmb_eq, (UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL E 2 w).1]
      exact hS w hw _ (locAt_retract w ((UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL E 2 w).2 ▸ hk)) _
    exact ((hB' w hw).2.2 _ hfix fun e => hne (congrArg Subtype.val e)).map π.V.subtype (fun _ _ => rfl) hne
  · obtain ⟨v, hv, hr⟩ := hφ.rep
    refine ⟨v, hv, ?_⟩
    simp only [UpperTheory.V.Cm.coe_ofCusp, hΦ]
    exact hr

private def GS (S : Set (Pl E)) (F : Submodule ℂ (G1 E 2 → ℂ)) : Submodule ℂ (G1 E 2 → ℂ) where
  carrier := {φ | φ ∈ F ∧ (∀ u : KG E 2, (fun m => φ (m * u)) ∈ F) ∧ ∀ w ∉ S, ∀ x, LocAt w x → ∀ g, φ (g * x) = φ g}
  add_mem' := fun {a b} ha hb => ⟨F.add_mem ha.1 hb.1, fun u => F.add_mem (ha.2.1 u) (hb.2.1 u), fun w hw x hx g => by
    simp only [Pi.add_apply]
    rw [ha.2.2 w hw x hx, hb.2.2 w hw x hx]⟩
  zero_mem' := ⟨F.zero_mem, fun _ => F.zero_mem, fun _ _ _ _ _ => rfl⟩
  smul_mem' := fun c a ha => ⟨F.smul_mem c ha.1, fun u => F.smul_mem c (ha.2.1 u), fun w hw x hx g => by
    simp only [Pi.smul_apply]
    rw [ha.2.2 w hw x hx]⟩

private theorem out_eq {φ : G1 E 2 → ℂ} (h : ∀ γ ∈ Gam E 2, ∀ m, φ (γ * m) = φ m) (q : RightCosetSpace (Gam E 2)) :
    φ (Quotient.out q) = quotFun φ h q := by
  conv_rhs => rw [← Quotient.out_eq q]
  rfl

private theorem qint {τ τ' : Submodule ℂ (L2 (BW.mu1 E 2))} {φ ψ : G1 E 2 → ℂ} (hφ : Rd τ φ) (hψ : Rd τ' ψ) :
    Integrable (fun q : RightCosetSpace (Gam E 2) => φ (Quotient.out q) * starRingEnd ℂ (ψ (Quotient.out q))) (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := by
  have := isFiniteMeasure_quotientMeasure (K := E) (n := 2) (BW.mu1 E 2)
  obtain ⟨C, hC⟩ := hφ.decay 0
  obtain ⟨C', hC'⟩ := hψ.decay 0
  have hc : Continuous fun q : RightCosetSpace (Gam E 2) => φ (Quotient.out q) * starRingEnd ℂ (ψ (Quotient.out q)) := by
    have e : (fun q : RightCosetSpace (Gam E 2) => φ (Quotient.out q) * starRingEnd ℂ (ψ (Quotient.out q))) =
        fun q => quotFun φ hφ.rat q * starRingEnd ℂ (quotFun ψ hψ.rat q) :=
      funext fun q => by rw [out_eq hφ.rat, out_eq hψ.rat]
    rw [e]
    exact (continuous_quotFun _ hφ.cont).mul (Complex.continuous_conj.comp (continuous_quotFun _ hψ.cont))
  refine Integrable.of_bound hc.aestronglyMeasurable (C * C') (Eventually.of_forall fun q => ?_)
  have h1 := hC (Quotient.out q)
  have h2 := hC' (Quotient.out q)
  simp only [pow_zero, mul_one] at h1 h2
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

private theorem qpos {τ : Submodule ℂ (L2 (BW.mu1 E 2))} {φ : G1 E 2 → ℂ} (hφ : Rd τ φ) (h0 : φ ≠ 0) :
    ∫ q : RightCosetSpace (Gam E 2), φ (Quotient.out q) * starRingEnd ℂ (φ (Quotient.out q)) ∂(quotientMeasure (Gam E 2) (BW.mu1 E 2)) ≠ 0 := by
  intro hz
  have e : (fun q : RightCosetSpace (Gam E 2) => φ (Quotient.out q) * starRingEnd ℂ (φ (Quotient.out q))) =
      fun q => (((‖φ (Quotient.out q)‖ ^ 2 : ℝ)) : ℂ) := funext fun q => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hi := qint hφ hφ
  rw [e] at hz hi
  rw [integral_complex_ofReal] at hz
  have hr : ∫ q : RightCosetSpace (Gam E 2), ‖φ (Quotient.out q)‖ ^ 2 ∂(quotientMeasure (Gam E 2) (BW.mu1 E 2)) = 0 := by exact_mod_cast hz
  have hi' : Integrable (fun q : RightCosetSpace (Gam E 2) => ‖φ (Quotient.out q)‖ ^ 2) (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := hi.re
  have hae := (integral_eq_zero_iff_of_nonneg (fun q => by positivity) hi').1 hr
  have hμ : ∀ᵐ y ∂(BW.mu1 E 2), φ y = 0 := by
    have h2 := (quasiMeasurePreserving_mk (Gam E 2) (BW.mu1 E 2)).ae hae
    refine h2.mono fun y hy => ?_
    have h3 : φ (Quotient.out (mk (Gam E 2) y)) = φ y := by
      rw [out_eq hφ.rat, quotFun_mk]
    have h4 : ‖φ (Quotient.out (mk (Gam E 2) y))‖ ^ 2 = 0 := hy
    rw [h3] at h4
    simpa using h4
  exact h0 ((Continuous.ae_eq_iff_eq (BW.mu1 E 2) hφ.cont continuous_const).1 hμ)

private theorem blo_gs [IsTotallyComplex E] {S : Set (Pl E)} {τ : Submodule ℂ (L2 (BW.mu1 E 2))} (hτ : CuspIrr (BW.mu1 E 2) τ)
    {m : (E →+* ℂ) → Multiset ℂ} {B : Pl E → Multiset ℂ} (hAt : At (BW.mu1 E 2) S τ m B) {F : Submodule ℂ (G1 E 2 → ℂ)}
    [FiniteDimensional ℂ F] (r : ∀ φ ∈ F, Rd τ φ) {φ : G1 E 2 → ℂ} (hφ : φ ∈ GS S F) (h0 : φ ≠ 0) :
    ∃ b : BW.Blo S 2, BloIn b τ m B ∧ ∀ g : G1 E 2, b.f.1 (g : GlobalTheory.CuspRep.GA E 2) = φ g := by
  refine blo_of hτ hAt h0 (r _ hφ.1) ?_ hφ.2.2
  have hle : Submodule.span ℂ (Set.range fun k : KG E 2 => fun m => φ (m * k)) ≤ F :=
    Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hφ.2.1 u)
  exact Submodule.finiteDimensional_of_le hle

private theorem core [IsTotallyComplex E] {S : Set (Pl E)} {τa τb : Submodule ℂ (L2 (BW.mu1 E 2))} (ha : CuspIrr (BW.mu1 E 2) τa)
    (hb : CuspIrr (BW.mu1 E 2) τb) {ma mb : (E →+* ℂ) → Multiset ℂ} {Ba Bb : Pl E → Multiset ℂ}
    (Aa : At (BW.mu1 E 2) S τa ma Ba) (Ab : At (BW.mu1 E 2) S τb mb Bb) {Ea Eb : Submodule ℂ (G1 E 2 → ℂ)}
    [FiniteDimensional ℂ Ea] [FiniteDimensional ℂ Eb] (ra : ∀ φ ∈ Ea, Rd τa φ) (rb : ∀ φ ∈ Eb, Rd τb φ)
    (F : G1 E 2 → G1 E 2 → ℂ) (h1 : ∀ y, (fun x => F x y) ∈ GS S Ea) (h2 : ∀ x, F x ∈ GS S Eb)
    (hz : ∀ (b b' : BW.Blo S 2), BloIn b τa ma Ba → BloIn b' τb mb Bb →
      ∫ m₁ : RightCosetSpace (Gam E 2), ∫ m₂ : RightCosetSpace (Gam E 2), F (Quotient.out m₁) (Quotient.out m₂) *
        starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) *
        starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))
        ∂quotientMeasure (Gam E 2) (BW.mu1 E 2) ∂quotientMeasure (Gam E 2) (BW.mu1 E 2) = 0) :
    ∀ x y, F x y = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨x₀, y₀, hne⟩ := hcon
  haveI : FiniteDimensional ℂ (GS S Ea) := Submodule.finiteDimensional_of_le (fun φ (h : φ ∈ GS S Ea) => h.1)
  haveI : FiniteDimensional ℂ (GS S Eb) := Submodule.finiteDimensional_of_le (fun φ (h : φ ∈ GS S Eb) => h.1)
  have hψ0 : F x₀ ≠ 0 := fun e => hne (congrFun e y₀)
  obtain ⟨b', hb'in, hb'⟩ := blo_gs hb Ab rb (h2 x₀) hψ0
  obtain ⟨a, c, φ, ψ, xs, ys, s, t, hφ, hψ, hexp⟩ := tens (GS S Ea) (GS S Eb)
  have r0 : Rd τb (F x₀) := rb _ (h2 x₀).1
  set H : G1 E 2 → ℂ := fun u => ∫ m₂ : RightCosetSpace (Gam E 2), F u (Quotient.out m₂) * starRingEnd ℂ (F x₀ (Quotient.out m₂))
    ∂quotientMeasure (Gam E 2) (BW.mu1 E 2) with hHdef
  have hH : H ∈ GS S Ea := by
    set C : Fin a → Fin c → ℂ := fun i j => ∑ p, ∑ q, s i p * t j q * F (xs i p) (ys j q) with hC
    set l : Fin c → ℂ := fun j => ∫ m₂ : RightCosetSpace (Gam E 2), ψ j (Quotient.out m₂) * starRingEnd ℂ (F x₀ (Quotient.out m₂))
      ∂quotientMeasure (Gam E 2) (BW.mu1 E 2) with hl
    have e : H = ∑ i, (∑ j, C i j * l j) • φ i := by
      funext u
      have hi : ∀ i j, Integrable (fun q : RightCosetSpace (Gam E 2) => C i j * φ i u * (ψ j (Quotient.out q) * starRingEnd ℂ (F x₀ (Quotient.out q))))
          (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := fun i j => (qint (rb _ (hψ j).1) r0).const_mul _
      have e1 : ∀ q : RightCosetSpace (Gam E 2), F u (Quotient.out q) * starRingEnd ℂ (F x₀ (Quotient.out q)) =
          ∑ i, ∑ j, C i j * φ i u * (ψ j (Quotient.out q) * starRingEnd ℂ (F x₀ (Quotient.out q))) := fun q => by
        rw [hexp F h1 h2 u (Quotient.out q), Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      simp only [hHdef, e1]
      rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi i j]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ fun j _ => hi i j, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      ring
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i)
  have hH0 : H ≠ 0 := fun e => qpos r0 hψ0 (congrFun e x₀)
  obtain ⟨b, hbin, hb0⟩ := blo_gs ha Aa ra hH hH0
  refine qpos (ra _ hH.1) hH0 ((integral_congr_ae (Eventually.of_forall fun m₁ => ?_)).trans (hz b b' hbin hb'in))
  show H (Quotient.out m₁) * starRingEnd ℂ (H (Quotient.out m₁)) = _
  have e2 : ∀ m₂ : RightCosetSpace (Gam E 2), F (Quotient.out m₁) (Quotient.out m₂) *
      starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) *
      starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) =
      starRingEnd ℂ (H (Quotient.out m₁)) * (F (Quotient.out m₁) (Quotient.out m₂) * starRingEnd ℂ (F x₀ (Quotient.out m₂))) := fun m₂ => by
    rw [hb0, hb']
    ring
  simp only [e2]
  rw [integral_const_mul, mul_comm]

private theorem slices_zero [IsTotallyComplex E] {S : Set (Pl E)} {τa τb : Submodule ℂ (L2 (BW.mu1 E 2))} (ha : CuspIrr (BW.mu1 E 2) τa)
    (hb : CuspIrr (BW.mu1 E 2) τb) {ma mb : (E →+* ℂ) → Multiset ℂ} {Ba Bb : Pl E → Multiset ℂ}
    (Aa : At (BW.mu1 E 2) S τa ma Ba) (Ab : At (BW.mu1 E 2) S τb mb Bb) {Ea Eb : Submodule ℂ (G1 E 2 → ℂ)}
    [FiniteDimensional ℂ Ea] [FiniteDimensional ℂ Eb] (ra : ∀ φ ∈ Ea, Rd τa φ) (rb : ∀ φ ∈ Eb, Rd τb φ)
    (f : G1 E (2 + 2) → ℂ)
    (hs : ∀ k ∈ KG E (2 + 2), (∀ m₂ : G1 E 2, (fun m₁ => f (lv m₁ m₂ 0 * k)) ∈ Ea) ∧ ∀ m₁ : G1 E 2, (fun m₂ => f (lv m₁ m₂ 0 * k)) ∈ Eb)
    (hfix : ∀ w ∉ S, ∀ x : G1 E (2 + 2), LocAt w x → ∀ g, f (g * x) = f g)
    (hv : ∀ (b b' : BW.Blo S 2), BloIn b τa ma Ba → BloIn b' τb mb Bb → ∀ k ∈ KG E (2 + 2), ell b b' k f = 0)
    (k : G1 E (2 + 2)) (hk : k ∈ KG E (2 + 2)) (x y : G1 E 2) : f (lv x y 0 * k) = 0 := by
  obtain ⟨-, hmul, -, -, -, -, -, -, -, -, hK, -⟩ := blkLaws (K := E)
  have h1 : ∀ y : G1 E 2, (fun x : G1 E 2 => f (lv x y 0 * k)) ∈ GS S Ea := fun y => by
    refine ⟨(hs k hk).1 y, fun u => ?_, fun w hw x hx g => ?_⟩
    · have e : (fun m : G1 E 2 => f (lv (m * (u : G1 E 2)) y 0 * k)) = fun m => f (lv m y 0 * (lv (u : G1 E 2) 1 0 * k)) := funext fun m => by
        rw [← mul_assoc, hmul, mul_one, add_zero]
      show (fun m : G1 E 2 => f (lv (m * (u : G1 E 2)) y 0 * k)) ∈ Ea
      rw [e]
      exact (hs _ (mul_mem (hK _ u.2 1 (one_mem _)) hk)).1 y
    · have e : lv (g * x) y 0 * k = lv g y 0 * k * (k⁻¹ * lv x 1 0 * k) := by
        have e0 : lv (g * x) y 0 = lv g y 0 * lv x 1 0 := by rw [hmul, mul_one, add_zero]
        rw [e0]
        simp only [mul_assoc, mul_inv_cancel_left]
      show f (lv (g * x) y 0 * k) = f (lv g y 0 * k)
      rw [e]
      exact hfix w hw _ (locAt_conj w (locAt_lv₁ w hx) hk) _
  have h2 : ∀ x : G1 E 2, (fun y : G1 E 2 => f (lv x y 0 * k)) ∈ GS S Eb := fun x => by
    refine ⟨(hs k hk).2 x, fun u => ?_, fun w hw y hy g => ?_⟩
    · have e : (fun m : G1 E 2 => f (lv x (m * (u : G1 E 2)) 0 * k)) = fun m => f (lv x m 0 * (lv 1 (u : G1 E 2) 0 * k)) := funext fun m => by
        rw [← mul_assoc, hmul, mul_one, add_zero]
      show (fun m : G1 E 2 => f (lv x (m * (u : G1 E 2)) 0 * k)) ∈ Eb
      rw [e]
      exact (hs _ (mul_mem (hK 1 (one_mem _) _ u.2) hk)).2 x
    · have e : lv x (g * y) 0 * k = lv x g 0 * k * (k⁻¹ * lv 1 y 0 * k) := by
        have e0 : lv x (g * y) 0 = lv x g 0 * lv 1 y 0 := by rw [hmul, mul_one, add_zero]
        rw [e0]
        simp only [mul_assoc, mul_inv_cancel_left]
      show f (lv x (g * y) 0 * k) = f (lv x g 0 * k)
      rw [e]
      exact hfix w hw _ (locAt_conj w (locAt_lv₂ w hy) hk) _
  exact core ha hb Aa Ab ra rb (fun x y => f (lv x y 0 * k)) h1 h2 (fun b b' hb hb' => hv b b' hb hb' k hk) x y

private theorem eq_zero_of_slices {f : G1 E (2 + 2) → ℂ} (hun : ∀ X g, f (nn X * g) = f g) (hray : ∀ t g, f (lv 1 1 t * g) = f g)
    (h : ∀ k ∈ KG E (2 + 2), ∀ x y, f (lv x y 0 * k) = 0) : f = 0 := by
  obtain ⟨-, hmul, -⟩ := blkLaws (K := E)
  funext g
  obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
  have e : lv m₁ m₂ t = lv 1 1 t * lv m₁ m₂ 0 := by rw [hmul, one_mul, one_mul, add_zero]
  rw [mul_assoc, hun, e, mul_assoc, hray]
  exact h k hk m₁ m₂

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bloEx :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (v : Eu 𝔵.d'),
      (∀ (b b' : BW.Blo 𝔢.S 2), BloIn b 𝔵.τ₂ 𝔵.m₂ 𝔵.B₂ → BloIn b' 𝔵.τ₁ 𝔵.m₁ 𝔵.B₁ → ∀ k ∈ KG E (2 + 2), ell b b' k (𝔵.A'.sec v) = 0) → v = 0 := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 v hv
  have hfS := (𝔵.A'.onto (𝔵.A'.sec v)).1 ⟨v, rfl⟩
  have hp := 𝔵.pair
  obtain ⟨hc, -, hun, hray, hsl⟩ := (secCrit (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ 𝔵.D hp.irr₂ hp.irr₁ _ hfS.2).1 hfS.1
  obtain ⟨E₁, E₂, fd₁, fd₂, r₁, r₂, hst⟩ := secStr (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ 𝔵.D hp.irr₂ hp.irr₁
  have hs := hst _ hc hfS.2 hsl
  have hfix : ∀ w ∉ 𝔢.S, ∀ x : G1 E (2 + 2), LocAt w x → ∀ g, 𝔵.A'.sec v (g * x) = 𝔵.A'.sec v g := fun w hw x hx g =>
    fix_loc 𝔵.level hfS.2 (𝔢.max w hw) hx g
  have h0 := eq_zero_of_slices hun hray fun k hk x y => slices_zero hp.irr₂ hp.irr₁ 𝔵.at₂ 𝔵.at₁ r₁ r₂ _ hs hfix hv k hk x y
  exact 𝔵.A'.inj (by rw [h0, map_zero])
