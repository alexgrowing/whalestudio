import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeOperatorExistence

section Abs

variable {G X : Type} [Group G] [Group X]

private def dbl (U : Subgroup G) (h : G) : Set (G ⧸ U) :=
  {c | ∃ u ∈ U, c = QuotientGroup.mk (u * h)}

private theorem dbl_finite [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G} (hU : CO U) (h : G) :
    (dbl U h).Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * h) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hU.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private noncomputable def ops (j : G →* X) (U : Subgroup G) (h : G) (Φ : X → ℂ) (x : X) : ℂ :=
  ∑ᶠ c ∈ dbl U h, Φ (x * j c.out)

private def Inv (j : G →* X) (U : Subgroup G) (Φ : X → ℂ) : Prop := ∀ u ∈ U, ∀ x, Φ (x * j u) = Φ x

variable {j : G →* X} {U : Subgroup G} {h h' : G} {Φ Ψ : X → ℂ}

private theorem val_congr (hΦ : Inv j U Φ) {a b : G} (hab : (QuotientGroup.mk a : G ⧸ U) = QuotientGroup.mk b) (x : X) :
    Φ (x * j a) = Φ (x * j b) := by
  have h1 := hΦ _ (QuotientGroup.eq.1 hab) (x * j a)
  have h2 : x * j a * j (a⁻¹ * b) = x * j b := by rw [mul_assoc, ← map_mul, mul_inv_cancel_left]
  rw [h2] at h1
  exact h1.symm

private theorem ops_sum (hf : (dbl U h).Finite) (x : X) :
    ops j U h Φ x = ∑ c ∈ hf.toFinset, Φ (x * j c.out) :=
  finsum_mem_eq_finite_toFinset_sum _ hf

private theorem ops_rep (hf : (dbl U h).Finite) (hΦ : Inv j U Φ) (r : G ⧸ U → G)
    (hr : ∀ c, (QuotientGroup.mk (r c) : G ⧸ U) = c) (x : X) :
    ops j U h Φ x = ∑ c ∈ hf.toFinset, Φ (x * j (r c)) := by
  rw [ops_sum hf]
  refine Finset.sum_congr rfl fun c _ => val_congr hΦ ?_ x
  rw [hr, QuotientGroup.out_eq']

private theorem ops_add (hf : (dbl U h).Finite) : ops j U h (Φ + Ψ) = ops j U h Φ + ops j U h Ψ := by
  funext x
  simp only [Pi.add_apply, ops_sum hf, Finset.sum_add_distrib]

private theorem ops_smul (hf : (dbl U h).Finite) (a : ℂ) : ops j U h (a • Φ) = a • ops j U h Φ := by
  funext x
  simp only [Pi.smul_apply, ops_sum hf, Finset.smul_sum]

private theorem mk_left {u a b : G} (hab : (QuotientGroup.mk a : G ⧸ U) = QuotientGroup.mk b) :
    (QuotientGroup.mk (u * a) : G ⧸ U) = QuotientGroup.mk (u * b) := by
  rw [QuotientGroup.eq] at hab ⊢
  simpa [mul_assoc] using hab

private theorem ops_inv (hΦ : Inv j U Φ) : Inv j U (ops j U h Φ) := by
  intro u hu x
  have hm : ∀ v ∈ U, Set.MapsTo (fun c : G ⧸ U => (QuotientGroup.mk (v * c.out) : G ⧸ U)) (dbl U h) (dbl U h) := by
    rintro v hv c ⟨t, ht, rfl⟩
    refine ⟨v * t, U.mul_mem hv ht, ?_⟩
    change (QuotientGroup.mk (v * (QuotientGroup.mk (t * h) : G ⧸ U).out) : G ⧸ U) = _
    rw [mk_left (QuotientGroup.out_eq' _), mul_assoc]
  have hi : ∀ v : G, Set.LeftInvOn (fun c : G ⧸ U => (QuotientGroup.mk (v⁻¹ * c.out) : G ⧸ U))
      (fun c : G ⧸ U => (QuotientGroup.mk (v * c.out) : G ⧸ U)) (dbl U h) := by
    intro v c _
    change (QuotientGroup.mk (v⁻¹ * (QuotientGroup.mk (v * c.out) : G ⧸ U).out) : G ⧸ U) = c
    rw [mk_left (QuotientGroup.out_eq' _), inv_mul_cancel_left, QuotientGroup.out_eq']
  have hi' : Set.RightInvOn (fun c : G ⧸ U => (QuotientGroup.mk (u⁻¹ * c.out) : G ⧸ U))
      (fun c : G ⧸ U => (QuotientGroup.mk (u * c.out) : G ⧸ U)) (dbl U h) := by
    intro c _
    change (QuotientGroup.mk (u * (QuotientGroup.mk (u⁻¹ * c.out) : G ⧸ U).out) : G ⧸ U) = c
    rw [mk_left (QuotientGroup.out_eq' _), mul_inv_cancel_left, QuotientGroup.out_eq']
  have hb : Set.BijOn (fun c : G ⧸ U => (QuotientGroup.mk (u * c.out) : G ⧸ U)) (dbl U h) (dbl U h) :=
    Set.InvOn.bijOn ⟨hi u, hi'⟩ (hm u hu) (hm u⁻¹ (U.inv_mem hu))
  refine finsum_mem_eq_of_bijOn _ hb fun c _ => ?_
  have h1 := val_congr (x := x) hΦ (QuotientGroup.out_eq' (QuotientGroup.mk (u * c.out) : G ⧸ U)).symm
  rw [map_mul, ← mul_assoc] at h1
  exact h1

private theorem ops_comm (hf : (dbl U h).Finite) (hf' : (dbl U h').Finite) (hΦ : Inv j U Φ) (r r' : G ⧸ U → G)
    (hr : ∀ c, (QuotientGroup.mk (r c) : G ⧸ U) = c) (hr' : ∀ c, (QuotientGroup.mk (r' c) : G ⧸ U) = c)
    (hc : ∀ c ∈ dbl U h, ∀ c' ∈ dbl U h', Commute (r c) (r' c')) (x : X) :
    ops j U h (ops j U h' Φ) x = ops j U h' (ops j U h Φ) x := by
  rw [ops_rep hf (ops_inv hΦ) r hr, ops_rep hf' (ops_inv hΦ) r' hr']
  simp only [ops_rep hf' hΦ r' hr', ops_rep hf hΦ r hr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' hc' => Finset.sum_congr rfl fun c hc₁ => ?_
  have := (hc c (hf.mem_toFinset.1 hc₁) c' (hf'.mem_toFinset.1 hc')).eq
  rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul, this]

private theorem rep_in (P : Subgroup G) (hh : h ∈ P)
    (hs : ∀ u ∈ U, ∃ a ∈ P, ∃ t ∈ U, u = a * t ∧ Commute t h) :
    ∃ r : G ⧸ U → G, (∀ c, (QuotientGroup.mk (r c) : G ⧸ U) = c) ∧ ∀ c ∈ dbl U h, r c ∈ P := by
  have h1 : ∀ c : G ⧸ U, ∃ p : G, (QuotientGroup.mk p : G ⧸ U) = c ∧ (c ∈ dbl U h → p ∈ P) := by
    intro c
    by_cases hc : c ∈ dbl U h
    · obtain ⟨u, hu, rfl⟩ := hc
      obtain ⟨a, ha, t, ht, rfl, hcm⟩ := hs u hu
      refine ⟨a * h, ?_, fun _ => P.mul_mem ha hh⟩
      rw [QuotientGroup.eq]
      have : (a * h)⁻¹ * (a * t * h) = t := by
        rw [mul_assoc a t h, hcm.eq]
        group
      rw [this]
      exact ht
    · exact ⟨c.out, QuotientGroup.out_eq' c, fun h' => absurd h' hc⟩
  choose r h2 h3 using h1
  exact ⟨r, h2, h3⟩

end Abs

section Con

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem lev_split (W : ∀ v : Pl K, Subgroup (Gw n v)) (w : Pl K) (g : Gw n w) :
    ∀ u ∈ UpperTheory.ConvolutionTheory.GM.levF W, ∃ a ∈ (AdelicGLn.localEmbedding (K := K) (n := n) w).range, ∃ t ∈ UpperTheory.ConvolutionTheory.GM.levF W, u = a * t ∧
      Commute t (AdelicGLn.localEmbedding w g) := by
  intro u hu
  obtain ⟨-, h1, h2, -, h4⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have ha : AdelicGLn.localEmbedding w (finAt w (finEmb K n u)) ∈ UpperTheory.ConvolutionTheory.GM.levF W := by
    intro v
    by_cases hv : v = w
    · subst hv
      rw [h1]
      exact hu v
    · rw [h2 v hv]
      exact one_mem _
  refine ⟨_, ⟨finAt w (finEmb K n u), rfl⟩, _, mul_mem (inv_mem ha) hu, (mul_inv_cancel_left _ _).symm, ?_⟩
  have h5 : finAt w (finEmb K n ((AdelicGLn.localEmbedding w (finAt w (finEmb K n u)))⁻¹ * u)) = 1 := by
    rw [map_mul, finAt_mul, map_inv, finAt_inv, h1, inv_mul_cancel]
  exact (h4 _ h5 g).symm

private theorem norm_one_adelic_split_arch_finite (g : G1 K n) (hu : finPart K n (g : AdelicGLn.AdelicGL K n) ∈ AdelicGLn.integralFiniteGL K n) :
    g = archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) * fin1 (finPart K n (g : AdelicGLn.AdelicGL K n)) := by
  have h1 := detModule_finEmb hu
  have hg := (mem_normOneGL_iff_detModule).1 g.2
  have h2 := infEmb_infPart_mul_finEmb_finPart (g : AdelicGLn.AdelicGL K n)
  have h3 : detModule K n (infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n))) = 1 := by
    rw [← h2, map_mul, h1, mul_one] at hg
    exact hg
  ext1
  rw [Subgroup.coe_mul, ← retract_infEmb, coe_retractOne, MultiplicityOne.coe_finProj, h1, h3, map_one, inv_one, mul_one, mul_one]
  exact h2.symm

end Con

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeOperatorExistence

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeOperatorExistence in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.heckeEx :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeEx := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ _ κ e he S U hU D hD d A
  obtain ⟨hL, hLle⟩ := (levLaws (K := K) (2 + 2) S).1 U hU
  obtain ⟨⟨h0, hadd⟩, hfix, hinj, htr⟩ := secTr μ₂ τ₁ τ₂ κ e he
  obtain ⟨-, -, -, hac, -⟩ := levLaws (K := K) (2 + 2) S
  haveI := he.haar.prob
  have hHH : Continuous (HP (K := K) 2 2) := (hpSpec (K := K)).2.2.2.1
  have hflc : ∀ f : G1 K (2 + 2) → ℂ, Continuous f → Continuous (flat 0 f) := fun f hf =>
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hHH))).mul hf
  have hfadd : ∀ (f f' : G1 K (2 + 2) → ℂ) (c : ℂ), flat 0 (f + c • f') = flat 0 f + c • flat 0 f' := by
    intro f f' c
    funext x
    simp only [flat, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hA0 : FixA κ e 0 := fun g => by simp
  have hAadd : ∀ f f' : G1 K (2 + 2) → ℂ, Continuous f → Continuous f' → FixA κ e f → FixA κ e f' → ∀ c : ℂ,
      FixA κ e (f + c • f') := by
    intro f f' hc hc' hf hf' c g
    have hi : ∀ f₁ : G1 K (2 + 2) → ℂ, Continuous f₁ → Integrable (fun k => e k * f₁ (g * arc1 k)) κ := fun f₁ h₁ =>
      (he.cont.mul (h₁.comp (continuous_const.mul hac))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h1 : ∀ k, e k * (f + c • f') (g * arc1 k) = e k * f (g * arc1 k) + c * (e k * f' (g * arc1 k)) := by
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h1]
    rw [integral_add (hi f hc) ((hi f' hc').const_mul c), integral_const_mul, hf g, hf' g]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : ∀ f, IsSec τ₁ τ₂ f → FixA κ e f → ∀ C : Finset (FA K (2 + 2) ⧸ levOn S U),
      ∃ f', IsSec τ₁ τ₂ f' ∧ FixA κ e f' ∧ ∀ x, flat 0 f' x = ∑ c ∈ C, flat 0 f (x * fin1 c.out) := by
    intro f hs hA C
    induction C using Finset.induction_on with
    | empty => exact ⟨0, h0, hA0, fun x => by simp [flat]⟩
    | insert c C hc ih =>
      obtain ⟨f₁, hs₁, hA₁, hx₁⟩ := ih
      obtain ⟨f₂, hs₂, hA₂, hx₂⟩ := htr f c.out hs hA
      refine ⟨f₂ + (1 : ℂ) • f₁, hadd _ _ hs₂ hs₁ 1, hAadd _ _ hs₂.cont hs₁.cont hA₂ hA₁ 1, fun x => ?_⟩
      rw [hfadd, Finset.sum_insert hc, Pi.add_apply, Pi.smul_apply, hx₁, hx₂, one_smul]
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hFx : ∀ v, FixA κ e (A.sec v) ∧ FixF (levOn S U) (A.sec v) := fun v =>
    (hD.fix _ (hsec v).1.cont).1 (hsec v).2
  have hTc : ∀ v, Continuous (flat 0 (A.sec v)) := fun v => hflc _ (hsec v).1.cont
  have hTi : ∀ v, Inv (MultiplicityOne.finProj K (2 + 2)) (levOn S U) (flat 0 (A.sec v)) := fun v =>
    ((hfix _ (hsec v).1.cont).2 _ hLle).2 (hFx v).2
  have hTj : ∀ a b, flat 0 (A.sec a) = flat 0 (A.sec b) → a = b := fun a b h => A.inj (hinj _ _ h)
  have hTa : ∀ a b : Eu d, flat 0 (A.sec (a + b)) = flat 0 (A.sec a) + flat 0 (A.sec b) := by
    intro a b
    have h1 := hfadd (A.sec a) (A.sec b) 1
    rw [one_smul, one_smul] at h1
    rw [map_add, h1]
  have hTs : ∀ (c : ℂ) (a : Eu d), flat 0 (A.sec (c • a)) = c • flat 0 (A.sec a) := by
    intro c a
    funext x
    simp only [flat, map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hop_eq : ∀ h (Φ : G1 K (2 + 2) → ℂ), hop (levOn S U) h Φ = ops (MultiplicityOne.finProj K (2 + 2)) (levOn S U) h Φ :=
    fun _ _ => rfl
  have hex : ∀ h v, ∃ v', flat 0 (A.sec v') = hop (levOn S U) h (flat 0 (A.sec v)) := by
    intro h v
    obtain ⟨f', hs', hA', hx'⟩ := hsum _ (hsec v).1 (hFx v).1 (dbl_finite hL h).toFinset
    have h1 : flat 0 f' = hop (levOn S U) h (flat 0 (A.sec v)) := by
      funext x
      rw [hx', hop_eq, ops_sum (dbl_finite hL h)]
    have h2 : FixF (levOn S U) f' :=
      ((hfix _ hs'.cont).2 _ hLle).1 (by rw [h1, hop_eq]; exact ops_inv (hTi v))
    obtain ⟨v', rfl⟩ := (A.onto f').2 ⟨hs', (hD.fix _ hs'.cont).2 ⟨hA', h2⟩⟩
    exact ⟨v', h1⟩
  refine ⟨fun h => ?_, fun w w' hne g g' M M' hM hM' => ?_, fun b φ β hφ hAct h M hM => ?_⟩
  · have hf := dbl_finite hL h
    choose m hm using hex h
    refine ⟨{ toFun := m, map_add' := fun a b => ?_, map_smul' := fun c a => ?_ }, fun v => hm v, fun M' hM' => ?_⟩
    · apply hTj
      rw [hm (a + b), hTa a b, hTa (m a) (m b), hm a, hm b, hop_eq, hop_eq, hop_eq]
      exact ops_add hf
    · apply hTj
      simp only [RingHom.id_apply]
      rw [hm (c • a), hTs c a, hTs c (m a), hm a, hop_eq, hop_eq]
      exact ops_smul hf c
    · exact LinearMap.ext fun v => hTj _ _ ((hM' v).trans (hm v).symm)
  · have hf := dbl_finite hL (AdelicGLn.localEmbedding w g)
    have hf' := dbl_finite hL (AdelicGLn.localEmbedding w' g')
    obtain ⟨r, hr, hrP⟩ := rep_in (AdelicGLn.localEmbedding w).range ⟨g, rfl⟩ (lev_split _ w g)
    obtain ⟨r', hr', hrP'⟩ := rep_in (AdelicGLn.localEmbedding w').range ⟨g', rfl⟩ (lev_split _ w' g')
    refine LinearMap.ext fun v => hTj _ _ ?_
    change flat 0 (A.sec (M (M' v))) = flat 0 (A.sec (M' (M v)))
    rw [hM (M' v), hM' v, hM' (M v), hM v]
    funext x
    refine ops_comm hf hf' (hTi v) r r' hr hr' (fun c hc c' hc' => ?_) x
    obtain ⟨y, hy⟩ := hrP c hc
    obtain ⟨y', hy'⟩ := hrP' c' hc'
    rw [← hy, ← hy']
    exact (UpperTheory.ConvolutionTheory.Tf.locEmb K (2 + 2) w).2.2.2.1 w' hne.symm y y'
  · have hf := dbl_finite hL h
    have hsupp : ∀ g, tens b φ g ≠ 0 → finPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2)) ∈ levOn S U := by
      intro g hg
      by_cases hc : Continuous (tensFun b φ) ∧ HasCompactSupport (tensFun b φ)
      · have h1 : tens b φ g = tensFun b φ g := by
          rw [tens, dif_pos hc]
          rfl
        rw [h1, tensFun, hφ] at hg
        by_contra hn
        exact hg (by rw [Set.indicator_of_notMem (show _ ∉ (levOn S U : Set (FA K (2 + 2))) from hn), mul_zero])
      · have h1 : tens b φ g = 0 := by
          rw [tens, dif_neg hc]
          rfl
        exact absurd h1 hg
    have hAB := hAct.2.2 0
    refine LinearMap.ext fun v => hTj _ _ ?_
    change flat 0 (A.sec (M (PositivityTheory.Rg.Tf.IntegralApplyAeEq.symb β 0 v))) = flat 0 (A.sec (PositivityTheory.Rg.Tf.IntegralApplyAeEq.symb β 0 (M v)))
    funext x
    rw [hM (PositivityTheory.Rg.Tf.IntegralApplyAeEq.symb β 0 v), ← hAB (M v) x, hop_eq, ops_sum hf]
    have h2 : ∀ c : FA K (2 + 2) ⧸ levOn S U, flat 0 (A.sec (PositivityTheory.Rg.Tf.IntegralApplyAeEq.symb β 0 v)) (x * fin1 c.out) =
        ∫ g, tens b φ g * flat 0 (A.sec v) (x * fin1 c.out * g) ∂μ := fun c => (hAB v _).symm
    simp only [h2]
    have hint : ∀ c : FA K (2 + 2) ⧸ levOn S U, Integrable (fun g => tens b φ g * flat 0 (A.sec v) (x * fin1 c.out * g)) μ :=
      fun c => ((tens b φ).continuous.mul ((hTc v).comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        (tens b φ).hasCompactSupport.mul_right
    rw [← integral_finset_sum _ fun c _ => hint c]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    by_cases hg : tens b φ g = 0
    · simp [hg]
    have hu := hsupp g hg
    have hd := norm_one_adelic_split_arch_finite g (hLle hu)
    obtain ⟨p, hp⟩ : ∃ p, p = archP K (2 + 2) (infPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2))) := ⟨_, rfl⟩
    have hpc : ∀ y : FA K (2 + 2), p * fin1 y = fin1 y * p := fun y => by
      rw [hp]
      exact (MultiplicityOne.finProj_mul_archProj_comm y _).symm
    rw [← hp] at hd
    simp only []
    rw [← Finset.mul_sum]
    congr 1
    rw [hM v, hop_eq]
    have h3 : x * g = x * p * MultiplicityOne.finProj K (2 + 2) (finPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2))) := by
      rw [mul_assoc, ← hd]
    rw [h3, ops_inv (hTi v) _ hu, ops_sum hf]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h4 : x * fin1 c.out * g = x * p * fin1 c.out * fin1 (finPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2))) := by
      have h5 : x * fin1 c.out * g = x * fin1 c.out * (p * fin1 (finPart K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2)))) :=
        congrArg _ hd
      rw [h5, ← mul_assoc (x * fin1 c.out), mul_assoc x (fin1 c.out) p, ← hpc, ← mul_assoc x p]
    rw [h4]
    exact hTi v _ hu _
