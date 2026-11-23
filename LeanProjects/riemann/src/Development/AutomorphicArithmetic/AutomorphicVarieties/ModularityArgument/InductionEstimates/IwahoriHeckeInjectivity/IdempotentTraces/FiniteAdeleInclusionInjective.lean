import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.GalLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.FamScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.UiwAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.IrreducibleCuspidalWeightComponent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.ExistsTracePowNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CosAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

private theorem coset_tr {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f) (t : H ≃* H)
    (ht : ∀ g, t (t g) = g) (L : Subgroup G) (hL : ∀ u ∈ L, ∃ u' ∈ L, t (f u) = f u') (h h' : G) (hh : t (f h) = f h')
    (ψ : H → ℂ) (hψ : ∀ u ∈ L, ∀ y, ψ (y * f u) = ψ y) (x : H) :
    ∑ᶠ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h)}, ψ (x * f c.out) =
      ∑ᶠ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h')}, ψ (t (t x * f c.out)) := by
  have hh' : t (f h') = f h := by rw [← hh, ht]
  have dec : ∀ (a : G) (c : G ⧸ L), c = QuotientGroup.mk a → ∃ l ∈ L, c.out = a * l := by
    intro a c hc
    have : (QuotientGroup.mk c.out : G ⧸ L) = QuotientGroup.mk a := by rw [QuotientGroup.out_eq', hc]
    have h2 := QuotientGroup.eq.1 this.symm
    exact ⟨_, h2, by group⟩
  have imgOf : ∀ (p p' : G), t (f p) = f p' → ∀ u ∈ L, ∀ l ∈ L, ∃ g' u' l', u' ∈ L ∧ l' ∈ L ∧ g' = u' * p' * l' ∧ t (f (u * p * l)) = f g' := by
    intro p p' hp u hu l hl
    obtain ⟨u', hu', e1⟩ := hL u hu
    obtain ⟨l', hl', e2⟩ := hL l hl
    exact ⟨_, u', l', hu', hl', rfl, by simp only [map_mul, e1, e2, hp]⟩
  have key : ∀ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h)}, ∃ g', t (f c.out) = f g' ∧
      ∃ u' ∈ L, ∃ l' ∈ L, g' = u' * h' * l' := by
    rintro c ⟨u, hu, rfl⟩
    obtain ⟨l, hl, e⟩ := dec _ _ rfl
    obtain ⟨g', u', l', hu', hl', e1, e2⟩ := imgOf h h' hh u hu l hl
    exact ⟨g', by rw [e, e2], u', hu', l', hl', e1⟩
  classical
  let m : G ⧸ L → G ⧸ L := fun c => if hc : ∃ g', t (f c.out) = f g' then QuotientGroup.mk hc.choose else c
  have hm : ∀ c g', t (f c.out) = f g' → m c = QuotientGroup.mk g' := by
    intro c g' hg
    have hc : ∃ g', t (f c.out) = f g' := ⟨g', hg⟩
    have : hc.choose = g' := hf (hc.choose_spec.symm.trans hg)
    simp only [m, dif_pos hc, this]
  refine finsum_mem_eq_of_bijOn m ⟨?_, ?_, ?_⟩ ?_
  · intro c hc
    obtain ⟨g', e, u', hu', l', hl', rfl⟩ := key c hc
    refine ⟨u', hu', ?_⟩
    rw [hm c _ e]
    exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hl')
  · intro c hc c' hc' e
    obtain ⟨g, eg, -⟩ := key c hc
    obtain ⟨g', eg', -⟩ := key c' hc'
    rw [hm c _ eg, hm c' _ eg'] at e
    obtain ⟨l', hl', e2⟩ := hL _ (QuotientGroup.eq.1 e)
    have e3 : f (c.out⁻¹ * c'.out) = f l' := by
      rw [← e2]
      simp only [map_mul, map_inv, ← eg, ← eg', ht]
    have e4 : c.out⁻¹ * c'.out ∈ L := by rw [hf e3]; exact hl'
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    exact QuotientGroup.eq.2 e4
  · rintro c' ⟨u', hu', rfl⟩
    obtain ⟨u, hu, e1⟩ := hL u' hu'
    have e0 : t (f (u * h)) = f (u' * h') := by
      have : f (u * h) = t (f (u' * h')) := by simp only [map_mul, e1, hh']
      rw [this, ht]
    refine ⟨QuotientGroup.mk (u * h), ⟨u, hu, rfl⟩, ?_⟩
    obtain ⟨l, hl, e⟩ := dec (u * h) _ rfl
    obtain ⟨l', hl', e2⟩ := hL l hl
    have e3 : t (f (QuotientGroup.mk (u * h) : G ⧸ L).out) = f (u' * h' * l') := by
      rw [e, map_mul, map_mul, e0, e2]
      simp only [map_mul]
    rw [hm _ _ e3]
    exact (QuotientGroup.eq.2 (by simpa [mul_assoc] using L.inv_mem hl')).symm
  · intro c hc
    obtain ⟨g', e, -⟩ := key c hc
    obtain ⟨l, hl, e2⟩ := dec g' (m c) (hm c _ e)
    obtain ⟨l', hl', e3⟩ := hL l hl
    rw [e2, map_mul, map_mul, map_mul, ht, ← e, ht, e3, ← mul_assoc, hψ _ hl']

end SlopeTestRemainingChoices

section Hop

variable {K : Type} [Field K] [NumberField K]

private theorem finite_adele_inclusion_injective {n : ℕ} : Function.Injective (fin1 : FA K n → G1 K n) := by
  intro a b h
  have h2 : ((MultiplicityOne.finProj K n a : G1 K n) : AdelicGLn.AdelicGL K n) = (MultiplicityOne.finProj K n b : G1 K n) :=
    congrArg Subtype.val h
  rw [MultiplicityOne.coe_finProj, MultiplicityOne.coe_finProj] at h2
  have h3 := congrArg (CuspidalSpectrum.finPart K n) h2
  simpa only [map_mul, map_inv, finPart_centralSection, inv_one, mul_one, finPart_finEmb] using h3

private theorem hop_tr {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (θ : Twist μ) (hinv : ∀ g, θ.e (θ.e g) = g)
    (L : Subgroup (FA K n)) (hL : ∀ u ∈ L, ∃ u' ∈ L, θ.e (fin1 u) = fin1 u') (h h' : FA K n) (hh : θ.e (fin1 h) = fin1 h')
    (ψ : G1 K n → ℂ) (hψ : FixF L ψ) (x : G1 K n) :
    hop L h ψ x = hop L h' (fun y => ψ (θ.e y)) (θ.e x) :=
  coset_tr (MultiplicityOne.finProj K n) finite_adele_inclusion_injective θ.e.toMulEquiv hinv L hL h h' hh ψ hψ x

private theorem flat_fix {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure]
    {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d) {κ : Measure (archCompact K (2 + 2))} {e : archCompact K (2 + 2) → ℂ}
    {L : Subgroup (FA K (2 + 2))} (hty : IsTy D κ e L) (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2)) (v : Eu d) :
    FixF L (flat 0 (A.sec v)) := by
  obtain ⟨hs, hD⟩ := (A.onto _).1 ⟨v, rfl⟩
  have hF := ((hty.fix _ hs.cont).1 hD).2
  intro u hu g
  have hk : fin1 u ∈ KG K (2 + 2) := by
    change ((MultiplicityOne.finProj K (2 + 2) u : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup _)
    rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact (hle hu)))]
    exact finEmb_mem_maxCompact (hle hu)
  have hh : HP 2 2 (g * fin1 u) = HP 2 2 g := ((hpSpec (K := K)).2.1 _ hk).2 g
  simp only [flat, hh, hF u hu g]

end Hop

section Lines

variable {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
  {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure] {D : TypeDat K (2 + 2)} {d d' : ℕ}

private theorem flat_tw (θ : Twist μ) (hH : ∀ g, HH (θ.e g) = HH g) (f f' : G1 K (2 + 2) → ℂ)
    (h : ∀ x, f' x = f (θ.e.symm x)) (x : G1 K (2 + 2)) : flat 0 f' x = flat 0 f (θ.e.symm x) := by
  have h1 : HP 2 2 (θ.e.symm x) = HP 2 2 x := by
    have := hH (θ.e.symm x)
    rw [ContinuousMulEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [flat, h1, h]

private theorem exists_heckeAt_transport_of_linearIsometryEquiv (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d') {κ : Measure (archCompact K (2 + 2))}
    {e : archCompact K (2 + 2) → ℂ} {L : Subgroup (FA K (2 + 2))} (hty : IsTy D κ e L)
    (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2)) (θ : Twist μ) (hinv : ∀ g, θ.e (θ.e g) = g)
    (hH : ∀ g, HH (θ.e g) = HH g) (hL : ∀ u ∈ L, ∃ u' ∈ L, θ.e (fin1 u) = fin1 u') (s : Eu d ≃ₗᵢ[ℂ] Eu d')
    (hs : ∀ v x, A'.sec (s v) x = A.sec v (θ.e.symm x)) (h h' : FA K (2 + 2)) (hh : θ.e (fin1 h) = fin1 h')
    (M : Eu d →ₗ[ℂ] Eu d) (hM : HeckeAt A L h M) :
    ∃ M' : Eu d' →ₗ[ℂ] Eu d', HeckeAt A' L h' M' ∧ ∀ v, M' (s v) = s (M v) := by
  have hsy : ∀ y, θ.e.symm y = θ.e y := fun y => θ.e.injective (by rw [ContinuousMulEquiv.apply_symm_apply, hinv])
  refine ⟨(s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d') ∘ₗ M ∘ₗ (s.symm.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d), fun v' => ?_, fun v => ?_⟩
  · obtain ⟨v, rfl⟩ := s.surjective v'
    funext x
    have e1 : ((s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d') ∘ₗ M ∘ₗ (s.symm.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d)) (s v) = s (M v) := by simp
    rw [e1, flat_tw θ hH _ _ (hs (M v)) x, hM v, hop_tr θ hinv L hL h h' hh _ (flat_fix A hty hle v),
      ContinuousMulEquiv.apply_symm_apply]
    congr 1
    funext y
    rw [flat_tw θ hH _ _ (hs v) y, hsy]
  · simp

private theorem hecke_N (hp : Pair μ₂ τ₁ τ₂) [IsTotallyComplex K] (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d')
    {L : Subgroup (FA K (2 + 2))} (hlev : D.Level L) (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2))
    (hu : ∀ h, ∃! M, HeckeAt A L h M) (hu' : ∀ h, ∃! M, HeckeAt A' L h M) (N : Eu d' ≃ₗᵢ[ℂ] Eu d)
    (hN : ∀ (Y : L2 μ →L[ℂ] L2 μ) s s', Act A.J Y s → Act A'.J Y s' → ∀ w, N (s' 0 w) = s 0 (N w))
    (h : FA K (2 + 2)) (M : Eu d →ₗ[ℂ] Eu d) (M' : Eu d' →ₗ[ℂ] Eu d') (hM : HeckeAt A L h M) (hM' : HeckeAt A' L h M')
    (w : Eu d') : N (M' w) = M (N w) := by
  have hp' : Pair μ₂ τ₂ τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  obtain ⟨Y, hY⟩ : ∃ Y : L2 μ →L[ℂ] L2 μ, Y = (∑ᶠ c ∈ {c : AdelicGLn.FiniteAdelicGL K (2 + 2) ⧸ L | ∃ k ∈ L, c = QuotientGroup.mk (k * h)},
      rhoF μ c.out) ∘L prj (fixF μ L) := ⟨_, rfl⟩
  obtain ⟨⟨s, hs, hsv⟩, -⟩ := cosAct K μ μ₂ τ₁ τ₂ hp D d d' A A' L hlev hle h Y hY
  obtain ⟨⟨s', hs', hsv'⟩, -⟩ := cosAct K μ μ₂ τ₂ τ₁ hp' D d' d A' A L hlev hle h Y hY
  have e1 : M = (s 0 : Eu d →ₗ[ℂ] Eu d) := (hu h).unique hM fun v => funext fun x => hsv 0 v x
  have e2 : M' = (s' 0 : Eu d' →ₗ[ℂ] Eu d') := (hu' h).unique hM' fun v => funext fun x => hsv' 0 v x
  rw [e1, e2]
  exact hN Y s s' hs hs' w

end Lines

section Tr

private theorem gl_surj {R T : Type*} [Field R] [Field T] (f : R →+* T) (hf : Function.Surjective f) {n : ℕ}
    (g : GL (Fin n) T) : ∃ g', mapGL n f g' = g := by
  let e : R ≃+* T := RingEquiv.ofBijective f ⟨f.injective, hf⟩
  refine ⟨Matrix.GeneralLinearGroup.map (e.symm : T →+* R) g, ?_⟩
  ext i j
  exact e.apply_symm_apply _

private theorem trace_step {d d' : ℕ} (N : Eu d' ≃ₗᵢ[ℂ] Eu d) (s : Eu d ≃ₗᵢ[ℂ] Eu d') (u a g : Eu d' →L[ℂ] Eu d')
    (V : Module.End ℂ (Eu d)) (hV : ∀ w, N (u w) = V (N w)) (x : ℝ) (r : ℂ) (ha : a = (x : ℂ) • 1) (hg : g = r • 1) (j : ℕ) :
    LinearMap.trace ℂ (Eu d) ((N.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d) ∘ₗ
      ((eigP a x ∘L (u ^ j) ∘L g : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ (s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d')) =
    r * LinearMap.trace ℂ (Eu d) ((V ^ j) ∘ₗ ((s.toLinearEquiv.trans N.toLinearEquiv : Eu d ≃ₗ[ℂ] Eu d) : Eu d →ₗ[ℂ] Eu d)) := by
  have hpow : ∀ (j : ℕ) (y : Eu d'), N ((u ^ j) y) = (V ^ j) (N y) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ih, hV, Module.End.mul_apply]
  have hP : ∀ y, eigP a x y = y := by
    intro y
    refine Submodule.starProjection_eq_self_iff.2 ?_
    rw [Module.End.mem_eigenspace_iff, ha]
    simp
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  refine LinearMap.ext fun w => ?_
  change N (eigP a x ((u ^ j) (g (s w)))) = r • (V ^ j) (N (s w))
  rw [hP, hg]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul, hpow]

end Tr

private abbrev Zs (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (Pl E)) : Type :=
  {v : Pl F // ∃ w ∈ S, w.under (𝓞 F) = v}

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.famNe :
    FamNe := by
  intro F E _ _ _ _ _ _ _ _ σ hdeg hgen μ _ θ hθ 𝔢 𝔵 κ e κ₂ p₁ p₂ k₀ hAL S U hU hS heU hty hUθ w₀ hw₀ hI ν hν hUq φ hφ hg hac hBi hne N hN
  obtain ⟨c, hc, ha⟩ := hac
  have hp := 𝔵.pair
  have hp' : Pair (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  have hle : levOn S U ≤ AdelicGLn.integralFiniteGL E (2 + 2) := by
    intro u hu
    refine (AdelicGLn.mem_integralFiniteGL_iff_forall E (2 + 2)).2 fun v => ?_
    have h : finAt v (finEmb E (2 + 2) u) ∈ (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion E) (2 + 2)) := hu v
    split_ifs at h
    · exact (hU v).2 h
    · exact h
  have hac := ha
  rw [hg] at hac

  obtain ⟨β, hβ⟩ := convR E μ _ 𝔵.τ₁ 𝔵.τ₂ hp 𝔵.D 𝔵.d 𝔵.d' 𝔵.A 𝔵.A' 𝔢.a 𝔵.a_hecke
  rw [hac] at hβ
  obtain ⟨hd, x, hx, hsym⟩ := famScalar E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e κ₂ p₁ p₂ k₀ hAL S U hU 𝔵.D hty 𝔵.d 𝔵.A 𝔢.toAmp φ c β heU hφ hc
    (by rw [← hac]; exact 𝔢.a_op) hβ hne
  have hAct : Act 𝔵.A.J (Rop μ 𝔢.a) (symb β) := by
    rw [hac]
    exact (actLaws 𝔵.A.J).2.1 _ β hβ.1 hβ.2.1
  have hAct' : Act 𝔵.A'.J (Rop μ 𝔢.a) (symb 𝔵.βa) := (actLaws 𝔵.A'.J).2.1 _ 𝔵.βa 𝔵.a_acts.1 𝔵.a_acts.2.1
  have ha0 : 𝔵.a₀ = (x : ℂ) • 1 := by
    refine ContinuousLinearMap.ext fun w => N.injective ?_
    have := hN _ _ _ hAct hAct' w
    rw [hsym] at this
    change N (symb 𝔵.βa 0 w) = N (((x : ℂ) • (1 : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d')) w)
    rw [this]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul]
  have hg0 : symb 𝔵.βg 0 = ((x : ℂ) / c) • 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hsec : 𝔵.A'.sec (𝔵.a₀ v) = 𝔵.A'.sec (c • symb 𝔵.βg 0 v) := by
      funext y
      have e1 := 𝔵.a_acts.2.2 0 v y
      have e2 := 𝔵.g_acts.2.2 0 v y
      have e3 : ∫ g, 𝔢.a g * flat 0 (𝔵.A'.sec v) (y * g) ∂μ = c * ∫ g, 𝔢.g g * flat 0 (𝔵.A'.sec v) (y * g) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp [ha, mul_assoc]
      rw [e1, e2] at e3
      rw [map_smul]
      simp only [flat, Pi.smul_apply, smul_eq_mul] at e3 ⊢
      have hne' := Complex.exp_ne_zero ((0 + 2) * (HP 2 2 y : ℂ))
      apply mul_left_cancel₀ hne'
      rw [show symb 𝔵.βa 0 = 𝔵.a₀ from rfl] at e3
      rw [e3]
      ring
    have h1 := 𝔵.A'.inj hsec
    rw [ha0] at h1
    have h2 : (x : ℂ) • v = c • symb 𝔵.βg 0 v := by simpa using h1
    have h3 : symb 𝔵.βg 0 v = c⁻¹ • (x : ℂ) • v := by rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h3]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul, div_eq_inv_mul]

  have HE := heckeEx E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e hAL.idem S U hU 𝔵.D hty 𝔵.d 𝔵.A
  have HE' := heckeEx E μ _ 𝔵.τ₂ 𝔵.τ₁ hp' κ e hAL.idem S U hU 𝔵.D hty 𝔵.d' 𝔵.A'
  choose Mh hMh using fun h => (HE.1 h).exists
  have huniq : ∀ h M, HeckeAt 𝔵.A (levOn S U) h M → M = Mh h := fun h M hM => (HE.1 h).unique hM (hMh h)
  obtain ⟨hinv, -, hsplit⟩ := (galLoc F E σ hdeg hgen (2 + 2) (by norm_num) μ θ).2 hθ
  have hH : ∀ g, HH (θ.e g) = HH g := (galLaws μ _ 𝔵.σ θ 𝔵.θ₂ 𝔵.gal 𝔵.gal₂).2.2.2.2
  have hsp : ∀ z : Zs F E S, GM.Split E z.1 := by
    rintro ⟨_, w, hw, rfl⟩
    exact (hS w hw).1
  choose wv hwv using fun z : Zs F E S => hsplit z.1 (hsp z)
  obtain ⟨hh, hhd⟩ : ∃ hh : Fin 2 → (Σ z : Zs F E S, Gw (2 + 2) z.1) → FA E (2 + 2), ∀ i z g, hh i ⟨z, g⟩ =
      AdelicGLn.localEmbedding (wv z i).1 (mapGL (2 + 2) (completionMap z.1 (wv z i).1) g) :=
    ⟨fun i x => AdelicGLn.localEmbedding (wv x.1 i).1 (mapGL (2 + 2) (completionMap x.1.1 (wv x.1 i).1) x.2), fun _ _ _ => rfl⟩
  have hθh : ∀ i x, θ.e (fin1 (hh i x)) = fin1 (hh (i + 1) x) := by
    rintro i ⟨z, g⟩
    rw [hhd, hhd]
    exact hwv z i g
  have hreach : ∀ w ∈ S, ∀ g : Gw (2 + 2) w, ∃ i x, hh i x = AdelicGLn.localEmbedding w g := by
    intro w hw g
    have hlies : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : Zs F E S, z = ⟨w.under (𝓞 F), w, hw, rfl⟩ := ⟨_, rfl⟩
    have hlies' : w.asIdeal.LiesOver z.1.asIdeal := by rw [hz]; exact hlies
    obtain ⟨i, hi⟩ := (wv z).surjective ⟨w, hlies'⟩
    have H : ∀ g' : Gw (2 + 2) (wv z i).1, ∃ i' x, hh i' x = AdelicGLn.localEmbedding (wv z i).1 g' := by
      intro g'
      obtain ⟨g₀, rfl⟩ := gl_surj _ (hsp z (wv z i)) g'
      exact ⟨i, ⟨z, g₀⟩, hhd i z g₀⟩
    rw [hi] at H
    exact H g
  have hcomm : ∀ x y, Commute (Mh (hh 0 x)) (Mh (hh 1 y)) := by
    rintro ⟨z, g⟩ ⟨z', g'⟩
    rw [hhd, hhd]
    refine HE.2.1 _ _ ?_ _ _ _ _ (hMh _) (hMh _)
    intro heq
    have o1 : (wv z 0).1.under (𝓞 F) = z.1 := HeightOneSpectrum.ext (wv z 0).2.over.symm
    have o2 : (wv z' 1).1.under (𝓞 F) = z'.1 := HeightOneSpectrum.ext (wv z' 1).2.over.symm
    have hz : z = z' := Subtype.ext (o1.symm.trans ((congrArg (HeightOneSpectrum.under (𝓞 F)) heq).trans o2))
    subst hz
    exact absurd ((wv z).injective (Subtype.ext heq)) (by decide)
  have hirr : ∀ P : Submodule ℂ (Eu 𝔵.d), (∀ i x, ∀ w ∈ P, Mh (hh i x) w ∈ P) → P = ⊥ ∨ P = ⊤ := fun P hP =>
    irrW E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e κ₂ p₁ p₂ k₀ hAL S U hU 𝔵.D hty 𝔵.d 𝔵.A P fun w hw g M hM v hv => by
      obtain ⟨i, x', hx'⟩ := hreach w hw g
      rw [← hx'] at hM
      rw [huniq _ _ hM]
      exact hP i x' v hv
  have htw : ∀ i x (w : Eu 𝔵.d), ((𝔵.s.toLinearEquiv.trans N.toLinearEquiv : Eu 𝔵.d ≃ₗ[ℂ] Eu 𝔵.d)) (Mh (hh (i + 1) x) w) =
      Mh (hh i x) ((𝔵.s.toLinearEquiv.trans N.toLinearEquiv : Eu 𝔵.d ≃ₗ[ℂ] Eu 𝔵.d) w) := by
    intro i x' w
    have hi2 : i + 1 + 1 = i := by revert i; decide
    have e1 : θ.e (fin1 (hh (i + 1) x')) = fin1 (hh i x') := by
      have := hθh (i + 1) x'
      rwa [hi2] at this
    obtain ⟨M', hM', hcmp⟩ := exists_heckeAt_transport_of_linearIsometryEquiv 𝔵.A 𝔵.A' hty hle θ hinv hH hUθ 𝔵.s 𝔵.s_sec _ _ e1 _ (hMh _)
    have h2 := hecke_N hp 𝔵.A 𝔵.A' hty.level hle HE.1 HE'.1 N hN _ _ _ (hMh (hh i x')) hM' (𝔵.s w)
    rw [hcmp] at h2
    exact h2

  obtain ⟨⟨s₀, hact, hs₀⟩, -⟩ := (uiwAct E μ _ 𝔵.τ₁ 𝔵.τ₂ hp S U hU 𝔵.D hty.level 𝔵.d 𝔵.d' 𝔵.A 𝔵.A' w₀ hw₀ hI ν)
  have hv0 : 𝔵.v 0 = s₀ := actUniq _ _ _ _ (hUq ▸ 𝔵.v_act 0) hact
  obtain ⟨i₀, x₀, hx₀⟩ := hreach w₀ hw₀ (Cartan.diagPow (w₀.adicCompletion E) (2 + 2) ν)
  have hV : Mh (hh i₀ x₀) = (𝔵.v 0 0 : Eu 𝔵.d →ₗ[ℂ] Eu 𝔵.d) := by
    rw [hv0]
    refine (huniq _ _ ?_).symm
    rw [hx₀]
    exact hs₀
  have hinj : Function.Injective (Mh (hh i₀ x₀)) :=
    heckeInj E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e hAL.idem S U hU 𝔵.D hty 𝔵.d 𝔵.A w₀ hw₀ hI ν hν _ (hx₀ ▸ hMh _)
  have hN0 : ∀ w, N (𝔵.u 0 0 w) = Mh (hh i₀ x₀) (N w) := by
    intro w
    rw [hV]
    exact hN _ _ _ (𝔵.v_act 0) (𝔵.u_act 0) w
  haveI : Nontrivial (Eu 𝔵.d) := Module.nontrivial_of_finrank_pos (R := ℂ) (by simpa using hd)
  have hF := finTw (Eu 𝔵.d) _ (fun i x => Mh (hh i x)) hcomm hirr (𝔵.s.toLinearEquiv.trans N.toLinearEquiv) htw i₀ x₀ hinj
  refine ⟨x, hx, hF.mono fun j hj => ?_⟩
  have hxc : (x : ℂ) / c ≠ 0 := div_ne_zero (by exact_mod_cast hx.ne') hc
  have hT := trace_step N 𝔵.s (𝔵.u 0 0) 𝔵.a₀ (symb 𝔵.βg 0) (Mh (hh i₀ x₀)) hN0 x ((x : ℂ) / c) ha0 hg0 j
  change LinearMap.trace ℂ (Eu 𝔵.d) _ ≠ 0
  rw [hT]
  exact mul_ne_zero hxc hj
