import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TensAmp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SideE
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopLevel
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AvgTens
import Development.AutomorphicArithmetic.AdelicGluing.GaloisTwistCompUOperatorEqUOperatorSmulPlace
import Development.AutomorphicArithmetic.AdelicGluing.BaseChangeLevelIsOpenIsCompactContainsIwahori

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IwahoriHeckeOperatorComm

section One

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]

private theorem iw_oc (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (w : Pl K) :
    IsOpen (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) ∧
      IsCompact (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) := by
  have hI := UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w 0 0 (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
  exact ⟨hI.2.2.1, hI.2.2.2.1⟩

private theorem rho_comm {w w' : Pl K} (h : w ≠ w') (g : GL (Fin n) (w.adicCompletion K))
    (g' : GL (Fin n) (w'.adicCompletion K)) : Commute (rhoL μ w g) (rhoL μ w' g') := by
  obtain ⟨-, -, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  change rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
  rw [← hmul, ← hmul, hc]

private theorem hop_comm {w w' : Pl K} (h : w ≠ w') (J : Subgroup (GL (Fin n) (w.adicCompletion K)))
    (J' : Subgroup (GL (Fin n) (w'.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K))
    (x' : GL (Fin n) (w'.adicCompletion K)) (hJo : IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))))
    (hJc : IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))))
    (hJo' : IsOpen (J' : Set (GL (Fin n) (w'.adicCompletion K))))
    (hJc' : IsCompact (J' : Set (GL (Fin n) (w'.adicCompletion K)))) :
    Commute (Hop μ w J x) (Hop μ w' J' x') :=
  (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w' J' x' hJo' hJc').2.2.2.2.1 _ fun g =>
    ((UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJo hJc).2.2.2.2.1 (rhoL μ w' g) fun g' => (rho_comm h g' g).symm).symm

private theorem hop_amp (hn : 0 < n) (𝔞 : Amp μ) (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K)))
    (x : GL (Fin n) (w.adicCompletion K)) (hJo : IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))))
    (hJc : IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))))
    (h1 : J.map (AdelicGLn.localEmbedding w) ≤ 𝔞.U) (h2 : ∀ u ∈ 𝔞.U, finAt w (finEmb K n u) ∈ J) :
    Commute (Hop μ w J x) 𝔞.A := by
  obtain ⟨m, hm, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  have hUc : IsCompact (𝔞.U : Set (FA K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ 𝔞.isOpen) 𝔞.le
  have hP := (UpperTheory.ConvolutionTheory.Tf.hopLevel K n μ m w J x 𝔞.U hJo hJc 𝔞.isOpen hUc h1 h2).1
  have hO : Commute (Oinf μ 𝔞.ν 𝔞.a₀) (Hop μ w J x) :=
    (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJo hJc).2.2.2.2.1 _ fun g =>
      (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m).2.2.2.2.2.2.2.2 _ _
  change Commute _ (Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U))
  exact Commute.mul_right hO.symm hP

end One

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private noncomputable def pv (v : Pl F) (x : AdelicGLn.FiniteAdelicGL E n) : GL (Fin n) (CompletionsOver E v) :=
  mapGL n (atFin v) (finEmb E n x)

private theorem finEmb_entry (x : AdelicGLn.FiniteAdelicGL E n) (a b : Fin n) :
    ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd E n (finEmb E n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cmp_pv {v : Pl F} (w : PlacesOver E v) (x : AdelicGLn.FiniteAdelicGL E n) :
    GM.cmp w (pv v x) = AdelicGLn.finiteRestrictedEquiv E n x w.1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 w.1 = _
  rw [finEmb_entry]
  rfl

private theorem pv_finPart (v : Pl F) (g : AdelicGLn.AdelicGL E n) :
    pv v (CuspidalSpectrum.finPart E n g) = mapGL n (atFin v) g := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  funext w
  change ((finEmb E n (CuspidalSpectrum.finPart E n g) : AdelicGLn.AdelicGL E n) a b).2 w.1 = (g a b).2 w.1
  rw [finEmb_entry]
  rfl

private theorem mem_levE (U : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v)))
    (x : AdelicGLn.FiniteAdelicGL E n) : x ∈ GM.levE U ↔ ∀ v, pv v x ∈ U v := by
  simp only [GM.levE, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

private theorem finprod_ind (S : Finset (Pl F)) (U : ∀ v : Pl F, Subgroup (GL (Fin n) (CompletionsOver E v)))
    (hU : ∀ v ∉ S, (U v : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v) (x : AdelicGLn.FiniteAdelicGL E n) :
    ∏ᶠ v, (U v : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ) (pv v x) =
      (GM.levE U : Set (AdelicGLn.FiniteAdelicGL E n)).indicator (1 : AdelicGLn.FiniteAdelicGL E n → ℂ) x := by
  classical
  by_cases hx : x ∈ GM.levE U
  · rw [Set.indicator_of_mem (show x ∈ (GM.levE U : Set (AdelicGLn.FiniteAdelicGL E n)) from hx), Pi.one_apply]
    exact finprod_eq_one_of_forall_eq_one fun v => by
      rw [Set.indicator_of_mem (show pv v x ∈ (U v : Set _) from (mem_levE U x).1 hx v), Pi.one_apply]
  · rw [Set.indicator_of_notMem (show x ∉ (GM.levE U : Set (AdelicGLn.FiniteAdelicGL E n)) from hx)]
    rw [mem_levE, not_forall] at hx
    obtain ⟨v₀, hv₀⟩ := hx
    have hB : {w : Pl E | AdelicGLn.finiteRestrictedEquiv E n x w ∉
        GLnLocal.integralGL (w.adicCompletion E) n}.Finite :=
      Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv E n x).2
    refine finprod_eq_zero _ v₀ (Set.indicator_of_notMem hv₀ _) ?_
    refine (S.finite_toSet.union (hB.image fun w : Pl E => w.under (𝓞 F))).subset fun v hv => ?_
    by_cases hvS : v ∈ S
    · exact Or.inl hvS
    · right
      have hnot : pv v x ∉ unitSet E n v := by
        intro h
        refine hv ?_
        rw [← hU v hvS] at h
        change (U v : Set (GL (Fin n) (CompletionsOver E v))).indicator (1 : GL (Fin n) (CompletionsOver E v) → ℂ) (pv v x) = 1
        rw [Set.indicator_of_mem h, Pi.one_apply]
      simp only [unitSet, Set.mem_setOf_eq, not_forall] at hnot
      obtain ⟨w', hw'⟩ := hnot
      refine ⟨w'.1, ?_, under_eq w'⟩
      intro h
      refine hw' ?_
      have : GM.cmp w' (pv v x) ∈ GLnLocal.integralGL (w'.1.adicCompletion E) n := by
        rw [cmp_pv]
        exact h
      exact this

end Two

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IwahoriHeckeOperatorComm

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IwahoriHeckeOperatorComm Pointwise in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.sideX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
          [IsTotallyComplex E] (σ : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ τ, τ ∈ Subgroup.zpowers σ) →
          ∀ n : ℕ, 0 < n → ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q →
          ∀ (L : GM.Loc σ n q w₀) (νE : Measure (archGroup E n)) (aE : TI E n) (ν : Fin n → ℤ) (𝔢 : Side θ 2), GM.IsSideE L νE aE ν 𝔢 →
          (∀ v, L.φ v = (L.UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1) →
          ∃ (𝔢' : Side θ 2) (φ : TF E n) (w₁ : PlacesOver E q), 𝔢'.toAmp = 𝔢.toAmp ∧ 𝔢'.g = 𝔢.g ∧ 𝔢'.Uq 0 = 𝔢.Uq 0 ∧ 𝔢'.Uq 1 = Uiw μ w₁.1 ν ∧
            (∀ x, φ x = (𝔢.U : Set (FA E n)).indicator 1 x) ∧ 𝔢'.g = tens 𝔢'.a₀ φ ∧ ∃ c : ℂ, c ≠ 0 ∧ 𝔢'.a = c • 𝔢'.g := by
  intro F E _ _ _ _ _ _ _ _ σ hfr hσ n hn μ _ θ hθ q w₀ hsplit L νE aE ν 𝔢 hside hφ
  classical
  obtain ⟨hν, ha, hS, hU, hg, hq0⟩ := hside
  have hfac := (UpperTheory.baseChangeLevel_isOpen_isCompact_contains_iwahori F E σ n hn q w₀ L).2.2.2.2.2
  have hσ2 : σ * σ = 1 := by
    have h1 : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, hfr]
    have h2 := pow_card_eq_one' (x := σ)
    rw [h1, pow_two] at h2
    exact h2
  have hl : (σ • w₀.1).asIdeal.LiesOver q.asIdeal := by
    haveI := w₀.2
    change (σ • w₀.1.asIdeal).LiesOver q.asIdeal
    infer_instance
  let w₁ : PlacesOver E q := ⟨σ • w₀.1, hl⟩
  have hne : w₀.1 ≠ w₁.1 := by
    intro e
    obtain ⟨p, -⟩ := ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc F E σ hfr hσ n hn μ θ).2 ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc F E σ hfr hσ n hn μ θ).1.2 ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc F E σ hfr hσ n hn μ θ).1.1 hθ))).2.2 q hsplit
    have hfix : ∀ k : ℤ, (σ ^ k) • w₀.1 = w₀.1 := fun k => by
      have hm : σ ∈ MulAction.stabilizer (E ≃ₐ[F] E) w₀.1 := e.symm
      exact (Subgroup.zpow_mem _ hm k)
    have hall : ∀ w : PlacesOver E q, w = w₀ := by
      intro w
      haveI := w.1.isPrime
      haveI := w₀.1.isPrime
      haveI := w.2
      haveI := w₀.2
      obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup q.asIdeal w₀.1.asIdeal w.1.asIdeal (E ≃ₐ[F] E)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ τ)
      exact Subtype.ext (HeightOneSpectrum.ext (hτ.symm.trans (congrArg HeightOneSpectrum.asIdeal (hfix k))))
    have h01 : p 0 = p 1 := (hall _).trans (hall _).symm
    exact absurd (p.injective h01) (by decide)
  have hw10 : σ • w₁.1 = w₀.1 := by
    change σ • σ • w₀.1 = _
    rw [smul_smul, hσ2, one_smul]
  have hA : ∀ w : PlacesOver E q, Commute (Uiw μ w.1 ν) 𝔢.toAmp.A := fun w =>
    hop_amp hn 𝔢.toAmp w.1 _ _ (iw_oc μ w.1).1 (iw_oc μ w.1).2 (by rw [hU]; exact (hfac w).1)
      (by rw [hU]; exact (hfac w).2)
  have hUo : IsOpen (𝔢.U : Set (FA E n)) := 𝔢.isOpen
  have hUc : IsCompact (𝔢.U : Set (FA E n)) :=
    (AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hUo) 𝔢.le
  have hlc : IsLocallyConstant ((𝔢.U : Set (FA E n)).indicator (1 : FA E n → ℂ)) := by
    rw [← LocallyConstant.coe_charFn ℂ (⟨Subgroup.isClosed_of_isOpen _ hUo, hUo⟩ : IsClopen (𝔢.U : Set (FA E n)))]
    exact LocallyConstant.isLocallyConstant _
  have hcs : HasCompactSupport ((𝔢.U : Set (FA E n)).indicator (1 : FA E n → ℂ)) :=
    HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _
  let φ : TF E n := ⟨⟨(𝔢.U : Set (FA E n)).indicator (1 : FA E n → ℂ), hlc.continuous⟩, hcs⟩
  have hφx : ∀ x, φ x = (𝔢.U : Set (FA E n)).indicator 1 x := fun _ => rfl
  have hoff : ∀ v ∉ insert q L.S, (L.UE v : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v := fun v hv =>
    (L.off v (fun h => hv (Finset.mem_insert_of_mem h)) (fun h => hv (Finset.mem_insert.2 (Or.inl h)))).2.2.1
  have hgt : 𝔢.g = tens 𝔢.a₀ φ := by
    ext x
    rw [hg x, ha]
    refine (UpperTheory.ConvolutionTheory.Tf.avgTens E n hn aE φ _ fun g => ?_).1 x
    have key : ∏ᶠ v, L.φ v (mapGL n (atFin v) g) = φ (CuspidalSpectrum.finPart E n g) := by
      have h := finprod_ind (insert q L.S) L.UE hoff (CuspidalSpectrum.finPart E n g)
      simp only [pv_finPart] at h
      simp only [hφ]
      rw [h, hφx, hU]
    change _ * ∏ᶠ v, L.φ v (mapGL n (atFin v) g) = aE _ * φ _
    rw [key]
    congr 1
  obtain ⟨⟨c, hc, -, hop⟩, hsm⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.tensAmp E n hn μ 𝔢.toAmp φ hφx
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hRop : Rop μ 𝔢.g = (c : ℂ) • 𝔢.toAmp.A := by
    rw [hgt]
    exact hop
  have hsm' : (c : ℂ)⁻¹ • 𝔢.g = tens 𝔢.a₀ ((c : ℂ)⁻¹ • φ) := by
    rw [hgt]
    exact (((UpperTheory.ConvolutionTheory.Tf.tensApply E n hn 𝔢.a₀ φ).2.2.2.2 _).2).symm
  have haop : Rop μ ((c : ℂ)⁻¹ • 𝔢.g) = 𝔢.toAmp.A := by
    obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx E n hn).2.1 μ 𝔢.ν
    have hrr := UpperTheory.ConvolutionTheory.Tf.rrTens E n hn μ 𝔢.ν m hC
    have h1 : Rop μ 𝔢.g = Oinf μ 𝔢.ν 𝔢.a₀ ∘L Ofin μ m φ := by
      rw [hgt]
      exact hrr _ _
    have h2 : Rop μ ((c : ℂ)⁻¹ • 𝔢.g) = Oinf μ 𝔢.ν 𝔢.a₀ ∘L Ofin μ m ((c : ℂ)⁻¹ • φ) := by
      rw [hsm']
      exact hrr _ _
    rw [h2, ((UpperTheory.ConvolutionTheory.Tf.opAlg E n μ 𝔢.ν m).2.2.1 _ 𝔢.a₀ φ).2, ContinuousLinearMap.comp_smul, ← h1, hRop,
      smul_smul, inv_mul_cancel₀ hcc, one_smul]
  have hasm : IsLeftSmooth ((c : ℂ)⁻¹ • 𝔢.g : TG E n) := by
    rw [hgt]
    exact hsm _
  have hcases : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  let Uq : ZMod 2 → LL μ →L[ℂ] LL μ := fun i => if i = 0 then Uiw μ w₀.1 ν else Uiw μ w₁.1 ν
  have h0 : Uq 0 = Uiw μ w₀.1 ν := if_pos rfl
  have h1 : Uq 1 = Uiw μ w₁.1 ν := if_neg (by decide)
  have hin : ∀ w : PlacesOver E q, Inner μ (Uiw μ w.1 ν) := fun w =>
    (UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.2.2 w.1 _ _ (iw_oc μ w.1).1 (iw_oc μ w.1).2
  have hcm : Commute (Uiw μ w₀.1 ν) (Uiw μ w₁.1 ν) :=
    hop_comm hne _ _ _ _ (iw_oc μ w₀.1).1 (iw_oc μ w₀.1).2 (iw_oc μ w₁.1).1 (iw_oc μ w₁.1).2
  have hP : ∀ w w' : PlacesOver E q, σ • w.1 = w'.1 →
      (Rop μ 𝔢.g ∘L θ.U) ∘L Uiw μ w.1 ν = Uiw μ w'.1 ν ∘L (Rop μ 𝔢.g ∘L θ.U) := by
    intro w w' h
    have h1 := UpperTheory.galoisTwist_comp_uOperator_eq_uOperator_smul_place F E σ n hn μ θ hθ w.1 ν
    rw [h] at h1
    have h2 : Rop μ 𝔢.g ∘L Uiw μ w'.1 ν = Uiw μ w'.1 ν ∘L Rop μ 𝔢.g := by
      have h3 : Commute (Rop μ 𝔢.g) (Uiw μ w'.1 ν) := by
        rw [hRop]
        exact (hA w').symm.smul_left _
      exact h3.eq
    rw [ContinuousLinearMap.comp_assoc, h1, ← ContinuousLinearMap.comp_assoc, h2, ContinuousLinearMap.comp_assoc]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  refine ⟨⟨𝔢.toAmp, (c : ℂ)⁻¹ • 𝔢.g, haop, hasm, 𝔢.g, 𝔢.g_smooth, Uq, ?_, ?_, ?_, ?_⟩, φ, w₁, rfl, rfl, ?_, ?_, hφx, hgt,
    (c : ℂ)⁻¹, inv_ne_zero hcc, rfl⟩
  · intro i
    rcases hcases i with rfl | rfl
    · rw [h0]; exact hin w₀
    · rw [h1]; exact hin w₁
  · intro i k
    rcases hcases i with rfl | rfl <;> rcases hcases k with rfl | rfl
    · exact Commute.refl _
    · rw [h0, h1]; exact hcm
    · rw [h0, h1]; exact hcm.symm
    · exact Commute.refl _
  · intro i
    rcases hcases i with rfl | rfl
    · rw [h0]; exact hA w₀
    · rw [h1]; exact hA w₁
  · intro i
    rcases hcases i with rfl | rfl
    · rw [zero_add, h0, h1]; exact hP w₀ w₁ rfl
    · rw [h11, h0, h1]; exact hP w₁ w₀ hw10
  · exact h0.trans hq0.symm
  · exact h1
