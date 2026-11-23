import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActLoc
import Development.DiscreteGroups.PiInvariants.CasimirInfinity.CasInfOfIm
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm

noncomputable section

open NumberField MeasureTheory Measure
open GlobalTheory.CuspRep
open PositivityTheory.RgTw (G)

namespace UpperTheory.V.Z.GSp4Splitting

section Iter

variable {X Γ U ι : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [Monoid Γ] [TopologicalSpace Γ] [ContinuousMul Γ] [AddCommGroup U] [Module ℂ U]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem prod_cs {κ : Type} [Fintype κ] (e : κ → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) :
    Continuous (fun y : κ → X => ∏ v, e v (y v)) ∧ HasCompactSupport (fun y : κ → X => ∏ v, e v (y v)) := by
  refine ⟨continuous_finsetProd _ fun v _ => (he v).1.comp (continuous_apply v), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun v => (he v).2.isCompact) fun y hy => ?_
  obtain ⟨v, hv⟩ := not_forall.1 (mt Set.mem_univ_pi.2 hy)
  exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)

private theorem iter_fin (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (m : ℕ) :
    ∀ (s : Fin m → ι) (u : U) (g : Γ),
      ∫ y : Fin m → X, (∏ i, e (s i) (y i)) * Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod) ∂(Measure.pi fun _ => μ) =
        (∏ i, val (s i)) * Φ ((List.ofFn fun i => P (s i)).prod u) g := by
  induction m with
  | zero =>
    intro s u g
    simp [Measure.pi_of_empty (fun _ : Fin 0 => μ)]
  | succ m ih =>
    intro s u g
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hl : Continuous fun y : Fin (m + 1) → X => (List.ofFn fun i => j (s i) (y i)).prod := by
      simp only [List.ofFn_eq_map]
      exact continuous_list_prod _ fun i _ => (hj _).comp (continuous_apply i)
    have hF : Integrable (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) (Measure.pi fun _ => μ) :=
      ((prod_cs (fun i => e (s i)) fun i => he _).1.mul ((hΦ u).comp (continuous_const.mul hl))).integrable_of_hasCompactSupport
        (prod_cs (fun i => e (s i)) fun i => he _).2.mul_right
    rw [← (hmp.symm _).integral_comp']
    refine (integral_prod _ (((hmp.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF)).trans ?_
    have hin : ∀ t : X, ∫ z : Fin m → X, (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) ((MeasurableEquiv.piFinSuccAbove (fun _ => X) 0).symm (t, z))
          ∂(Measure.pi fun _ => μ) = (∏ i : Fin m, val (s i.succ)) *
            (e (s 0) t * Φ ((List.ofFn fun i : Fin m => P (s i.succ)).prod u) (g * j (s 0) t)) := by
      intro t
      have e1 : ∀ z : Fin m → X, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0).symm (t, z) = Fin.cons t z :=
        fun z => Fin.insertNth_zero' t z
      simp only [e1, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]
      simp only [← mul_assoc g, mul_assoc (e (s 0) t)]
      rw [integral_const_mul, ih (fun i => s i.succ) u (g * j (s 0) t)]
      ring
    refine (integral_congr_ae (Filter.Eventually.of_forall hin)).trans ?_
    rw [integral_const_mul, hloc, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    ring

private theorem iter_list [Fintype ι] (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (l : List ι) (hl : l.Nodup) (hm : ∀ v, v ∈ l)
    (u : U) (g : Γ) :
    ∫ y : ι → X, (∏ v, e v (y v)) * Φ u (g * (l.map fun v => j v (y v)).prod) ∂(Measure.pi fun _ => μ) =
      (∏ v, val v) * Φ ((l.map P).prod u) g := by
  classical
  let σ : Fin l.length ≃ ι := List.Nodup.getEquivOfForallMemList l hl hm
  have hσ : ∀ {β : Type} (f : ι → β), (List.ofFn fun i => f (σ i)) = l.map f := fun f => by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  have hmp := measurePreserving_piCongrLeft (fun _ : ι => μ) σ
  have key := iter_fin μ e he j hj Φ hΦ val P hloc _ σ u g
  rw [hσ P, Equiv.prod_comp σ val] at key
  rw [← key, ← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 : ∀ i, MeasurableEquiv.piCongrLeft (fun _ : ι => X) σ y (σ i) = y i := fun i =>
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => X) σ y i
  beta_reduce
  rw [← hσ, ← Equiv.prod_comp σ]
  simp only [e1]

end Iter

private theorem prod_single {ι M : Type} [DecidableEq ι] [Monoid M] (y : ι → M) :
    ∀ l : List ι, l.Nodup → ∀ w, (l.map fun v => (Pi.mulSingle v (y v) : ι → M)).prod w = if w ∈ l then y w else 1 := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hl w
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl.2]
    by_cases h : w = a
    · subst h
      simp [hl.1]
    · simp [h]

private theorem split_two {X Y K : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (e : X × Y ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ]
    (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = c * ∫ x, ∫ y, f (e (x, y)) ∂mY ∂mX := by
  let em : X × Y ≃ᵐ K := e.toHomeomorph.toMeasurableEquiv
  haveI : IsHaarMeasure ((mX.prod mY).map e) := ContinuousMulEquiv.isHaarMeasure_map _ e
  haveI : LocallyCompactSpace K := e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology K := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  have h := isMulLeftInvariant_eq_smul μ ((mX.prod mY).map e)
  have hpos := haarScalarFactor_pos_of_isHaarMeasure μ ((mX.prod mY).map e)
  generalize haarScalarFactor μ ((mX.prod mY).map e) = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun f hf hs => ?_⟩
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  congr 1
  refine (integral_map_equiv em f).trans ?_
  exact integral_prod (fun z => f (e z))
    ((hf.comp e.continuous).integrable_of_hasCompactSupport (hs.comp_homeomorph e.toHomeomorph))

private theorem hecke_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Subgroup Γ)
    (hK : IsOpen (K : Set Γ)) (h : Γ → ℂ) (hh : ∀ k ∈ K, ∀ g, h (g * k) = h g) : Continuous h := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hn : (fun x => g⁻¹ * x) ⁻¹' (K : Set Γ) ∈ nhds g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  refine continuousAt_const.congr (f := fun _ => h g) (Filter.mem_of_superset hn fun x hx => ?_)
  have := hh _ hx g
  simpa using this.symm

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG in

private def split0 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (InfinitePlace E → G n) × GL (Fin n) (Af E) ≃ₜ* PositivityTheory.Rg.BcB.E.H E n 0 where
  toFun p := (splitGA n p, 1)
  invFun g := (splitGA n).symm g.1
  left_inv p := by simp
  right_inv g := Prod.ext (by simp) (Subsingleton.elim _ _)
  map_mul' p q := by simp
  continuous_toFun := (splitGA n).continuous.prodMk continuous_const
  continuous_invFun := (splitGA n).symm.continuous.comp continuous_fst

end UpperTheory.V.Z.GSp4Splitting

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH PositivityTheory.Rg.BcB.CG.lc_G PositivityTheory.Rg.BcB.CG.sc_G PositivityTheory.Rg.BcB.CG.lc_GLf
  PositivityTheory.Rg.BcB.CG.sc_GLf PositivityTheory.Rg.BcB.CG.t2_GL_finite_adeles PositivityTheory.Rg.BcB.CG.borelSpaceH in
open PositivityTheory.Rg.BcB.CG in
theorem UpperTheory.V.Z.GSp4Splitting.opForm :
    HeckeMem → RlComm → LocAct → OpForm := by
  intro _ _ hL E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D lam hch _ _ ν _ hν _ _ μC _ μ _ P hP
  classical
  haveI : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μC) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := split_two (split0 E n) μ (Measure.pi fun _ : InfinitePlace E => μC) μf
  refine ⟨c, hc0, fun k val T hk h hh ψ u hu x => ?_⟩
  set e : InfinitePlace E → G n → ℂ := fun w => phiOf (lefE n (lam w)) (lefT n (lam w)) (k w) with he
  have hecs : ∀ w, Continuous (e w) ∧ HasCompactSupport (e w) := fun w =>
    PositivityTheory.Rg.BcB.F.F0.phiOf_cs μC _ _ _ _ _ (hk w)
  have hhc : Continuous h := hecke_cont K hKo h fun k hk g => by simpa using hh.2 1 K.one_mem k hk g
  have hcont : ∀ φ : π.V, Continuous φ.1.1 := fun φ => DiscreteGroups.T1.G.continuous_of_mem π φ.2
  have hphi : ∀ p : (InfinitePlace E → G n) × GL (Fin n) (Af E), phiProd lam k h (split0 E n p) = (∏ w, e w (p.1 w)) * h p.2 := by
    intro p
    have e1 : ∀ w, infAt E n w (split0 E n p).1 = p.1 w := fun w => gInf_splitGA n p w
    have e2 : finOf E n (split0 E n p).1 = p.2 := gFin_splitGA n p
    simp only [phiProd, e1, e2, he]
  have hphi' : phiProd lam k h = (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2) ∘
      (split0 E n).symm.toHomeomorph := by
    funext y
    obtain ⟨p, rfl⟩ := (split0 E n).surjective y
    rw [hphi]
    exact (congrArg (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2)
      ((split0 E n).symm_apply_apply p)).symm
  have hpc : Continuous (phiProd lam k h) := by
    rw [hphi']
    exact (((prod_cs e hecs).1.comp continuous_fst).mul (hhc.comp continuous_snd)).comp (Homeomorph.continuous _)
  have hps : HasCompactSupport (phiProd lam k h) := by
    rw [hphi']
    refine HasCompactSupport.comp_homeomorph ?_ _
    refine HasCompactSupport.intro ((prod_cs e hecs).2.isCompact.prod hh.1.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h1 | h1
    · rw [show (∏ w, e w (p.1 w)) = 0 from
        image_eq_zero_of_notMem_tsupport (f := fun y : InfinitePlace E → G n => ∏ v, e v (y v)) h1, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]
  rw [hc (fun y => phiProd lam k h y * ψ.1.1 (x * y.1))
    (hpc.mul ((hcont ψ).comp (continuous_const.mul continuous_fst))) hps.mul_right, mul_assoc]
  congr 1
  let j : InfinitePlace E → G n → GA E n := fun w t => infP n (Pi.mulSingle w t)
  let l := (Finset.univ : Finset (InfinitePlace E)).toList
  let ih : (InfinitePlace E → G n) →* GA E n := MonoidHom.mk' (infP n) (infinitePart_mul n)
  have hjl : ∀ y : InfinitePlace E → G n, (l.map fun v => j v (y v)).prod = infP n y := by
    intro y
    have e1 : (l.map fun v => (Pi.mulSingle v (y v) : InfinitePlace E → G n)).prod = y := by
      funext w
      rw [prod_single y l (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (map_list_prod ih _).symm
    rw [List.map_map]
    rfl
  have hj : ∀ w, Continuous (j w) := fun w => (continuous_infP n).comp (continuous_mulSingle (A := fun _ => G n) w)
  have key := iter_list μC e hecs j hj (fun u => (D.i u).1.1) (fun u => hcont _) (fun w => val w (infOf (lam w))) P
    (fun w u g => by
      have := hL E n hn π hθ K hKo hKc hKθ μf D w (lam w) (hch w) ν hν μC _ _ (P w) (hP w) (k w) (val w) (T w) (hk w) u g
      simp only [along_val] at this
      exact this) l (Finset.nodup_toList _) (fun v => Finset.mem_toList.2 (Finset.mem_univ v)) u x
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hjl, hu, heckeOp, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  beta_reduce
  rw [hphi, mul_assoc, mul_assoc x]
  rfl
