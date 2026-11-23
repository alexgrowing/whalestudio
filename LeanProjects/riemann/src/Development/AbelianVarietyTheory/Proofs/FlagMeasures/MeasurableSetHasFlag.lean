import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.FlagMeas

theorem totCx (I : AutInst) : IsTotallyComplex I.E := by
  obtain ⟨h, -⟩ := I.cm.cmUnram
  exact h

theorem frm_unit (I : AutInst) (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have hU : IsUnit (uMat (x.1 (w.comap (algebraMap I.F I.E)))).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have hP : IsUnit (I.P (w.comap (algebraMap I.F I.E))).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit _)
  by_cases h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))
  · simp only [frm, if_pos h]
    rw [Matrix.det_mul]
    exact hP.mul hU
  · simp only [frm, if_neg h]
    have hm : ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).map
        (starRingEnd ℂ)).det = starRingEnd ℂ (I.P (w.comap (algebraMap I.F I.E)) *
          uMat (x.1 (w.comap (algebraMap I.F I.E)))).det := by
      rw [RingHom.map_det]; rfl
    rw [hm, Matrix.det_mul]
    exact (hP.mul hU).map _

abbrev rho (I : AutInst) (x : I.GA) := Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)

theorem continuous_frm (I : AutInst) (w : InfinitePlace I.E) :
    Continuous fun g : I.Ginf => frm I (g, 1) w := by
  have hc : Continuous fun g : I.Ginf => uMat (g (w.comap (algebraMap I.F I.E))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply _))
  by_cases h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))
  · simp only [frm, if_pos h]
    exact continuous_const.mul hc
  · simp only [frm, if_neg h]
    exact (continuous_const.mul hc).matrix_map Complex.continuous_conj

theorem continuous_frm_inv (I : AutInst) (w : InfinitePlace I.E) :
    Continuous fun g : I.Ginf => (frm I (g, 1) w)⁻¹ := by
  have hc := continuous_frm I w
  have hd : ∀ g : I.Ginf, (frm I (g, 1) w).det ≠ 0 := fun g => (frm_unit I (g, 1) w).ne_zero
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hc.matrix_det.inv₀ hd).smul hc.matrix_adjugate

private theorem continuous_fcoord_frm (I : AutInst) (w : InfinitePlace I.E) (y : Fin I.n → I.E) (i : Fin I.n) :
    Continuous fun g : I.Ginf => Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I (g, 1)) w y i := by
  show Continuous fun g : I.Ginf => ((frm I (g, 1) w)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt (bas I) w y) i
  exact (continuous_apply i).comp ((continuous_frm_inv I w).matrix_mulVec continuous_const)

private theorem exists_linearIndependent_span_le_rkK_eq (I : AutInst) (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    ∃ (j : ℕ) (e : Fin j → Fin I.n → I.E), LinearIndependent I.E e ∧
      Submodule.span (𝓞 I.E) (Set.range e) ≤ N ∧ rkK N = j := by
  obtain ⟨b, hbN, hspan, hli⟩ := exists_linearIndependent I.E (N : Set (Fin I.n → I.E))
  have : Finite b := hli.finite_of_isNoetherian
  haveI : Fintype b := Fintype.ofFinite b
  have hli' : LinearIndependent I.E fun i : Fin (Fintype.card b) =>
      ((Fintype.equivFin b).symm i : Fin I.n → I.E) :=
    hli.comp _ (Fintype.equivFin b).symm.injective
  have hre : Set.range (fun i : Fin (Fintype.card b) => ((Fintype.equivFin b).symm i : Fin I.n → I.E)) = b := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hv
      exact ⟨Fintype.equivFin b ⟨v, hv⟩, by simp⟩
  refine ⟨Fintype.card b, _, hli', ?_, ?_⟩
  · rw [Submodule.span_le, hre]
    exact hbN
  · show Module.finrank I.E (Submodule.span I.E (N : Set (Fin I.n → I.E))) = _
    have hc := finrank_span_eq_card hli'
    rw [hre] at hc
    rw [← hspan, hc, Fintype.card_fin]

theorem measurable_deg (I : AutInst) (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hN : N.FG) :
    Measurable fun x : I.GA => deg (rho I x) N := by
  have := totCx I
  obtain ⟨j, e, he, hle, hrk⟩ := exists_linearIndependent_span_le_rkK_eq I N
  set idx : ℝ := ((Submodule.span (𝓞 I.E) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup : ℝ) with hidx_def
  set C1 : ℝ := (2 : ℝ) ^ (nPl I.E * rkK N) * |(NumberField.discr I.E : ℝ)| ^ (-(rkK N : ℝ) / 2) with hC1_def
  have hC1 : 0 < C1 := mul_pos (pow_pos two_pos _)
    (Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero I.E)) _)
  have key : ∀ x : I.GA, deg (rho I x) N =
      -Real.log ((∏ v, (gramPl (bas I) (frm I x) v e).det.re) / idx / C1) := by
    intro x
    obtain ⟨h1, h2⟩ := Formalism.HN.htGram I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (frm_unit I x) j e he
    have h3 : ht (bas I) (frm I x) N * idx = ht (bas I) (frm I x) (Submodule.span (𝓞 I.E) (Set.range e)) :=
      h2 N hN hle hrk
    have hpos := (Formalism.HN.plLat I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (frm_unit I x)
      (Submodule.span (𝓞 I.E) (Set.range e)) (Submodule.fg_span (Set.finite_range e))).2.2
    have hidx : idx ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h3
      linarith
    have hht : ht (bas I) (frm I x) N = C1 * Formalism.F.covol (zl (rho I x) N) := rfl
    have hcov : Formalism.F.covol (zl (rho I x) N) = (∏ v, (gramPl (bas I) (frm I x) v e).det.re) / idx / C1 := by
      rw [← h1, ← h3, hht, mul_div_cancel_right₀ _ hidx, mul_div_cancel_left₀ _ hC1.ne']
    show -Real.log (Formalism.F.covol (zl (rho I x) N)) = _
    rw [hcov]
  have hH : Continuous fun g : I.Ginf => ∏ v, (gramPl (bas I) (frm I (g, 1)) v e).det.re := by
    refine continuous_finsetProd _ fun v _ => Complex.continuous_re.comp (Continuous.matrix_det ?_)
    refine continuous_matrix fun a c => ?_
    show Continuous fun g : I.Ginf => Formalism.HermitianLatticesTheory.majAt (bas I) (frm I (g, 1)) v (e a) (e c)
    unfold Formalism.HermitianLatticesTheory.majAt
    exact continuous_finsetSum _ fun i _ =>
      (continuous_star.comp (continuous_fcoord_frm I v (e a) i)).mul (continuous_fcoord_frm I v (e c) i)
  have hm : Measurable fun x : I.GA => ∏ v, (gramPl (bas I) (frm I x) v e).det.re :=
    hH.measurable.comp measurable_fst
  rw [show (fun x : I.GA => deg (rho I x) N) = fun x =>
      -Real.log ((∏ v, (gramPl (bas I) (frm I x) v e).det.re) / idx / C1) from funext key]
  exact ((hm.div_const _).div_const _).log.neg

private theorem countable_E' (I : AutInst) : Countable I.E :=
  (Module.finBasis ℚ I.E).equivFun.toEquiv.injective.countable

theorem countable_fg (I : AutInst) : {N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG}.Countable := by
  have := countable_E' I
  refine (Set.countable_range fun s : Finset (Fin I.n → I.E) =>
    Submodule.span (𝓞 I.E) (s : Set (Fin I.n → I.E))).mono ?_
  rintro N ⟨s, hs⟩
  exact ⟨s, hs⟩

theorem rk_eq (I : AutInst) (x : I.GA) (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hN : N.FG) :
    rk (rho I x) N = Module.finrank ℚ I.E * rkK N := (Formalism.HN.plLat I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (frm_unit I x) N hN).2.1

theorem isLat (I : AutInst) (x : I.GA) (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hN : N.FG) :
    IsLat (rho I x) N := (Formalism.HN.plLat I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (frm_unit I x) N hN).1

theorem measurable_muMin (I : AutInst) (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hN : N.FG) (h0 : N ≠ ⊥) :
    Measurable fun x : I.GA => muMin (rho I x) N := by
  refine measurable_of_Ici fun θ => ?_
  have hset : (fun x : I.GA => muMin (rho I x) N) ⁻¹' Set.Ici θ =
      ⋂ M ∈ {M : Submodule (𝓞 I.E) (Fin I.n → I.E) | M.FG ∧ M ≤ N},
        {x | θ * (((Module.finrank ℚ I.E * rkK N : ℕ) : ℝ) - ((Module.finrank ℚ I.E * rkK M : ℕ) : ℝ)) ≤
          deg (rho I x) N - deg (rho I x) M} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [(Formalism.HN.muChar _ _ _ (rho I x) N (isLat I x N hN) h0).2.1 θ]
    constructor
    · intro h M hM
      have := h M hM.2
      rwa [rk_eq I x N hN, rk_eq I x M hM.1] at this
    · intro h M hMN
      have hM := Submodule.FG.of_le hN hMN
      have := h M ⟨hM, hMN⟩
      rwa [rk_eq I x N hN, rk_eq I x M hM]
  rw [hset]
  refine MeasurableSet.biInter ((countable_fg I).mono fun M hM => hM.1) fun M hM => ?_
  exact measurableSet_le measurable_const ((measurable_deg I N hN).sub (measurable_deg I M hM.1))

def cE (I : AutInst) : ℝ := Real.log 2 / 2 - logDisc I.E / (2 * (Module.finrank ℚ I.E : ℝ))

theorem largest_eq (I : AutInst) (x : I.GA) (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hN : N.FG) (h0 : N ≠ ⊥) :
    largestSize (bas I) (frm I x) N = Real.exp (cE I - muMin (rho I x) N) := by
  have := totCx I
  exact (Formalism.HN.sizeMu I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (frm_unit I x) N hN h0).2.2.2.2.1

theorem measurable_largest (I : AutInst) (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hN : N.FG) (h0 : N ≠ ⊥) :
    Measurable fun x : I.GA => largestSize (bas I) (frm I x) N := by
  rw [show (fun x : I.GA => largestSize (bas I) (frm I x) N) = fun x => Real.exp (cE I - muMin (rho I x) N) from
    funext fun x => largest_eq I x N hN h0]
  exact (measurable_const.sub (measurable_muMin I N hN h0)).exp

theorem isSat_indep (I : AutInst) (x y : I.GA) (A B : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hA : A.FG)
    (h : IsSat (rho I x) A B) : IsSat (rho I y) A B := by
  have hBA : B ≤ A := h.1
  have hB : B.FG := Submodule.FG.of_le hA hBA
  have hLy := isLat I y A hA
  obtain ⟨N', hBN, hNA, hz⟩ := Formalism.HN.satR _ _ _ (rho I y) A B hLy hBA
  obtain ⟨hsat, -, hrk⟩ := Formalism.F.saturProps _ (zl (rho I y) A) (zl (rho I y) B) hLy.2
    (Formalism.HN.satBasic_zl_mono (rho I y) hBA)
  have hN' : N'.FG := Submodule.FG.of_le hA hNA
  have hrky : rk (rho I y) N' = rk (rho I y) B := by
    show Formalism.F.rk (zl (rho I y) N') = Formalism.F.rk (zl (rho I y) B)
    rw [hz, hrk]
  have hrkx : rk (rho I x) N' = rk (rho I x) B := by
    rw [rk_eq I y N' hN', rk_eq I y B hB] at hrky
    rw [rk_eq I x N' hN', rk_eq I x B hB, hrky]
  have hNB : N' = B := (Formalism.HN.satBasic _ _ _ (rho I x) A (isLat I x A hA)).2.2.1 B N' h hBN hNA hrkx
  rw [← hNB]
  refine ⟨hNA, ?_⟩
  rw [hz]
  exact hsat

theorem measurable_sizeQ (I : AutInst) (A B : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hA : A.FG)
    (h : ∀ x, IsSat (rho I x) A B) (hne : B ≠ A) :
    Measurable fun x : I.GA => sizeQ (bas I) (frm I x) A B := by
  have hB : B.FG := Submodule.FG.of_le hA (h 1).1
  have key : ∀ x : I.GA, sizeQ (bas I) (frm I x) A B =
      ((2 : ℝ) ^ ((nPl I.E : ℝ) * ((rkK A : ℝ) - rkK B)) *
        |(NumberField.discr I.E : ℝ)| ^ (-((rkK A : ℝ) - rkK B) / 2) *
        Real.exp (-(deg (rho I x) A - deg (rho I x) B))) ^
        ((1 : ℝ) / (2 * (nPl I.E : ℝ) * ((rkK A : ℝ) - rkK B))) := by
    intro x
    have hL := isLat I x A hA
    have hq := ((Formalism.HN.satBasic _ _ _ (rho I x) A hL).2.2.2.2.2.2.2 B (h x)).2.2
    obtain ⟨hdisc, -, -⟩ := Formalism.F.degQuot _ (zl (rho I x) A) (zl (rho I x) B) hL.2 (h x).2
    have := hdisc
    have hpos := Formalism.F.covol_pos (Formalism.F.quot (zl (rho I x) A) (zl (rho I x) B))
    have hc : Formalism.F.covol (Formalism.F.quot (zl (rho I x) A) (zl (rho I x) B)) =
        Real.exp (-(deg (rho I x) A - deg (rho I x) B)) := by
      rw [← hq]
      show _ = Real.exp (-(-Real.log _))
      rw [neg_neg, Real.exp_log hpos]
    show (2 ^ ((nPl I.E : ℝ) * ((rkK A : ℝ) - rkK B)) *
        |(NumberField.discr I.E : ℝ)| ^ (-((rkK A : ℝ) - rkK B) / 2) *
        Formalism.F.covol (Formalism.F.quot (zl (rho I x) A) (zl (rho I x) B))) ^
        ((1 : ℝ) / (2 * (nPl I.E : ℝ) * ((rkK A : ℝ) - rkK B))) = _
    rw [hc]
  rw [show (fun x : I.GA => sizeQ (bas I) (frm I x) A B) = _ from funext key]
  exact (measurable_const.mul ((measurable_deg I A hA).sub (measurable_deg I B hB)).neg.exp).pow_const _

theorem mand {α : Type*} [MeasurableSpace α] {p q : α → Prop} (hp : MeasurableSet {x | p x})
    (hq : MeasurableSet {x | q x}) : MeasurableSet {x | p x ∧ q x} := hp.inter hq

theorem lam_fg (I : AutInst) (x : I.GA) : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

theorem measurableSet_mem_lam (I : AutInst) (y : Fin I.n → I.E) :
    MeasurableSet {x : I.GA | y ∈ lamX I x} := by
  obtain ⟨-, -, -, -, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hopen : IsOpen {g : I.Gf | y ∈ lamX I (1, g)} := by
    rw [isOpen_iff_mem_nhds]
    intro g hg
    have h1 : (fun k => g * k) '' I.Kset ∈ nhds g := by
      refine (isOpenMap_mul_left g _ hKo).mem_nhds ⟨1, ?_, mul_one g⟩
      rw [← hK]
      exact K.one_mem
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨k, hk, rfl⟩
    have := (GlobalTheory.PointLattice.lamX_selfDual I (1, g)).2.2.2.2 (1, k) hk
    show y ∈ lamX I (1, g * k)
    rw [show ((1, g * k) : I.GA) = (1, g) * (1, k) by rw [Prod.mk_mul_mk, one_mul], this]
    exact hg
  exact measurable_snd hopen.measurableSet

theorem countable_V (I : AutInst) : Countable (Fin I.n → I.E) := by
  have := countable_E' I
  infer_instance

theorem measurableSet_le_lam (I : AutInst) (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    MeasurableSet {x : I.GA | N ≤ lamX I x} := by
  have := countable_E' I
  have e : {x : I.GA | N ≤ lamX I x} = ⋂ y ∈ (N : Set (Fin I.n → I.E)), {x | y ∈ lamX I x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h y hy => h hy, fun h y hy => h y hy⟩
  rw [e]
  exact MeasurableSet.biInter (Set.to_countable _) fun y _ => measurableSet_mem_lam I y

theorem measurableSet_sSup (I : AutInst) (p : I.GA → Submodule (𝓞 I.E) (Fin I.n → I.E) → Prop)
    (hfg : ∀ x N, p x N → N.FG) (hp : ∀ N, N.FG → MeasurableSet {x | p x N})
    (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : MeasurableSet {x | S = sSup {N | p x N}} := by
  have := countable_E' I
  have : Countable ↥{N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG} := (countable_fg I).to_subtype
  have hmem : ∀ y : Fin I.n → I.E, Measurable fun x : I.GA => y ∈ sSup {N | p x N} := by
    intro y
    have e : (fun x : I.GA => y ∈ sSup {N | p x N}) = fun x =>
        ∃ s : Finset ↥{N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG},
          (∀ N, N ∈ s → p x N.1) ∧ y ∈ ⨆ N ∈ s, (N.1 : Submodule (𝓞 I.E) (Fin I.n → I.E)) := by
      funext x
      apply propext
      constructor
      · intro hy
        obtain ⟨s, hs, hys⟩ := Submodule.mem_sSup_iff_exists_finset.1 hy
        classical
        refine ⟨s.subtype (· ∈ {N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG}), fun N hN => hs (Finset.mem_subtype.1 hN), ?_⟩
        refine (iSup₂_le fun i hi => ?_ : ⨆ i ∈ s, i ≤ _) hys
        exact le_iSup₂_of_le (⟨i, hfg x i (hs hi)⟩ : ↥{N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG})
          (Finset.mem_subtype.2 hi) le_rfl
      · rintro ⟨s, hs, hys⟩
        exact (iSup₂_le fun N hN => le_sSup (hs N hN) : _ ≤ sSup {N | p x N}) hys
    rw [e]
    refine Measurable.exists fun s => Measurable.and ?_ measurable_const
    exact Measurable.forall fun N => Measurable.imp measurable_const (measurableSet_setOfPred.1 (hp N.1 N.2))
  have e2 : {x : I.GA | S = sSup {N | p x N}} = {x | ∀ y, (y ∈ S ↔ y ∈ sSup {N | p x N})} := by
    ext x
    exact SetLike.ext_iff
  rw [e2]
  exact measurableSet_setOfPred.2 (Measurable.forall fun y => measurable_const.iff (hmem y))

theorem measurableSet_stepLe (I : AutInst) (g : I.GA → ℝ) (hg : Measurable g)
    (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : MeasurableSet {x | S = stepLe I x (g x)} := by
  refine measurableSet_sSup I
    (fun x N => N ≤ lamX I x ∧ N ≠ ⊥ ∧ largestSize (bas I) (frm I x) N ≤ g x)
    (fun x N h => Submodule.FG.of_le (lam_fg I x) h.1) (fun N hN => ?_) S
  by_cases h0 : N = ⊥
  · have e : {x : I.GA | N ≤ lamX I x ∧ N ≠ ⊥ ∧ largestSize (bas I) (frm I x) N ≤ g x} = ∅ := by
      ext x
      exact ⟨fun hx => (hx.2.1 h0).elim, fun hx => hx.elim⟩
    rw [e]
    exact MeasurableSet.empty
  · exact (measurableSet_le_lam I N).inter ((MeasurableSet.const (N ≠ ⊥)).inter
      (measurableSet_le (measurable_largest I N hN h0) hg))

theorem measurableSet_stepLt (I : AutInst) (t : ℝ)
    (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : MeasurableSet {x | S = stepLt I x t} := by
  refine measurableSet_sSup I
    (fun x N => N ≤ lamX I x ∧ N ≠ ⊥ ∧ largestSize (bas I) (frm I x) N < t)
    (fun x N h => Submodule.FG.of_le (lam_fg I x) h.1) (fun N hN => ?_) S
  by_cases h0 : N = ⊥
  · have e : {x : I.GA | N ≤ lamX I x ∧ N ≠ ⊥ ∧ largestSize (bas I) (frm I x) N < t} = ∅ := by
      ext x
      exact ⟨fun hx => (hx.2.1 h0).elim, fun hx => hx.elim⟩
    rw [e]
    exact MeasurableSet.empty
  · exact (measurableSet_le_lam I N).inter ((MeasurableSet.const (N ≠ ⊥)).inter
      (measurableSet_lt (measurable_largest I N hN h0) measurable_const))

private theorem largestSize_le_of_ne_bot (I : AutInst) (x : I.GA) (t : ℝ) (h0 : stepLe I x t ≠ ⊥) :
    largestSize (bas I) (frm I x) (stepLe I x t) ≤ t := by
  have hfgL := lam_fg I x
  have hlat := isLat I x (lamX I x) hfgL
  obtain ⟨s, hsT, hsup⟩ := Formalism.HN.finSup _ _ _ (rho I x) (lamX I x)
    {N | N ≤ lamX I x ∧ N ≠ ⊥ ∧ largestSize (bas I) (frm I x) N ≤ t} hlat (fun N hN => hN.1)
  have hst : stepLe I x t = s.sup id := hsup
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact h0 (by rw [hst, Finset.sup_empty])
  obtain ⟨N0, hN0⟩ := hsne
  have hN0T := hsT hN0
  have hN0fg := Submodule.FG.of_le hfgL hN0T.1
  have ht : 0 < t := lt_of_lt_of_le (by rw [largest_eq I x N0 hN0fg hN0T.2.1]; exact Real.exp_pos _) hN0T.2.2
  have hθ : ∀ N ∈ s, id N ≤ lamX I x ∧ id N ≠ ⊥ ∧ cE I - Real.log t ≤ muMin (rho I x) (id N) := by
    intro N hN
    obtain ⟨h1, h2, h3⟩ := hsT hN
    have hfg := Submodule.FG.of_le hfgL h1
    rw [largest_eq I x N hfg h2, ← Real.le_log_iff_exp_le ht] at h3
    exact ⟨h1, h2, by simp only [id]; linarith⟩
  have hsum := (Formalism.HN.hnSum _ _ _ (rho I x)).1 (lamX I x) _ s id (cE I - Real.log t) hlat ⟨N0, hN0⟩ hθ
  have hsfg : (stepLe I x t).FG := Submodule.FG.of_le hfgL (sSup_le fun N hN => hN.1)
  rw [largest_eq I x _ hsfg h0]
  have heq : stepLe I x t = ⨆ i ∈ s, id i := by rw [hst, Finset.sup_eq_iSup]
  rw [heq, ← Real.le_log_iff_exp_le ht]
  linarith

theorem stepLe_cases (I : AutInst) (x : I.GA) (t : ℝ) :
    stepLe I x t = ⊥ ∨ ∃ N : Submodule (𝓞 I.E) (Fin I.n → I.E), N.FG ∧ N ≠ ⊥ ∧
      largestSize (bas I) (frm I x) N ≤ t ∧ stepLe I x t = stepLe I x (largestSize (bas I) (frm I x) N) := by
  by_cases h0 : stepLe I x t = ⊥
  · exact Or.inl h0
  right
  have hfgL := lam_fg I x
  have hfg : (stepLe I x t).FG := Submodule.FG.of_le hfgL (sSup_le fun N hN => hN.1)
  have hlarge := largestSize_le_of_ne_bot I x t h0
  refine ⟨stepLe I x t, hfg, h0, hlarge, le_antisymm ?_ ?_⟩
  · exact le_sSup ⟨sSup_le fun N hN => hN.1, h0, le_rfl⟩
  · exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, hN.2.2.trans hlarge⟩

theorem measurableSet_steps (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    MeasurableSet {x : I.GA | S 0 = ⊥ → ∀ t : ℝ, t < 1 / 2 → stepLe I x t ∈ Set.range S} := by
  by_cases h0 : S 0 = ⊥
  · have e : {x : I.GA | S 0 = ⊥ → ∀ t : ℝ, t < 1 / 2 → stepLe I x t ∈ Set.range S} =
        ⋂ N ∈ {N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG ∧ N ≠ ⊥},
          {x | largestSize (bas I) (frm I x) N < 1 / 2 →
            ∃ i, S i = stepLe I x (largestSize (bas I) (frm I x) N)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_range]
      constructor
      · intro h N _ hlt
        exact h h0 _ hlt
      · intro h _ t ht
        rcases stepLe_cases I x t with hb | ⟨N, hN, hN0, hle, heq⟩
        · exact ⟨0, by rw [h0, hb]⟩
        · rw [heq]
          exact h N ⟨hN, hN0⟩ (lt_of_le_of_lt hle ht)
    rw [e]
    refine MeasurableSet.biInter ((countable_fg I).mono fun N hN => hN.1) fun N hN => ?_
    refine measurableSet_setOfPred.2 (Measurable.imp ?_ (Measurable.exists fun i => ?_))
    · exact measurableSet_setOfPred.1 (measurableSet_lt (measurable_largest I N hN.1 hN.2) measurable_const)
    · exact measurableSet_setOfPred.1 (measurableSet_stepLe I _ (measurable_largest I N hN.1 hN.2) (S i))
  · have e : {x : I.GA | S 0 = ⊥ → ∀ t : ℝ, t < 1 / 2 → stepLe I x t ∈ Set.range S} = Set.univ := by
      ext x
      exact ⟨fun _ => trivial, fun _ h => (h0 h).elim⟩
    rw [e]
    exact MeasurableSet.univ

theorem measurableSet_hasFlag (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hS : ∀ i : Fin a, Measurable fun x : I.GA => sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc)) :
    MeasurableSet {x : I.GA |
      HasFlag I x S fun i => sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc)} := by
  have hs : ∀ i : Fin a, Measurable fun x : I.GA => sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := hS
  by_cases h0 : S 0 = ⊥
  swap
  · have e : {x : I.GA | HasFlag I x S fun i => sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc)} = ∅ := by
      ext x
      exact ⟨fun hx => (h0 hx.1).elim, fun hx => hx.elim⟩
    rw [e]
    exact MeasurableSet.empty
  have hst : Measurable fun x : I.GA => ∀ t : ℝ, t < 1 / 2 → stepLe I x t ∈ Set.range S := by
    have e : (fun x : I.GA => ∀ t : ℝ, t < 1 / 2 → stepLe I x t ∈ Set.range S) =
        fun x => S 0 = ⊥ → ∀ t : ℝ, t < 1 / 2 → stepLe I x t ∈ Set.range S :=
      funext fun x => propext ⟨fun h _ => h, fun h => h h0⟩
    rw [e]
    exact measurableSet_setOfPred.1 (measurableSet_steps I S)
  have hmono : Measurable fun x : I.GA =>
      StrictMono fun i : Fin a => sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
    unfold StrictMono
    exact Measurable.forall fun i => Measurable.forall fun k => Measurable.imp measurable_const
      (measurableSet_setOfPred.1 (measurableSet_lt (hs i) (hs k)))
  have hall : Measurable fun x : I.GA => ∀ i : Fin a,
      0 < sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) ∧
      sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) < 1 / 2 ∧
      S i.succ = stepLe I x (sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc)) ∧
      sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) = sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
    refine Measurable.forall fun i => ?_
    exact (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (hs i))).and
      ((measurableSet_setOfPred.1 (measurableSet_lt (hs i) measurable_const)).and
        ((measurableSet_setOfPred.1 (measurableSet_stepLe I _ (hs i) (S i.succ))).and
          (measurableSet_setOfPred.1 (measurableSet_eq_fun (hs i) (hs i)))))
  have hlast : Measurable fun x : I.GA => S (Fin.last a) = stepLt I x (1 / 2) :=
    measurableSet_setOfPred.1 (measurableSet_stepLt I (1 / 2) (S (Fin.last a)))
  exact measurableSet_setOfPred.2 (measurable_const.and (measurable_const.and
    (hlast.and (hmono.and (hall.and hst)))))

theorem stepLe_sat (I : AutInst) (x : I.GA) (t : ℝ) (ht : 0 < t) :
    IsSat (rho I x) (lamX I x) (stepLe I x t) := by
  have hfgL := lam_fg I x
  have hlat := isLat I x (lamX I x) hfgL
  have heq : stepLe I x t = hnStep (rho I x) (lamX I x) (cE I - Real.log t) := by
    show sSup {N | N ≤ lamX I x ∧ N ≠ ⊥ ∧ largestSize (bas I) (frm I x) N ≤ t} =
      sSup {N | N ≤ lamX I x ∧ N ≠ ⊥ ∧ cE I - Real.log t ≤ muMin (rho I x) N}
    congr 1
    ext N
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [largest_eq I x N (Submodule.FG.of_le hfgL h1) h2, ← Real.le_log_iff_exp_le ht] at h3
      linarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [largest_eq I x N (Submodule.FG.of_le hfgL h1) h2, ← Real.le_log_iff_exp_le ht]
      linarith
  rw [heq]
  exact (Formalism.HN.hnStep_spec _ _ _ (rho I x) (lamX I x) hlat (cE I - Real.log t)).1

theorem flag_sat (I : AutInst) (x : I.GA) {a : ℕ} {S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)}
    {τ : Fin a → ℝ} (h : HasFlag I x S τ) (i : Fin (a + 1)) : IsSat (rho I x) (lamX I x) (S i) := by
  obtain ⟨h0, -, -, -, hτ, -⟩ := h
  induction i using Fin.cases with
  | zero =>
    rw [h0]
    exact (Formalism.HN.satBasic _ _ _ (rho I x) (lamX I x) (isLat I x _ (lam_fg I x))).2.2.2.2.2.1
  | succ j =>
    rw [(hτ j).2.2.1]
    exact stepLe_sat I x _ (hτ j).1

theorem flag_unique (I : AutInst) (x : I.GA) {a : ℕ} {S S' : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)}
    {τ τ' : Fin a → ℝ} (h : HasFlag I x S τ) (h' : HasFlag I x S' τ') : S = S' := by
  have sub : ∀ {T T' : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)} {σ σ' : Fin a → ℝ},
      HasFlag I x T σ → HasFlag I x T' σ' → Set.range T ⊆ Set.range T' := by
    intro T T' σ σ' hT hT'
    obtain ⟨t0, -, -, -, hσ, -⟩ := hT
    obtain ⟨t0', -, -, -, -, hall'⟩ := hT'
    rintro _ ⟨i, rfl⟩
    induction i using Fin.cases with
    | zero => exact ⟨0, by rw [t0, t0']⟩
    | succ j =>
      rw [(hσ j).2.2.1]
      exact hall' _ (hσ j).2.1
  obtain ⟨-, hm, -⟩ := (id h : HasFlag I x S τ)
  obtain ⟨-, hm', -⟩ := (id h' : HasFlag I x S' τ')
  exact (StrictMono.range_inj hm hm').1 (Set.Subset.antisymm (sub h h') (sub h' h))

private theorem isSat_of_le_of_le (I : AutInst) (x : I.GA) {L A B : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (h : IsSat (rho I x) L B) (hBA : B ≤ A) (hAL : A ≤ L) : IsSat (rho I x) A B := by
  obtain ⟨-, -, h3⟩ := h
  exact ⟨hBA, Formalism.HN.satBasic_zl_mono (rho I x) hBA,
    fun z hz hs => h3 z (Formalism.HN.satBasic_zl_mono (rho I x) hAL hz) hs⟩

theorem type_measurable : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ), ∃ s : I.GA → Fin a → ℝ, Measurable s ∧
    MeasurableSet {x : I.GA | ∃ τ, HasType I x j τ} ∧ ∀ x τ, HasType I x j τ → s x = τ := by
  intro I a j
  classical
  have : Countable ↥{N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG} := (countable_fg I).to_subtype
  let sz : (Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) → I.GA → Fin a → ℝ :=
    fun S x i => sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc)
  let P : (Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) → I.GA → Prop :=
    fun S x => HasFlag I x S (sz S x) ∧ ∀ i, rkK (S i.succ) = rkK (S i.castSucc) + j i
  have fgOf : ∀ {x : I.GA} {S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)} {τ : Fin a → ℝ},
      HasFlag I x S τ → ∀ i, (S i).FG := fun hf i =>
    Submodule.FG.of_le (lam_fg I _) (flag_sat I _ hf i).1
  have hPm : ∀ S, MeasurableSet {x | P S x} ∧ ∀ B : Set (Fin a → ℝ), MeasurableSet B →
      MeasurableSet ({x | P S x} ∩ sz S ⁻¹' B) := by
    intro S
    by_cases hex : ∃ x0, P S x0
    · obtain ⟨x0, hf0, -⟩ := hex
      have hSm : StrictMono S := by
        obtain ⟨-, hm, -⟩ := (id hf0 : HasFlag I x0 S (sz S x0))
        exact hm
      have hsat : ∀ i : Fin a, ∀ x, IsSat (rho I x) (S i.succ) (S i.castSucc) := fun i x =>
        isSat_indep I x0 x (S i.succ) (S i.castSucc) (fgOf hf0 i.succ)
          (isSat_of_le_of_le I x0 (flag_sat I x0 hf0 i.castSucc)
            (hSm.monotone (show i.castSucc ≤ i.succ from Fin.castSucc_lt_succ.le)) (flag_sat I x0 hf0 i.succ).1)
      have hsm : ∀ i : Fin a, Measurable fun x : I.GA => sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) :=
        fun i => measurable_sizeQ I _ _ (fgOf hf0 i.succ) (hsat i) (hSm (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).ne
      have hszm : Measurable (sz S) := measurable_pi_lambda _ hsm
      have hm1 : MeasurableSet {x | P S x} :=
        (measurableSet_hasFlag I S hsm).inter (MeasurableSet.const _)
      exact ⟨hm1, fun B hB => hm1.inter (hszm hB)⟩
    · have e : {x | P S x} = ∅ := by
        ext x
        exact ⟨fun hx => (hex ⟨x, hx⟩).elim, fun hx => hx.elim⟩
      refine ⟨by rw [e]; exact MeasurableSet.empty, fun B _ => by rw [e, Set.empty_inter]; exact MeasurableSet.empty⟩
  have hTyp : ∀ x τ, HasType I x j τ → ∃ S' : Fin (a + 1) → ↥{N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG},
      P (fun i => (S' i).1) x ∧ sz (fun i => (S' i).1) x = τ := by
    rintro x τ ⟨S, hf, hr⟩
    have hτ : sz S x = τ := by
      obtain ⟨-, -, -, -, h1, -⟩ := (id hf : HasFlag I x S τ)
      funext i
      exact (h1 i).2.2.2
    refine ⟨fun i => ⟨S i, fgOf hf i⟩, ⟨?_, hr⟩, hτ⟩
    rw [show sz (fun i => ((⟨S i, fgOf hf i⟩ : ↥{N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG}) : Submodule (𝓞 I.E) (Fin I.n → I.E))) x = τ from hτ]
    exact hf
  have hTyp' : ∀ x S, P S x → HasType I x j (sz S x) := fun x S hP => ⟨S, hP.1, hP.2⟩
  have huniq : ∀ x τ τ', HasType I x j τ → HasType I x j τ' → τ = τ' := by
    rintro x τ τ' ⟨S, hf, -⟩ ⟨S', hf', -⟩
    have hSS := flag_unique I x hf hf'
    subst hSS
    obtain ⟨-, -, -, -, h1, -⟩ := hf
    obtain ⟨-, -, -, -, h1', -⟩ := hf'
    funext i
    rw [← (h1 i).2.2.2, ← (h1' i).2.2.2]
  let s : I.GA → Fin a → ℝ := fun x => if h : ∃ τ, HasType I x j τ then h.choose else 0
  have hs : ∀ x τ, HasType I x j τ → s x = τ := by
    intro x τ hx
    show (if h : ∃ τ, HasType I x j τ then h.choose else 0) = τ
    rw [dif_pos ⟨τ, hx⟩]
    exact huniq x _ _ (Exists.choose_spec _) hx
  have hD : {x : I.GA | ∃ τ, HasType I x j τ} =
      ⋃ S' : Fin (a + 1) → ↥{N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG}, {x | P (fun i => (S' i).1) x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨τ, hx⟩
      obtain ⟨S', hP, -⟩ := hTyp x τ hx
      exact ⟨S', hP⟩
    · rintro ⟨S', hP⟩
      exact ⟨_, hTyp' x _ hP⟩
  refine ⟨s, ?_, ?_, hs⟩
  · intro B hB
    have e : s ⁻¹' B = (⋃ S' : Fin (a + 1) → ↥{N : Submodule (𝓞 I.E) (Fin I.n → I.E) | N.FG},
        ({x | P (fun i => (S' i).1) x} ∩ sz (fun i => (S' i).1) ⁻¹' B)) ∪
        ({x | ∃ τ, HasType I x j τ}ᶜ ∩ {_x | (0 : Fin a → ℝ) ∈ B}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_compl_iff]
      by_cases hx : ∃ τ, HasType I x j τ
      · obtain ⟨τ, hxτ⟩ := hx
        rw [hs x τ hxτ]
        constructor
        · intro hB'
          obtain ⟨S', hP, hsz⟩ := hTyp x τ hxτ
          exact Or.inl ⟨S', hP, by rw [hsz]; exact hB'⟩
        · rintro (⟨S', hP, hB'⟩ | ⟨hn, -⟩)
          · rwa [huniq x _ _ (hTyp' x _ hP) hxτ] at hB'
          · exact (hn ⟨τ, hxτ⟩).elim
      · have h0 : s x = 0 := by
          show (if h : ∃ τ, HasType I x j τ then h.choose else 0) = 0
          rw [dif_neg hx]
        rw [h0]
        constructor
        · intro hB'
          exact Or.inr ⟨hx, hB'⟩
        · rintro (⟨S', hP, -⟩ | ⟨-, hB'⟩)
          · exact (hx ⟨_, hTyp' x _ hP⟩).elim
          · exact hB'
    rw [e]
    refine (MeasurableSet.iUnion fun S' => (hPm _).2 B hB).union ?_
    refine MeasurableSet.inter ?_ (MeasurableSet.const _)
    rw [hD]
    exact (MeasurableSet.iUnion fun S' => (hPm _).1).compl
  · rw [hD]
    exact MeasurableSet.iUnion fun S' => (hPm _).1

end GlobalTheory.FlagMeas
