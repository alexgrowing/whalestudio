import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.Published.ArDegreeModel

theorem birational_int (t : ℝ) : IsArithVar (𝟙 (Sp ℤ)) 0 ∧ ((⊤ : (Sp ℤ).Opens) : Set (Sp ℤ)).Nonempty ∧
    IsIso (𝟙 (Sp ℤ) ∣_ ⊤) ∧ (ArithBase.trivShift t).IsSelfInter t ∧
    ((ArithBase.trivShift t).pull (𝟙 _) (Category.id_comp _)).IsSelfInter t :=
  ⟨ArithBase.isArithVar_int, ⟨genericPoint _, trivial⟩, inferInstance, ArithBase.isSelfInter_trivShift t,
    ArInt.Model.IsConst.isSelfInter fun i => ⟨fun _ => Set.mem_iInter.2 fun _ => trivial, fun σ y =>
      (((ArithBase.trivShift t).φ σ).pull_φ _ _ i y).trans (zero_add _)⟩⟩

variable {F : Type} [Field F] (Y : Var F) (σ : F →+* ℂ)

theorem chernDegree_triv (h : 1 ≤ Y.dim) (c : ℝ) :
    Presents (0 : Y.Dv) (LB.triv Y.X) (fun _ => 1) ∧ (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c).IsCInf ∧
      (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c).ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧
      (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c).chernInt Y.dim Set.univ (fun _ => 1) =
        (Y.inter (fun _ => (0 : Y.Dv)) : ℝ) := by
  have hd (ch : AlgChart Y.str σ Y.dim) (y) :
      ch.chernDens (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c) y = 0 := by
    have : Nonempty (Fin Y.dim) := ⟨⟨0, h⟩⟩
    have e : ch.hess (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c) PUnit.unit y = 0 := by
      ext a b
      have e₀ : ReciprocityTheory.L2DbarEstimates.wdb Y.dim b (fun _ => (c : ℂ)) = fun _ => 0 := by
        funext v; simp [ReciprocityTheory.L2DbarEstimates.wdb]
      simp [AlgChart.hess, Weight.ofFun, ReciprocityTheory.L2DbarEstimates.cHess, ReciprocityTheory.L2DbarEstimates.wd, e₀]
    rw [AlgChart.chernDens]
    erw [e]
    simp
  have hz (ε : ℤˣ) : (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c).chernPart Y.dim ε = 0 := by
    refine le_antisymm (iSup_le fun ch => le_of_eq ?_) bot_le
    simp only [hd, mul_zero, ENNReal.ofReal_zero, ChartGlue.chartMeas]
    rw [show ((fun _ => (0 : ENNReal)) ∘ ch.e.symm) = 0 from rfl]
    simp
  refine ⟨presents_zero, Weight.isCInf_ofFun (cInfAt_const c), ⟨by rw [hz]; simp [MeasureTheory.IntegrableOn],
    by rw [hz]; simp [MeasureTheory.IntegrableOn]⟩, ?_⟩
  rw [Y.inter_eq_zero_of_principal _ ⟨0, h⟩ 1 rfl, Weight.chernInt, hz, hz]
  simp

def fs : Weight Y.str σ Y.O1 :=
  Weight.fsBasis Y.str σ Y.isLineBundle_twistingSheafOne Y.coordSec Y.basePointFree_coordSys 1 (by simp)

theorem isCInf_fs : (fs Y σ).IsCInf := Weight.isCInf_fsBasis _ _ _ _ _

theorem mass_proj (H : ChernDegree) (n : ℕ) :
    (fs (proj F n) σ).chernInt n Set.univ (fun _ => 1) = 1 := by
  have := (H F (proj F n) σ _ _ _ ((proj F n).presents_hyp (proj_gen_mem F n 0)) _ (isCInf_fs _ σ)).2
  exact this.trans (by exact_mod_cast inter_projHyp F n)

theorem unique_pt (h : Y.dim = 0) : Nonempty (CxPts Y.str σ) ∧ Subsingleton (CxPts Y.str σ) := by
  have : Etale Y.str := (Etale.iff_smoothOfRelativeDimension_zero _).2 (h ▸ Y.smooth_str)
  let q := Limits.pullback.snd Y.str (spMap σ)
  have : IsIntegral (Limits.pullback Y.str (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := Y.str) _ _ _ (IsPullback.of_hasPullback _ _)
  have hs (s : Sp ℂ ⟶ Limits.pullback Y.str (spMap σ)) (hs : s ≫ q = 𝟙 _) : IsIso q := by
    have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
    have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
    have : Etale (s ≫ q) := by rw [hs]; infer_instance
    have : Etale s := Etale.of_comp s q
    have : Mono s := (SplitMono.mk q hs).mono
    have : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono s
    have : IsIso s := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (Opens.ext
      (IsClopen.eq_univ ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩ (Set.range_nonempty _)))
    have : IsIso (s ≫ q) := by rw [hs]; infer_instance
    exact IsIso.of_isIso_comp_left s _
  have : JacobsonSpace (Limits.pullback Y.str (spMap σ) :) := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (X := (Limits.pullback Y.str (spMap σ) :)) Set.univ_nonempty
    isOpen_univ.isLocallyClosed
  have := hs _ (pointOfClosedPoint_comp q c hc)
  refine ⟨⟨⟨inv q ≫ Limits.pullback.fst _ _, by rw [Category.assoc, Limits.pullback.condition]; simp [q]⟩⟩,
    ⟨fun a b => Subtype.ext ?_⟩⟩
  have e : Limits.pullback.lift a.1 (𝟙 _) (by simpa using a.2) = Limits.pullback.lift b.1 (𝟙 _) (by simpa using b.2) :=
    (cancel_mono q).1 ((Limits.pullback.lift_snd _ _ _).trans (Limits.pullback.lift_snd _ _ _).symm)
  exact (Limits.pullback.lift_fst _ _ _).symm.trans
    ((congrArg (· ≫ Limits.pullback.fst _ _) e).trans (Limits.pullback.lift_fst _ _ _))

theorem chernDegree_point (Δ : (proj F 0).Dv) (L : LB (proj F 0).X) (φ : Weight (proj F 0).str σ L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn 0 Set.univ (fun _ => 1) ∧
      φ.chernInt 0 Set.univ (fun _ => 1) = ((proj F 0).inter (fun _ => Δ) : ℝ) := by
  obtain ⟨⟨y⟩, _⟩ := unique_pt (proj F 0) σ rfl
  have : SmoothOfRelativeDimension 0 (proj F 0).str := (proj F 0).smooth_str
  have := CxPts.secondCountableTopology_of_isProjOver σ (proj F 0).isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth (proj F 0).str 0 σ
  obtain ⟨a, ha⟩ := R.cover y
  have hm (ε : ℤˣ) : φ.chernPart 0 ε Set.univ = ENNReal.ofReal (ε : ℤ) := by
    rw [Weight.chernPart_apply h ε (R.chart a) MeasurableSet.univ fun z _ => Subsingleton.elim y z ▸ ha]
    simp only [AlgChart.chernDens_zero, mul_one]
    rw [show (R.chart a).e '' Set.univ = Set.univ from
      Set.eq_univ_of_forall fun v => ⟨y, trivial, Subsingleton.elim _ _⟩]
    have hv : (MeasureTheory.volume : MeasureTheory.Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1 := by
      have := (stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped
      rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
        (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, Subsingleton.elim _ _⟩] at this
    simp [hv]
  have hf (ε : ℤˣ) : MeasureTheory.IsFiniteMeasure (φ.chernPart 0 ε) := ⟨by rw [hm]; exact ENNReal.ofReal_lt_top⟩
  have hi : (proj F 0).inter (fun _ => Δ) = 1 :=
    (congrArg _ (funext fun i : Fin 0 => i.elim0)).trans (inter_projHyp F 0)
  refine ⟨⟨MeasureTheory.integrableOn_univ.2 (MeasureTheory.integrable_const _),
    MeasureTheory.integrableOn_univ.2 (MeasureTheory.integrable_const _)⟩, ?_⟩
  rw [hi, Weight.chernInt]
  simp [MeasureTheory.Measure.real, hm, ENNReal.toReal_ofReal']

theorem hyp_proj (N : ℕ) : GenSmooth (𝟙 (Sp ℤ)) 0 ∧ IsArithVar (PSpace.str ℤ N) N ∧ GenSmooth (PSpace.str ℤ N) N ∧
    IsIso (𝟙 (PSpace ℤ N) ∣_ ⊤) :=
  ⟨genSmooth_of_smooth _ _, ProjSpace.isArithVar_int N, genSmooth_of_smooth _ _, inferInstance⟩

theorem birational_id {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (a : ℝ) (h : L.IsSelfInter a) :
    (L.pull (𝟙 X) (Category.id_comp p)).IsSelfInter a := by
  obtain ⟨f, hf, e⟩ := h
  have hr : TwistTop.Refines L (L.pull (𝟙 X) (Category.id_comp p)) (fun c _ => c) 0 := by
    refine ⟨fun c y hy => Set.mem_iInter.2 fun _ => hy, fun Z r z c c' hc hc' => ?_, fun σ c y _ => ?_⟩
    · refine Eq.trans ?_ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pull_g L.B (𝟙 X) r z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · refine Eq.trans ?_ (((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).symm.trans (add_zero _).symm)
      exact congrArg _ (Subtype.ext (Category.comp_id _).symm)
  exact ⟨f, hr.isArithHeight hX hf, e⟩

end GlobalTheory.Published.ArDegreeModel
