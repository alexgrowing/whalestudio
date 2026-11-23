import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FinConv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocGLMemKglob
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinTestTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.FC GlobalTheory.CompanionTheory.FinLevelTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem exists_lift (Y : ∀ w : Pl E, GLw n w) (hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w n) :
    ∃ x : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) x = Y w := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun w => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem eventually_mem_KGL (g : GL (Fin n) (Af E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem coe_pair_compact_subgroup (a b : ℕ) (w : Pl E) : (K2 a b w : Set (GLw a w × GLw b w)) =
    (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w b : Set (GLw b w)) := Subgroup.coe_prod _ _

theorem mem_prod_Kf {x : Gf E a b} :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ w : Pl E, atHom a b w x ∈ K2 a b w := by
  simp only [Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap, forall_and]
  rfl

theorem isRestrW (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (atHom (E := E) a b) (K2 a b) := by
  have hset : {x : Gf E a b | ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
      (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
    Set.ext fun x => (mem_prod_Kf (x := x)).symm.trans Subgroup.mem_prod
  refine ⟨fun w => w.elim, continuous_atHom, fun w => ?_, fun w => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  · exact Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.fst (H w))
      (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.snd (H w))
  · filter_upwards [eventually_mem_KGL x.1, eventually_mem_KGL x.2] with w h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun w => (y w).1) (hy.mono fun w h => h.1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun w => (y w).2) (hy.mono fun w h => h.2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun w => Prod.ext (h₁ w) (h₂ w)⟩
  · rw [hset]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← hset]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf

def psi (n : ℕ) (w : Pl E) (g : GLw n (GlobalTheory.EulerTw.cPl E w)) : GLw n w :=
  thetaGL n (RingHom.id _) (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g)

theorem continuous_psi (n : ℕ) (w : Pl E) : Continuous (psi (E := E) n w) :=
  (GlobalTheory.ThetaPull.continuous_thetaGL _ continuous_id).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1))

theorem psi_mem (w : Pl E) {g : GLw n (GlobalTheory.EulerTw.cPl E w)} (hg : g ∈ GlobalTheory.LFun.KGL (GlobalTheory.EulerTw.cPl E w) n) :
    psi n w g ∈ GlobalTheory.LFun.KGL w n :=
  GlobalTheory.EulerTwSplit.theta_mem _ (conjLoc_spec _ w).2.2 hg

theorem pc_eq_psi (w : Pl E) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) x =
      psi n w (GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E w)) (thF E n x)) := by
  have h := GlobalTheory.EulerTwU.pc_thF w (thF E n x)
  rwa [GlobalTheory.EulerTwU.thF_thF] at h

def psi2 (a b : ℕ) (w : Pl E) (y : GLw a (GlobalTheory.EulerTw.cPl E w) × GLw b (GlobalTheory.EulerTw.cPl E w)) : GLw a w × GLw b w :=
  (psi a w y.1, psi b w y.2)

theorem continuous_pair_projection (a b : ℕ) (w : Pl E) : Continuous (psi2 (E := E) a b w) :=
  ((continuous_psi a w).comp continuous_fst).prodMk ((continuous_psi b w).comp continuous_snd)

theorem place_component_eq_pair (w : Pl E) (y : Gf E a b) :
    atW w y = psi2 a b w (atW (GlobalTheory.EulerTw.cPl E w) (thP E a b y)) :=
  Prod.ext (pc_eq_psi w y.1) (pc_eq_psi w y.2)

theorem eventually_eq_indicator {φ : Fam E a b} (h : IsTestP φ) :
    ∀ᶠ w : Pl E in cofinite, φ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact h.2

theorem hasCompactSupport_loc {φ : Fam E a b} (h : IsTestP φ) (w : Pl E) : HasCompactSupport (φ w) := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact (h.1 w).1

theorem factors_ne_zero {S : Set (Pl E)} {φ₁ φ₂ : Fam E a b} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) {y : Gf E a b}
    (hy : finFn S φ₁ φ₂ y ≠ 0) (w : Pl E) (hw : w ∈ S) :
    φ₁ w (atW w y) ≠ 0 ∧ (IsSplitAt w → φ₂ w (atW w (thP E a b y)) ≠ 0) := by
  set g : Pl E → ℂ := fun w => φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg
  have hone : ∀ᶠ w in cofinite, g w = 1 := by
    filter_upwards [eventually_eq_indicator h₁, eventually_eq_indicator h₂, (isRestrW a b).eventually_mem y,
      (isRestrW a b).eventually_mem (thP E a b y)] with w e₁ e₂ m₁ m₂
    have m₁' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₁
    have m₂' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₂
    simp only [hg]
    rw [e₁, e₂, Set.indicator_of_mem m₁', Set.indicator_of_mem m₂']
    simp
  have hfin : (S ∩ Function.mulSupport g).Finite :=
    (eventually_cofinite.1 hone).subset fun w hw => hw.2
  have hz : g w ≠ 0 := by
    intro h0
    apply hy
    change ∏ᶠ w ∈ S, g w = 0
    rw [finprod_mem_eq_prod g hfin]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.2 ⟨hw, by simp [Function.mem_mulSupport, h0]⟩) h0
  refine ⟨left_ne_zero_of_mul hz, fun hs => ?_⟩
  have hz' := right_ne_zero_of_mul hz
  rwa [if_pos hs] at hz'

theorem tsupport_indicator_subset (w : Pl E) :
    tsupport ((K2 a b w : Set (GLw a w × GLw b w)).indicator (1 : GLw a w × GLw b w → ℂ)) ⊆
      (K2 a b w : Set (GLw a w × GLw b w)) :=
  closure_minimal (fun _ hx => by_contra fun h => hx (Set.indicator_of_notMem h _)) ((isRestrW a b).isCompact_K w).isClosed

theorem hasCompactSupport_finFn {S : Set (Pl E)} (hS : IsSection S) {φ₁ φ₂ : Fam E a b} (h₁ : IsTestP φ₁)
    (h₂ : IsTestP φ₂) : HasCompactSupport (finFn S φ₁ φ₂) := by
  haveI : T2Space (Af E) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  let D : ∀ w : Pl E, Set (GLw a w × GLw b w) := fun w =>
    if w ∈ S then tsupport (φ₁ w) else psi2 a b w '' tsupport (φ₂ (GlobalTheory.EulerTw.cPl E w))
  have hD : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ S
    · simp only [D, if_pos hw]
      exact hasCompactSupport_loc h₁ w
    · simp only [D, if_neg hw]
      exact (hasCompactSupport_loc h₂ _).image (continuous_pair_projection a b w)
  have hinj : Function.Injective (GlobalTheory.EulerTw.cPl E) :=
    Function.LeftInverse.injective GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl
  have hev : ∀ᶠ w : Pl E in cofinite, φ₁ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 ∧
      φ₂ (GlobalTheory.EulerTw.cPl E w) = (K2 a b (GlobalTheory.EulerTw.cPl E w) : Set _).indicator 1 :=
    (eventually_eq_indicator h₁).and (hinj.tendsto_cofinite.eventually (eventually_eq_indicator h₂))
  have hT := eventually_cofinite.1 hev
  have hDK : ∀ w ∉ hT.toFinset, D w ⊆ (K2 a b w : Set (GLw a w × GLw b w)) := by
    intro w hw
    have he : φ₁ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 ∧
        φ₂ (GlobalTheory.EulerTw.cPl E w) = (K2 a b (GlobalTheory.EulerTw.cPl E w) : Set _).indicator 1 := by
      by_contra h
      exact hw (hT.mem_toFinset.2 h)
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS]
      rw [he.1]
      exact tsupport_indicator_subset w
    · simp only [D, if_neg hwS]
      rw [he.2]
      rintro _ ⟨z, hz, rfl⟩
      have hz' := tsupport_indicator_subset _ hz
      exact ⟨psi_mem w hz'.1, psi_mem w hz'.2⟩
  have hC := GlobalTheory.CptPartRestr.isCompact_setOf_forall_mem (isRestrW (E := E) a b) hT.toFinset D hD hDK
  haveI : T2Space (Gf E a b) := inferInstance
  haveI : R1Space (Gf E a b) := T2Space.r1Space
  refine HasCompactSupport.intro hC fun y hy => ?_
  by_contra hne
  refine hy fun w => ?_
  by_cases hwS : w ∈ S
  · change atW w y ∈ D w
    simp only [D, if_pos hwS]
    exact subset_tsupport _ (factors_ne_zero h₁ h₂ hne w hwS).1
  · change atW w y ∈ D w
    simp only [D, if_neg hwS]
    obtain ⟨v, hv, e⟩ := (GlobalTheory.CompanionTheory.SuppFinTw.mem_or_conj hS w).resolve_left hwS
    have hcv : GlobalTheory.EulerTw.cPl E w = v := by rw [e, GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]
    have hcS : GlobalTheory.EulerTw.cPl E w ∈ S := hcv ▸ hv
    have hsp : IsSplitAt (GlobalTheory.EulerTw.cPl E w) := by
      refine GlobalTheory.CompanionTheory.SuppFinTw.split_of_conj_ne ?_
      rw [GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]
      exact fun h => hwS (h ▸ hcS)
    exact ⟨_, subset_tsupport _ ((factors_ne_zero h₁ h₂ hne _ hcS).2 hsp), (place_component_eq_pair w y).symm⟩

theorem finTest : PositivityTheory.Rg.BcB.FC.FinTest := by
  intro E _ _ _ _ a b S hS φ₁ φ₂ h₁ h₂
  haveI : T2Space (Af E) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  obtain ⟨L₁, o₁, e₁, i₁⟩ := exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := exists_level_of_test h₂
  let A : Subgroup (Gf E a b) := ⨅ w, (L₁ w ⊓ L₂ w).comap (atHom a b w)
  have hA : IsOpen (A : Set (Gf E a b)) := by
    refine isOpen_family _ (fun w => ?_) ?_
    · rw [Subgroup.coe_inf]
      exact (o₁ w).inter (o₂ w)
    · filter_upwards [e₁, e₂] with w f₁ f₂
      rw [f₁, f₂, inf_idem]
  have mA : ∀ {u}, u ∈ A → ∀ w, atW w u ∈ L₁ w ⊓ L₂ w := fun hu w =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu w)
  let U : Subgroup (Gf E a b) := (A ⊓ A.comap (thP E a b)) ⊓ (Kf E a).prod (Kf E b)
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  have hKc : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf
  have hUo : IsOpen (U : Set (Gf E a b)) := by
    simp only [U, Subgroup.coe_inf]
    exact (hA.inter (hA.preimage continuous_thP)).inter hKo
  have hUc : IsCompact (U : Set (Gf E a b)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo) fun _ hu => hu.2
  have hinv : ∀ u ∈ U, ∀ y, finFn S φ₁ φ₂ (u * y) = finFn S φ₁ φ₂ y ∧ finFn S φ₁ φ₂ (y * u) = finFn S φ₁ φ₂ y := by
    intro u hu y
    have hu₁ := mA hu.1.1
    have hu₂ := mA (Subgroup.mem_comap.1 hu.1.2)
    have l₁ : ∀ w, atW w (u * y) = atW w u * atW w y := fun w => map_mul (atHom a b w) u y
    have r₁ : ∀ w, atW w (y * u) = atW w y * atW w u := fun w => map_mul (atHom a b w) y u
    have l₂ : ∀ w, atW w (thP E a b (u * y)) = atW w (thP E a b u) * atW w (thP E a b y) := fun w => by
      rw [map_mul]; exact map_mul (atHom a b w) _ _
    have r₂ : ∀ w, atW w (thP E a b (y * u)) = atW w (thP E a b y) * atW w (thP E a b u) := fun w => by
      rw [map_mul]; exact map_mul (atHom a b w) _ _
    constructor
    · unfold finFn
      refine finprod_congr fun w => finprod_congr fun _ => ?_
      rw [l₁, l₂, (i₁ w _ (hu₁ w).1 _).1, (i₂ w _ (hu₂ w).2 _).1]
    · unfold finFn
      refine finprod_congr fun w => finprod_congr fun _ => ?_
      rw [r₁, r₂, (i₁ w _ (hu₁ w).1 _).2, (i₂ w _ (hu₂ w).2 _).2]
  refine ⟨?_, hasCompactSupport_finFn hS h₁ h₂, U, hUo, hUc, hinv⟩
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
  have hc : Continuous fun y : Gf E a b => x⁻¹ * y := continuous_const.mul continuous_id
  have hm : ∀ᶠ y in nhds x, x⁻¹ * y ∈ U :=
    hc.continuousAt.eventually_mem (hUo.mem_nhds (by simp [one_mem]))
  filter_upwards [hm] with y hy
  have := (hinv _ hy x).2
  rwa [mul_inv_cancel_left] at this

end GlobalTheory.CompanionTheory.FinTestTw

end
