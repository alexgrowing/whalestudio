import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L1NormSectionBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

abbrev UN (N : ℕ) : Type := Matrix.unitaryGroup (Fin N) ℂ

instance msUN (N : ℕ) : MeasurableSpace (UN N) := borel _
instance bsUN (N : ℕ) : BorelSpace (UN N) := ⟨rfl⟩
instance csUN (N : ℕ) : CompactSpace (UN N) := GlobalTheory.compactSpace_unitaryGroup (Fin N) ℂ

def nuN (N : ℕ) : Measure (UN N) := Measure.haar

instance (N : ℕ) : (nuN N).IsHaarMeasure := by unfold nuN; infer_instance

instance (N : ℕ) : IsFiniteMeasure (nuN N) := CompactSpace.isFiniteMeasure

open Classical in

def jvMat (v : InfinitePlace E) (u : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) (Cinf E) :=
  Matrix.of fun i j w => if w = v then u i j else (1 : Matrix (Fin N) (Fin N) ℂ) i j

theorem jvMat_mem (v : InfinitePlace E) (u : UN N) : jvMat v u.1 ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hu := Matrix.mem_unitaryGroup_iff.mp u.2
  ext i j w
  have hij := congrFun (congrFun hu i) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hij
  simp only [Matrix.mul_apply, Matrix.star_apply, jvMat, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Matrix.one_apply]
  by_cases hw : w = v
  · simp only [hw, if_true]
    rw [hij]
    split_ifs <;> rfl
  · simp only [hw, if_false]
    by_cases h : i = j
    · subst h; simp
    · simp [h]

def jv (v : InfinitePlace E) (u : UN N) : Kinf E N := ⟨jvMat v u.1, jvMat_mem v u⟩

def Yv (v : InfinitePlace E) (t : G N) : GL (Fin N) (Cinf E) :=
  Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm (Pi.mulSingle v t))

theorem Yv_apply (v : InfinitePlace E) (t : G N) (i j : Fin N) (w : InfinitePlace E) :
    (Yv v t).val i j w = if w = v then t.val i j else (1 : Matrix (Fin N) (Fin N) ℂ) i j := by
  have e : (Yv v t).val i j w = ((Pi.mulSingle v t : InfinitePlace E → G N) w).val i j := rfl
  rw [e]
  by_cases hw : w = v
  · subst hw; simp
  · simp [Pi.mulSingle_eq_of_ne hw, hw]

theorem infinitePart_mulSingle (v : InfinitePlace E) (t : G N) : infP N (Pi.mulSingle v t) = infGL E N (Yv v t) := rfl

theorem toUnits_jv (v : InfinitePlace E) (u : UN N) : Unitary.toUnits (jv v u) = Yv v (Unitary.toUnits u) := by
  ext i j w
  rw [Yv_apply]
  rfl

theorem infGL_jv (v : InfinitePlace E) (u : UN N) :
    infGL E N (Unitary.toUnits (jv v u)) = infP N (Pi.mulSingle v (Unitary.toUnits u)) := by
  rw [toUnits_jv, infinitePart_mulSingle]

theorem atW_eq (v : InfinitePlace E) (t : G N) : Bridge.atW v t.val = toL (Yv v t).val := by
  funext i j w
  show Bridge.atW v t.val i j w = (Yv v t).val i j w
  rw [Yv_apply]
  unfold Bridge.atW
  split_ifs <;> rfl

def Wv (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : Submodule ℂ (UN N → ℂ) :=
  W.map (LinearMap.funLeft ℂ ℂ (jv v))

def S0 (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : Submodule ℂ (UN N → ℂ) where
  carrier := {w | Continuous w ∧ ∀ u', (fun u => w (u' * u)) ∈ Wv W v}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun u' => (Wv W v).add_mem (ha.2 u') (hb.2 u')⟩
  zero_mem' := ⟨continuous_const, fun _ => (Wv W v).zero_mem⟩
  smul_mem' := fun c w hw => ⟨hw.1.const_smul c, fun u' => (Wv W v).smul_mem c (hw.2 u')⟩

def V0 (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : Type := S0 W v

instance (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : AddCommGroup (V0 W v) :=
  inferInstanceAs (AddCommGroup (S0 W v))
instance (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : Module ℂ (V0 W v) :=
  inferInstanceAs (Module ℂ (S0 W v))

def toFun (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : V0 W v →ₗ[ℂ] (UN N → ℂ) := (S0 W v).subtype

theorem serre_vanishing_zero_trans {W : Submodule ℂ (Kinf E N → ℂ)} {v : InfinitePlace E} {w w' : V0 W v}
    (h : ∀ u, toFun W v w u = toFun W v w' u) : w = w' :=
  Subtype.ext (funext h)

theorem toFun_mem (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (w : V0 W v) :
    toFun W v w ∈ S0 W v := (w : S0 W v).2

theorem continuous_toFun' (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (w : V0 W v) :
    Continuous (toFun W v w) := (toFun_mem W v w).1

theorem integrable_toFun (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (b w : V0 W v) :
    Integrable (fun u => conj (toFun W v b u) * toFun W v w u) (nuN N) :=
  (((continuous_toFun' W v b).star).mul (continuous_toFun' W v w)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

abbrev core (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : InnerProductSpace.Core ℂ (V0 W v) where
  inner b w := ∫ u, conj (toFun W v b u) * toFun W v w u ∂nuN N
  conj_inner_symm b w := by
    rw [← integral_conj]
    congr 1; funext u
    simp [mul_comm]
  re_inner_nonneg w := by
    have e : (fun u => conj (toFun W v w u) * toFun W v w u) = fun u => ((‖toFun W v w u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [Complex.conj_mul']; norm_cast
    show 0 ≤ RCLike.re (∫ u, conj (toFun W v w u) * toFun W v w u ∂nuN N)
    rw [e, integral_complex_ofReal]
    exact integral_nonneg fun u => by positivity
  add_left a b w := by
    show ∫ u, conj (toFun W v (a + b) u) * toFun W v w u ∂nuN N = _
    simp only [map_add, Pi.add_apply, add_mul]
    exact integral_add (integrable_toFun W v a w) (integrable_toFun W v b w)
  smul_left a w c := by
    show ∫ u, conj (toFun W v (c • a) u) * toFun W v w u ∂nuN N = _
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    exact integral_const_mul _ _
  definite w h := by
    have e : (fun u => conj (toFun W v w u) * toFun W v w u) = fun u => ((‖toFun W v w u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [Complex.conj_mul']; norm_cast
    change ∫ u, conj (toFun W v w u) * toFun W v w u ∂nuN N = 0 at h
    rw [e, integral_complex_ofReal] at h
    have h0 : ∫ u, ‖toFun W v w u‖ ^ 2 ∂nuN N = 0 := by exact_mod_cast h
    have hc : Continuous fun u => ‖toFun W v w u‖ ^ 2 := ((continuous_toFun' W v w).norm).pow 2
    have hae := (integral_eq_zero_iff_of_nonneg (fun u => by positivity)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 h0
    have hz : (fun u => ‖toFun W v w u‖ ^ 2) = 0 := (Continuous.ae_eq_iff_eq (nuN N) hc continuous_const).1 hae
    exact serre_vanishing_zero_trans fun u => by
      have := congrFun hz u
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
      simpa using this

instance nacg (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : NormedAddCommGroup (V0 W v) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core W v)
instance ips (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : InnerProductSpace ℂ (V0 W v) where
  toNormedSpace := { toModule := (inferInstance : Module ℂ (V0 W v))
                     norm_smul_le := (InnerProductSpace.ofCore (core W v).toCore).norm_smul_le }
  inner := (core W v).inner
  norm_sq_eq_re_inner := (InnerProductSpace.ofCore (core W v).toCore).norm_sq_eq_re_inner
  conj_inner_symm := (core W v).conj_inner_symm
  add_left := (core W v).add_left
  smul_left := (core W v).smul_left

theorem rootsOfUnityRing_le_wittIntegers (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : S0 W v ≤ Wv W v := fun w hw => by
  simpa using hw.2 1

theorem fd (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    FiniteDimensional ℂ (V0 W v) := by
  have : FiniteDimensional ℂ (Wv W v) := by unfold Wv; infer_instance
  exact Submodule.finiteDimensional_of_le (rootsOfUnityRing_le_wittIntegers W v)

theorem inner_eq (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (b w : V0 W v) :
    ⟪b, w⟫_ℂ = ∫ u, conj (toFun W v b u) * toFun W v w u ∂nuN N := rfl

theorem exists_finset_eval (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    ∃ s : Finset (UN N), ∀ w : V0 W v, (∀ x ∈ s, toFun W v w x = 0) → w = 0 := by
  have := fd W hW v
  suffices H : ∀ n : ℕ, ∀ M : Submodule ℂ (V0 W v), Module.finrank ℂ M ≤ n →
      ∃ s : Finset (UN N), ∀ w ∈ M, (∀ x ∈ s, toFun W v w x = 0) → w = 0 by
    obtain ⟨s, hs⟩ := H _ ⊤ le_rfl
    exact ⟨s, fun w hw => hs w Submodule.mem_top hw⟩
  intro n
  induction n with
  | zero =>
    intro M hM
    have hb : M = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hM)
    exact ⟨∅, fun w hw _ => by rw [hb] at hw; exact (Submodule.mem_bot ℂ).mp hw⟩
  | succ n ih =>
    intro M hM
    by_cases hb : M = ⊥
    · exact ⟨∅, fun w hw _ => by rw [hb] at hw; exact (Submodule.mem_bot ℂ).mp hw⟩
    obtain ⟨w0, hw0M, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have hx : ∃ x, toFun W v w0 x ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 (serre_vanishing_zero_trans fun u => by rw [h u]; rfl)
    obtain ⟨x0, hx0⟩ := hx
    set M' := M ⊓ LinearMap.ker ((LinearMap.proj x0).comp (toFun W v)) with hM'
    have hlt : M' < M := by
      refine lt_of_le_of_ne inf_le_left fun h => hx0 ?_
      have : w0 ∈ M' := h ▸ hw0M
      exact (Submodule.mem_inf.mp this).2
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨s', hs'⟩ := ih M' (by omega)
    refine ⟨insert x0 s', fun w hw hz => hs' w (Submodule.mem_inf.mpr ⟨hw, ?_⟩)
      fun x hx => hz x (Finset.mem_insert_of_mem hx)⟩
    exact hz x0 (Finset.mem_insert_self _ _)

theorem exists_linv (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    ∃ (s : Finset (UN N)) (L : (s → ℂ) →L[ℂ] V0 W v), ∀ w : V0 W v, L (fun x => toFun W v w x) = w := by
  have := fd W hW v
  obtain ⟨s, hs⟩ := exists_finset_eval W hW v
  let Ev : V0 W v →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun x : s => (LinearMap.proj (x : UN N)).comp (toFun W v)
  have hk : LinearMap.ker Ev = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun w hw => hs w fun x hx => congrFun hw ⟨x, hx⟩
  obtain ⟨g, hg⟩ := Ev.exists_leftInverse_of_injective hk
  exact ⟨s, LinearMap.toContinuousLinearMap g, fun w => LinearMap.congr_fun hg w⟩

theorem continuous_of_toFun (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E)
    {X : Type} [TopologicalSpace X] (F : X → V0 W v) (h : ∀ u, Continuous fun a => toFun W v (F a) u) :
    Continuous F := by
  obtain ⟨s, L, hL⟩ := exists_linv W hW v
  have e : F = fun a => L (fun x => toFun W v (F a) x) := funext fun a => (hL (F a)).symm
  rw [e]
  exact L.continuous.comp (continuous_pi fun x => h x)

def rhoL (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (u' : UN N) : V0 W v →ₗ[ℂ] V0 W v where
  toFun w := (⟨fun u => toFun W v w (u'⁻¹ * u), (continuous_toFun' W v w).comp (continuous_const.mul continuous_id),
    fun u'' => by simpa only [mul_assoc] using (toFun_mem W v w).2 (u'⁻¹ * u'')⟩ : S0 W v)
  map_add' a b := rfl
  map_smul' c a := rfl

def Mv (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) : KMod N :=
  haveI := fd W hW v
  { V := V0 W v
    ρ := { toFun := fun u' => LinearMap.toContinuousLinearMap (rhoL W v u')
           map_one' := ContinuousLinearMap.ext fun w => serre_vanishing_zero_trans fun u => by
             show toFun W v w (1⁻¹ * u) = toFun W v w u
             rw [inv_one, one_mul]
           map_mul' := fun a b => ContinuousLinearMap.ext fun w => serre_vanishing_zero_trans fun u => by
             show toFun W v w ((a * b)⁻¹ * u) = toFun W v w (b⁻¹ * (a⁻¹ * u))
             rw [mul_inv_rev, mul_assoc] }
    iso := fun k w => by
      show ‖rhoL W v k w‖ = ‖w‖
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq, inner_eq]
      congr 2
      exact integral_mul_left_eq_self (fun u => conj (toFun W v w u) * toFun W v w u) k⁻¹
    cont := continuous_clm_apply.2 fun w =>
      continuous_of_toFun W hW v _ fun u => (continuous_toFun' W v w).comp (continuous_inv.mul continuous_const) }

theorem toFun_rho (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (u' : UN N)
    (w : (Mv W hW v).V) (u : UN N) : toFun W v ((Mv W hW v).ρ u' w) u = toFun W v w (u'⁻¹ * u) := rfl

theorem continuous_toFun (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (w : V0 W v) :
    Continuous (toFun W v w) :=
  w.2.1

def evL (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (u : UN N) :
    (Mv W hW v).V →L[ℂ] ℂ :=
  haveI := fd W hW v
  LinearMap.toContinuousLinearMap ((LinearMap.proj u).comp (toFun W v))

theorem evL_apply (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (u : UN N)
    (w : (Mv W hW v).V) : evL W hW v u w = toFun W v w u := rfl

theorem continuous_toFun₂ (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    Continuous fun p : (Mv W hW v).V × UN N => toFun W v p.1 p.2 := by
  have := fd W hW v
  obtain ⟨s, L, hL⟩ := exists_linv W hW v
  have key : ∀ (w : V0 W v) (u : UN N), toFun W v w u =
      ∑ x : s, toFun W v w x • toFun W v (L fun j => if x = j then 1 else 0) u := by
    intro w u
    have := LinearMap.pi_apply_eq_sum_univ
      ((LinearMap.proj u).comp ((toFun W v).comp (L : (s → ℂ) →ₗ[ℂ] V0 W v))) (fun x => toFun W v w x)
    simpa [hL w] using this
  have e : (fun p : (Mv W hW v).V × UN N => toFun W v p.1 p.2) =
      fun p => ∑ x : s, toFun W v p.1 x • toFun W v (L fun j => if x = j then 1 else 0) p.2 :=
    funext fun p => key p.1 p.2
  rw [e]
  refine continuous_finsetSum _ fun x _ => ?_
  exact ((LinearMap.continuous_of_finiteDimensional ((LinearMap.proj (x : UN N)).comp (toFun W v))).comp
    continuous_fst).smul ((continuous_toFun' W v _).comp continuous_snd)

theorem along_val (v : InfinitePlace E) (g : GA E N) (φ : GA E N → ℂ) (t : G N) :
    Bridge.along v g φ t.val = φ (g * infP N (Pi.mulSingle v t)) := by
  rw [infinitePart_mulSingle, ← chart_val φ g (Yv v t)]
  show chart φ g (Bridge.atW v t.val) = _
  rw [atW_eq]

theorem along_one' (v : InfinitePlace E) (g : GA E N) (φ : GA E N → ℂ) : Bridge.along v g φ 1 = φ g := by
  have := along_val v g φ 1
  simp only [Units.val_one, Pi.mulSingle_one] at this
  rw [this]
  simp [infP]

theorem atW_mem_invSet (v : InfinitePlace E) {x : Mat N} (hx : x ∈ GLs N) : Bridge.atW v x ∈ invSet E N := by
  have := atW_eq v (Matrix.GeneralLinearGroup.mkOfDetNeZero x hx)
  have e : (Matrix.GeneralLinearGroup.mkOfDetNeZero x hx).val = x := rfl
  rw [e] at this
  rw [this]
  exact val_mem_invSet _

theorem contDiff_atW (v : InfinitePlace E) : ContDiff ℝ ∞ (Bridge.atW (E := E) (a := N) v) := by
  unfold Bridge.atW
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun w => ?_
  split_ifs
  · exact (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin N → ℂ) i)
  · exact contDiff_const

theorem contDiffOn_along (v : InfinitePlace E) {φ : GA E N → ℂ} (hs : φ ∈ Sm E N) (g : GA E N) :
    ContDiffOn ℝ ∞ (Bridge.along v g φ) (GLs N) :=
  ((show ∀ g, ContDiffOn ℝ ∞ (chart φ g) (invSet E N) from hs) g).comp (contDiff_atW v).contDiffOn
    fun _ hx => atW_mem_invSet v hx

theorem mem_ktype_space_along_chart (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) {φ : GA E N → ℂ}
    (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W) (g : GA E N)
    {y : Mat N} (hy : y ∈ GLs N) : (fun u : UN N => Bridge.along v g φ (y * u.1)) ∈ S0 W v := by
  refine ⟨(contDiffOn_along v hs g).continuousOn.comp_continuous
    ((GlobalTheory.CompanionTheory.RCalc.mulL y).continuous.comp continuous_subtype_val : Continuous fun u : UN N => y * u.1)
    fun u => GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hy (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs u), fun u' => ?_⟩
  set Y := Matrix.GeneralLinearGroup.mkOfDetNeZero y hy
  refine ⟨fun k => φ ((g * infP N (Pi.mulSingle v (Y * Unitary.toUnits u'))) * infGL E N (Unitary.toUnits k)),
    hφ _, ?_⟩
  funext u
  simp only [LinearMap.funLeft_apply]
  have e : y * (u' * u).1 = (Y * Unitary.toUnits u' * Unitary.toUnits u).val := by
    simp only [Units.val_mul, mul_assoc]
    rfl
  rw [e, along_val, infGL_jv]
  simp only [Pi.mulSingle_mul, infinitePart_mul, mul_assoc]

section GelClm

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']

theorem Rd_clm (L : V →L[ℂ] V') (X : Mat N) {f : Mat N → V} {y : Mat N} (hf : DifferentiableAt ℝ f y) :
    Rd X (fun z => L (f z)) y = L (Rd X f y) := by
  unfold Rd
  have h := ((L.restrictScalars ℝ).hasFDerivAt.comp y hf.hasFDerivAt).fderiv
  have e : (fun z => L (f z)) = (L.restrictScalars ℝ) ∘ f := rfl
  rw [e]
  exact (DFunLike.congr_fun h (y * X)).trans rfl

theorem Eu_clm (L : V →L[ℂ] V') (s : Bool) (a b : Fin N) {f : Mat N → V} {y : Mat N}
    (hf : DifferentiableAt ℝ f y) : Eu s a b (fun z => L (f z)) y = L (Eu s a b f y) := by
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_clm L _ hf, map_add, map_smul]

theorem Epow_clm (L : V →L[ℂ] V') (s : Bool) {f : Mat N → V} (hf : ContDiffOn ℝ ∞ f (GLs N)) (m : ℕ) :
    ∀ a b : Fin N, Set.EqOn (Epow s m a b (fun z => L (f z))) (fun z => L (Epow s m a b f z)) (GLs N) := by
  induction m with
  | zero =>
    intro a b y _
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b y hy
    simp only [Epow, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.RCalc.isOpen_GLs (ih c b) s a c hy]
    exact Eu_clm L s a c (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth
      (GlobalTheory.CompanionTheory.WaveAll.Epow_smooth GlobalTheory.CompanionTheory.RCalc.rcalc hf s m c b) hy)

theorem gel_clm (L : V →L[ℂ] V') (s : Bool) (m : ℕ) {f : Mat N → V} (hf : ContDiffOn ℝ ∞ f (GLs N)) {y : Mat N}
    (hy : y ∈ GLs N) : gel s m (fun z => L (f z)) y = L (gel s m f y) := by
  simp only [gel, Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_clm L s hf m a a hy

end GelClm

theorem exists_linv' (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    ∃ (s : Finset (UN N)) (L : (s → ℂ) →L[ℂ] (Mv W hW v).V), ∀ w : (Mv W hW v).V,
      L (fun x => toFun W v w x) = w := by
  obtain ⟨s, L, hL⟩ := exists_linv W hW v
  exact ⟨s, L, hL⟩

def ofKTypeVector (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (w : S0 W v) :
    (Mv W hW v).V := w

def sec (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (φ : GA E N → ℂ)
    (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W) (g : GA E N) :
    Mat N → (Mv W hW v).V :=
  fun y => if hy : y ∈ GLs N then ofKTypeVector W hW v ⟨fun u => Bridge.along v g φ (y * u.1), mem_ktype_space_along_chart W v hs hφ g hy⟩
    else 0

theorem toFun_sec (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E)
    (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W)
    (g : GA E N) {y : Mat N} (hy : y ∈ GLs N) (u : UN N) :
    toFun W v (sec W hW v φ hs hφ g y) u = Bridge.along v g φ (y * u.1) := by
  unfold sec
  rw [dif_pos hy]
  rfl

theorem sec_mem_CE (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E)
    (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W)
    (g : GA E N) : sec W hW v φ hs hφ g ∈ CE (Mv W hW v) := by
  obtain ⟨s, L, hL⟩ := exists_linv' W hW v
  refine ⟨?_, fun y hy k => ?_⟩
  · have e : ∀ y ∈ GLs N, sec W hW v φ hs hφ g y = L (fun x : s => Bridge.along v g φ (y * (x : UN N).1)) := by
      intro y hy
      conv_lhs => rw [← hL (sec W hW v φ hs hφ g y)]
      congr 1
      funext x
      exact toFun_sec W hW v φ hs hφ g hy x
    refine ContDiffOn.congr ?_ e
    refine (L.restrictScalars ℝ).contDiff.comp_contDiffOn (contDiffOn_pi.2 fun x => ?_)
    exact (contDiffOn_along v hs g).comp (GlobalTheory.CompanionTheory.RCalc.mulR (x : UN N).1).contDiff.contDiffOn
      fun z hz => GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hz (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs _)
  · have hyk : y * k.1 ∈ GLs N := GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hy (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs k)
    apply serre_vanishing_zero_trans
    intro u
    rw [toFun_rho, toFun_sec W hW v φ hs hφ g hyk, toFun_sec W hW v φ hs hφ g hy, inv_inv]
    congr 1
    show y * k.1 * u.1 = y * (k.1 * u.1)
    rw [mul_assoc]

theorem sec_isEig (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E)
    (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W)
    (g : GA E N) (χ : Inf N) (h : IsEig χ (Bridge.along v g φ)) : IsEig χ (sec W hW v φ hs hφ g) := by
  obtain ⟨s, L, hL⟩ := exists_linv' W hW v
  intro sb m y hy
  set G' : Mat N → (s → ℂ) := fun z x => Bridge.along v g φ (z * (x : UN N).1) with hG'd
  have hG' : ContDiffOn ℝ ∞ G' (GLs N) := contDiffOn_pi.2 fun x =>
    (contDiffOn_along v hs g).comp (GlobalTheory.CompanionTheory.RCalc.mulR (x : UN N).1).contDiff.contDiffOn
      fun z hz => GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hz (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs _)
  have e : Set.EqOn (sec W hW v φ hs hφ g) (fun z => L (G' z)) (GLs N) := by
    intro z hz
    conv_lhs => rw [← hL (sec W hW v φ hs hφ g z)]
    congr 1
    funext x
    exact toFun_sec W hW v φ hs hφ g hz x
  rw [GlobalTheory.CompanionTheory.WaveAll.gel_congr GlobalTheory.CompanionTheory.RCalc.isOpen_GLs e sb m hy, gel_clm L sb m hG' hy, e hy, ← L.map_smul]
  congr 1
  funext x
  have h1 := gel_clm (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : s => ℂ) x) sb m hG' hy
  simp only [ContinuousLinearMap.proj_apply] at h1
  rw [Pi.smul_apply, ← h1]
  show gel sb m (fun z => Bridge.along v g φ (z * (x : UN N).1)) y = _
  rw [GlobalTheory.CompanionTheory.RCalc.gel_right sb m (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs _) (contDiffOn_along v hs g) hy]
  exact h sb m _ (GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hy (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs _))

end PositivityTheory.Rg.BcB.CG.ReproL
