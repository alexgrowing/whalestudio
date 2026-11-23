import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKGLIffVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.EulerV

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finite_above (v : PlF E) : Finite (Above v) := by
  by_cases h : Nonempty (Above v)
  · obtain ⟨u⟩ := h
    refine Finite.of_injective (β := (GlobalTheory.EulerTw.orb E u.1 : Finset (Pl E)))
      (fun w => ⟨w.1, (GlobalTheory.EulerTwRestr.mem_orb_iff u.1 w.1).2 (w.2.trans u.2.symm)⟩) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  · haveI := not_nonempty_iff.1 h
    infer_instance

def pn (n : ℕ) (v : PlF E) : GL (Fin n) (Af E) →* GL (Fin n) (Av v) := GeneralLinearGroup.map (projv v)

def ev {v : PlF E} (w : Above v) : GL (Fin n) (Av v) →* GLw n w.1 :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun w : Above v => w.1.adicCompletion E) w)

def Kn (n : ℕ) (v : PlF E) : Subgroup (GL (Fin n) (Av v)) :=
  ⨅ w : Above v, (GlobalTheory.LFun.KGL w.1 n).comap (ev w)

theorem mem_Kn {v : PlF E} {y : GL (Fin n) (Av v)} : y ∈ Kn n v ↔ ∀ w : Above v, ev w y ∈ GlobalTheory.LFun.KGL w.1 n := by
  simp only [Kn, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem ev_pn {v : PlF E} (w : Above v) (g : GL (Fin n) (Af E)) :
    ev w (pn n v g) = GeneralLinearGroup.map (pLoc E w.1) g := rfl

theorem mem_Kv {a b : ℕ} {v : PlF E} {y : Yv a b v} : y ∈ Kv a b v ↔ y.1 ∈ Kn a v ∧ y.2 ∈ Kn b v := by
  simp only [Kv, Subgroup.mem_iInf, Subgroup.mem_comap, mem_Kn, Subgroup.mem_prod, forall_and]
  rfl

theorem mem_Kf_iff {g : GL (Fin n) (Af E)} : g ∈ Kf E n ↔ ∀ v : PlF E, pn n v g ∈ Kn n v := by
  have h : g ∈ Kf E n ↔ ∀ w : Pl E, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
    simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [h]
  refine ⟨fun H v => mem_Kn.2 fun w => H w.1, fun H w => ?_⟩
  exact mem_Kn.1 (H (w.under (𝓞 (maximalRealSubfield E)))) ⟨w, rfl⟩

theorem continuous_projv (v : PlF E) : Continuous (projv v) :=
  continuous_pi fun w => RestrictedProduct.continuous_eval w.1

theorem continuous_pn (v : PlF E) : Continuous (pn n v) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_projv v))

theorem continuous_ev {v : PlF E} (w : Above v) : Continuous (ev (n := n) w) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_apply w))

theorem isOpen_Kn (v : PlF E) : IsOpen (Kn n v : Set (GL (Fin n) (Av v))) := by
  haveI := finite_above v
  rw [Kn, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun w =>
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w.1 n).1.preimage (continuous_ev w)

theorem pn_ext {g h : GL (Fin n) (Af E)} (H : ∀ v : PlF E, pn n v g = pn n v h) : g = h :=
  GlobalTheory.EulerTwRestr.gl_ext fun w => by
    exact congrArg (ev ⟨w, rfl⟩) (H (w.under (𝓞 (maximalRealSubfield E))))

theorem eventually_mem_Kn (g : GL (Fin n) (Af E)) : ∀ᶠ v : PlF E in cofinite, pn n v g ∈ Kn n v := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  have hx : ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
    filter_upwards [h1, h2] with w h1 h2
    exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
      fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩
  refine eventually_cofinite.2 (((eventually_cofinite.1 hx).image
    fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, mem_Kn, not_forall, ev_pn] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, w.2⟩

theorem exists_lift (y : ∀ v : PlF E, GL (Fin n) (Av v)) (hy : ∀ᶠ v : PlF E in cofinite, y v ∈ Kn n v) :
    ∃ x : GL (Fin n) (Af E), ∀ v, pn n v x = y v := by
  let un : Pl E → PlF E := fun w => w.under (𝓞 (maximalRealSubfield E))
  let Y : ∀ w : Pl E, GLw n w := fun w => ev (⟨w, rfl⟩ : Above (un w)) (y (un w))
  have hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w n := by
    have hB := eventually_cofinite.1 hy
    refine eventually_cofinite.2 ((hB.biUnion fun v _ => Set.finite_coe_iff.1 (finite_above v)).subset ?_)
    intro w hw
    refine Set.mem_iUnion₂.2 ⟨un w, fun h => hw (mem_Kn.1 h ⟨w, rfl⟩), rfl⟩
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
  refine ⟨⟨M, M', hMM', hM'M⟩, fun v => Units.ext (Matrix.ext fun i j => funext ?_)⟩
  rintro ⟨w, rfl⟩
  rfl

theorem exists_Kf_lift {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    ∃ x ∈ Kf E n, pn n v x = k := by
  have hm : ∀ u : PlF E, (Function.update (fun u : PlF E => (1 : GL (Fin n) (Av u))) v k) u ∈ Kn n u := by
    intro u
    by_cases h : u = v
    · subst h
      simpa using hk
    · simp [Function.update_of_ne h, one_mem]
  obtain ⟨x, hx⟩ := exists_lift _ (Eventually.of_forall hm)
  exact ⟨x, mem_Kf_iff.2 fun u => by rw [hx]; exact hm u, by rw [hx]; simp⟩

theorem isCompact_Kn (v : PlF E) : IsCompact (Kn n v : Set (GL (Fin n) (Av v))) := by
  have e : (Kn n v : Set (GL (Fin n) (Av v))) = pn n v '' (Kf E n : Set (GL (Fin n) (Af E))) := by
    ext k
    refine ⟨fun hk => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
      exact ⟨x, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact mem_Kf_iff.1 hg v
  rw [e]
  exact (GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).image (continuous_pn v)

theorem coe_Kv (a b : ℕ) (v : PlF E) : (Kv a b v : Set (Yv a b v)) =
    (Kn a v : Set (GL (Fin a) (Av v))) ×ˢ (Kn b v : Set (GL (Fin b) (Av v))) :=
  Set.ext fun _ => mem_Kv

theorem mem_prod_iff (a b : ℕ) (x : Gf E a b) :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ v, pv a b v x ∈ Kv a b v := by
  rw [Subgroup.mem_prod, mem_Kf_iff, mem_Kf_iff]
  simp only [mem_Kv, forall_and]
  rfl

theorem isOpen_Kf : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isOpen_Kglob

theorem isCompact_Kf : IsCompact (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isCompact_Kglob

theorem coe_level (a b : ℕ) : {x : Gf E a b | ∀ v, pv a b v x ∈ Kv a b v} =
    (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
  Set.ext fun x => (mem_prod_iff a b x).symm

theorem isRestrGroup (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (pv (E := E) a b) (Kv a b) := by
  refine ⟨fun w => w.elim, fun v => ?_, fun v => ?_, fun v => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · exact ((continuous_pn v).comp continuous_fst).prodMk ((continuous_pn v).comp continuous_snd)
  · rw [coe_Kv]
    exact (isOpen_Kn v).prod (isOpen_Kn v)
  · rw [coe_Kv]
    exact (isCompact_Kn v).prod (isCompact_Kn v)
  · exact Prod.ext (pn_ext fun v => congrArg Prod.fst (H v)) (pn_ext fun v => congrArg Prod.snd (H v))
  · filter_upwards [eventually_mem_Kn x.1, eventually_mem_Kn x.2] with v h1 h2
    exact mem_Kv.2 ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun v => (y v).1) (hy.mono fun v h => (mem_Kv.1 h).1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun v => (y v).2) (hy.mono fun v h => (mem_Kv.1 h).2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun v => Prod.ext (h₁ v) (h₂ v)⟩
  · rw [coe_level]
    exact isOpen_Kf.prod isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ v, pv a b v x ∈ Kv a b v} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← coe_level]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact isCompact_Kf.prod isCompact_Kf

theorem cjv_spec (hC : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hC E v
  rw [cjv, dif_pos h]
  exact h.choose_spec.2 x

theorem pn_thF (hC : CjEx) (n : ℕ) (v : PlF E) (x : GL (Fin n) (Af E)) :
    pn n v (thF E n x) = thetaGL n (cjv v) (pn n v x) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_spec hC v) x

theorem pv_thP (hC : CjEx) (a b : ℕ) (v : PlF E) (x : Gf E a b) :
    pv a b v (thP E a b x) = thv a b v (pv a b v x) :=
  Prod.ext (pn_thF hC a v x.1) (pn_thF hC b v x.2)

theorem theta_mem_Kn (hC : CjEx) {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    thetaGL n (cjv v) k ∈ Kn n v := by
  obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
  rw [← pn_thF hC]
  exact mem_Kf_iff.1 (GlobalTheory.EulerTwKU.thF_mem_Kglob x hx) v

theorem main : RestrV := fun hC E _ _ _ a b =>
  ⟨isRestrGroup a b, fun v x => pv_thP hC a b v x,
    fun v k hk => mem_Kv.2 ⟨theta_mem_Kn hC (mem_Kv.1 hk).1, theta_mem_Kn hC (mem_Kv.1 hk).2⟩,
    mem_prod_iff a b⟩

end GlobalTheory.CompanionTheory.EulerV

end
