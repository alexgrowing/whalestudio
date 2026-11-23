import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts

namespace GlobalTheory.CxConn

variable {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {d : ℕ}

theorem exists_algX_eq [IsProper p] [GeometricallyIntegral p] (a : Γ(Y, ⊤)) : ∃ c : F, algX p ⊤ c = a := by
  have : IsIso p.appTop := ProperFunctions.isIso_appTop_of_field p
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso p.appTop).2 a
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 b
  exact ⟨c, congrArg (fun g : Γ(Sp F, ⊤) ⟶ Γ(Y, ⊤) => g ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c))
    (p.appLE_eq_app (U := ⊤))⟩

theorem eq_of_holoOn_univ [SmoothOfRelativeDimension d p] [IsProper p] [GeometricallyIntegral p]
    (hp : IsProjOver p) (R : AnRead p σ d) {f : CxPts p σ → ℂ} (hf : R.HoloOn univ f) (y z : CxPts p σ) :
    f y = f z := by
  have hs : (fun _ => f) ∈ R.holSec (Out.Inh.trivLB Y) := by
    refine ⟨⟨fun i j w hi hj => ?_, fun i w h => (h mem_ptsIn_top).elim⟩, fun i => hf.mono (subset_univ _)⟩
    have e : gv p σ (Out.Inh.trivLB Y) i j w = 1 :=
      (ev_eq (mem_ptsIn_inf.2 ⟨hi, hj⟩) _).trans (map_one _)
    rw [e, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC hp R (Out.Inh.trivLB_isLB Y)).2 ⟨_, hs⟩
  let L : ((Out.Inh.trivLB Y).ι → CxPts p σ → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => s PUnit.unit y - s PUnit.unit z
      map_add' := fun s t => add_sub_add_comm _ _ _ _
      map_smul' := fun c s => (mul_sub c _ _).symm }
  have h := SecC.val_mem_of (M := LinearMap.ker L) (fun s => by
    obtain ⟨c, hc⟩ := exists_algX_eq (p := p) (s.f PUnit.unit)
    have e (w : CxPts p σ) : secVal p σ s PUnit.unit w = σ c :=
      (congrArg (fun a => ev p σ ⊤ a w) hc.symm).trans (ev_algX mem_ptsIn_top c)
    change secVal p σ s PUnit.unit y - secVal p σ s PUnit.unit z = 0
    rw [e, e, sub_self]) x
  have e : SecC.val x = fun _ => f := congrArg Subtype.val hx
  rw [e] at h
  exact sub_eq_zero.1 h

theorem exists_holoOn_univ_of_local {R : AnRead p σ d} {A : Set (CxPts p σ)} (hA : Dense A) {u : CxPts p σ → ℂ}
    (h : ∀ y, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn univ f ∧ EqOn f u A := by
  choose T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := T) hT (fun y _ => ⟨y, hy y⟩)
    fun y => ((hf y).mono inter_subset_right).congr fun z hz => ?_, fun y hS => he y ⟨hy y, hS⟩⟩
  have ho := (hT z).inter (hT y)
  have e : EqOn (f z) (f y) (T z ∩ T y ∩ A) := fun w hw =>
    (he z ⟨hw.1.1, hw.2⟩).trans (he y ⟨hw.1.2, hw.2⟩).symm
  exact e.of_subset_closure (((hf z).mono inter_subset_left).continuousOn ho)
    (((hf y).mono inter_subset_right).continuousOn ho) inter_subset_left (hA.open_subset_closure_inter ho)
    ⟨hy z, hz.2⟩

theorem exists_local_extension [GeometricallyIntegral p] [LocallyOfFiniteType p] (R : AnRead p σ d) {W : Y.Opens}
    (hW : (W : Set Y).Nonempty) {u : CxPts p σ → ℂ} (hu : R.HoloOn (ptsIn p σ W) u) {C : ℝ}
    (hC : ∀ y, ‖u y‖ ≤ C) (y : CxPts p σ) :
    ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ ptsIn p σ W) := by
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton p
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  obtain ⟨φ, hφ, hφW⟩ := CxPtsDense.exists_ne_zero_basicOpen_le c.affine
    ⟨_, mem_ptsIn.1 (c.source_subset hi)⟩ hW
  have hD : Dense (ptsIn p σ (Y.basicOpen φ)) := by
    refine (CxPtsDense.nonempty_and_dense_of_geometricallyIntegral p σ).2 _ (nonempty_iff_ne_empty.2 fun h => hφ ?_)
    exact (basicOpen_eq_bot_iff φ).1 (Opens.ext h)
  have hin {z} (hz : z ∈ c.e.source) : z ∈ ptsIn p σ (Y.basicOpen φ) ↔ ev p σ c.U φ z ≠ 0 :=
    mem_ptsIn_basicOpen (c.source_subset hz) φ
  obtain ⟨v, hv, he⟩ := GlobalTheory.LogExt.riemann_extension_log _ c.e.target (ev p σ c.U φ ∘ c.e.symm) (u ∘ c.e.symm)
    c.e.open_target ((c.holo c.U φ).mono fun b hb => ⟨hb, c.source_subset (c.e.map_target hb)⟩)
    ((hu i).mono fun b hb => ⟨hb.1, ptsIn_mono hφW ((hin (c.e.map_target hb.1)).2 hb.2)⟩)
    (fun b hb => by
      have hs := c.e.map_target hb
      have h₁ := hD.open_subset_closure_inter c.e.open_source hs
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨c.e.map_source hz.1, ?_⟩
      rw [Function.comp_apply, c.e.left_inv hz.1]
      exact (hin hz.1).1 hz.2)
    fun b _ => ⟨C, 0, Eventually.of_forall fun b' _ => by rw [pow_zero, mul_one]; exact hC _⟩
  have hf : R.HoloOn c.e.source (v ∘ c.e) := by
    have := AnRead.holoOn_of_chart (R := R) (S := univ) (f := v ∘ c.e) c
      ((hv.mono inter_subset_left).congr fun b hb => congrArg v (c.e.right_inv hb.1))
    rwa [inter_univ] at this
  refine ⟨c.e.source, v ∘ c.e, c.e.open_source, hi, hf, ?_⟩
  have ho := c.e.open_source.inter (isOpen_ptsIn (p := p) (σ := σ) W)
  have e : EqOn (v ∘ c.e) u (c.e.source ∩ ptsIn p σ W ∩ ptsIn p σ (Y.basicOpen φ)) := fun z hz => by
    have := he (x := c.e z) ⟨c.e.map_source hz.1.1, by
      rw [Function.comp_apply, c.e.left_inv hz.1.1]; exact (hin hz.1.1).1 hz.2⟩
    simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this
  exact e.of_subset_closure ((hf.mono inter_subset_left).continuousOn ho)
    ((hu.mono inter_subset_right).continuousOn ho) inter_subset_left (hD.open_subset_closure_inter ho)

theorem isPreconnected_ptsIn_of_isProjOver (d : ℕ) [SmoothOfRelativeDimension d p] [IsProper p]
    [GeometricallyIntegral p] (hp : IsProjOver p) (W : Y.Opens) : IsPreconnected (ptsIn p σ W) := by
  refine isPreconnected_of_forall_constant fun g hg y hy z hz => ?_
  have hW : (W : Set Y).Nonempty := ⟨_, mem_ptsIn.1 hy⟩
  let R := AnRead.all p σ d
  let κ : Bool → ℂ := fun b => if b then 1 else 0
  have hu : R.HoloOn (ptsIn p σ W) (κ ∘ g) := fun i b hb => by
    have h₁ : ContinuousAt (g ∘ (R.chart i).e.symm) b :=
      (hg.continuousAt ((isOpen_ptsIn W).mem_nhds hb.2)).comp ((R.chart i).e.continuousAt_symm hb.1)
    have h₂ : ∀ᶠ b' in 𝓝 b, (g ∘ (R.chart i).e.symm) b' = (g ∘ (R.chart i).e.symm) b :=
      h₁.eventually ((isOpen_discrete _).mem_nhds (mem_singleton _))
    refine ((differentiableAt_const (κ ((g ∘ (R.chart i).e.symm) b))).congr_of_eventuallyEq
      (h₂.mono fun b' hb' => congrArg κ hb')).differentiableWithinAt
  have hC (w) : ‖(κ ∘ g) w‖ ≤ 1 := by
    simp only [Function.comp_apply, κ]
    split_ifs <;> simp
  obtain ⟨f, hf, he⟩ := exists_holoOn_univ_of_local
    ((CxPtsDense.nonempty_and_dense_of_geometricallyIntegral p σ).2 W hW) (exists_local_extension R hW hu hC)
  have e : κ (g y) = κ (g z) := (he hy).symm.trans ((eq_of_holoOn_univ hp R hf y z).trans (he hz))
  revert e
  cases g y <;> cases g z <;> simp [κ]

theorem isPreconnected_ptsIn : ∀ (F : Type) [Field F] [NumberField F] (B : GlobalTheory.ProjVar.Var F) (e : F →+* ℂ)
    (W : B.X.Opens), IsPreconnected (GlobalTheory.CxPts.ptsIn B.str e W) :=
  fun _ _ _ B _ W => isPreconnected_ptsIn_of_isProjOver B.dim B.isProjOver W

end GlobalTheory.CxConn
