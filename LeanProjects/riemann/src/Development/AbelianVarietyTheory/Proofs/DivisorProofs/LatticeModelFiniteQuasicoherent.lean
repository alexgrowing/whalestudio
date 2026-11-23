import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.LatFinite

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M : X → AddSubgroup V} {F : X.Modules}

theorem val_linearCombination (L : LatModel M F) {U W : X.Opens} (h : W ≤ U)
    (hW : genericPoint X ∈ W) {m : ℕ} (e : Fin m → Γ(F, U)) (a : Fin m → Γ(X, W)) :
    L.val W hW (Fintype.linearCombination Γ(X, W) (fun i => Twist.resM F h (e i)) a) =
      ∑ i, fnOf W hW (a i) • L.val U (h hW) (e i) := by
  simp only [Fintype.linearCombination_apply, map_sum, L.smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← L.res U W h hW (e i)]

theorem val_mem (L : LatModel M F) {W : X.Opens} (hW : genericPoint X ∈ W) (s : Γ(F, W))
    {z : X} (hz : z ∈ W) : L.val W hW s ∈ M z := by
  have h : L.val W hW s ∈ latSec M W := L.range W hW ▸ ⟨s, rfl⟩
  simp only [latSec, AddSubgroup.mem_iInf] at h
  exact h z hz

theorem isFrame (L : LatModel M F) {U : X.Opens} (hU : genericPoint X ∈ U) {m : ℕ}
    {v : Fin m → V} (hv : LinearIndependent X.functionField v)
    (hM : ∀ z ∈ U, ∀ w, w ∈ M z ↔
      ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i)
    (e : Fin m → Γ(F, U)) (he : ∀ i, L.val U hU (e i) = v i) : VB.IsFrame e := by
  refine VB.isFrame_of_forall_exists fun W h x hx => ⟨W, le_rfl, hx, ?_⟩
  have hW : genericPoint X ∈ W := gen_mem hx
  have key : ∀ a : Fin m → Γ(X, W), L.val W hW (Fintype.linearCombination Γ(X, W)
      (fun i => Twist.resM F (le_rfl.trans h) (e i)) a) = ∑ i, fnOf W hW (a i) • v i := fun a => by
    rw [val_linearCombination L]
    simp only [he]
  constructor
  · intro a b hab
    have := congrArg (L.val W hW) hab
    rw [key, key] at this
    funext i
    exact fnOf_injective W hW (Fintype.linearIndependent_iffₛ.1 hv _ _ this i)
  · intro s
    obtain ⟨c, -, hc⟩ := (hM _ (h hW) _).1 (val_mem L hW s hW)
    have hreg : ∀ i, ∀ z ∈ W, RegAt z (c i) := by
      intro i z hz
      obtain ⟨c', hc', e'⟩ := (hM z (h hz) _).1 (val_mem L hW s hz)
      rw [Fintype.linearIndependent_iffₛ.1 hv _ _ (hc.symm.trans e') i]
      exact hc' i
    choose a ha using fun i => exists_fnOf_eq hW (hreg i)
    refine ⟨a, L.inj W hW ?_⟩
    rw [key, hc]
    simp only [ha]

theorem isFiniteQC_of_latModel : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules), LatModel M F →
    (∀ y : X, ∃ (U : X.Opens) (m : ℕ) (v : Fin m → V), y ∈ U ∧ IsAffineOpen U ∧
      LinearIndependent X.functionField v ∧ ∀ z ∈ U, ∀ w, w ∈ M z ↔
        ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i) →
    GlobalTheory.QCoh.IsFiniteQC F := by
  intro X _ V _ _ M F L H
  choose U m v hy _ hv hM using H
  have frame : ∀ y, ∃ e : Fin (m y) → Γ(F, U y), VB.IsFrame e := by
    intro y
    have hU : genericPoint X ∈ U y := gen_mem (hy y)
    have hmem : ∀ i, v y i ∈ latSec M (U y) := by
      intro i
      simp only [latSec, AddSubgroup.mem_iInf]
      intro z hz
      classical
      refine (hM y z hz _).2 ⟨Pi.single i 1, fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simpa using (unitAt_one z).regAt
        · simpa [Pi.single_apply, hj] using regAt_zero z
      · simp [Pi.single_apply]
    choose e he using fun i => (L.range (U y) hU).ge (hmem i)
    exact ⟨e, isFrame L hU (hv y) (hM y) e he⟩
  choose e he using frame
  refine QCoh.IsFiniteQC.of_restrict (fun y => (U y).ι) (fun x => ⟨x, by simpa using hy x⟩)
    fun y => ?_
  have hf := (VB.isFrame_restrict_iff (U y).ι _).2 ((he y).res ((U y).ι_image_le ⊤))
  exact hf.isVB.isFiniteQC

end GlobalTheory.LogDR.LatFinite
