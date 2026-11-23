import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section S1

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M) (p : PlF D)

theorem local_form_add_right (x y y' : L.V p) : (L.H p).h x (y + y') = (L.H p).h x y + (L.H p).h x y' := by
  rw [(L.H p).h_herm (y + y') x, (L.H p).h_add_left, map_add, ← (L.H p).h_herm y x,
    ← (L.H p).h_herm y' x]

theorem local_form_smul_right (x y : L.V p) (a : (D.s.atP p).Ep) :
    (L.H p).h x (a • y) = (M p).L.cj a * (L.H p).h x y := by
  rw [(L.H p).h_herm (a • y) x, (L.H p).h_smul_left, map_mul, ← (L.H p).h_herm y x]

theorem local_form_zero_left (y : L.V p) : (L.H p).h 0 y = 0 := by
  have h := (L.H p).h_smul_left 0 0 y
  rwa [zero_smul, zero_mul] at h

theorem local_form_zero_right (x : L.V p) : (L.H p).h x 0 = 0 := by
  rw [(L.H p).h_herm 0 x, local_form_zero_left, map_zero]

theorem base_change_smul_integral {δ : ∀ p : PlF D, (D.s.atP p).Fp} (hA : Agree δ M p) (o : 𝓞 D.host.E) (x : (VS D).V) :
    ∃ c ∈ (M p).L.O, L.bc p (o • x) = c • L.bc p x := by
  refine ⟨(D.s.atP p).ιE (o : D.host.E), ?_, ?_⟩
  · rw [hA.2.2.2.1]
    exact PI.CntNotIntW.iE_mem_O D p o
  · rw [← L.bc_smul p (o : D.host.E) x]
    congr 1
    first
    | exact (algebraMap_smul D.host.E o x).symm
    | rfl

theorem local_form_integral_on_lattice (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hcjO : ∀ a ∈ (M p).L.O, (M p).L.cj a ∈ (M p).L.O)
    (hint : ∀ a ∈ Λ, ∀ b ∈ Λ, (L.H p).h (L.bc p a) (L.bc p b) ∈ (M p).L.O)
    {x y : L.V p} (hx : x ∈ lattice₂ L p Λ) (hy : y ∈ lattice₂ L p Λ) : (L.H p).h x y ∈ (M p).L.O := by
  unfold lattice₂ at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx0 =>
    obtain ⟨a, ha, rfl⟩ := hx0
    induction hy using Submodule.span_induction with
    | mem y hy0 =>
      obtain ⟨b, hb, rfl⟩ := hy0
      exact hint a ha b hb
    | zero => rw [local_form_zero_right]; exact (M p).L.O.zero_mem
    | add y y' _ _ h1 h2 => rw [local_form_add_right]; exact add_mem h1 h2
    | smul c y _ h1 =>
      rw [show c • y = (c : (D.s.atP p).Ep) • y from rfl, local_form_smul_right]
      exact mul_mem (hcjO _ c.2) h1
  | zero => rw [local_form_zero_left]; exact (M p).L.O.zero_mem
  | add x x' _ _ h1 h2 => rw [(L.H p).h_add_left]; exact add_mem h1 h2
  | smul c x _ h1 =>
    rw [show c • x = (c : (D.s.atP p).Ep) • x from rfl, (L.H p).h_smul_left]
    exact mul_mem c.2 h1

end S1

set_option maxHeartbeats 1000000 in
theorem local_self_dual_holds : LocSelfDual := by
  intro D δ M hA L p
  have hAp := hA p
  obtain ⟨-, -, hcj, hO, -⟩ := hAp
  have hLat := (VS D).standardTuple_isLattice
  have hU := (VS D).baseLattice_isUnimodular

  have hform : ∀ a b : (VS D).V, (L.H p).h (L.bc p a) (L.bc p b) = (D.s.atP p).ιE ((VS D).hT b a) := by
    intro a b; rw [L.bc_form p]; rfl
  have hcjO : ∀ a ∈ (M p).L.O, (M p).L.cj a ∈ (M p).L.O := by
    intro a ha; rw [hcj, hO] at *; exact LocFacts.lf_cj_mem p a ha

  have hint : ∀ a ∈ (VS D).L0, ∀ b ∈ (VS D).L0, (L.H p).h (L.bc p a) (L.bc p b) ∈ (M p).L.O := by
    intro a ha b hb
    rw [hform]
    have ha' : a ∈ Formalism.E.hdual (VS D).hT (VS D).L0 := by
      have : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := hU
      rw [← this] at ha; exact ha
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((LocFacts.lf_mem_hdual).1 ha' b hb)
    rw [← ho, hO]
    exact PI.CntNotIntW.iE_mem_O D p o
  refine ⟨?_, ?_, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  ·
    obtain ⟨s, hs⟩ := hLat.fg
    have : lattice₂ L p (VS D).L0 = Submodule.span (M p).L.O (L.bc p '' (s : Set (VS D).V)) := by
      apply le_antisymm
      · rw [lattice₂, Submodule.span_le, ← hs]
        rintro _ ⟨x, hx, rfl⟩
        induction hx using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
        | smul o y _ hy =>
          obtain ⟨c, hc, he⟩ := base_change_smul_integral L p (hA p) o y
          rw [he]
          exact Submodule.smul_mem _ (⟨c, hc⟩ : (M p).L.O) hy
      · rw [← hs]; exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
    rw [this]
    exact Submodule.fg_span (s.finite_toSet.image _)
  ·
    rw [eq_top_iff, ← L.bc_span p, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by rw [hLat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Submodule.subset_span ⟨y, hy, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy => rw [L.bc_smul p]; exact Submodule.smul_mem _ _ hy
  ·
    exact local_form_integral_on_lattice L p _ hcjO hint hx hy
  ·
    obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := D.host.E) (VS D).L0 hLat.fg
      (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    choose μ hμL0 hμ using fun i => LocFacts.lf_riesz_lat hLat hU (f i)
    have hV : ∀ v : (VS D).V, v = ∑ i, (VS D).hT (μ i) v • ((g i : (VS D).L0) : (VS D).V) := by
      let L2 : (VS D).V →ₗ[D.host.E] (VS D).V := ∑ i, ((VS D).hT (μ i)).smulRight ((g i : (VS D).L0) : (VS D).V)
      have hL2 : ∀ v, L2 v = ∑ i, (VS D).hT (μ i) v • ((g i : (VS D).L0) : (VS D).V) := by
        intro v; simp [L2]
      have heq : LinearMap.id = L2 := by
        apply LinearMap.ext_on hLat.span_eq_top
        intro y hy
        have e1 := congrArg (fun z : (VS D).L0 => (z : (VS D).V)) (hgf ⟨y, hy⟩)
        rw [LinearMap.id_apply, hL2]
        refine e1.trans ?_
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, ← algebraMap_smul D.host.E, hμ i ⟨y, hy⟩]
      intro v
      rw [← hL2, ← heq, LinearMap.id_apply]
    have hVp : ∀ w : L.V p, w = ∑ i, (L.H p).h w (L.bc p (μ i)) • L.bc p ((g i : (VS D).L0) : (VS D).V) := by
      intro w
      have hw : w ∈ Submodule.span (D.s.atP p).Ep (Set.range (L.bc p)) := by rw [L.bc_span p]; trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨v, rfl⟩ := hw
        have e : ∀ i, (L.H p).h (L.bc p v) (L.bc p (μ i)) = (D.s.atP p).ιE ((VS D).hT (μ i) v) := fun i => hform _ _
        simp only [e, ← L.bc_smul p]
        rw [← map_sum, ← hV v]
      | zero => simp [local_form_zero_left]
      | add w w' _ _ h1 h2 =>
        simp only [(L.H p).h_add_left, add_smul, Finset.sum_add_distrib]
        rw [← h1, ← h2]
      | smul a w _ h1 =>
        simp only [(L.H p).h_smul_left, mul_smul]
        rw [← Finset.smul_sum, ← h1]
    have hmem : (∑ i, (L.H p).h x (L.bc p (μ i)) • L.bc p ((g i : (VS D).L0) : (VS D).V)) ∈ lattice₂ L p (VS D).L0 := by
      refine Submodule.sum_mem _ fun i _ => ?_
      have hc : (L.H p).h x (L.bc p (μ i)) ∈ (M p).L.O := h _ (Submodule.subset_span ⟨μ i, hμL0 i, rfl⟩)
      have hg : L.bc p ((g i : (VS D).L0) : (VS D).V) ∈ lattice₂ L p (VS D).L0 := Submodule.subset_span ⟨_, (g i).2, rfl⟩
      exact Submodule.smul_mem _ (⟨_, hc⟩ : (M p).L.O) hg
    have hxe := hVp x
    rw [← hxe] at hmem
    exact hmem

end Formalism.L2.SG.Pf.Cnt
