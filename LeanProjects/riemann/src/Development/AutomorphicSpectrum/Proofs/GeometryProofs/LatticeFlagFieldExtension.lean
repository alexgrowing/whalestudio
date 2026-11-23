import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbPull

theorem dual_frame_ext {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {W W' : Type} [AddCommGroup W] [Module Ω W]
    [AddCommGroup W'] [Module Ω' W'] (j : W →+ W') (hj : ∀ (a : Ω) (e : W), j (a • e) = i a • j e)
    (hs : Submodule.span Ω' (Set.range j) = ⊤) (jW : Module.Dual Ω W →+ Module.Dual Ω' W')
    (hjW : ∀ u e, jW u (j e) = i (u e)) {r : ℕ} (b : Fin r → Module.Dual Ω W) (hli : LinearIndependent Ω b)
    (hb : Submodule.span Ω (Set.range b) = ⊤) :
    LinearIndependent Ω' (fun k => jW (b k)) ∧ Submodule.span Ω' (Set.range fun k => jW (b k)) = ⊤ := by
  classical
  let c := Module.Basis.mk hli hb.ge
  have hc : ∀ k, c k = b k := fun k => by simp [c]
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis c
  haveI : Module.Finite Ω W := (Module.finite_dual_iff Ω).1 inferInstance
  let e : Fin r → W := fun l => (Module.evalEquiv Ω W).symm (c.dualBasis l)
  have he : ∀ k l, b k (e l) = if k = l then 1 else 0 := by
    intro k l
    simp only [e]
    rw [Module.apply_evalEquiv_symm_apply, ← hc k, Module.Basis.dualBasis_apply_self]
  have hx : ∀ x : W, x = ∑ k, b k x • e k := by
    intro x
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff Ω _).1
    intro u
    have hu : u ∈ Submodule.span Ω (Set.range b) := by rw [hb]; trivial
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      simp [he, map_sum]
    | zero => simp
    | add y z _ _ hy hz => simp only [LinearMap.add_apply, hy, hz, add_zero]
    | smul a y _ hy => simp only [LinearMap.smul_apply, hy, smul_zero]
  have hjx : ∀ x, j x = ∑ k, i (b k x) • j (e k) := by
    intro x
    conv_lhs => rw [hx x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hj _ _
  have hext : ∀ v v' : Module.Dual Ω' W', (∀ k, v (j (e k)) = v' (j (e k))) → v = v' := by
    intro v v' h
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨x, rfl⟩
    rw [hjx x]
    simp only [map_sum, map_smul, h]
  have hpair : ∀ k l, jW (b k) (j (e l)) = if k = l then 1 else 0 := by
    intro k l
    rw [hjW, he]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg l
    have := congrArg (fun v : Module.Dual Ω' W' => v (j (e l))) hg
    simpa [hpair] using this
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k, v (j (e k)) • jW (b k) := by
      apply hext
      intro l
      simp [hpair]
    rw [hv]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem isVBOn_dual_pull : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (Lo : Lat ξ (Module.Dual Ω V)) (Lo' : Lat ξ' (Module.Dual Ω' V')) (T : Set (Cpt ξ)) (T' : Set (Cpt ξ')) (r : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (Lo.map W.dualRestrict).IsVBOn T r ⊤ → (∀ p' ∈ T', ∃ hq : genPt ξ ⤳ f p'.1, (⟨f p'.1, hq⟩ : Cpt ξ) ∈ T ∧ (0 < r → Lo' p' = Submodule.span (regAt ξ' p') (jd '' (Lo ⟨f p'.1, hq⟩ : Set (Module.Dual Ω V))))) → (Lo'.map W'.dualRestrict).IsVBOn T' r ⊤ := by
  intro X X' Ω Ω' _ _ ξ ξ' f i V V' _ _ _ _ j jd W W' Lo Lo' T T' r hd _ hj hjd hW hvb hT
  have hmem : ∀ e : W, j e ∈ W' := fun e => by
    rw [hW]
    exact Submodule.subset_span ⟨e, e.2, rfl⟩
  let jr : W →+ W' :=
    { toFun := fun e => ⟨j e, hmem e⟩
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j _ _) }
  have hsm : ∀ (a : Ω) (e : W), jr (a • e) = i a • jr e := fun a e => Subtype.ext (hj.1 a e)
  have hext : IsExtOver i jr := ⟨hsm, fun n b hb => by
    have h1 := hj.2 n (fun k => (b k : V)) (hb.map' W.subtype W.ker_subtype)
    exact LinearIndependent.of_comp W'.subtype h1⟩
  have hs : Submodule.span Ω' (Set.range jr) = ⊤ := by
    have h1 : (Submodule.span Ω' (Set.range jr)).map W'.subtype = W' := by
      rw [Submodule.map_span]
      conv_rhs => rw [hW]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
        exact ⟨e, e.2, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
    have h2 := Submodule.comap_map_eq_of_injective W'.injective_subtype (Submodule.span Ω' (Set.range jr))
    rw [h1, Submodule.comap_subtype_self] at h2
    exact h2.symm
  obtain ⟨jW, hjW⟩ := DualExt.dual_ext Ω Ω' i W W' jr hext hs
  have hcomp : ∀ w, W'.dualRestrict (jd w) = jW (W.dualRestrict w) := by
    intro w
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    rw [hjW]
    exact hjd w e
  have hsemi : ∀ (a : Ω) (u : Module.Dual Ω W), jW (a • u) = i a • jW u := by
    intro a u
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    simp [hjW]
  intro p' hp'
  obtain ⟨hq, hpT, -⟩ := hT p' hp'
  obtain ⟨U, hU, b, hb, hfr⟩ := hvb _ hpT
  obtain ⟨hli', hspan'⟩ := dual_frame_ext i jr hsm hs jW hjW b (hfr _ hpT hU).1 hb
  refine ⟨f ⁻¹ᵁ U, hU, fun k => jW (b k), hspan', fun q' hq' hq'U => ⟨hli', ?_⟩⟩
  obtain ⟨hq2, hqT, hL⟩ := hT q' hq'
  have hfrq := (hfr _ hqT hq'U).2
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : Subsingleton (Module.Dual Ω' W') := by
      rw [← Submodule.subsingleton_iff Ω', ← subsingleton_iff_bot_eq_top]
      rw [← hspan']
      simp
    exact Subsingleton.elim _ _
  · obtain ⟨hq3, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
    apply le_antisymm
    · show Submodule.map _ _ ≤ _
      rw [hL hr, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      show W'.dualRestrict (jd w) ∈ _
      rw [hcomp]
      have hin : W.dualRestrict w ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b) := by
        rw [← hfrq]
        exact ⟨w, hw, rfl⟩
      have key : ∀ y ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b),
          jW y ∈ Submodule.span (regAt ξ' q') (Set.range fun k => jW (b k)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact Submodule.subset_span ⟨k, rfl⟩
        | zero => simp
        | add y z _ _ hy hz =>
          rw [map_add]
          exact Submodule.add_mem _ hy hz
        | smul a y _ hy =>
          have : jW (a • y) = (⟨i a, hreg _ a.2⟩ : regAt ξ' q') • jW y := hsemi (a : Ω) y
          rw [this]
          exact Submodule.smul_mem _ _ hy
      exact key _ hin
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hin : b k ∈ (Lo.map W.dualRestrict) ⟨f q'.1, hq2⟩ := by
        rw [hfrq]
        exact Submodule.subset_span ⟨k, rfl⟩
      obtain ⟨w, hw, hwk⟩ := hin
      refine ⟨jd w, ?_, ?_⟩
      · rw [hL hr]
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      · show W'.dualRestrict (jd w) = jW (b k)
        rw [hcomp]
        exact congrArg jW hwk

end GlobalTheory.CompanionTheory.Ar.VbPull
