import Mathlib
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem mem_span_of_semilinear {B K O Kf V W ι : Type*} [CommRing B] [IsDomain B] [IsPrincipalIdealRing B] [Field K]
    [Algebra B K] [IsFractionRing B K] [CommRing O] [Field Kf] [Algebra O Kf]
    [AddCommGroup V] [Module K V] [Module B V] [IsScalarTower B K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (σ : K →+* Kf) (hσ : ∀ k, σ k ∈ Set.range (algebraMap O Kf) ↔ k ∈ Set.range (algebraMap B K))
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Module.Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (S : Set V) (x : V) (hx : φ x ∈ Submodule.span O (φ '' S)) :
    x ∈ Submodule.span B S := by
  classical
  obtain ⟨T, hTS, hxT⟩ := Submodule.mem_span_finite_of_mem_span hx
  obtain ⟨T', hT'S, rfl⟩ := Finset.subset_set_image_iff.1 hTS
  refine Submodule.span_mono hT'S ?_
  set N := Submodule.span B (T' : Set V) with hN
  have : Module.Finite B N := Module.Finite.span_of_finite B T'.finite_toSet
  have : Module.IsTorsionFree B V := Module.IsTorsionFree.trans_faithfulSMul B K V
  have : Module.Free B N := inferInstance
  let e0 := Module.Free.chooseBasis B N
  let e : Module.Free.ChooseBasisIndex B N → V := fun i => (e0 i : V)
  have heB : LinearIndependent B e := e0.linearIndependent.map' N.subtype N.ker_subtype
  have heK : LinearIndependent K e := (LinearIndependent.iff_fractionRing B K).1 heB
  have hspan : N ≤ Submodule.span B (Set.range e) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : N) ∈ Submodule.span B (Set.range e0) := by rw [e0.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := N.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hxe : φ x ∈ Submodule.span O (Set.range (φ ∘ e)) := by
    refine (Submodule.span_le.2 ?_) hxT
    rw [Finset.coe_image]
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hspan (Submodule.subset_span hy)
    rw [SetLike.mem_coe]
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add z z' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
    | smul a z _ h =>
      obtain ⟨o, ho⟩ := (hσ (algebraMap B K a)).2 ⟨a, rfl⟩
      rw [← algebraMap_smul K a z, hφ, ← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ h
  have hxK : x ∈ Submodule.span K (Set.range e) := by
    by_contra hn
    have h1 : LinearIndependent K (fun o => Option.casesOn' o x e) := heK.option hn
    have h2 := FBC.li_of_basis_li σ φ hφ b hb _ h1
    have h3 : (φ ∘ fun o => Option.casesOn' o x e) = fun o => Option.casesOn' o (φ x) (φ ∘ e) := by
      ext o; cases o <;> rfl
    rw [h3, linearIndependent_option'] at h2
    exact h2.2 (Submodule.span_subset_span O Kf _ hxe)
  obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxK
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hxe
  have hli := FBC.li_of_basis_li σ φ hφ b hb _ heK
  have heq : ∀ i, σ (k i) = algebraMap O Kf (o i) := by
    apply Fintype.linearIndependent_iffₛ.1 hli
    simp only [algebraMap_smul, ho]
    rw [← hk, map_sum]
    simp [hφ]
  rw [← hk]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a, ha⟩ := (hσ (k i)).1 ⟨o i, (heq i).symm⟩
  rw [← ha, algebraMap_smul]
  exact Submodule.smul_mem _ _ (e0 i).2

theorem NP_full (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (∀ x, c.cmp u w hg (D.nuIn u x) ∈ G.NP X Y K u w hg → InLoc (D.plEq w) (DV.MramL D u) x) ∧
      ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ DV.MramL D u, c.cmp u w hg (D.nuIn u (n • x)) ∈ G.NP X Y K u w hg := by
  constructor
  · intro x hx
    have hM : c.cmp u w hg (D.nuIn u x) ∈ (D.gat u w hg).M := by
      obtain ⟨⟨-, F, hF, hFe⟩, -⟩ := hx
      rw [← hFe]
      exact Submodule.smul_mem _ _ hF
    rw [← c.cmp_M u w hg] at hM
    have := D.intW_dvr w
    have := D.intW_frac w
    have h1 : D.nuIn u x ∈ Submodule.span (intW D.what₂.places w) (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
      refine mem_span_of_semilinear (c.embW u w hg) (fun k => ?_) (c.cmp u w hg) (c.cmp_smul u w hg)
        ((D.fm u).lat 0).b (c.cmp_li u w hg) _ _ hM
      rw [← c.embW_int u w hg k]
      exact ⟨fun h => ⟨⟨k, h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩
    obtain ⟨s, hs, hsx⟩ := (D.mem_locW_iff w ((D.fm u).lat 0).L (D.nuIn u x)).1 h1
    refine ⟨s, hs, ?_⟩
    show ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) (s • x) ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hsx
  · set a : ℕ := ∑ t0 ∈ G.VV X K (G.aL L) (G.bL L) (D.what₂.places.resChar w),
      ⌈G.Sv X K (G.aL L) (G.bL L) (D.what₂.places.resChar w) t0⌉.toNat with ha
    set b : ℕ := ⌈G.tauP X K (G.aL L) (G.bL L) (D.what₂.places.resChar w)⌉.toNat with hb
    refine ⟨D.what₂.places.resChar w ^ (b + a), pow_ne_zero _ (D.what₂.places.resChar_prime w).ne_zero, fun x hx => ?_⟩
    have hF1 : c.cmp u w hg (D.nuIn u x) ∈ (D.gat u w hg).M := by
      rw [← c.cmp_M u w hg]
      exact Submodule.subset_span ⟨D.nuIn u x, hx, rfl⟩
    have hF2 : c.cmp u w hg (D.nuIn u x) ∈ Y.Vram u w hg := by
      rw [← SetLike.mem_coe, hv u w hg]
      refine Submodule.subset_span ⟨D.nuIn u x, ?_, rfl⟩
      rw [← D.nuIn_range u]
      exact ⟨x, rfl⟩
    rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (D.gat u w hg).O, Nat.cast_pow]
    generalize c.cmp u w hg (D.nuIn u x) = F at hF1 hF2
    unfold G.NP
    refine ⟨⟨?_, ?_⟩, Submodule.smul_mem _ _ hF2⟩
    · rw [pow_add, mul_smul]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨∅, Finset.empty_subset _, F, hF1, ?_⟩
      simp [G.yProd, ha]
    · refine ⟨((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ a • F, Submodule.smul_mem _ _ hF1, ?_⟩
      rw [pow_add, mul_smul]
      rfl

end GlobalTheory.EX.OB
