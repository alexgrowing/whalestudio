import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.Pf.FlagCoordinates

variable {D : D7} (X : HidaSetting D)

theorem gE_sub_one (Z : Matrix (Kap X) (Kap X) X.B.I.E) :
    Formalism.L2.SG.Pf.UnipB.gE X Z - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X := by
  unfold Formalism.L2.SG.Pf.UnipB.gE
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bm_mul_Bm']

theorem Bm_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → X.B.I.E) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bm X *ᵥ c ∈ Submodule.span X.B.I.E (X.eR '' S) := by
  rw [Bm_mulVec]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem flag_coord {Z : Matrix (Kap X) (Kap X) X.B.I.E} (hZ : InPat (lvk X) 1 Z) (a : Fin D.R.rS) :
    (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ X.eR a ∈ Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1}) := by
  rw [gE_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hB : Bm' X *ᵥ X.eR a = Pi.single (Sum.inl a) 1 := by
    rw [Bm'_mulVec]
    funext k
    rw [show X.eR a = bv X (Sum.inl a) from rfl, cE_bv]
    simp [Pi.single_apply]
  rw [hB]
  refine Bm_mulVec_mem X _ _ fun k hk => ?_
  rw [mulVec_single_one]
  refine cay_sub_one _ hZ k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem orth_coord {Z : Matrix (Kap X) (Kap X) X.B.I.E} (hZ : InPat (lvk X) 1 Z) (x : Fin X.B.I.n → X.B.I.E)
    (hx : ∀ a, hE X (X.eR a) x = 0) :
    (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ x ∈ Submodule.span X.B.I.E (X.eR '' Set.univ) := by
  rw [gE_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Bm'_mulVec]
  refine Bm_mulVec_mem X Set.univ _ fun k hk => ?_
  have hk' : ∀ b, k ≠ Sum.inl b := by
    rintro b rfl
    exact hk ⟨b, Set.mem_univ _, rfl⟩
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hlk := lvk_notinl X k hk'
  rcases j with b | i | b
  · rw [cay_sub_one _ hZ k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
  · rw [cay_sub_one _ hZ k _ (by rw [lvk_w]; omega), zero_mul]
  · rw [show cE X x (Sum.inr (Sum.inr b)) = hE X (X.eR b) x from rfl, hx b, mul_zero]

theorem crd_desc (S : Set (Fin D.R.rS)) (v : (VS D).V)
    (hv : X.crd v ∈ Submodule.span X.B.I.E (X.eR '' S)) :
    v ∈ Submodule.span D.host.E (X.eX '' S) := by
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun X.B.I.E).1 hv
  have e : v = ∑ i : S, X.ιE (c i) • X.eX i := by
    rw [← Formalism.L2.SG.Pf.Level.toV_crd X v, ← hc, Formalism.L2.SG.Pf.Level.toV_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.L2.SG.Pf.Level.toV_smul, show X.eR i = X.crd (X.eX i) from rfl, Formalism.L2.SG.Pf.Level.toV_crd]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩)

end Formalism.L2.SG.Pf.FlagCoordinates

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.FlagCoordinates

theorem memFlagOf_holds : MemFlagOf := by
  intro D X u Z n hZ hn
  have hm : ∀ v, (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ X.crd v = X.crd (n v - v) := fun v => Formalism.L2.SG.Pf.Vanish2.mcrd X hn v
  have hXf : ∀ k, Xflag (lf D (X.Fu u)) k = Submodule.span D.host.E (X.eX '' {i | i.1 < k}) := by
    intro k
    show Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < k}) = _
    rw [X.Fu_e]
  have hXs : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (X.eX '' Set.univ) := by
    show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
    rw [X.Fu_e, Set.image_univ]
  have he : ∀ a : Fin D.R.rS, n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
    intro a
    have hd := flag_coord X hZ a
    rw [show X.eR a = X.crd (X.eX a) from rfl, hm] at hd
    exact crd_desc X _ _ hd
  refine ⟨fun j x hx => ?_, fun x hx => ?_⟩
  · rw [hXf] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨b, lt_of_lt_of_le hb (Nat.lt_succ_iff.1 ha), rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, add_sub_add_comm]
      exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  · have hx0 : ∀ a, hE X (X.eR a) (X.crd x) = 0 := by
      intro a
      have hmem : X.eX a ∈ Xsp (lf D (X.Fu u)) := by
        rw [hXs]
        exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩
      have h0 : (VS D).hT (X.eX a) x = 0 := (Formalism.L2.SG.Pf.mem_orth_iff _ _).1 hx _ hmem
      rw [show X.eR a = X.crd (X.eX a) from rfl, hE_crd, h0, map_zero]
    have hd := orth_coord X hZ _ hx0
    rw [hm] at hd
    rw [hXs]
    exact crd_desc X _ _ hd

end Formalism.L2.SG.TermOp.Vanish
