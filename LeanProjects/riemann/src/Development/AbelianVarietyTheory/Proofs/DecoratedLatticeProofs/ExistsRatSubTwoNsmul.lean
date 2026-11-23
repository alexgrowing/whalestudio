import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassically
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatApprox

theorem two_nsmul_cancel {D : D7} (a b : AE D) (h : (2 : ℕ) • a = (2 : ℕ) • b) : a = b := by
  have key : ∀ c : AE D, c = algebraMap D.host.F (AE D) (2 : D.host.F)⁻¹ * ((2 : ℕ) • c) := by
    intro c
    rw [nsmul_eq_mul, ← mul_assoc, Nat.cast_ofNat, show (2 : AE D) = algebraMap D.host.F (AE D) 2 from (map_ofNat _ 2).symm,
      ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]
  rw [key a, key b, h]

theorem map_eq_zero_apply {D : D7} {S T : HSp D} {R : Type} [Semiring R] (f : AE D →+* R) {x : WO S T}
    (hx : x.map f = 0) (i : Fin T.rank) (j : Fin S.rank) : f (x i j) = 0 := by
  have := congrFun (congrFun hx i) j
  rwa [Matrix.map_apply, Matrix.zero_apply] at this

theorem eq_two_nsmul {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {x l : WO S T} (hx : x.map (infPart D) = 0) (hl : l ∈ latO S T LS LT fun _ => True)
    (hf : (x - (2 : ℕ) • l).map (finPart D) = 0) : x = (2 : ℕ) • l := by
  rw [← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ (map_eq_zero_apply _ hf i j)
  rw [Matrix.sub_apply, Matrix.smul_apply, map_sub, map_nsmul, map_eq_zero_apply _ hx i j,
    GlobalTheory.LatVac.infPart_of_mem hl i j, nsmul_zero, sub_zero]

theorem exists_rat_sub_two_nsmul : ∀ (D : D7) (S T : HSp D) (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True), ∃ γ, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), l ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ u - GlobalTheory.LatVac.finTens 1 γ = 2 • l := by
  intro D S T ΛS ΛS' ΛT ΛT' hS hS' hT hT' u hu
  let H : AddSubgroup (WO S T) :=
    ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓
      (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True)).map
      (nsmulAddMonoidHom 2)
  have hH : ∃ U : Set (WO S T), IsOpen U ∧ ∀ x : WO S T, x.map (infPart D) = 0 → (x ∈ H ↔ x ∈ U) := by
    refine ⟨_, (GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 2 two_pos).inter
      (GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS' ΛT' hS' hT' 2 two_pos), fun x hx => ⟨?_, ?_⟩⟩
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨l, hl.1, ?_⟩, ⟨l, hl.2, ?_⟩⟩ <;>
        rw [nsmulAddMonoidHom_apply, sub_self, Matrix.map_zero _ (map_zero _)]
    · rintro ⟨⟨l, hl, hf⟩, ⟨l', hl', hf'⟩⟩
      have e1 := eq_two_nsmul hx hl hf
      have e2 := eq_two_nsmul hx hl' hf'
      have hll : l = l' := by
        ext i j
        exact two_nsmul_cancel _ _ (by rw [← Matrix.smul_apply, ← Matrix.smul_apply, ← e1, ← e2])
      subst hll
      exact ⟨l, ⟨hl, hl'⟩, by rw [nsmulAddMonoidHom_apply, ← e1]⟩
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.AdTh.SplitClass.exists_rat_sub_mem (LS := (ΛS' : Set (Fin S.rank → D.host.E)))
    (LT := (ΛT' : Set (Fin T.rank → D.host.E))) hH hu
  obtain ⟨l, hl, hle⟩ := hγ
  exact ⟨γ, l, hl.1, hl.2, by rw [← hle, nsmulAddMonoidHom_apply]⟩

end GlobalTheory.LatApprox
