import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.CuspMult.CutFull

open GlobalTheory.CuspMult GlobalTheory.CuspMult.EqCut

theorem mem_killed_union {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (I I' : Set (MonoidAlgebra ℂ H)) (v : X) : v ∈ killed ρ (I ∪ I') ↔ v ∈ killed ρ I ∧ v ∈ killed ρ I' := by
  simp only [mem_killed, Set.mem_union, or_imp, forall_and]

theorem mem_partFull_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ) (T : MMap M) :
    T ∈ partFull θ M J χ SF a ↔ T ∈ Mult θ M J χ ∧ ∀ Q d R, Hecke₂ V J χ SF Q d R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = a Q d * T v x := by
  unfold partFull
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_partFull_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ partFull θ M (levS V β (withP L (LevelP.triv L.Pg L.r ℂ))) (levChi V β (withP L (LevelP.triv L.Pg L.r ℂ))) SF a = GlobalTheory.CuspMult.allMaps θ M ⊓ GlobalTheory.CuspMult.killed (GlobalTheory.CuspMult.finRep M) (GlobalTheory.CuspMult.eqSet V β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim ∪ {x | ∃ (Q : Pl D.host.E) (d : List ℤ) (B : Finset (GfC V)), Hecke₂ V (levS V β (withP L (LevelP.triv L.Pg L.r ℂ))) (levChi V β (withP L (LevelP.triv L.Pg L.r ℂ))) SF Q d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ∧ x = ∑ γ ∈ B, MonoidAlgebra.single γ 1 - MonoidAlgebra.single 1 (a Q d)}) := by
  intro D V S θ M β L G _ _ eG c P SF a hs hQ hlift
  have h0 := good_hecke_eq_killed θ M β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim hs hQ hlift
  have h1 : ∀ T : MMap M, T ∈ goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ↔
      T ∈ allMaps θ M ∧ T ∈ killed (finRep M) (eqSet V β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) := by
    intro T
    rw [← Submodule.mem_inf, ← h0, Submodule.mem_inf, mem_hPart]
    exact ⟨fun h => ⟨h, fun p => p.elim⟩, fun h => h.1⟩
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_killed_union, ← and_assoc, ← h1, mem_partFull_iff]
  refine and_congr_right fun hg => ?_
  rw [mem_killed]
  constructor
  · rintro ⟨-, hh⟩ x ⟨Q, d, B, hB, rfl⟩
    refine (alg_sum M B (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
    have := hh Q d _ hB v x
    rw [Finset.sum_map] at this
    simp only [one_mul]
    exact this
  · intro hk
    have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hg.1
    refine ⟨(GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).2 ⟨hm.aut, hm.cusp, fun v k hkk x => ?_, hm.equiv, hm.cont⟩, ?_⟩
    · exact hasType_flag1 P (F := T v) (fun k hk h => hm.lev v k hk h) k hkk x
    · intro Q d R hR v x
      classical
      have hf : ∀ γ ∈ R, γ ∈ GfC V := by
        obtain ⟨e, f, ϖ, α, -, -, -, -, -, -, -, -, -, -, h⟩ := hR
        exact fun γ hγ => (h.1 γ hγ).1
      obtain ⟨B, rfl⟩ : ∃ B : Finset (GfC V), B.map ⟨Subtype.val, Subtype.val_injective⟩ = R :=
        ⟨R.subtype (· ∈ GfC V), Finset.subtype_map_of_mem hf⟩
      have := (alg_sum M B (fun γ => γ) (fun _ => 1) _ T).1 (hk _ ⟨Q, d, B, hR, rfl⟩) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.CutFull

end
