import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipAevalUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.FinLev

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

section Mod

variable (T : LocLat G Qp LL O) (A : ArcP n) (c : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
  (Rst : Finset (Fin d))

theorem inFr1_add {f g : W.EE} (hf : InFr W c 1 (abelian₂ W A c e) f) (hg : InFr W c 1 (abelian₂ W A c e) g) :
    InFr W c 1 (abelian₂ W A c e) (f + g) :=
  (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_add W
    ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hf) ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hg))

theorem inFr1_smul (o : O) {f : W.EE} (hf : InFr W c 1 (abelian₂ W A c e) f) :
    InFr W c 1 (abelian₂ W A c e) (o • f) :=
  (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_smul W
    ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 hf) o)

theorem inFr1_zero : InFr W c 1 (abelian₂ W A c e) 0 := ⟨0, W.AΔ.zero_mem, by simp⟩

def Msub : Submodule O (Fin d → W.EE) where
  carrier := {f | (∀ k, InFr W c 1 (abelian₂ W A c e) (f k)) ∧ ∀ k ∉ Rst, f k = 0}
  add_mem' := fun {f g} hf hg => ⟨fun k => inFr1_add W A c e (hf.1 k) (hg.1 k),
    fun k hk => by simp [hf.2 k hk, hg.2 k hk]⟩
  zero_mem' := ⟨fun _ => inFr1_zero W A c e, fun _ _ => rfl⟩
  smul_mem' := fun o f hf => ⟨fun k => inFr1_smul W A c e o (hf.1 k), fun k hk => by simp [hf.2 k hk]⟩

def Psub : Submodule O (Fin d → W.EE) where
  carrier := {f | f ∈ Msub W A c e Rst ∧
    ∃ g, InNL W T c e (abelian₂ W A c e) b g ∧ ∀ k, f k = ιE W.π₀ * g k}
  add_mem' := by
    rintro f f' ⟨hf, g, hg, hfg⟩ ⟨hf', g', hg', hfg'⟩
    exact ⟨(Msub W A c e Rst).add_mem hf hf', g + g',
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A c e b hg hg', fun k => by simp [hfg k, hfg' k, mul_add]⟩
  zero_mem' := ⟨(Msub W A c e Rst).zero_mem, 0, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_zero W T A c e b,
    fun k => by simp⟩
  smul_mem' := by
    rintro o f ⟨hf, g, hg, hfg⟩
    exact ⟨(Msub W A c e Rst).smul_mem o hf, fun k => o • g k,
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A c e b o hg, fun k => by
        rw [Pi.smul_apply, hfg k, mul_smul_comm]⟩

def Isub : Submodule O (Fin d → W.EE) where
  carrier := {f | f ∈ Msub W A c e Rst ∧ InvNL W T c e (abelian₂ W A c e) b f}
  add_mem' := by
    rintro f f' ⟨hf, g, hg, hfg⟩ ⟨hf', g', hg', hfg'⟩
    refine ⟨(Msub W A c e Rst).add_mem hf hf', g + g',
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A c e b hg hg', fun k => ?_⟩
    simp only [Pi.add_apply, map_add]
    rw [mul_add, ← hfg k, ← hfg' k]; ring
  zero_mem' := ⟨(Msub W A c e Rst).zero_mem, 0, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_zero W T A c e b,
    fun k => by simp⟩
  smul_mem' := by
    rintro o f ⟨hf, g, hg, hfg⟩
    refine ⟨(Msub W A c e Rst).smul_mem o hf, fun k => o • g k,
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A c e b o hg, fun k => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, hfg k, mul_smul_comm]

theorem inFr1_of_pi0Lam {f : W.EE} (hf : InFr W c (W.π₀ * abelian₂ W A c e) 1 f) :
    InFr W c 1 (abelian₂ W A c e) f := by
  obtain ⟨w, hw, hfw⟩ := hf
  have hΛm : abelian₂ W A c e ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem
    (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _
  refine ⟨abelian₂ W A c e * (W.π₀ * abelian₂ W A c e) * w,
    W.AΔ.mul_mem (W.AΔ.mul_mem hΛm (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) hΛm)) hw, ?_⟩
  rw [map_one, one_mul] at hfw
  rw [hfw, ← map_mul]; congr 1; ring

theorem psub_of_pi0Lam [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hbij : Function.Bijective (algebraMap K₀ K)) (hA : A.OK) (hc : c ∈ A.cuts) (hT : Win W A T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T (c - ((A.len c : ℕ) : ZMod n)) b) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 (f k)) (hs : ∀ k ∉ Rst, f k = 0) :
    f ∈ Psub W T A c (A.len c) b Rst := by
  obtain ⟨g, hg, hfg⟩ := nl_of_pi0Lam W hR hbij A hA c hc T hT b hb f hf
  exact ⟨⟨fun k => inFr1_of_pi0Lam W A c _ (hf k), hs⟩, g, hg, hfg⟩

end Mod

end Formalism.MainNotions.UnusedSlot80.UGen
