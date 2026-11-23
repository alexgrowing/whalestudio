import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfLocalMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdxLift

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem imA_vecV_smul (p : TypX X) (t : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (t • w) = PI.FinKW.psiV X.B.I p.1 t • PI.FinKW.vecV X.B.I p.1 w := by
  funext i; simp [PI.FinKW.vecV, map_mul]

theorem imA_vecV_add (p : TypX X) (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (a + b) = PI.FinKW.vecV X.B.I p.1 a + PI.FinKW.vecV X.B.I p.1 b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_zero (p : TypX X) :
    PI.FinKW.vecV X.B.I p.1 (0 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) = 0 := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_OEp_mul (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s * t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb', rfl⟩ := ht
  exact ⟨a * b, Subring.mul_mem _ ha hb', map_mul _ _ _⟩

theorem smul_mem_spanAt (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {w : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hw : w ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s}) :
    t • w ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s} := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t', ht', s, hs, rfl⟩ := hx
    exact Submodule.subset_span ⟨t * t', imA_OEp_mul X p ht ht', s, hs, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem imA_inMod_loc (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (h : InMod X.B.I m S w) :
    InModP X p m (PI.FinKW.vecV X.B.I p.1 '' S) (PI.FinKW.vecV X.B.I p.1 w) := by
  obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp h
  clear h
  rw [imA_vecV_add]
  refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, rfl⟩
  · induction ha using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span ⟨1, ⟨1, one_mem _, map_one _⟩, _, ⟨x, hx, rfl⟩, (one_smul _ _).symm⟩
    | zero => rw [imA_vecV_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [imA_vecV_add]; exact add_mem hx hy
    | smul c x _ hx =>
      show PI.FinKW.vecV X.B.I p.1 ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x) ∈ _
      rw [imA_vecV_smul]
      exact smul_mem_spanAt X p _ ⟨c, c.2, rfl⟩ hx
  · have key : ∃ x ∈ X.B.I.Lf, b = (m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x := by
      induction hb' using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨y', hy', rfl⟩ := hy
        obtain ⟨z', hz', rfl⟩ := hz
        exact ⟨y' + z', add_mem hy' hz', (smul_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨y', hy', rfl⟩ := hy
        refine ⟨c • y', Submodule.smul_mem _ c hy', ?_⟩
        show (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • _ = _ • ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • y')
        rw [smul_smul, smul_smul, mul_comm]
    obtain ⟨x, hx, rfl⟩ := key
    rw [imA_vecV_smul, map_natCast, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (p.1.adicCompletionIntegers X.B.I.F)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I x hx p.1)

theorem imA_vecV_mulVec (p : TypX X) (x : X.B.I.Gf)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 ((X.B.I.fmat x - 1) *ᵥ w) =
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (piV X.B.I p.1 (tf X.B.I hb x)) :
        GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 w := by
  rw [LocIdxLift_vecV_mulVec, Matrix.map_sub _ (map_sub _), LocIdxLift_psiV_fmat X.B.I hb,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem imA_kpp_sub (p : TypX X) : KppX X hb p ⊆ {y | y ∈ KvX X p ∧ LocCong X p y} := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hx' : x ∈ X.B.I.Kset ∧ K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := hx
  obtain ⟨hxK, h1, h2, h3⟩ := hx'
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hK := (Bridge_mem_Kf_iff X.B.I hb x).mpr hxK
    rw [Kf, Subgroup.mem_iInf] at hK
    exact hK p.1
  · intro a
    have h := imA_inMod_loc X p _ _ _ (h1 a)
    rw [imA_vecV_mulVec X hb, Set.image_image] at h
    exact h
  · have h := imA_inMod_loc X p _ _ _ h2
    rw [imA_vecV_mulVec X hb, ← Set.range_comp] at h
    exact h
  · intro i
    have h := imA_inMod_loc X p _ _ _ (h3 i)
    rw [imA_vecV_mulVec X hb, Set.image_union, Set.image_image, ← Set.range_comp] at h
    exact h

end MassDataIdxSteps
