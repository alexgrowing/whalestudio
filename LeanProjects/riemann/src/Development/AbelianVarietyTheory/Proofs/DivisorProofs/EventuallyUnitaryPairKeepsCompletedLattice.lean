import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatNhds

open GlobalTheory.SplitScalar

variable {D : D7}

theorem continuous_mt (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mt_inv (V : HSp D) : Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_actO (S T : HSp D) (x : WO S T) :
    Continuous fun p : GA D S × GA D T => actO S T p.1 p.2 x := by
  have h1 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt T p.2 := (continuous_mt T).comp continuous_snd
  have h2 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt S p.1⁻¹ := (continuous_mt_inv S).comp continuous_fst
  exact (h1.matrix_mul continuous_const).matrix_mul h2

theorem actO_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  have h : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun _ => rfl
  rw [actO, inv_one, h, h, Matrix.one_mul, Matrix.mul_one]

theorem actO_smul {S T : HSp D} (g : GA D S) (h : GA D T) (a : AE D) (x : WO S T) :
    actO S T g h (a • x) = a • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem fin_iff {S T : HSp D} {u : WO S T} : u.map (infPart D) = 0 ↔ realIdem D • u = 0 := by
  constructor
  · exact fun h => Matrix.ext fun i j => realIdem_mul_of_fin (congrFun (congrFun h i) j)
  · intro h
    funext i j
    have h1 := congrArg (infPart D) (congrFun (congrFun h i) j)
    rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, infPart_realIdem, one_mul] at h1
    exact h1.trans (infPart D).map_zero

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  rw [fin_iff] at hu ⊢
  rw [← actO_smul, hu, actO, Matrix.mul_zero, Matrix.zero_mul]

theorem continuous_sub_const' {X G : Type} [TopologicalSpace X] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {f : X → G} (hf : Continuous f) (x : G) : Continuous fun p => f p - x :=
  hf.sub continuous_const

theorem sub_nsmul_zero {G : Type} [AddCommGroup G] (x : G) (N : ℕ) : x - x - N • (0 : G) = 0 := by
  rw [sub_self, smul_zero, sub_self]

theorem eventually_move (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (x : WO S T) (hx : x.map (infPart D) = 0) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  have hO := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT N hN
  have hc : Continuous fun p : GA D S × GA D T => actO S T p.1 p.2 x - x :=
    continuous_sub_const' (continuous_actO S T x) x
  have h1 := (hO.preimage hc).mem_nhds (x := 1) ⟨0, AddSubgroup.zero_mem _, by
    show (actO S T 1 1 x - x - N • (0 : WO S T)).map (finPart D) = 0
    rw [actO_one, sub_nsmul_zero]
    exact Matrix.ext fun _ _ => (finPart D).map_zero⟩
  filter_upwards [h1] with p hp
  obtain ⟨l, hl, e⟩ := hp
  refine ⟨l, hl, ?_⟩
  have hi : (actO S T p.1 p.2 x - x - N • l).map (infPart D) = 0 := by
    have a1 := fin_iff.1 (actO_fin p.1 p.2 hx)
    have a2 := fin_iff.1 hx
    have a3 := fin_iff.1 (latO_fin (AddSubgroup.nsmul_mem _ hl N))
    rw [fin_iff, smul_sub, smul_sub, a1, a2, a3, sub_zero, sub_zero]
  have hz : actO S T p.1 p.2 x - x - N • l = 0 :=
    Matrix.ext fun i j => adele_ext ((congrFun (congrFun hi i) j).trans (infPart D).map_zero.symm)
      ((congrFun (congrFun e i) j).trans (finPart D).map_zero.symm)
  rw [sub_sub, sub_eq_zero] at hz
  exact hz

theorem eventually_actO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ x : WO S T, x.map (infPart D) = 0 → ∀ N : ℕ, 0 < N → ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  rintro D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  refine ⟨?_, eventually_move S T ΛS ΛT hS hT⟩
  have h := (Filter.eventually_all_finite hG).2 fun u hu =>
    eventually_move S T ΛS ΛT hS hT u (latO_fin (hGl u hu)) 1 one_pos
  filter_upwards [h] with p hp
  intro w hw
  refine hgen (AddSubgroup.comap (AddMonoidHom.mk' (actO S T p.1 p.2) (actO_add p.1 p.2))
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  rw [AddSubgroup.mem_comap, AddMonoidHom.mk'_apply, actO_smul, e]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _
    (AddSubgroup.add_mem _ (hGl u hu) (AddSubgroup.nsmul_mem _ hl 1))
  exact AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩

end GlobalTheory.LatNhds

end
