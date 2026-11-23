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

namespace GlobalTheory.LatLevel

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_nsmul_smul_mem {m n : ℕ} (U : AddSubgroup (Mx D m n)) (hU : IsOpen (U : Set (Mx D m n)))
    (y : Mx D m n) : ∃ N : ℕ, 0 < N ∧ ∀ α ∈ intAf D.host.F,
      N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) ∈ U := by
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F → Mx D m n := fun α => Matrix.of fun i j => pairA D.host.F 0 α • y i j
  have hp : Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 α :=
    continuous_const.prodMk continuous_id
  have hφ : Continuous φ := continuous_pi fun i => continuous_pi fun j => hp.smul continuous_const
  have h0 : φ 0 = 0 := Matrix.ext fun i j => zero_smul (AF D.host.F) (y i j)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele D.host.F (φ ⁻¹' U)
    (hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (h0 ▸ U.zero_mem)))
  refine ⟨N, hN, fun α hα => ?_⟩
  have h1 : φ (N • α) ∈ U := h α hα
  have h2 : φ (N • α) = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) := by
    refine Matrix.ext fun i j => ?_
    have e1 : pairA D.host.F 0 (N • α) = N • pairA D.host.F 0 α :=
      Prod.ext (show (0 : Ainf D.host.F) = N • 0 by rw [smul_zero]) rfl
    show pairA D.host.F 0 (N • α) • y i j = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * y i j)
    rw [e1, smul_assoc, Algebra.smul_def (pairA D.host.F 0 α)]
  rwa [h2] at h1

def actHom (S T : HSp D) (g : GA D S) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T g h) fun x y => by
    unfold actO
    rw [Matrix.mul_add, Matrix.add_mul]

theorem continuous_actO (S T : HSp D) (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [actO, Matrix.mul_apply]
  refine continuous_finset_sum _ fun k _ => Continuous.mul (continuous_finset_sum _ fun l _ =>
    continuous_const.mul ?_) continuous_const
  exact (continuous_apply k).comp (continuous_apply l)

theorem actO_map_inf (S T : HSp D) (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

def finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) : AddSubgroup (Mx D m n) :=
  (L.map (finPart D).toAddMonoidHom.mapMatrix).comap (finPart D).toAddMonoidHom.mapMatrix

theorem mem_finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) (x : Mx D m n) :
    x ∈ finSat L ↔ ∃ l ∈ L, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 := by
  have key : ∀ l : Mx D m n, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 ↔
      (finPart D).toAddMonoidHom.mapMatrix l = (finPart D).toAddMonoidHom.mapMatrix x := by
    intro l
    rw [one_smul, eq_comm (b := (finPart D).toAddMonoidHom.mapMatrix x), ← sub_eq_zero (a := (finPart D).toAddMonoidHom.mapMatrix x), ← map_sub]
    rfl
  simp only [key]
  rfl

theorem level_of_generators : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • u ∈ U) ∧ ∀ (g : GA D S) (h : GA D T), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D S T ΛS ΛT hS hT ⟨G, hG, _, hgen⟩
  have h1 : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        N • u ∈ U := by
    intro U hU
    choose M hM hMU using fun y : WO S T => exists_nsmul_smul_mem U hU y
    refine ⟨∏ y ∈ hG.toFinset, M y, Finset.prod_pos fun y _ => hM y, ?_⟩
    refine hgen (U.comap (nsmulAddMonoidHom (∏ y ∈ hG.toFinset, M y))) fun α hα u hu => ?_
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem M (hG.mem_toFinset.2 hu)
    show (∏ y ∈ hG.toFinset, M y) • _ ∈ U
    rw [hc, mul_comm, mul_smul]
    exact U.nsmul_mem (hMU u α hα) c
  refine ⟨h1, fun g h => ?_⟩
  have hop : IsOpen (finSat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) : Set (WO S T)) := by
    convert GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 1 one_pos using 1
    exact Set.ext fun x => mem_finSat _ x
  obtain ⟨N, hN, hNU⟩ := h1 ((finSat _).comap (actHom S T g h)) (hop.preimage (continuous_actO S T g h))
  refine ⟨N, hN, fun u hu => ?_⟩
  have h2 : actHom S T g h (N • u) ∈ finSat _ := hNU u hu
  obtain ⟨l, hl, hl0⟩ := (mem_finSat _ _).1 h2
  have h3 : (actHom S T g h (N • u)).map (infPart D) = 0 :=
    actO_map_inf S T g h (latO_fin (AddSubgroup.nsmul_mem _ hu N))
  have h4 := latO_fin hl
  have h5 : actHom S T g h (N • u) = l := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · exact (congrFun (congrFun h3 i) j).trans (congrFun (congrFun h4 i) j).symm
    · have h6 : finPart D (actHom S T g h (N • u) i j - (1 : ℕ) • l i j) = 0 := congrFun (congrFun hl0 i) j
      rwa [one_smul, RingHom.map_sub, sub_eq_zero] at h6
  rw [map_nsmul] at h5
  exact h5 ▸ hl

end GlobalTheory.LatLevel

end
