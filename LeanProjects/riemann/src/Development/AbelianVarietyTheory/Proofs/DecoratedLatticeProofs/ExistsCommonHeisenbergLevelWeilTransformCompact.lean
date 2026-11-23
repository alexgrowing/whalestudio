import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.LevelCompact

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem actO_actO' (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_inv_actO' (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  rw [actO_actO', mul_inv_cancel, mul_inv_cancel]
  unfold actO
  rw [inv_one, mt_one', mt_one']
  simp

theorem actO_add' (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_map_infPart (S T : HSp D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    (actO S T g h x).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hx]; simp

theorem continuous_actO_inv (S T : HSp D) :
    Continuous fun q : (GA D S × GA D T) × WO S T => actO S T q.1.1⁻¹ q.1.2⁻¹ q.2 := by
  have hmt : ∀ V : HSp D, Continuous (Formalism.L2.Theta.mt V) := fun V =>
    Units.continuous_val.comp continuous_subtype_val
  have hmti : ∀ V : HSp D, Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := fun V =>
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [actO, inv_inv]
  exact (((hmti T).comp (continuous_snd.comp continuous_fst)).matrix_mul continuous_snd).matrix_mul
    ((hmt S).comp (continuous_fst.comp continuous_fst))

theorem exists_level_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ p ∈ K, om p f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  intro D ψ S T χS χT om hom f hf K hK
  obtain ⟨U0, hU0, hf0⟩ := hf.level
  have hz : ∀ p : GA D S × GA D T, actO S T p.1⁻¹ p.2⁻¹ 0 = 0 := fun p => by simp [actO]
  let U : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ p ∈ K, actO S T p.1⁻¹ p.2⁻¹ u ∈ U0}
      add_mem' := fun {a b} ha hb p hp => by
        rw [actO_add']; exact U0.add_mem (ha p hp) (hb p hp)
      zero_mem' := fun p _ => by rw [hz]; exact U0.zero_mem
      neg_mem' := fun {a} ha p hp => by
        have : actO S T p.1⁻¹ p.2⁻¹ (-a) = -actO S T p.1⁻¹ p.2⁻¹ a := by
          simp only [actO, Matrix.mul_neg, Matrix.neg_mul]
        rw [this]; exact U0.neg_mem (ha p hp) }
  have hU : ∀ u, u ∈ U ↔ ∀ p ∈ K, actO S T p.1⁻¹ p.2⁻¹ u ∈ U0 := fun _ => Iff.rfl
  refine ⟨U, ?_, ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds U (g := 0) ?_
    have hn : IsOpen ((fun q : (GA D S × GA D T) × WO S T => actO S T q.1.1⁻¹ q.1.2⁻¹ q.2) ⁻¹'
        (U0 : Set (WO S T))) := hU0.preimage (continuous_actO_inv S T)
    obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hn (by
      rintro ⟨p, w⟩ ⟨_, hw⟩
      rw [Set.mem_singleton_iff] at hw
      subst hw
      show actO S T p.1⁻¹ p.2⁻¹ 0 ∈ U0
      rw [hz]; exact U0.zero_mem)
    refine Filter.mem_of_superset (hv.mem_nhds (h0v rfl)) fun w hw => (hU w).2 fun p hp => ?_
    have h2 := Set.mem_preimage.1 (huv (Set.mk_mem_prod (hKu hp) hw))
    exact SetLike.mem_coe.1 h2
  · rintro ⟨g, h⟩ hp
    change IsThetaFunO ψ S T (om (g, h) f) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (g, h) f) = om (g, h) f
    refine ⟨hom.om_pres (g, h) f hf, fun u hu h0 => ?_⟩
    have h1 : actO S T g⁻¹ h⁻¹ u ∈ U0 := (hU u).1 hu (g, h) hp
    have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) f hf
    rw [actO_inv_actO', hf0 _ h1 (actO_map_infPart S T _ _ h0)] at e
    exact e.symm

end GlobalTheory.LevelCompact
