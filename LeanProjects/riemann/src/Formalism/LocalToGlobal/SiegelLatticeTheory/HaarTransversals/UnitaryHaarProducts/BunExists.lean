import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrdStronglyMeasurable
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionD
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdIndexEq
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

noncomputable section

section PartT

open scoped TensorProduct InnerProductSpace

namespace Formalism.L2.SG.Pf.BunT

structure IPS : Type 1 where
  C : Type
  [n : NormedAddCommGroup C]
  [i : InnerProductSpace ℂ C]

attribute [instance] IPS.n IPS.i

variable {V : Type} (H : V → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]

def tw : List V → IPS
  | [] => ⟨ℂ⟩
  | v :: l => ⟨(tw l).C ⊗[ℂ] H v⟩

def pt : (l : List V) → (∀ v, H v) → (tw H l).C
  | [], _ => (1 : ℂ)
  | v :: l, x => (pt l x ⊗ₜ[ℂ] x v : (tw H l).C ⊗[ℂ] H v)

def op : (l : List V) → (∀ v, H v →L[ℂ] H v) → ((tw H l).C →L[ℂ] (tw H l).C)
  | [], _ => ContinuousLinearMap.id ℂ ℂ
  | v :: l, A => (TensorProduct.mapL (op l A) (A v) : (tw H l).C ⊗[ℂ] H v →L[ℂ] (tw H l).C ⊗[ℂ] H v)

theorem pt_inner (l : List V) (x y : ∀ v, H v) :
    ⟪pt H l x, pt H l y⟫_ℂ = (l.map fun v => ⟪x v, y v⟫_ℂ).prod := by
  induction l with
  | nil =>
    show inner ℂ (1 : ℂ) (1 : ℂ) = 1
    simp
  | cons v l ih =>
    show inner ℂ ((pt H l x ⊗ₜ[ℂ] x v : (tw H l).C ⊗[ℂ] H v)) (pt H l y ⊗ₜ[ℂ] y v) = _
    rw [TensorProduct.inner_tmul, ih, List.map_cons, List.prod_cons, mul_comm]

theorem op_pt (l : List V) (A : ∀ v, H v →L[ℂ] H v) (x : ∀ v, H v) :
    op H l A (pt H l x) = pt H l (fun v => A v (x v)) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    show TensorProduct.mapL (op H l A) (A v) (pt H l x ⊗ₜ[ℂ] x v) = pt H l (fun v => A v (x v)) ⊗ₜ[ℂ] A v (x v)
    rw [TensorProduct.mapL_tmul, ih]

theorem pt_congr (l : List V) {x y : ∀ v, H v} (h : ∀ v ∈ l, x v = y v) : pt H l x = pt H l y := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    show (pt H l x ⊗ₜ[ℂ] x v : (tw H l).C ⊗[ℂ] H v) = pt H l y ⊗ₜ[ℂ] y v
    rw [ih (fun w hw => h w (List.mem_cons_of_mem v hw)), h v (by simp)]

theorem span_one (α : Type) [Nonempty α] : Submodule.span ℂ (Set.range (fun _ : α => (1 : ℂ))) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a⟩ := ‹Nonempty α›
  have h1 : (1 : ℂ) ∈ Submodule.span ℂ (Set.range (fun _ : α => (1 : ℂ))) := Submodule.subset_span ⟨a, rfl⟩
  simpa using Submodule.smul_mem _ z h1

theorem pt_span [DecidableEq V] (l : List V) (hl : l.Nodup) :
    Submodule.span ℂ (Set.range (pt H l)) = ⊤ := by
  induction l with
  | nil => exact span_one (∀ v, H v)
  | cons v l ih =>
    obtain ⟨hv, hl'⟩ := List.nodup_cons.1 hl
    have ih' := ih hl'
    have key : ∀ (a : (tw H l).C) (b : H v),
        (a ⊗ₜ[ℂ] b : (tw H l).C ⊗[ℂ] H v) ∈ Submodule.span ℂ (Set.range (pt H (v :: l))) := by
      intro a b
      have hspan : Submodule.span ℂ (Set.range (pt H l)) ≤ Submodule.comap
          ((TensorProduct.mk ℂ (tw H l).C (H v)).flip b) (Submodule.span ℂ (Set.range (pt H (v :: l)))) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        show (pt H l x ⊗ₜ[ℂ] b : (tw H l).C ⊗[ℂ] H v) ∈ Submodule.span ℂ (Set.range (pt H (v :: l)))
        refine Submodule.subset_span ⟨Function.update x v b, ?_⟩
        show (pt H l (Function.update x v b) ⊗ₜ[ℂ] Function.update x v b v : (tw H l).C ⊗[ℂ] H v) = _
        rw [Function.update_self, pt_congr H l (x := Function.update x v b) (y := x)
          (fun w hw => Function.update_of_ne (fun e : w = v => hv (e ▸ hw)) b x)]
      have ha : a ∈ Submodule.span ℂ (Set.range (pt H l)) := by rw [ih']; trivial
      exact hspan ha
    rw [eq_top_iff]
    intro t ht
    clear ht
    change (tw H l).C ⊗[ℂ] H v at t
    induction t using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul a b => exact key a b
    | add s t hs ht => exact Submodule.add_mem _ hs ht

abbrev Cw (l : List V) : Type := UniformSpace.Completion (tw H l).C

def ctens (l : List V) (x : ∀ v, H v) : Cw H l := ((pt H l x : (tw H l).C) : Cw H l)

def cop (l : List V) (A : ∀ v, H v →L[ℂ] H v) : Cw H l →L[ℂ] Cw H l :=
  ((UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := (tw H l).C)).comp (op H l A)).extend
    (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := (tw H l).C))

theorem ctens_inner (l : List V) (x y : ∀ v, H v) :
    ⟪ctens H l x, ctens H l y⟫_ℂ = (l.map fun v => ⟪x v, y v⟫_ℂ).prod := by
  unfold ctens
  rw [UniformSpace.Completion.inner_coe]
  exact pt_inner H l x y

theorem cop_ctens (l : List V) (A : ∀ v, H v →L[ℂ] H v) (x : ∀ v, H v) :
    cop H l A (ctens H l x) = ctens H l (fun v => A v (x v)) := by
  have e1 : ctens H l x = UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := (tw H l).C) (pt H l x) := rfl
  rw [e1, cop, ContinuousLinearMap.extend_eq]
  · rw [ContinuousLinearMap.comp_apply, op_pt]; rfl
  all_goals first
    | exact UniformSpace.Completion.denseRange_coe
    | exact UniformSpace.Completion.isUniformInducing_coe _

theorem ctens_dense [DecidableEq V] (l : List V) (hl : l.Nodup) :
    Dense (Submodule.span ℂ (Set.range (ctens H l)) : Set (Cw H l)) := by
  have h1 : Set.range ((↑) : (tw H l).C → Cw H l) ⊆
      (Submodule.span ℂ (Set.range (ctens H l)) : Set (Cw H l)) := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ Submodule.span ℂ (Set.range (pt H l)) := by rw [pt_span H l hl]; trivial
    have h2 := Submodule.mem_map_of_mem
      (f := (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := (tw H l).C)).toLinearMap) hy
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  exact Dense.mono h1 UniformSpace.Completion.denseRange_coe

end Formalism.L2.SG.Pf.BunT

end PartT

section PartM

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates

namespace Formalism.L2.SG.Pf.BunM

variable (I : AutInst)

def muF : Measure I.Gf :=
  Measure.haarMeasure ⟨⟨I.Kset, PI.WAU.maximal_compact_isCompact I⟩, by
    rw [(PI.WAU.kset_open I).interior_eq]; exact ⟨1, Formalism.L2.SG.Pf.one_mem_kset I⟩⟩

instance muF_haar : (muF I).IsHaarMeasure := by unfold muF; infer_instance

instance muF_sigma : SigmaFinite (muF I) :=
  PI.WAU.sigmaFinite_of_K I _ inferInstance (PI.WAU.maximal_compact_isCompact I) (PI.WAU.compact_countable I)

instance muF_right : (muF I).IsMulRightInvariant :=
  PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable
    PI.adelic_index_eq I (muF I) inferInstance

instance gf_sc : SecondCountableTopology I.Gf := Formalism.L2.SG.Pf.gf_secondCountable I

instance muA_sigma : SigmaFinite (I.muA (muF I)) := rr_muA_sigmaFinite I (muF I)
instance muA_left : (I.muA (muF I)).IsMulLeftInvariant := rr_muA_left I (muF I)
instance muA_right : (I.muA (muF I)).IsMulRightInvariant := rr_muA_right I (muF I)
instance gf_disc : DiscreteTopology (rr_GF I) := Formalism.L2.SG.Pf.gf_discrete I

theorem exists_fund : ∃ F : Set I.GA, MeasurableSet F ∧ (∀ y, ∃ γ ∈ rr_GF I, γ * y ∈ F) ∧
    ∀ x ∈ F, ∀ γ ∈ rr_GF I, γ * x ∈ F → γ = 1 :=
  Formalism.L2.SG.Pf.exists_strictFund (rr_GF I)

def fundF : Set I.GA := (exists_fund I).choose

theorem fundF_spec : MeasurableSet (fundF I) ∧ (∀ y, ∃ γ ∈ rr_GF I, γ * y ∈ fundF I) ∧
    ∀ x ∈ fundF I, ∀ γ ∈ rr_GF I, γ * x ∈ fundF I → γ = 1 := (exists_fund I).choose_spec

theorem fundF_isFund (μf : Measure I.Gf) [SigmaFinite μf] : I.IsFundDom (I.muA μf) (fundF I) := by
  obtain ⟨h1, h2, h3⟩ := fundF_spec I
  refine ⟨h1, fun y => h2 y, fun γ hγ hne => ?_⟩
  have : (fun y => γ * y) '' fundF I ∩ fundF I = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨x, hx, rfl⟩ hz
    exact hne (h3 x hx γ hγ hz)
  rw [this, measure_empty]

theorem fundF_FD : rr_FD (I.muA (muF I)) (rr_GF I) (fundF I) := rr_FD_of I (muF I) (fundF I) (fundF_isFund I (muF I))

theorem exists_rep : ∃ r : I.GA → I.GA, Measurable r ∧ ∀ y, ∃ γ ∈ rr_GF I, r y = γ * y ∧ γ * y ∈ fundF I :=
  rr_exists_meas_rep (fundF_FD I)

def repF : I.GA → I.GA := (exists_rep I).choose

theorem repF_meas : Measurable (repF I) := (exists_rep I).choose_spec.1
theorem repF_spec (y : I.GA) : ∃ γ ∈ rr_GF I, repF I y = γ * y ∧ γ * y ∈ fundF I := (exists_rep I).choose_spec.2 y

theorem rep_ae (g : I.GA) :
    (fun x => I.rep (fundF I) (x * g)) =ᵐ[(I.muA (muF I)).restrict (fundF I)] fun x => repF I (x * g) :=
  ae_restrict_of_ae (rr_rep_ae_eq (fundF_FD I) (repF_spec I) g)

theorem repF_mp (g : I.GA) : MeasurePreserving (fun x => repF I (x * g))
    ((I.muA (muF I)).restrict (fundF I)) ((I.muA (muF I)).restrict (fundF I)) := by
  obtain ⟨_, h2⟩ := rr_map (fundF_FD I) g
  refine ⟨(repF_meas I).comp (measurable_mul_const g), ?_⟩
  rw [← Measure.map_congr (rep_ae I g)]
  exact h2

def regR (g : I.GA) : I.L2 (muF I) (fundF I) →L[ℂ] I.L2 (muF I) (fundF I) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => repF I (x * g)) (repF_mp I g)).toContinuousLinearMap

theorem regR_spec : I.IsRightReg (muF I) (fundF I) (regR I) := by
  intro g Fv
  have h1 := Lp.coeFn_compMeasurePreserving Fv (repF_mp I g)
  have h2 : (fun x => (Fv : I.GA → ℂ) (repF I (x * g))) =ᵐ[(I.muA (muF I)).restrict (fundF I)]
      fun x => (Fv : I.GA → ℂ) (I.rep (fundF I) (x * g)) := by
    filter_upwards [rep_ae I g] with x hx
    rw [hx]
  exact h1.trans h2

theorem regR_iso (g : I.GA) (x : I.L2 (muF I) (fundF I)) : ‖regR I g x‖ = ‖x‖ := by
  unfold regR
  exact LinearIsometry.norm_map _ x

theorem regR_meas (x y : I.L2 (muF I) (fundF I)) : StronglyMeasurable fun g => ⟪x, regR I g y⟫_ℂ :=
  rr_weak_meas (fundF_FD I) (regR_spec I) x y

instance secondCountable_L2_fundamental : SecondCountableTopology (I.L2 (muF I) (fundF I)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

end Formalism.L2.SG.Pf.BunM

namespace Formalism.L2.SG.Pf.BunM

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem exists_opInt (π : G → (H →L[ℂ] H)) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) (f : G → ℂ) (hf : Integrable f μ) :
    ∃ T : H →L[ℂ] H, ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, f g * ⟪x, π g y⟫_ℂ ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun v => rrd_vec μ π f v
      map_add' := fun a b => by
        unfold rrd_vec
        rw [← integral_add (rrd_int hiso hmeas hf a) (rrd_int hiso hmeas hf b)]
        congr 1; funext g; rw [map_add, smul_add]
      map_smul' := fun c a => by
        unfold rrd_vec
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext g; rw [map_smul, smul_comm] }
  refine ⟨L.mkContinuous (∫ g, ‖f g‖ ∂μ) fun v => ?_, fun x y => ?_⟩
  · show ‖rrd_vec μ π f v‖ ≤ _
    unfold rrd_vec
    calc ‖∫ g, f g • π g v ∂μ‖ ≤ ∫ g, ‖f g‖ * ‖v‖ ∂μ := by
          refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (Eventually.of_forall fun g => ?_)
          rw [norm_smul, hiso]
      _ = (∫ g, ‖f g‖ ∂μ) * ‖v‖ := integral_mul_const _ _
  · exact rrd_inner_vec hiso hmeas hf x y

end Formalism.L2.SG.Pf.BunM

end PartM

section PartD

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.BunD

theorem b_gap (R : Ranks) (P : HCParam R) {h : ℚ} (hh : 0 ≤ h)
    (hb : ∀ (j : Fin R.m) (hj : j.1 + 1 < R.m), h ≤ P.b ⟨j.1 + 1, hj⟩ - P.b j) :
    ∀ (d : ℕ) (i : Fin R.m) (hi : i.1 + d + 1 < R.m), h ≤ P.b ⟨i.1 + d + 1, hi⟩ - P.b i := by
  intro d
  induction d with
  | zero => intro i hi; simpa using hb i (by omega)
  | succ d ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := hb ⟨i.1 + d + 1, by omega⟩ (by simp only; omega)
    have e1 : (⟨i.1 + (d + 1) + 1, hi⟩ : Fin R.m) =
        ⟨(⟨i.1 + d + 1, by omega⟩ : Fin R.m).1 + 1, by simp only; omega⟩ := by
      ext; simp only; omega
    rw [e1]
    linarith

theorem b_lt (R : Ranks) (P : HCParam R) {h : ℚ} (hh : 0 ≤ h)
    (hb : ∀ (j : Fin R.m) (hj : j.1 + 1 < R.m), h ≤ P.b ⟨j.1 + 1, hj⟩ - P.b j) (i j : Fin R.m) (hij : i < j) :
    h ≤ P.b j - P.b i := by
  have hij' : i.1 < j.1 := hij
  have := b_gap R P hh hb (j.1 - i.1 - 1) i (by omega)
  have e : (⟨i.1 + (j.1 - i.1 - 1) + 1, by omega⟩ : Fin R.m) = j := Fin.ext (by simp only; omega)
  rw [e] at this
  exact this

theorem u_anti (R : Ranks) (P : HCParam R) : ∀ (d : ℕ) (i : Fin R.k) (hi : i.1 + d < R.k),
    P.u ⟨i.1 + d, hi⟩ ≤ P.u i := by
  intro d
  induction d with
  | zero => intro i hi; exact le_refl _
  | succ d ih =>
    intro i hi
    have h1 : P.u ⟨i.1 + d, by omega⟩ ≤ P.u i := ih i (by omega)
    have h2 : P.u ⟨i.1 + d + 1, by omega⟩ < P.v ⟨i.1 + d, by omega⟩ := P.v_gt_u ⟨i.1 + d, by omega⟩
    have h3 : P.v ⟨i.1 + d, by omega⟩ < P.u ⟨i.1 + d, by omega⟩ := P.u_gt_v ⟨i.1 + d, by omega⟩
    show P.u ⟨i.1 + d + 1, by omega⟩ ≤ P.u i
    linarith

theorem v_gt (R : Ranks) (P : HCParam R) (i : Fin (R.k - 1)) : -P.b ⟨0, by have := R.two_le_m; omega⟩ < P.v i := by
  have hk : 0 < R.k := by have := i.2; omega
  have hm : 0 < R.m := by have := R.two_le_m; omega
  have h1 : -P.b ⟨0, hm⟩ < P.u ⟨R.k - 1, by omega⟩ := P.u_last_gt hk hm
  have h2 : P.u ⟨i.1 + 1, by omega⟩ < P.v i := P.v_gt_u i
  have h3 : P.u ⟨i.1 + 1 + (R.k - 1 - (i.1 + 1)), by omega⟩ ≤ P.u ⟨i.1 + 1, by omega⟩ :=
    u_anti R P (R.k - 1 - (i.1 + 1)) ⟨i.1 + 1, by omega⟩ (by simp only; omega)
  have e : (⟨i.1 + 1 + (R.k - 1 - (i.1 + 1)), by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ := by
    ext; simp only; omega
  rw [e] at h3
  linarith

theorem gap_lamS (R : Ranks) (P : HCParam R) {h : ℚ} (hh : 0 ≤ h)
    (hb : ∀ (j : Fin R.m) (hj : j.1 + 1 < R.m), h ≤ P.b ⟨j.1 + 1, hj⟩ - P.b j) :
    Formalism.QuantumDeterminants.GapAtLeast (epsS R) (lamS R P) (h : ℝ) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hr : R.r = R.k + R.m - 1 := rfl

  have mixed : ∀ (a : Fin (R.k - 1)) (j : Fin R.m), 0 < j.1 → (h : ℝ) ≤ |(P.v a : ℝ) - (-(P.b j : ℝ))| := by
    intro a j hj
    have h1 := v_gt R P a
    have h2 := b_lt R P hh hb ⟨0, by omega⟩ j (Fin.lt_def.2 (by simp only; omega))
    have h3 : (h : ℝ) ≤ (P.v a : ℝ) - (-(P.b j : ℝ)) := by
      have : h ≤ P.v a - -P.b j := by linarith
      exact_mod_cast this
    exact h3.trans (le_abs_self _)
  have bb : ∀ j j' : Fin R.m, j ≠ j' → (h : ℝ) ≤ |(-(P.b j : ℝ)) - (-(P.b j' : ℝ))| := by
    intro j j' hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := b_lt R P hh hb j j' hl
      have : h ≤ -P.b j - -P.b j' := by linarith
      have h1 : (h : ℝ) ≤ (-(P.b j : ℝ)) - (-(P.b j' : ℝ)) := by exact_mod_cast this
      exact h1.trans (le_abs_self _)
    · have := b_lt R P hh hb j' j hl
      have : h ≤ -(-P.b j - -P.b j') := by linarith
      have h1 : (h : ℝ) ≤ -((-(P.b j : ℝ)) - (-(P.b j' : ℝ))) := by exact_mod_cast this
      exact h1.trans (neg_le_abs _)
  intro a b hab
  unfold epsS at hab
  unfold lamS
  by_cases ha : a.1 < R.k - 1 <;> by_cases hb' : b.1 < R.k - 1
  · simp [ha, hb'] at hab
  · have hbm : b.1 - (R.k - 1) < R.m := by have := b.isLt; omega
    simp only [ha, hb', if_true, if_false, dif_pos, dif_neg, not_false_eq_true, hbm] at hab ⊢
    have hodd : 0 < b.1 - (R.k - 1) := by
      by_contra h0
      have : b.1 - (R.k - 1) = 0 := by omega
      simp [this] at hab
    exact mixed ⟨a.1, ha⟩ ⟨b.1 - (R.k - 1), hbm⟩ hodd
  · have ham : a.1 - (R.k - 1) < R.m := by have := a.isLt; omega
    simp only [ha, hb', if_true, if_false, dif_pos, dif_neg, not_false_eq_true, ham] at hab ⊢
    have hodd : 0 < a.1 - (R.k - 1) := by
      by_contra h0
      have : a.1 - (R.k - 1) = 0 := by omega
      simp [this] at hab
    rw [abs_sub_comm]
    exact mixed ⟨b.1, hb'⟩ ⟨a.1 - (R.k - 1), ham⟩ hodd
  · have ham : a.1 - (R.k - 1) < R.m := by have := a.isLt; omega
    have hbm : b.1 - (R.k - 1) < R.m := by have := b.isLt; omega
    simp only [ha, hb', if_false, dif_neg, not_false_eq_true, ham, hbm] at hab ⊢
    refine bb _ _ fun e => hab ?_
    have := congrArg Fin.val e
    simp only at this
    rw [this]

theorem hc_cast {n m : ℕ} (h : n = m) {lam : Fin m → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin n => lam (Fin.cast h i)) := by
  subst h
  exact hl

theorem gap_cast {n m : ℕ} (h : n = m) {ε : Fin m → Bool} {lam : Fin m → ℝ} {c : ℝ}
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam c) :
    Formalism.QuantumDeterminants.GapAtLeast (fun i : Fin n => ε (Fin.cast h i)) (fun i : Fin n => lam (Fin.cast h i)) c := by
  subst h
  exact hg

theorem two_rS_add_two (D : D7) : 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  simp only [Ranks.rS]; omega

def v48 (D : D7) (τ : D.what₂.Tau) : Fin (D.R.k - 1) → ℝ := fun i => ((D.hc τ).v i : ℝ)

def b48 (D : D7) (τ : D.what₂.Tau) : Fin (2 * D.R.rS + 2) → ℝ :=
  fun j => ((D.hc τ).b (Fin.cast (two_rS_add_two D) j) : ℝ)

theorem lambda_highest_weight_eq (D : D7) (τ : D.what₂.Tau) (i : Fin (2 * D.R.rS + D.R.k + 1)) :
    Formalism.MainNotions.CayleySignature.lam48 D.R.k D.R.rS (v48 D τ) (b48 D τ) i = lamS D.R (D.hc τ) (Fin.cast (dimS_eq D.R) i) := by
  have hm := two_rS_add_two D
  have hk := D.R.m_add_three_le_k
  have hi := i.isLt
  by_cases h : i.val < D.R.k - 1
  · simp [Formalism.MainNotions.CayleySignature.lam48, lamS, v48, h]
  · have h' : i.val - (D.R.k - 1) < D.R.m := by omega
    simp [Formalism.MainNotions.CayleySignature.lam48, lamS, b48, h, h']

theorem epsilon_signature_eq (D : D7) (i : Fin (2 * D.R.rS + D.R.k + 1)) :
    Formalism.MainNotions.CayleySignature.eps48 D.R.k D.R.rS i = epsS D.R (Fin.cast (dimS_eq D.R) i) := by
  simp [Formalism.MainNotions.CayleySignature.eps48, epsS]

theorem gapBig_of (D : D7) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (τ : D.what₂.Tau) :
    Formalism.MainNotions.CayleySignature.GapBig D.R.k D.R.rS (b48 D τ) := by
  have hm : D.R.m = 2 * D.R.rS + 2 := (two_rS_add_two D).symm
  obtain ⟨hr, hgap⟩ := hG
  have hdim : 2 * D.R.rS + D.R.k + 1 = D.R.r := Formalism.MainNotions.S.dimS_eq D.R
  have hrk : Formalism.MainNotions.CayleySignature.rk48 D.R.k D.R.rS = D.R.r := by
    unfold Formalism.MainNotions.CayleySignature.rk48; omega
  refine ⟨2 * D.R.r + 7, ⟨D.R.r + 3, by ring⟩, ?_, ?_, ?_⟩
  · rw [hrk]; omega
  · rw [hrk]; omega
  · intro j hj
    have hj' : (Fin.cast hm.symm j).val + 1 < D.R.m := by simp; omega
    have h1 := hgap τ (Fin.cast hm.symm j) hj'
    have e1 : (Fin.cast hm.symm (⟨j.val + 1, hj⟩ : Fin (2 * D.R.rS + 2))) =
        ⟨(Fin.cast hm.symm j).val + 1, hj'⟩ := by ext; simp
    show 2 * ((Formalism.MainNotions.CayleySignature.rk48 D.R.k D.R.rS + (2 * D.R.rS + 2) * (2 * D.R.r + 7) : ℕ) : ℝ) ^ 3
        + ((2 * D.R.r + 7 : ℕ) : ℝ) + 3 <
      ((D.hc τ).b (Fin.cast hm.symm ⟨j.val + 1, hj⟩) : ℝ) - ((D.hc τ).b (Fin.cast hm.symm j) : ℝ)
    rw [e1]
    have h2 : 16 * (D.R.r : ℝ) ^ 19 ≤
        ((D.hc τ).b ⟨(Fin.cast hm.symm j).val + 1, hj'⟩ : ℝ) - ((D.hc τ).b (Fin.cast hm.symm j) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    have hk3 := D.R.m_add_three_le_k
    have hmle : 2 * D.R.rS + 2 ≤ D.R.r := by omega
    have hN : Formalism.MainNotions.CayleySignature.rk48 D.R.k D.R.rS + (2 * D.R.rS + 2) * (2 * D.R.r + 7) ≤ 3 * D.R.r ^ 2 := by
      rw [hrk]
      have : (2 * D.R.rS + 2) * (2 * D.R.r + 7) ≤ D.R.r * (2 * D.R.r + 7) := Nat.mul_le_mul_right _ hmle
      nlinarith
    have hNR : ((Formalism.MainNotions.CayleySignature.rk48 D.R.k D.R.rS + (2 * D.R.rS + 2) * (2 * D.R.r + 7) : ℕ) : ℝ)
        ≤ 3 * (D.R.r : ℝ) ^ 2 := by exact_mod_cast hN
    have hR : (1801 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hr
    set R : ℝ := (D.R.r : ℝ) with hRdef
    have hN0 : (0 : ℝ) ≤ ((Formalism.MainNotions.CayleySignature.rk48 D.R.k D.R.rS + (2 * D.R.rS + 2) * (2 * D.R.r + 7) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hcube : ((Formalism.MainNotions.CayleySignature.rk48 D.R.k D.R.rS + (2 * D.R.rS + 2) * (2 * D.R.r + 7) : ℕ) : ℝ) ^ 3
        ≤ (3 * R ^ 2) ^ 3 := pow_le_pow_left₀ hN0 hNR 3
    have ht : ((2 * D.R.r + 7 : ℕ) : ℝ) = 2 * R + 7 := by push_cast; ring
    rw [ht]
    have hR1 : (1 : ℝ) ≤ R := by linarith
    have hR6 : R ≤ R ^ 6 := by
      calc R = R ^ 1 := (pow_one R).symm
        _ ≤ R ^ 6 := pow_le_pow_right₀ hR1 (by norm_num)
    have hR13 : (1801 : ℝ) ≤ R ^ 13 := by
      calc (1801 : ℝ) ≤ R := hR
        _ = R ^ 1 := (pow_one R).symm
        _ ≤ R ^ 13 := pow_le_pow_right₀ hR1 (by norm_num)
    have hR6pos : (0 : ℝ) ≤ R ^ 6 := by positivity
    have h19 : R ^ 19 = R ^ 6 * R ^ 13 := by ring
    have hbig : 1801 * R ^ 6 ≤ R ^ 19 := by rw [h19]; nlinarith
    have h3 : (3 * R ^ 2) ^ 3 = 27 * R ^ 6 := by ring
    nlinarith

theorem coef_cont {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hds : IsDS ε lam σ) (w : H) :
    Continuous fun g : Formalism.REAL.UJ ε => ⟪w, σ (uMat g) w⟫_ℂ := by
  have hU := hds.2.2.1
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hmem : ∀ g : Formalism.REAL.UJ ε, uMat g ∈ UJset ε := fun g => g.2
  have h2 : Continuous fun g : Formalism.REAL.UJ ε => σ (uMat g) w :=
    (hU.2.2 w).comp_continuous hc hmem
  exact continuous_const.inner h2

theorem coef_int_gen (hC : CoefWeightedLoc) (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hp : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b)) (hg : Formalism.MainNotions.CayleySignature.GapBig k r b) :
    ∀ (N : ℕ) (hN : 2 * r + k + 1 = N) (ε : Fin N → Bool) (lam : Fin N → ℝ),
      (∀ i, ε i = Formalism.MainNotions.CayleySignature.eps48 k r (Fin.cast hN.symm i)) →
      (∀ i, lam i = Formalism.MainNotions.CayleySignature.lam48 k r v b (Fin.cast hN.symm i)) →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ w : H, IsLowUnit ε lam σ w →
        Integrable (fun g : Formalism.REAL.UJ ε => ⟪w, σ (uMat g) w⟫_ℂ) (Formalism.REAL.muG ε) := by
  intro N hN ε lam hε hl H _ _ σ hds w hw
  subst hN
  have e1 : ε = Formalism.MainNotions.CayleySignature.eps48 k r := funext fun i => by simpa using hε i
  have e2 : lam = Formalism.MainNotions.CayleySignature.lam48 k r v b := funext fun i => by simpa using hl i
  subst e1 e2
  have hwt := hC k r v b hp hg H σ hds w hw
  refine ⟨(coef_cont hds w).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hwt
  have h1 : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (uMat g)‖ ^
      (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))) :=
    Real.one_le_rpow (Formalism.L2.SG.WuDecayPf.one_le_opn (by omega) g) (by positivity)
  calc ‖⟪w, σ (uMat g) w⟫_ℂ‖ₑ = ‖⟪w, σ (uMat g) w⟫_ℂ‖ₑ * 1 := (mul_one _).symm
    _ ≤ _ := by
      gcongr
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1

end Formalism.L2.SG.Pf.BunD

end PartD

section PartA

open MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence
open scoped ComplexOrder TensorProduct Classical

namespace Formalism.L2.SG.Pf.BunA

variable (I : AutInst) (g : ℕ) {ψ : I.E ⊗[I.F] Af I.F → ℂ} {r k : ℕ}
  (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)

structure FrameOK (ψ : I.E ⊗[I.F] Af I.F → ℂ) : Prop where
  hg : g ≠ 0
  hadd : ∀ x y, ψ (x + y) = ψ x * ψ y
  hint : ∀ x ∈ IntAf I.F I.E, ψ x = 1
  he0 : ∀ a, e0 a ∈ I.Lf
  hf0 : ∀ a, f0 a ∈ I.Lf
  hz0 : z0 ∈ I.Lf
  hbw : ∀ i, bw i ∈ I.Lf
  hbwd : ∀ i, bwd i ∈ I.Lf
  hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b))
  hfz : ∀ a, ZMod' I g (hA I (f0 a) z0)
  hbe : ∀ i a, ZMod' I g (hA I (bwd i) (e0 a))
  hbb : ∀ i j : Fin k, i ≠ j → ZMod' I g (hA I (bwd i) (bw j))

variable {I g e0 f0 z0 bw bwd}

theorem unit_mul_star {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  show z * (starRingEnd ℂ) z = 1
  rw [RCLike.mul_conj, hz]
  simp

section Grp

variable (h : FrameOK I g e0 f0 z0 bw bwd ψ)
include h

theorem level_subgroup_one_mem : (1 : I.Gf) ∈ K2set I g e0 z0 bw := ⟨K_one _, cong_one _ _ _ _ _⟩

theorem level_subgroup_mul_mem {x y : I.Gf} (hx : x ∈ K2set I g e0 z0 bw) (hy : y ∈ K2set I g e0 z0 bw) :
    x * y ∈ K2set I g e0 z0 bw := ⟨K_mul _ hx.1 hy.1, cong_mul _ _ _ _ _ hx.1 hx.2 hy.2⟩

theorem level_subgroup_inv_mem {x : I.Gf} (hx : x ∈ K2set I g e0 z0 bw) : x⁻¹ ∈ K2set I g e0 z0 bw :=
  ⟨K_inv _ hx.1, cong_inv _ _ _ _ _ hx.1 hx.2⟩

theorem chi_mul {x y : I.Gf} (hx : x ∈ K2set I g e0 z0 bw) (hy : y ∈ K2set I g e0 z0 bw) :
    chi2f I ψ g e0 f0 z0 bw bwd (x * y) = chi2f I ψ g e0 f0 z0 bw bwd x * chi2f I ψ g e0 f0 z0 bw bwd y :=
  psi_mul_of_Z _ _ h.hadd h.hint h.hg
    (Afun_mul _ _ _ _ _ _ _ hx.1 hx.2 hy.2 h.hf0 h.hbwd h.hfe h.hfz h.hbe h.hbb)

theorem chi_norm {x : I.Gf} (hx : x ∈ K2set I g e0 z0 bw) : ‖chi2f I ψ g e0 f0 z0 bw bwd x‖ = 1 :=
  psi_norm _ _ h.hadd h.hint h.hg (Afun_int _ _ _ _ _ _ hx.1 h.he0 h.hf0 h.hz0 h.hbw h.hbwd)

theorem principal_congruence_le_level {x : I.Gf} (hx : x ∈ I.Kg g) : x ∈ K2set I g e0 z0 bw ∧ chi2f I ψ g e0 f0 z0 bw bwd x = 1 :=
  ⟨⟨hx.1, cong_Kg _ _ _ _ _ hx h.he0 h.hz0 h.hbw⟩,
    psi_Z _ _ h.hadd h.hint h.hg (Afun_Kg _ _ _ _ _ _ _ hx h.he0 h.hf0 h.hz0 h.hbw h.hbwd h.hfe h.hfz h.hbb)⟩

theorem kg_open : IsOpen (I.Kg g) := I.topf_open g (Nat.one_le_iff_ne_zero.2 h.hg)

theorem kg_one : (1 : I.Gf) ∈ I.Kg g :=
  ⟨K_one _, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩

theorem chi_one : chi2f I ψ g e0 f0 z0 bw bwd 1 = 1 := (principal_congruence_le_level h (kg_one h)).2

theorem chi_inv {x : I.Gf} (hx : x ∈ K2set I g e0 z0 bw) :
    chi2f I ψ g e0 f0 z0 bw bwd x⁻¹ = star (chi2f I ψ g e0 f0 z0 bw bwd x) := by
  have h1 := chi_mul h (level_subgroup_inv_mem h hx) hx
  rw [inv_mul_cancel, chi_one h] at h1
  have h2 := unit_mul_star (chi_norm h hx)
  calc chi2f I ψ g e0 f0 z0 bw bwd x⁻¹
      = chi2f I ψ g e0 f0 z0 bw bwd x⁻¹ * (chi2f I ψ g e0 f0 z0 bw bwd x *
          star (chi2f I ψ g e0 f0 z0 bw bwd x)) := by rw [h2, mul_one]
    _ = star (chi2f I ψ g e0 f0 z0 bw bwd x) := by rw [← mul_assoc, ← h1, one_mul]

theorem level_subgroup_isOpen : IsOpen (K2set I g e0 z0 bw) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hc : Continuous fun y : I.Gf => x⁻¹ * y := continuous_const.mul continuous_id
  have hn : (fun y : I.Gf => x⁻¹ * y) ⁻¹' I.Kg g ∈ 𝓝 x :=
    hc.continuousAt.preimage_mem_nhds (by simpa using (kg_open h).mem_nhds (kg_one h))
  refine Filter.mem_of_superset hn fun y hy => ?_
  have := level_subgroup_mul_mem h hx (principal_congruence_le_level h hy).1
  simpa using this

end Grp

section Idem

variable (μf : Measure I.Gf)

def eF (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (μf : Measure I.Gf) (ψ : I.E ⊗[I.F] Af I.F → ℂ) : I.Gf → ℂ := fun x =>
  if x ∈ K2set I g e0 z0 bw then star (chi2f I ψ g e0 f0 z0 bw bwd x) / ((μf (K2set I g e0 z0 bw)).toReal : ℂ)
  else 0

local notation "𝔢" => eF I g e0 f0 z0 bw bwd μf ψ

variable (h : FrameOK I g e0 f0 z0 bw bwd ψ)
include h

theorem eF_inv (x : I.Gf) : 𝔢 x⁻¹ = star (𝔢 x) := by
  unfold eF
  by_cases hx : x ∈ K2set I g e0 z0 bw
  · rw [if_pos (level_subgroup_inv_mem h hx), if_pos hx, chi_inv h hx, star_div₀, star_star, Complex.star_def, Complex.conj_ofReal]
  · have : x⁻¹ ∉ K2set I g e0 z0 bw := fun h' => hx (by simpa using level_subgroup_inv_mem h h')
    rw [if_neg this, if_neg hx, star_zero]

theorem eF_bi (x : I.Gf) (k : I.Gf) (hk : k ∈ I.Kg g) (k' : I.Gf) (hk' : k' ∈ I.Kg g) :
    𝔢 (k * x * k') = 𝔢 x := by
  have hk2 := principal_congruence_le_level h hk
  have hk2' := principal_congruence_le_level h hk'
  by_cases hx : x ∈ K2set I g e0 z0 bw
  · have hm : k * x * k' ∈ K2set I g e0 z0 bw := level_subgroup_mul_mem h (level_subgroup_mul_mem h hk2.1 hx) hk2'.1
    simp only [eF, if_pos hm, if_pos hx, chi_mul h (level_subgroup_mul_mem h hk2.1 hx) hk2'.1, chi_mul h hk2.1 hx, hk2.2, hk2'.2,
      one_mul, mul_one]
  · have hm : k * x * k' ∉ K2set I g e0 z0 bw := fun hm => hx (by
      have := level_subgroup_mul_mem h (level_subgroup_mul_mem h (level_subgroup_inv_mem h hk2.1) hm) (level_subgroup_inv_mem h hk2'.1)
      simpa [mul_assoc] using this)
    simp only [eF, if_neg hm, if_neg hx]

theorem eF_supp (x : I.Gf) (hx : 𝔢 x ≠ 0) : x ∈ I.Kset := by
  by_contra hK
  have : x ∉ K2set I g e0 z0 bw := fun h' => hK h'.1
  exact hx (by simp only [eF, if_neg this])

theorem eF_lc : IsLocallyConstant (𝔢) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : I.Gf => x⁻¹ * y := continuous_const.mul continuous_id
  have hn : (fun y : I.Gf => x⁻¹ * y) ⁻¹' I.Kg g ∈ 𝓝 x :=
    hc.continuousAt.preimage_mem_nhds (by simpa using (kg_open h).mem_nhds (kg_one h))
  filter_upwards [hn] with y hy
  have e := eF_bi μf h x 1 (kg_one h) (x⁻¹ * y) hy
  rwa [one_mul, mul_inv_cancel_left] at e

theorem eF_conv (hpos : 0 < μf (K2set I g e0 z0 bw)) (hfin : μf (K2set I g e0 z0 bw) < ⊤) :
    I.convF μf (𝔢) (𝔢) = 𝔢 := by
  funext x
  unfold AutInst.convF
  set V : ℝ := (μf (K2set I g e0 z0 bw)).toReal with hVdef
  have hV : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  have key : (fun y => 𝔢 y * 𝔢 (y⁻¹ * x)) =
      Set.indicator (K2set I g e0 z0 bw) (fun _ => 𝔢 x / (V : ℂ)) := by
    funext y
    by_cases hy : y ∈ K2set I g e0 z0 bw
    · rw [Set.indicator_of_mem hy]
      by_cases hx : x ∈ K2set I g e0 z0 bw
      · have hyx : y⁻¹ * x ∈ K2set I g e0 z0 bw := level_subgroup_mul_mem h (level_subgroup_inv_mem h hy) hx
        simp only [eF, if_pos hy, if_pos hyx, if_pos hx]
        have hc : chi2f I ψ g e0 f0 z0 bw bwd x =
            chi2f I ψ g e0 f0 z0 bw bwd y * chi2f I ψ g e0 f0 z0 bw bwd (y⁻¹ * x) := by
          rw [← chi_mul h hy hyx, mul_inv_cancel_left]
        rw [hc, star_mul', ← hVdef]
        field_simp
      · have hyx : y⁻¹ * x ∉ K2set I g e0 z0 bw := fun h' => hx (by simpa using level_subgroup_mul_mem h hy h')
        simp only [eF, if_neg hyx, if_neg hx, mul_zero, zero_div]
    · rw [Set.indicator_of_notMem hy]; simp only [eF, if_neg hy, zero_mul]
  rw [key, integral_indicator_const _ (level_subgroup_isOpen h).measurableSet, measureReal_def, ← hVdef, Complex.real_smul]
  field_simp

theorem fib_sum_nonneg {m : ℕ} (ρ : Fin m → Fin m) (a : Fin m → ℂ) :
    0 ≤ ∑ i, ∑ j, (if ρ i = ρ j then star (a i) * a j else 0) := by
  have key : ∀ i j, (if ρ i = ρ j then star (a i) * a j else 0) =
      ∑ c, star (if ρ i = c then a i else 0) * (if ρ j = c then a j else 0) := by
    intro i j
    by_cases hij : ρ i = ρ j
    · rw [if_pos hij, Finset.sum_eq_single (ρ i)]
      · simp [hij]
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    · rw [if_neg hij]
      symm
      apply Finset.sum_eq_zero
      intro c _
      by_cases h1 : ρ i = c
      · have h2 : ¬ ρ j = c := fun h2 => hij (h1.trans h2.symm)
        simp [h2]
      · simp [h1]
  calc (0 : ℂ) ≤ ∑ c, star (∑ i, if ρ i = c then a i else 0) * (∑ j, if ρ j = c then a j else 0) :=
        Finset.sum_nonneg fun c _ => star_mul_self_nonneg _
    _ = ∑ i, ∑ j, (if ρ i = ρ j then star (a i) * a j else 0) := by
        simp_rw [key, star_sum, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem eF_pos (hpos : 0 < μf (K2set I g e0 z0 bw)) (hfin : μf (K2set I g e0 z0 bw) < ⊤) :
    I.IsPosType 𝔢 := by
  intro m x c
  let rel : Fin m → Fin m → Prop := fun i j => (x i)⁻¹ * x j ∈ K2set I g e0 z0 bw
  have hrefl : ∀ i, rel i i := fun i => by
    show (x i)⁻¹ * x i ∈ _
    rw [inv_mul_cancel]; exact level_subgroup_one_mem h
  have hsymm : ∀ i j, rel i j → rel j i := fun i j hij => by
    have := level_subgroup_inv_mem h hij
    simpa [rel, mul_inv_rev] using this
  have htrans : ∀ i j l, rel i j → rel j l → rel i l := fun i j l a b => by
    have := level_subgroup_mul_mem h a b
    simpa [rel, mul_assoc] using this
  let ρ : Fin m → Fin m := fun i =>
    (Finset.univ.filter fun j => rel j i).min' ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hrefl i⟩⟩
  have hρ : ∀ i, rel (ρ i) i := fun i => by
    have := Finset.min'_mem (Finset.univ.filter fun j => rel j i) ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hrefl i⟩⟩
    exact (Finset.mem_filter.1 this).2
  have hρeq : ∀ i j, rel i j → ρ i = ρ j := by
    intro i j hij
    have hs : (Finset.univ.filter fun l => rel l i) = Finset.univ.filter fun l => rel l j := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun a => htrans _ _ _ a hij, fun a => htrans _ _ _ a (hsymm _ _ hij)⟩
    show Finset.min' _ _ = Finset.min' _ _
    congr 1
  have hrel : ∀ i j, rel i j ↔ ρ i = ρ j := fun i j =>
    ⟨hρeq i j, fun e => htrans _ _ _ (hsymm _ _ (hρ i)) (e ▸ hρ j)⟩
  let kk : Fin m → I.Gf := fun i => (x (ρ i))⁻¹ * x i
  have hkk : ∀ i, kk i ∈ K2set I g e0 z0 bw := hρ
  have hxx : ∀ i j, ρ i = ρ j → (x i)⁻¹ * x j = (kk i)⁻¹ * kk j := by
    intro i j e
    simp only [kk, e, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  set V : ℝ := (μf (K2set I g e0 z0 bw)).toReal with hVdef
  let a : Fin m → ℂ := fun i => c i * star (chi2f I ψ g e0 f0 z0 bw bwd (kk i))
  have hterm : ∀ i j, star (c i) * c j * 𝔢 ((x i)⁻¹ * x j) =
      (if ρ i = ρ j then star (a i) * a j else 0) * ((V⁻¹ : ℝ) : ℂ) := by
    intro i j
    by_cases e : ρ i = ρ j
    · have hin : (x i)⁻¹ * x j ∈ K2set I g e0 z0 bw := (hrel i j).2 e
      rw [if_pos e]
      simp only [eF, if_pos hin]
      rw [hxx i j e, chi_mul h (level_subgroup_inv_mem h (hkk i)) (hkk j), chi_inv h (hkk i), ← hVdef]
      simp only [a, star_mul', star_star]
      push_cast
      ring
    · have hin : (x i)⁻¹ * x j ∉ K2set I g e0 z0 bw := fun h' => e ((hrel i j).1 h')
      rw [if_neg e]
      simp only [eF, if_neg hin]
      ring
  simp_rw [hterm, ← Finset.sum_mul]
  refine mul_nonneg (fib_sum_nonneg h ρ a) ?_
  exact Complex.zero_le_real.2 (inv_nonneg.2 ENNReal.toReal_nonneg)

end Idem

end Formalism.L2.SG.Pf.BunA

end PartA

section PartU

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.BunEx

def UnipCore : Prop :=
  ∀ (I : AutInst) (g g₀ : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : I.E ⊗[I.F] Af I.F),
    0 < g → g₀ ∣ g → 2 * r + k + 1 ≤ I.n →
    ((∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf) →
    (∀ a b, ZMod' I g (hA I (e0 a) (e0 b)) ∧ ZMod' I g (hA I (f0 a) (f0 b)) ∧
      ZMod' I g (hA I (e0 a) (f0 b) - if a = b then 1 else 0)) →
    (ZMod' I g (hA I z0 z0 + 1) ∧ ∀ a, ZMod' I g (hA I (e0 a) z0) ∧ ZMod' I g (hA I (f0 a) z0)) →
    (∀ i, ZMod' I g (hA I z0 (bw i)) ∧ ZMod' I g (hA I z0 (bwd i)) ∧
      ∀ a, ZMod' I g (hA I (e0 a) (bw i)) ∧ ZMod' I g (hA I (f0 a) (bw i)) ∧
        ZMod' I g (hA I (e0 a) (bwd i)) ∧ ZMod' I g (hA I (f0 a) (bwd i))) →
    ew * ew = ew → ew * sigA I ew = 0 → ew ∈ IntAf I.F I.E →
    (∀ i, bw i = ew • bw i) → (∀ i, bwd i = sigA I ew • bwd i) →
    (∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)) →
    (∀ y ∈ I.Lf, InMod I g (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y) →
    ∀ x ∈ K2set I g e0 z0 bw, I.UnipMod g₀ x

namespace Unip

section H

variable (I : AutInst) (g : ℕ)

theorem hform_inv {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hdot : ∀ x y : n → A, Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [mulVec, dotProduct, map_sum, map_mul]
  rw [hdot, hdot, hσ, ← vecMul_transpose, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [show (M.map σ)ᵀ * J * M = J from hM]

theorem hA_fmat (x : I.Gf) (u v : VA I) : hA I (I.fmat x *ᵥ u) (I.fmat x *ᵥ v) = hA I u v :=
  hform_inv _ _ _ x.2 u v

theorem smul_Lf {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) {v : VA I} (hv : v ∈ I.Lf) : c • v ∈ I.Lf :=
  I.Lf.smul_mem (⟨c, hc⟩ : IntAf I.F I.E) hv

theorem smul_span {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) {S : Set (VA I)} {v : VA I}
    (hv : v ∈ S) : c • v ∈ Submodule.span (IntAf I.F I.E) S :=
  (Submodule.span (IntAf I.F I.E) S).smul_mem (⟨c, hc⟩ : IntAf I.F I.E) (Submodule.subset_span hv)

theorem Zv {c : I.E ⊗[I.F] Af I.F} (hc : ZMod' I g c) {v : VA I} (hv : v ∈ I.Lf) : c • v ∈ mL I g := by
  obtain ⟨t, ht, rfl⟩ := hc
  rw [mul_smul]; exact smul_mem_mL I (smul_Lf I ht hv)

theorem sumZ {ι : Type*} (s : Finset ι) (c : ι → I.E ⊗[I.F] Af I.F) (v : ι → VA I)
    (hc : ∀ i ∈ s, ZMod' I g (c i)) (hv : ∀ i ∈ s, v i ∈ I.Lf) : ∑ i ∈ s, c i • v i ∈ mL I g :=
  Submodule.sum_mem _ fun i hi => Zv I g (hc i hi) (hv i hi)

theorem sumLf {ι : Type*} (s : Finset ι) (c : ι → I.E ⊗[I.F] Af I.F) (v : ι → VA I)
    (hc : ∀ i ∈ s, c i ∈ IntAf I.F I.E) (hv : ∀ i ∈ s, v i ∈ I.Lf) : ∑ i ∈ s, c i • v i ∈ I.Lf :=
  Submodule.sum_mem _ fun i hi => smul_Lf I (hc i hi) (hv i hi)

theorem sumSpan {ι : Type*} (s : Finset ι) (c : ι → I.E ⊗[I.F] Af I.F) (v : ι → VA I) {S : Set (VA I)}
    (hc : ∀ i ∈ s, c i ∈ IntAf I.F I.E) (hv : ∀ i ∈ s, v i ∈ S) :
    ∑ i ∈ s, c i • v i ∈ Submodule.span (IntAf I.F I.E) S :=
  Submodule.sum_mem _ fun i hi => smul_span I (hc i hi) (hv i hi)

theorem Z_neg {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g c) : ZMod' I g (-c) := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨-t, neg_mem ht, by rw [mul_neg]⟩

theorem Z_swap {c d : I.E ⊗[I.F] Af I.F} (h : ZMod' I g (c - d)) : ZMod' I g (d - c) := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨-t, neg_mem ht, by rw [mul_neg, ← h, neg_sub]⟩

theorem Zleft {S : Set (VA I)} {u : VA I} (hu : u ∈ I.Lf) (hS : ∀ s ∈ S, ZMod' I g (hA I s u)) {v : VA I}
    (hv : v ∈ Mo I g S) : ZMod' I g (hA I v u) := by
  have h : Mo I g S ≤ Qs I g u := sup_le (Submodule.span_le.2 fun s hs => by
      show ZMod' I g (hA I u s)
      have := Z_sig I g (hS s hs)
      rwa [← hA_symm I s u] at this) (mL_Qs I g hu)
  have := Z_sig I g (h hv)
  rwa [← hA_symm I u v] at this

theorem hA_ew {ew : I.E ⊗[I.F] Af I.F} (horth : ew * sigA I ew = 0) (a b : VA I) :
    hA I (ew • a) (ew • b) = 0 := by
  rw [hA_smul_left, hA_smul_right]
  calc sigA I ew * (ew * hA I a b) = (ew * sigA I ew) * hA I a b := by ring
    _ = 0 := by rw [horth, zero_mul]

theorem hA_sew {ew : I.E ⊗[I.F] Af I.F} (horth : ew * sigA I ew = 0) (a b : VA I) :
    hA I (sigA I ew • a) (sigA I ew • b) = 0 := by
  rw [hA_smul_left, hA_smul_right, sigA_sigA]
  calc ew * (sigA I ew * hA I a b) = (ew * sigA I ew) * hA I a b := by ring
    _ = 0 := by rw [horth, zero_mul]

end H

section Exp

variable (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)

noncomputable def Rc (w : VA I) : VA I :=
  (∑ a, hA I (f0 a) w • e0 a) + (∑ a, hA I (e0 a) w • f0 a) - hA I z0 w • z0 +
    (∑ i, hA I (bwd i) w • bw i) + ∑ i, hA I (bw i) w • bwd i

private theorem hA_add_right_unitary_haar_products (I : AutInst) (u w w' : VA I) : hA I u (w + w') = hA I u w + hA I u w' := by
  unfold hA Formalism.UG.hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem Rc_add (w w' : VA I) : Rc I e0 f0 z0 bw bwd (w + w') = Rc I e0 f0 z0 bw bwd w + Rc I e0 f0 z0 bw bwd w' := by
  unfold Rc
  simp only [hA_add_right_unitary_haar_products, add_smul, Finset.sum_add_distrib]
  abel

private theorem hA_smul_right_unitary_haar_products (I : AutInst) (u : VA I) (c : I.E ⊗[I.F] Af I.F) (w : VA I) :
    hA I u (c • w) = c * hA I u w := by
  unfold hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Rc_smul (c : I.E ⊗[I.F] Af I.F) (w : VA I) :
    Rc I e0 f0 z0 bw bwd (c • w) = c • Rc I e0 f0 z0 bw bwd w := by
  unfold Rc
  simp only [hA_smul_right_unitary_haar_products, mul_smul, smul_add, smul_sub, Finset.smul_sum]

theorem Rc_Lf (hm : (∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf)
    {w : VA I} (hw : w ∈ I.Lf) : Rc I e0 f0 z0 bw bwd w ∈ I.Lf := by
  unfold Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sumLf I _ _ _ (fun a _ => hA_int I (hm.1 a).2 hw) (fun a _ => (hm.1 a).1)
  · exact sumLf I _ _ _ (fun a _ => hA_int I (hm.1 a).1 hw) (fun a _ => (hm.1 a).2)
  · exact smul_Lf I (hA_int I hm.2.1 hw) hm.2.1
  · exact sumLf I _ _ _ (fun i _ => hA_int I (hm.2.2 i).2 hw) (fun i _ => (hm.2.2 i).1)
  · exact sumLf I _ _ _ (fun i _ => hA_int I (hm.2.2 i).1 hw) (fun i _ => (hm.2.2 i).2)

theorem gen_ok (hm : (∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf)
    (u : VA I) (α β : Fin r → I.E ⊗[I.F] Af I.F) (γ : I.E ⊗[I.F] Af I.F) (δ ε : Fin k → I.E ⊗[I.F] Af I.F)
    (hu : u = (∑ a, α a • e0 a) + (∑ a, β a • f0 a) + γ • z0 + (∑ i, δ i • bw i) + ∑ i, ε i • bwd i)
    (hα : ∀ a, ZMod' I g (hA I (f0 a) u - α a)) (hβ : ∀ a, ZMod' I g (hA I (e0 a) u - β a))
    (hγ : ZMod' I g (-hA I z0 u - γ)) (hδ : ∀ i, ZMod' I g (hA I (bwd i) u - δ i))
    (hε : ∀ i, ZMod' I g (hA I (bw i) u - ε i)) :
    u - Rc I e0 f0 z0 bw bwd u ∈ mL I g := by
  have e1 : u - Rc I e0 f0 z0 bw bwd u =
      ((∑ a, α a • e0 a) + (∑ a, β a • f0 a) + γ • z0 + (∑ i, δ i • bw i) + ∑ i, ε i • bwd i) -
        Rc I e0 f0 z0 bw bwd u := by
    rw [← hu]
  have e2 : ((∑ a, α a • e0 a) + (∑ a, β a • f0 a) + γ • z0 + (∑ i, δ i • bw i) + ∑ i, ε i • bwd i) -
        Rc I e0 f0 z0 bw bwd u =
      (∑ a, (α a - hA I (f0 a) u) • e0 a) + (∑ a, (β a - hA I (e0 a) u) • f0 a) +
        (γ - -hA I z0 u) • z0 + (∑ i, (δ i - hA I (bwd i) u) • bw i) + ∑ i, (ε i - hA I (bw i) u) • bwd i := by
    simp only [Rc, sub_smul, neg_smul, Finset.sum_sub_distrib]
    abel
  rw [e1, e2]
  refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sumZ I g _ _ _ (fun a _ => Z_swap I g (hα a)) (fun a _ => (hm.1 a).1)
  · exact sumZ I g _ _ _ (fun a _ => Z_swap I g (hβ a)) (fun a _ => (hm.1 a).2)
  · exact Zv I g (Z_swap I g hγ) hm.2.1
  · exact sumZ I g _ _ _ (fun i _ => Z_swap I g (hδ i)) (fun i _ => (hm.2.2 i).1)
  · exact sumZ I g _ _ _ (fun i _ => Z_swap I g (hε i)) (fun i _ => (hm.2.2 i).2)

end Exp

section Main

variable {I : AutInst} {g : ℕ} {r k : ℕ} {e0 f0 : Fin r → VA I} {z0 : VA I} {bw bwd : Fin k → VA I}
  {ew : I.E ⊗[I.F] Af I.F}

structure FH (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : I.E ⊗[I.F] Af I.F) : Prop where
  mem : (∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf
  gram : ∀ a b, ZMod' I g (hA I (e0 a) (e0 b)) ∧ ZMod' I g (hA I (f0 a) (f0 b)) ∧
      ZMod' I g (hA I (e0 a) (f0 b) - if a = b then 1 else 0)
  zz : ZMod' I g (hA I z0 z0 + 1) ∧ ∀ a, ZMod' I g (hA I (e0 a) z0) ∧ ZMod' I g (hA I (f0 a) z0)
  W : ∀ i, ZMod' I g (hA I z0 (bw i)) ∧ ZMod' I g (hA I z0 (bwd i)) ∧
      ∀ a, ZMod' I g (hA I (e0 a) (bw i)) ∧ ZMod' I g (hA I (f0 a) (bw i)) ∧
        ZMod' I g (hA I (e0 a) (bwd i)) ∧ ZMod' I g (hA I (f0 a) (bwd i))
  orth : ew * sigA I ew = 0
  bw_w : ∀ i, bw i = ew • bw i
  bwd_w : ∀ i, bwd i = sigA I ew • bwd i
  dual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)
  span : ∀ y ∈ I.Lf, InMod I g (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y

theorem Zsym {u v : VA I} {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g (hA I u v - c)) :
    ZMod' I g (hA I v u - sigA I c) := by
  have := Z_sig I g h
  rwa [map_sub, ← hA_symm] at this

theorem Zsym0 {u v : VA I} (h : ZMod' I g (hA I u v)) : ZMod' I g (hA I v u - 0) := by
  have := Zsym (I := I) (g := g) (c := 0) (by rwa [sub_zero])
  first
    | rwa [map_zero] at this
    | simpa using this

theorem sig_ite {p : Prop} [Decidable p] : sigA I (if p then (1 : I.E ⊗[I.F] Af I.F) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

theorem Z0 {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g c) : ZMod' I g (c - 0) := by
  rwa [sub_zero]

theorem bwbw (h : FH I g e0 f0 z0 bw bwd ew) (i j : Fin k) : hA I (bw i) (bw j) = 0 := by
  rw [h.bw_w i, h.bw_w j]; exact hA_ew I h.orth _ _

theorem bdbd (h : FH I g e0 f0 z0 bw bwd ew) (i j : Fin k) : hA I (bwd i) (bwd j) = 0 := by
  rw [h.bwd_w i, h.bwd_w j]; exact hA_sew I h.orth _ _

theorem exp (h : FH I g e0 f0 z0 bw bwd ew) : ∀ w ∈ I.Lf, w - Rc I e0 f0 z0 bw bwd w ∈ mL I g := by
  let P : Submodule (IntAf I.F I.E) (VA I) :=
    { carrier := {w | w - Rc I e0 f0 z0 bw bwd w ∈ mL I g}
      add_mem' := fun {w w'} hw hw' => by
        show w + w' - Rc I e0 f0 z0 bw bwd (w + w') ∈ mL I g
        rw [Rc_add]
        have : w + w' - (Rc I e0 f0 z0 bw bwd w + Rc I e0 f0 z0 bw bwd w') =
          (w - Rc I e0 f0 z0 bw bwd w) + (w' - Rc I e0 f0 z0 bw bwd w') := by abel
        rw [this]; exact add_mem hw hw'
      zero_mem' := by
        show (0 : VA I) - Rc I e0 f0 z0 bw bwd 0 ∈ mL I g
        have : Rc I e0 f0 z0 bw bwd 0 = 0 := by
          have := Rc_smul I e0 f0 z0 bw bwd 0 0
          rwa [zero_smul, zero_smul] at this
        rw [this, sub_zero]; exact zero_mem _
      smul_mem' := fun c w hw => by
        show (c : I.E ⊗[I.F] Af I.F) • w - Rc I e0 f0 z0 bw bwd ((c : I.E ⊗[I.F] Af I.F) • w) ∈ mL I g
        rw [Rc_smul, ← smul_sub]
        exact (mL I g).smul_mem c hw }
  have hm := h.mem
  have hgen : Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ⊆ P := by
    rintro u ((((⟨b, rfl⟩ | ⟨b, rfl⟩) | hz) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · refine gen_ok I g e0 f0 z0 bw bwd hm (e0 b) (fun a => if a = b then 1 else 0) 0 0 0 0 (by simp [ite_smul])
        (fun a => ?_) (fun a => Z0 (h.gram a b).1) ?_ (fun i => Zsym0 ((h.W i).2.2 b).2.2.1)
        (fun i => Zsym0 ((h.W i).2.2 b).1)
      · have := Zsym (h.gram b a).2.2
        rw [sig_ite] at this
        simpa [eq_comm] using this
      · have := Z_neg I g (h.zz.2 b).1
        have h2 := Zsym0 (I := I) (g := g) (h.zz.2 b).1
        simpa using Z_neg I g (Z_sub I g h2 (Z_zero I g))
    · refine gen_ok I g e0 f0 z0 bw bwd hm (f0 b) 0 (fun a => if a = b then 1 else 0) 0 0 0 (by simp [ite_smul])
        (fun a => Z0 (h.gram a b).2.1) (fun a => (h.gram a b).2.2) ?_ (fun i => Zsym0 ((h.W i).2.2 b).2.2.2)
        (fun i => Zsym0 ((h.W i).2.2 b).2.1)
      have h2 := Zsym0 (I := I) (g := g) (h.zz.2 b).2
      simpa using Z_neg I g (Z_sub I g h2 (Z_zero I g))
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      refine gen_ok I g e0 f0 z0 bw bwd hm z0 0 0 1 0 0 (by simp) (fun a => Z0 (h.zz.2 a).2)
        (fun a => Z0 (h.zz.2 a).1) ?_ (fun i => Zsym0 (h.W i).2.1) (fun i => Zsym0 (h.W i).1)
      have := Z_neg I g h.zz.1
      have e : -(hA I z0 z0 + 1) = -hA I z0 z0 - 1 := by ring
      rwa [e] at this
    · refine gen_ok I g e0 f0 z0 bw bwd hm (bw j) 0 0 0 (fun i => if i = j then ew else 0) 0 ?_
        (fun a => Z0 ((h.W j).2.2 a).2.1) (fun a => Z0 ((h.W j).2.2 a).1) ?_ (fun i => h.dual i j)
        (fun i => by rw [bwbw h]; exact Z0 (Z_zero I g))
      · simp only [ite_smul, zero_smul, Pi.zero_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          Finset.sum_const_zero, add_zero, zero_add]
        exact h.bw_w j
      · simpa using Z_neg I g (h.W j).1
    · refine gen_ok I g e0 f0 z0 bw bwd hm (bwd j) 0 0 0 0 (fun i => if i = j then sigA I ew else 0) ?_
        (fun a => Z0 ((h.W j).2.2 a).2.2.2) (fun a => Z0 ((h.W j).2.2 a).2.2.1) ?_
        (fun i => by rw [bdbd h]; exact Z0 (Z_zero I g)) (fun i => ?_)
      · simp only [ite_smul, zero_smul, Pi.zero_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          Finset.sum_const_zero, add_zero, zero_add]
        exact h.bwd_w j
      · simpa using Z_neg I g (h.W j).2.1
      · have := Zsym (h.dual j i)
        have e : sigA I (if j = i then ew else 0) = if i = j then sigA I ew else 0 := by
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd h1.symm h2
          · exact absurd h2.symm h1
          · simp
        rwa [e] at this
  have hmL : mL I g ≤ P := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    show (g : I.E ⊗[I.F] Af I.F) • y - Rc I e0 f0 z0 bw bwd ((g : I.E ⊗[I.F] Af I.F) • y) ∈ mL I g
    rw [Rc_smul, ← smul_sub]
    exact smul_mem_mL I (sub_mem hy (Rc_Lf I e0 f0 z0 bw bwd hm hy))
  intro w hw
  exact (sup_le (Submodule.span_le.2 hgen) hmL) (h.span w hw)

end Main

section Chain

variable {I : AutInst} {g : ℕ} {r k : ℕ} {e0 f0 : Fin r → VA I} {z0 : VA I} {bw bwd : Fin k → VA I}
  {ew : I.E ⊗[I.F] Af I.F}

theorem hA_sub_left (a b c : VA I) : hA I (a - b) c = hA I a c - hA I b c := by
  unfold hA Formalism.UG.hform
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem adj (x : I.Gf) (u w : VA I) :
    hA I u ((I.fmat x - 1) *ᵥ w) = hA I ((I.fmat x⁻¹ - 1) *ᵥ u) w := by
  have h1 : hA I u (I.fmat x *ᵥ w) = hA I (I.fmat x⁻¹ *ᵥ u) w := by
    have := hA_fmat I x (I.fmat x⁻¹ *ᵥ u) w
    rw [Matrix.mulVec_mulVec, ← fmat_mul, mul_inv_cancel, fmat_one, Matrix.one_mulVec] at this
    exact this
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, hA_sub_right, hA_sub_left, h1]

theorem mem_Mo_of {S : Set (VA I)} {w : VA I} (h1 : w - Rc I e0 f0 z0 bw bwd w ∈ mL I g)
    (h2 : Rc I e0 f0 z0 bw bwd w ∈ Mo I g S) : w ∈ Mo I g S := by
  have h3 : w - Rc I e0 f0 z0 bw bwd w ∈ Mo I g S := by
    show _ ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g
    exact Submodule.mem_sup_right h1
  have h4 := Submodule.add_mem _ h3 h2
  simpa using h4

theorem span_Mo {S : Set (VA I)} {v : VA I} (h : v ∈ Submodule.span (IntAf I.F I.E) S) : v ∈ Mo I g S := by
  show v ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g
  exact Submodule.mem_sup_left h

theorem D1 (h : FH I g e0 f0 z0 bw bwd ew) {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) (j : Fin k) :
    (I.fmat x - 1) *ᵥ bwd j ∈ Mo I g (Set.range e0 ∪ {z0} ∪ bwd '' {l | j < l}) := by
  have hm := h.mem
  have hcx' := cong_inv I g e0 z0 bw hx hcx
  have hw : (I.fmat x - 1) *ᵥ bwd j ∈ I.Lf := K_sub_mv I hx (hm.2.2 j).2
  refine mem_Mo_of (exp h _ hw) ?_
  set w := (I.fmat x - 1) *ᵥ bwd j with hwdef
  unfold Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact span_Mo (sumSpan I _ _ _ (fun a _ => hA_int I (hm.1 a).2 hw)
      (fun a _ => Or.inl (Or.inl ⟨a, rfl⟩)))
  · refine mL_Mo I (sumZ I g _ _ _ (fun a _ => ?_) (fun a _ => (hm.1 a).2))
    rw [hwdef, adj]
    refine Zleft I g (hm.2.2 j).2 ?_ (hcx'.1 a)
    rintro _ ⟨c, -, rfl⟩
    exact ((h.W j).2.2 c).2.2.1
  · exact span_Mo (smul_span I (hA_int I hm.2.1 hw) (Or.inl (Or.inr rfl)))
  · refine mL_Mo I (sumZ I g _ _ _ (fun i _ => ?_) (fun i _ => (hm.2.2 i).1))
    have e : hA I (bwd i) w = 0 := by
      rw [hwdef, Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, bdbd h, sub_zero, h.bwd_w i,
        h.bwd_w j, Matrix.mulVec_smul]
      exact hA_sew I h.orth _ _
    rw [e]; exact Z_zero I g
  · refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hji : j < i
    · exact span_Mo (smul_span I (hA_int I (hm.2.2 i).1 hw) (Or.inr ⟨i, hji, rfl⟩))
    · refine mL_Mo I (Zv I g ?_ (hm.2.2 i).2)
      rw [hwdef, adj]
      refine Zleft I g (hm.2.2 j).2 ?_ (hcx'.2.2 i)
      rintro _ (⟨c, rfl⟩ | ⟨l, hl, rfl⟩)
      · exact ((h.W j).2.2 c).2.2.1
      · have hl' : l.1 < i.1 := hl
        have hlj : j ≠ l := fun e => hji (by rw [e]; exact hl')
        have := Zsym (h.dual j l)
        rw [if_neg hlj, map_zero, sub_zero] at this
        exact this

theorem F1 (h : FH I g e0 f0 z0 bw bwd ew) {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) (b : Fin r) :
    (I.fmat x - 1) *ᵥ f0 b ∈
      Mo I g (Set.range e0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ∪ f0 '' {c | b < c}) := by
  have hm := h.mem
  have hcx' := cong_inv I g e0 z0 bw hx hcx
  have hw : (I.fmat x - 1) *ᵥ f0 b ∈ I.Lf := K_sub_mv I hx (hm.1 b).2
  refine mem_Mo_of (exp h _ hw) ?_
  set w := (I.fmat x - 1) *ᵥ f0 b with hwdef
  unfold Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact span_Mo (sumSpan I _ _ _ (fun a _ => hA_int I (hm.1 a).2 hw)
      (fun a _ => Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))))
  · refine Submodule.sum_mem _ fun a _ => ?_
    by_cases hba : b < a
    · exact span_Mo (smul_span I (hA_int I (hm.1 a).1 hw) (Or.inr ⟨a, hba, rfl⟩))
    · refine mL_Mo I (Zv I g ?_ (hm.1 a).2)
      rw [hwdef, adj]
      refine Zleft I g (hm.1 b).2 ?_ (hcx'.1 a)
      rintro _ ⟨c, hc, rfl⟩
      have hc' : c.1 < a.1 := hc
      have hcb : c ≠ b := fun e => hba (by rw [← e]; exact hc')
      have := (h.gram c b).2.2
      rwa [if_neg hcb, sub_zero] at this
  · exact span_Mo (smul_span I (hA_int I hm.2.1 hw) (Or.inl (Or.inl (Or.inl (Or.inr rfl)))))
  · exact span_Mo (sumSpan I _ _ _ (fun i _ => hA_int I (hm.2.2 i).2 hw)
      (fun i _ => Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
  · exact span_Mo (sumSpan I _ _ _ (fun i _ => hA_int I (hm.2.2 i).1 hw)
      (fun i _ => Or.inl (Or.inr ⟨i, rfl⟩)))

end Chain

section Fin

variable {I : AutInst} {g : ℕ} {r k : ℕ} {e0 f0 : Fin r → VA I} {z0 : VA I} {bw bwd : Fin k → VA I}
  {ew : I.E ⊗[I.F] Af I.F}

def Gs (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (s : ℕ) : Set (VA I) :=
  e0 '' {b | b.1 + 1 ≤ s} ∪ {v | v = z0 ∧ r + 1 ≤ s} ∪ bw '' {j | r + 2 + j.1 ≤ s} ∪
    bwd '' {j | r + 1 + k ≤ s + j.1} ∪ f0 '' {b | 2 * r + 1 + k ≤ s + b.1}

theorem step (h : FH I g e0 f0 z0 bw bwd ew) {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) (s : ℕ) :
    ∀ v ∈ Mo I g (Gs e0 f0 z0 bw bwd (s + 1)), (I.fmat x - 1) *ᵥ v ∈ Mo I g (Gs e0 f0 z0 bw bwd s) := by
  refine pres1 I hx g _ _ ?_ (mL_Mo I)
  rintro u ((((⟨b, hb, rfl⟩ | ⟨rfl, hz⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨b, hb, rfl⟩)
  · have hb' : b.1 + 1 ≤ s + 1 := hb
    refine Mo_mono I ?_ (hcx.1 b)
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c.1 < b.1 := hc
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨c, show c.1 + 1 ≤ s by omega, rfl⟩)))
  · refine Mo_mono I ?_ hcx.2.1
    rintro _ ⟨c, rfl⟩
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨c, show c.1 + 1 ≤ s by have := c.isLt; omega, rfl⟩)))
  · have hj' : r + 2 + j.1 ≤ s + 1 := hj
    refine Mo_mono I ?_ (hcx.2.2 j)
    rintro _ (⟨c, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨c, show c.1 + 1 ≤ s by have := c.isLt; omega, rfl⟩)))
    · have hl' : l.1 < j.1 := hl
      exact Or.inl (Or.inl (Or.inr ⟨l, show r + 2 + l.1 ≤ s by omega, rfl⟩))
  · have hj' : r + 1 + k ≤ s + 1 + j.1 := hj
    have hjk := j.isLt
    refine Mo_mono I ?_ (D1 h hx hcx j)
    rintro _ ((⟨c, rfl⟩ | hz) | ⟨l, hl, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨c, show c.1 + 1 ≤ s by have := c.isLt; omega, rfl⟩)))
    · rw [Set.mem_singleton_iff] at hz
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hz, by omega⟩)))
    · have hl' : j.1 < l.1 := hl
      exact Or.inl (Or.inr ⟨l, show r + 1 + k ≤ s + l.1 by omega, rfl⟩)
  · have hb' : 2 * r + 1 + k ≤ s + 1 + b.1 := hb
    have hbr := b.isLt
    refine Mo_mono I ?_ (F1 h hx hcx b)
    rintro _ ((((⟨c, rfl⟩ | hz) | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨c, hc, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨c, show c.1 + 1 ≤ s by have := c.isLt; omega, rfl⟩)))
    · rw [Set.mem_singleton_iff] at hz
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hz, by omega⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨j, show r + 2 + j.1 ≤ s by have := j.isLt; omega, rfl⟩))
    · exact Or.inl (Or.inr ⟨j, show r + 1 + k ≤ s + j.1 by have := j.isLt; omega, rfl⟩)
    · have hc' : b.1 < c.1 := hc
      exact Or.inr ⟨c, show 2 * r + 1 + k ≤ s + c.1 by omega, rfl⟩

theorem iter (h : FH I g e0 f0 z0 bw bwd ew) {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) :
    ∀ (m s : ℕ), ∀ v ∈ Mo I g (Gs e0 f0 z0 bw bwd (s + m)),
      ((I.fmat x - 1) ^ m) *ᵥ v ∈ Mo I g (Gs e0 f0 z0 bw bwd s) := by
  intro m
  induction m with
  | zero => intro s v hv; simpa using hv
  | succ m ih =>
    intro s v hv
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    exact ih s _ (step h hx hcx (s + m) v (by rwa [← Nat.add_assoc] at hv))

theorem Gs_zero : Gs e0 f0 z0 bw bwd 0 = ∅ := by
  ext v
  simp only [Gs, Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ((((⟨b, hb, -⟩ | ⟨-, h⟩) | ⟨j, hj, -⟩) | ⟨j, hj, -⟩) | ⟨b, hb, -⟩)
  · omega
  · omega
  · omega
  · have := j.2; omega
  · have := b.2; omega

theorem Gs_top : Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ⊆
    Gs e0 f0 z0 bw bwd (2 * r + 1 + k) := by
  rintro v ((((⟨b, rfl⟩ | ⟨b, rfl⟩) | rfl) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨b, by have := b.2; show b.1 + 1 ≤ 2 * r + 1 + k; omega, rfl⟩)))
  · exact Or.inr ⟨b, by show 2 * r + 1 + k ≤ 2 * r + 1 + k + b.1; omega, rfl⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨rfl, by omega⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨j, by have := j.2; show r + 2 + j.1 ≤ 2 * r + 1 + k; omega, rfl⟩))
  · exact Or.inl (Or.inr ⟨j, by show r + 1 + k ≤ 2 * r + 1 + k + j.1; omega, rfl⟩)

theorem mL_pow {x : I.Gf} (hx : x ∈ I.Kset) : ∀ (m : ℕ), ∀ v ∈ mL I g, ((I.fmat x - 1) ^ m) *ᵥ v ∈ mL I g := by
  intro m
  induction m with
  | zero => intro v hv; simpa using hv
  | succ m ih =>
    intro v hv
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    refine ih _ ?_
    have h1 := pres1 I hx g (∅ : Set (VA I)) (mL I g) (fun s hs => absurd hs (Set.notMem_empty s)) le_rfl v
      (mL_Mo I hv)
    exact h1

theorem mL_dvd {g₀ : ℕ} (hdiv : g₀ ∣ g) : ∀ v ∈ mL I g, ∃ z ∈ I.Lf, v = (g₀ : I.E ⊗[I.F] Af I.F) • z := by
  obtain ⟨q, rfl⟩ := hdiv
  let N : Submodule (IntAf I.F I.E) (VA I) :=
    { carrier := {v | ∃ z ∈ I.Lf, v = (g₀ : I.E ⊗[I.F] Af I.F) • z}
      add_mem' := fun {a b} ⟨z, hz, ha⟩ ⟨z', hz', hb⟩ => ⟨z + z', add_mem hz hz', by rw [ha, hb, smul_add]⟩
      zero_mem' := ⟨0, zero_mem _, by rw [smul_zero]⟩
      smul_mem' := fun c a ⟨z, hz, ha⟩ => ⟨(c : I.E ⊗[I.F] Af I.F) • z, smul_Lf I c.2 hz, by
        show (c : I.E ⊗[I.F] Af I.F) • a = _
        rw [ha, smul_comm]⟩ }
  have hle : mL I (g₀ * q) ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(q : I.E ⊗[I.F] Af I.F) • y, smul_Lf I (natCast_mem _ q) hy, ?_⟩
    rw [← mul_smul, Nat.cast_mul]
  exact fun v hv => hle hv

end Fin

end Unip

theorem unipotence_mod_g : UnipCore := by
  intro I g g₀ r k e0 f0 z0 bw bwd ew hg hdiv hn hmem hgram hzz hW hidem horth hint hbw hbwd hdual hspan x hx y hy
  have h : Unip.FH I g e0 f0 z0 bw bwd ew := ⟨hmem, hgram, hzz, hW, horth, hbw, hbwd, hdual, hspan⟩
  have hN : ((I.fmat x - 1) ^ (2 * r + 1 + k)) *ᵥ y ∈ mL I g := by
    have := Unip.iter h hx.1 hx.2 (2 * r + 1 + k) 0 y (by
      rw [Nat.zero_add]
      exact Mo_mono I Unip.Gs_top (h.span y hy))
    rw [Unip.Gs_zero] at this
    have e : Mo I g (∅ : Set (VA I)) = mL I g := by
      unfold Mo; rw [Submodule.span_empty, bot_sup_eq]
    rwa [e] at this
  have hpow : (I.fmat x - 1) ^ I.n = (I.fmat x - 1) ^ (I.n - (2 * r + 1 + k)) * (I.fmat x - 1) ^ (2 * r + 1 + k) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, ← Matrix.mulVec_mulVec]
  exact Unip.mL_dvd hdiv _ (Unip.mL_pow hx.1 _ _ hN)

end Formalism.L2.SG.Pf.BunEx

end PartU

section PartX

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace Classical

namespace Formalism.L2.SG.Pf.BunEx

theorem gD_ne (D : D7) : gD D ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

variable {D : D7}

theorem level_set_unipotent_mod_g (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (Rf : ReferenceFrame A L) (x : A.I.Gf)
    (hx : x ∈ K2set A.I (gD D) Rf.e0 Rf.z0 Rf.bw) : A.I.UnipMod (D.host.g 0) x := by
  have hn : 2 * D.R.rS + D.R.k + 1 ≤ A.I.n := by rw [A.n_eq, Formalism.MainNotions.S.dimS_eq]
  exact unipotence_mod_g A.I (gD D) (D.host.g 0) Rf.e0 Rf.f0 Rf.z0 Rf.bw Rf.bwd Rf.ew
    (Nat.pos_of_ne_zero (gD_ne D)) (Dvd.intro _ rfl) hn Rf.vectorsInLattice Rf.gramIntegral Rf.formsAtZero Rf.weightVectorsIntegral Rf.ew_idem
    Rf.ew_orth Rf.ew_int Rf.bw_w Rf.bwd_w Rf.bw_dual Rf.latticeSpan x hx

theorem frameOK (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) :
    BunA.FrameOK A.I (gD D) Rf.e0 Rf.f0 Rf.z0 Rf.bw Rf.bwd P.psiEf where
  hg := gD_ne D
  hadd := P.psiEf_add
  hint := P.psiEf_int
  he0 := fun a => (Rf.vectorsInLattice.1 a).1
  hf0 := fun a => (Rf.vectorsInLattice.1 a).2
  hz0 := Rf.vectorsInLattice.2.1
  hbw := fun i => (Rf.vectorsInLattice.2.2 i).1
  hbwd := fun i => (Rf.vectorsInLattice.2.2 i).2
  hfe := fun a b hab => by
    have h := (Rf.gramIntegral b a).2.2
    rw [if_neg (Ne.symm hab), sub_zero] at h
    rw [unitaryCongruence.hA_symm A.I (Rf.e0 b)]; exact unitaryCongruence.Z_sig _ _ h
  hfz := fun a => (Rf.formsAtZero.2 a).2
  hbe := fun i a => by
    rw [unitaryCongruence.hA_symm A.I (Rf.e0 a)]; exact unitaryCongruence.Z_sig _ _ ((Rf.weightVectorsIntegral i).2.2 a).2.2.1
  hbb := fun i j hij => by
    have h := Rf.bw_dual i j
    rwa [if_neg hij, sub_zero] at h

theorem level_subgroup_measure_pos (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) (μf : Measure A.I.Gf)
    [μf.IsHaarMeasure] : 0 < μf (K2set A.I (gD D) Rf.e0 Rf.z0 Rf.bw) := by
  have hF := frameOK A P Rf
  have hsub : A.I.Kg (gD D) ⊆ K2set A.I (gD D) Rf.e0 Rf.z0 Rf.bw := fun x hx => (BunA.principal_congruence_le_level hF hx).1
  exact lt_of_lt_of_le ((BunA.kg_open hF).measure_pos μf ⟨1, BunA.kg_one hF⟩) (measure_mono hsub)

theorem level_subgroup_measure_finite (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (Rf : ReferenceFrame A L) (μf : Measure A.I.Gf)
    [μf.IsHaarMeasure] : μf (K2set A.I (gD D) Rf.e0 Rf.z0 Rf.bw) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (fun x hx => (show x ∈ A.I.Kset ∧ _ from hx).1)) ?_
  exact (PI.WAU.maximal_compact_isCompact A.I).measure_lt_top

theorem eOf_eq (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) (μf : Measure A.I.Gf) :
    eOf A P Rf μf = BunA.eF A.I (gD D) Rf.e0 Rf.f0 Rf.z0 Rf.bw Rf.bwd μf P.psiEf := rfl

theorem eAdm (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) (μf : Measure A.I.Gf)
    [μf.IsHaarMeasure] : A.I.IsAdmIdem μf (gD D) (D.host.g 0) (eOf A P Rf μf) := by
  rw [eOf_eq]
  have hF := frameOK A P Rf
  have hpos := level_subgroup_measure_pos A P Rf μf
  have hfin := level_subgroup_measure_finite A Rf μf
  refine ⟨BunA.eF_lc μf hF, BunA.eF_conv μf hF hpos hfin, BunA.eF_inv μf hF, BunA.eF_pos μf hF hpos hfin,
    BunA.eF_supp μf hF, BunA.eF_bi μf hF, fun x hx => ?_⟩
  have hx2 : x ∈ K2set A.I (gD D) Rf.e0 Rf.z0 Rf.bw := by
    by_contra hn
    exact hx (by simp [BunA.eF, hn])
  exact level_set_unipotent_mod_g A Rf x hx2

theorem eInt (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) (μf : Measure A.I.Gf)
    [μf.IsHaarMeasure] : Integrable (eOf A P Rf μf) μf := by
  rw [eOf_eq]
  have hF := frameOK A P Rf
  have hc : Continuous (BunA.eF A.I (gD D) Rf.e0 Rf.f0 Rf.z0 Rf.bw Rf.bwd μf P.psiEf) :=
    (BunA.eF_lc μf hF).continuous
  have hs : HasCompactSupport (BunA.eF A.I (gD D) Rf.e0 Rf.f0 Rf.z0 Rf.bw Rf.bwd μf P.psiEf) :=
    HasCompactSupport.intro (PI.WAU.maximal_compact_isCompact A.I)
      (fun x hx => by_contra fun h => hx (BunA.eF_supp μf hF x h))
  exact hc.integrable_of_hasCompactSupport hs

end Formalism.L2.SG.Pf.BunEx

namespace Formalism.L2.SG.Pf.BunEx

variable {D : D7}

theorem ds_exists (hDS : Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (A : UnitaryGroupInstance D) (v : InfinitePlace A.I.F) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin A.I.n) (Fin A.I.n) ℂ → (H →L[ℂ] H)), IsDS (A.I.ε v) (lamOf A v) σ := by
  have hε : A.I.ε v = fun i => epsS D.R (Fin.cast A.n_eq i) := funext (A.eps_eq v)
  have hp : Formalism.QuantumDeterminants.IsHCParam (lamOf A v) :=
    BunD.hc_cast A.n_eq (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (A.pl v)))
  have hgap : Formalism.QuantumDeterminants.GapAtLeast (A.I.ε v) (lamOf A v) (((16 * (D.R.r : ℚ) ^ 19 : ℚ)) : ℝ) := by
    rw [hε]
    exact BunD.gap_cast A.n_eq (BunD.gap_lamS D.R (D.hc (A.pl v)) (by positivity)
      (fun j hj => hG.2 (A.pl v) j hj))
  have hr : (1801 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hG.1
  have hthr : Formalism.MainNotions.GapDS.thrE (A.I.ε v) < (((16 * (D.R.r : ℚ) ^ 19 : ℚ)) : ℝ) := by
    have hn5 : (5 : ℝ) ≤ (A.I.n : ℝ) := by rw [A.n_eq]; linarith
    refine lt_of_le_of_lt (Formalism.MainNotions.GapDS.thrE_le _ hn5) ?_
    rw [A.n_eq]
    push_cast
    set R : ℝ := (D.R.r : ℝ)
    have h1 : (1 : ℝ) ≤ R ^ 16 := one_le_pow₀ (by linarith)
    have h2 : 0 < R ^ 3 := by positivity
    have e : R ^ 19 = R ^ 3 * R ^ 16 := by ring
    rw [e]; nlinarith
  exact hDS _ _ _ hp _ hgap hthr

end Formalism.L2.SG.Pf.BunEx

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BunEx

theorem automorphic_bundle_exists (hDS : Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG) (D : D7) : BunExists D := by
  intro hC hG A L P Rf
  choose Hv nv iv σv hσv using ds_exists hDS hG A
  letI : ∀ v, NormedAddCommGroup (Hv v) := nv
  letI : ∀ v, InnerProductSpace ℂ (Hv v) := iv
  haveI hCv : ∀ v, CompleteSpace (Hv v) := fun v => (hσv v).1
  have hw : ∀ v, ∃ w : Hv v, IsLowUnit (A.I.ε v) (lamOf A v) (σv v) w := by
    intro v
    obtain ⟨S, hS⟩ := (hσv v).2.2.2.2.2.1
    obtain ⟨u, huS, hu0, -⟩ := hS.2.2.2.1
    refine ⟨((‖u‖⁻¹ : ℝ) : ℂ) • u, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hu0)]
    · have hmem : u ∈ lowKSub (A.I.ε v) (lamOf A v) (σv v) :=
        (le_sSup (s := {S | IsKTypeOf (A.I.ε v) (σv v) (Formalism.QuantumDeterminants.lowK (A.I.ε v) (lamOf A v)) S}) hS) huS
      exact Submodule.smul_mem _ _ hmem
  choose wv hwv using hw
  have hN : 2 * D.R.rS + D.R.k + 1 = A.I.n := (Formalism.MainNotions.S.dimS_eq D.R).trans A.n_eq.symm
  have hci : ∀ v, Integrable (fun g : Formalism.REAL.UJ (A.I.ε v) => ⟪wv v, σv v (uMat g) (wv v)⟫_ℂ)
      (Formalism.REAL.muG (A.I.ε v)) := by
    intro v
    have hp48 : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 D.R.k D.R.rS (BunD.v48 D (A.pl v)) (BunD.b48 D (A.pl v))) := by
      have e : Formalism.MainNotions.CayleySignature.lam48 D.R.k D.R.rS (BunD.v48 D (A.pl v)) (BunD.b48 D (A.pl v)) =
          fun i => lamS D.R (D.hc (A.pl v)) (Fin.cast (Formalism.MainNotions.S.dimS_eq D.R) i) := funext (BunD.lambda_highest_weight_eq D (A.pl v))
      rw [e]
      exact BunD.hc_cast _ (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (A.pl v)))
    refine BunD.coef_int_gen hC D.R.k D.R.rS (BunD.v48 D (A.pl v)) (BunD.b48 D (A.pl v)) hp48
      (BunD.gapBig_of D hG (A.pl v)) A.I.n hN (A.I.ε v) (lamOf A v) (fun i => ?_) (fun i => ?_) (Hv v) (σv v)
      (hσv v) (wv v) (hwv v)
    · rw [A.eps_eq, BunD.epsilon_signature_eq]; rfl
    · rw [BunD.lambda_highest_weight_eq]; rfl
  have hph : Integrable (Formalism.L2.SG.ProjRows.phInf A.I σv wv fun v => fdegOf (Formalism.REAL.muG (A.I.ε v)) (σv v) (wv v))
      (Formalism.L2.SG.ProjRows.muInf A.I) := by
    unfold Formalism.L2.SG.ProjRows.phInf Formalism.L2.SG.ProjRows.mInf
    have hP := Integrable.fintype_prod_dep (E := fun v => Formalism.REAL.UJ (A.I.ε v))
      (f := fun v (g : Formalism.REAL.UJ (A.I.ε v)) => ⟪wv v, σv v (uMat g) (wv v)⟫_ℂ)
      (μ := fun v => Formalism.REAL.muG (A.I.ε v)) hci
    have hS : Integrable (fun x : A.I.Ginf => star (∏ v, ⟪wv v, σv v (uMat (x v)) (wv v)⟫_ℂ))
        (Formalism.L2.SG.ProjRows.muInf A.I) :=
      (hP.norm).mono' (continuous_star.comp_aestronglyMeasurable hP.1)
        (Filter.Eventually.of_forall fun x => by rw [norm_star])
    exact hS.const_mul _
  let l : List (InfinitePlace A.I.F) := (Finset.univ : Finset (InfinitePlace A.I.F)).toList
  have hten : A.I.IsHilbTensor σv (Hs := BunT.Cw Hv l) (fun g => BunT.cop Hv l (fun v => σv v (uMat (g v))))
      (BunT.ctens Hv l) := by
    refine ⟨fun x y => ?_, fun g x => BunT.cop_ctens Hv l _ x, BunT.ctens_dense Hv l (Finset.nodup_toList _)⟩
    rw [BunT.ctens_inner, Finset.prod_map_toList]
  have heint := eInt A P Rf (BunM.muF A.I)
  obtain ⟨Re, hRe⟩ := BunM.exists_opInt (BunM.muF A.I) (fun g => BunM.regR A.I (1, g))
    (fun g x => BunM.regR_iso A.I _ x)
    (fun x y => (BunM.regR_meas A.I x y).comp_measurable measurable_prodMk_left) _ heint
  obtain ⟨Rph, hRph⟩ := BunM.exists_opInt (Formalism.L2.SG.ProjRows.muInf A.I) (fun y => BunM.regR A.I (y, 1))
    (fun g x => BunM.regR_iso A.I _ x)
    (fun x y => (BunM.regR_meas A.I x y).comp_measurable measurable_prodMk_right) _ hph
  exact ⟨{ μf := BunM.muF A.I
           fund := BunM.fundF A.I
           fund_spec := BunM.fundF_isFund A.I _
           H := Hv
           hN := nv
           hI := iv
           hC := hCv
           σ := σv
           w := wv
           Hs := BunT.Cw Hv l
           σs := fun g => BunT.cop Hv l (fun v => σv v (uMat (g v)))
           tens := BunT.ctens Hv l
           tens_spec := hten
           R := BunM.regR A.I
           R_spec := BunM.regR_spec A.I
           e_adm := eAdm A P Rf _
           Re := Re
           Re_spec := ⟨heint, hRe⟩
           ds := hσv
           low := hwv
           Rph := Rph
           Rph_spec := hRph
           ph_int := hph }⟩

end Formalism.L2.SG.Pf

end PartX
