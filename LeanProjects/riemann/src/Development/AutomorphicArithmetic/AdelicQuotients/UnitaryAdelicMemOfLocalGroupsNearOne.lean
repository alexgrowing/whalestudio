import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

private theorem prj_of_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} {v : Pl F} {g : UA σ X.J} (hg : OffAt v g) : Euler.prj v g = 1 := by
  have h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ hg i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
  refine Subtype.ext (Units.ext ?_)
  show Euler.cut (PositivityTheory.ThKG.Loc.idem F v) (mat g) = 1
  rw [← sub_eq_zero, Euler.cut_sub, h]

theorem UpperTheory.unitaryAdelic_mem_of_localGroups_near_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (S : Finset (Pl F)) (H : Pl F → Subgroup (UA σ X.J)), (∀ v ∈ S, ∃ O : Set (UA σ X.J), IsOpen O ∧ 1 ∈ O ∧ ∀ g ∈ locGrp σ X v, g ∈ O → g ∈ H v) → (∀ b ∈ gAt σ X S, ∃ c : Pl F → UA σ X.J, (∀ v, c v ∈ locGrp σ X v) ∧ (∀ v ∈ S, OffAt v ((c v)⁻¹ * b)) ∧ ∀ H : Subgroup (UA σ X.J), (∀ v ∈ S, c v ∈ H) → b ∈ H) → IsOpen {b : gAt σ X S | b.1 ∈ ⨆ v ∈ S, H v} := by
  intro F E _ _ _ _ _ σ n X S H hO hb
  choose! O hOo h1 hOH using hO
  let K : Subgroup (gAt σ X S) := (⨆ v ∈ S, H v).subgroupOf (gAt σ X S)
  have hK : IsOpen (K : Set (gAt σ X S)) := by
    refine Subgroup.isOpen_of_mem_nhds K (g := 1) ?_
    let U : Set (gAt σ X S) := ⋂ v ∈ S, (fun b : gAt σ X S => Euler.prj v b.1) ⁻¹' O v
    have oU : IsOpen U := isOpen_biInter_finset fun v hv =>
      (hOo v hv).preimage (Euler.cont_prj.comp continuous_subtype_val)
    have mU : (1 : gAt σ X S) ∈ U := by
      refine Set.mem_iInter₂.2 fun v hv => ?_
      show Euler.prj v (1 : UA σ X.J) ∈ O v
      rw [map_one]
      exact h1 v hv
    refine Filter.mem_of_superset (oU.mem_nhds mU) fun b hbU => ?_
    obtain ⟨c, hc, hoff, hlast⟩ := hb b.1 b.2
    refine Subgroup.mem_subgroupOf.2 (hlast _ fun v hv => ?_)
    have e : Euler.prj v b.1 = c v := by
      have := prj_of_off (hoff v hv)
      rw [map_mul, map_inv, Euler.mem_loc.1 (hc v), inv_mul_eq_one] at this
      exact this.symm
    have hm : c v ∈ O v := e ▸ (Set.mem_iInter₂.1 hbU v hv)
    exact (le_iSup₂_of_le v hv le_rfl : H v ≤ ⨆ v ∈ S, H v) (hOH v hv _ (hc v) hm)
  exact hK
