import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormula

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LocalSituation TensorProduct Module GlobalTheory.Per GlobalTheory.Prism

noncomputable section
namespace GlobalTheory.BSCoeff

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

section Dcris

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem Dcris_resQ : Dcris (P.PD K) (resQ ρ) = (Dcris (P.PD K) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [Dcris, sub_eq_zero, actVB_resQ]

theorem isCrys_resQ_iff [FiniteDimensional ℚ_[l] LL] : IsCrys (P.PD K) (resQ ρ) ↔ IsCrys (P.PD K) ρ := by
  have e : finrank ℚ_[l] ↥(Dcris (P.PD K) (resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dcris (P.PD K) ρ) := by
    rw [Dcris_resQ, finrank_mul_finrank]
    rfl
  rw [IsCrys, IsCrys, e, ← finrank_mul_finrank ℚ_[l] LL V, mul_left_comm]
  exact Nat.mul_right_inj finrank_pos.ne'

end Dcris

variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000

theorem algebraMap_OL (LL : FinExt l) (z : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]; rfl

theorem finite_OL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

variable {G : Type} [Group G] [TopologicalSpace G]

@[reducible] def zlV (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : Module ℤ_[l] T.V :=
  Module.compHom T.V (algebraMap ℤ_[l] ↥(OL LL))

theorem modO_smul (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (o : ↥(OL LL)) (w : T.V) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ T.modO.toSMul) o w = algebraMap ↥(OL LL) ↥LL.1 o • w := by
  letI := T.modO
  haveI := T.towO
  exact (algebraMap_smul ↥LL.1 o w).symm

theorem zlV_smul (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (z : ℤ_[l]) (w : T.V) :
    (zlV LL T).toSMul.smul z w = (z : ℚ_[l]) • w := by
  change @HSMul.hSMul _ _ _ (@instHSMul _ _ T.modO.toSMul) (algebraMap ℤ_[l] ↥(OL LL) z) w = _
  rw [modO_smul, algebraMap_OL, algebraMap_smul]

theorem zlV_tower (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlV LL T
    IsScalarTower ℤ_[l] ℚ_[l] T.V := by
  letI := zlV LL T
  refine ⟨fun z q v => ?_⟩
  change (z • q) • v = (zlV LL T).toSMul.smul z (q • v)
  rw [zlV_smul, smul_smul]
  rfl

theorem finite_compHom {O M : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] :
    letI := Module.compHom M (algebraMap ℤ_[l] O)
    Module.Finite ℤ_[l] M := by
  letI := Module.compHom M (algebraMap ℤ_[l] O)
  haveI : IsScalarTower ℤ_[l] O M := ⟨fun c a x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact Module.Finite.trans O M

theorem denom (LL : FinExt l) (c : ↥LL.1) :
    ∃ (z : ℚ_[l]) (a : ↥(OL LL)), c = z • algebraMap ↥(OL LL) ↥LL.1 a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have halg : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz, hint⟩ := halg.exists_integral_multiple
  have hz' : (z : ℚ_[l]) ≠ 0 := fun h => hz (Subtype.ext h)
  refine ⟨(z : ℚ_[l])⁻¹, ⟨z • c, hint⟩, ?_⟩
  change c = (z : ℚ_[l])⁻¹ • ((z : ℚ_[l]) • c)
  rw [smul_smul, inv_mul_cancel₀ hz', one_smul]

end GlobalTheory.BSCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff GlobalTheory.BSCoeff

set_option maxHeartbeats 1600000 in

theorem bhattScholze_coeff : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.BhattScholzeCrystallineLattices := by
  intro h l _ K P₀ e hA
  obtain ⟨h1, h2⟩ := h l K P₀ e hA
  refine ⟨fun P AI hS LL T hC => ?_, h2⟩
  letI := zlV LL T
  haveI := zlV_tower LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : FiniteDimensional ℚ_[l] T.V := Module.Finite.trans ↥LL.1 T.V
  haveI : IsModuleTopology ℚ_[l] ↥LL.1 := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology ℚ_[l] T.V := isModuleTopology_of_tower ℚ_[l] ↥LL.1 T.V
  let TZ : Submodule ℤ_[l] T.V :=
    { carrier := (T.L.T : Set T.V)
      add_mem' := fun ha hb => T.L.T.add_mem ha hb
      zero_mem' := T.L.T.zero_mem
      smul_mem' := fun z v hv => T.L.T.smul_mem (algebraMap ℤ_[l] ↥(OL LL) z) hv }
  haveI := finite_OL LL
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  have hfin' := finite_compHom (l := l) (O := ↥(OL LL)) (M := ↥T.L.T)
  haveI hfin : Module.Finite ℤ_[l] ↥TZ := hfin'
  have hz : ∀ (z : ℤ_[l]) (v : T.V), z • v = (z : ℚ_[l]) • v := fun z v => zlV_smul LL T z v
  have htf : Module.IsTorsionFree ℤ_[l] ↥TZ := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro z x hx
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    right
    have h' : (z : ℚ_[l]) • (x : T.V) = 0 := by
      rw [← hz]; exact congrArg Subtype.val hx
    have hq : (z : ℚ_[l]) ≠ 0 := fun h0 => hz0 (PadicInt.coe_eq_zero.1 h0)
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left hq)
  have hspan : Submodule.span ℚ_[l] (TZ : Set T.V) = ⊤ := by
    let W : Submodule ↥LL.1 T.V :=
      { carrier := (Submodule.span ℚ_[l] (TZ : Set T.V) : Set T.V)
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := by
          intro a x hx
          induction hx using Submodule.span_induction with
          | mem t ht =>
            obtain ⟨q, o, rfl⟩ := denom LL a
            show (q • algebraMap ↥(OL LL) ↥LL.1 o) • t ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [smul_assoc, ← modO_smul]
            exact Submodule.smul_mem _ q (Submodule.subset_span (T.L.T.smul_mem o ht))
          | zero => simp
          | add x y _ _ hx hy =>
            show a • (x + y) ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [smul_add]; exact Submodule.add_mem _ hx hy
          | smul q x _ hx =>
            show a • (q • x) ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [← algebraMap_smul ↥LL.1 q x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
            exact Submodule.smul_mem _ q hx }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← T.L.span, Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ht
    rw [eq_top_iff]
    intro v _
    have : v ∈ W := hW ▸ Submodule.mem_top
    exact this
  let L : Lattice (O := ℤ_[l]) (resQ T.ρ) :=
    { T := TZ
      stable := fun g x hx => T.L.stable g x hx
      fg := Module.Finite.iff_fg.mp hfin
      free := Module.free_of_finite_type_torsion_free'
      span := hspan }
  obtain ⟨E, j, hR⟩ := h1 P AI hS T.V (resQ T.ρ) L (fun x => T.cont x) ((isCrys_resQ_iff P T.ρ).mpr hC)
  exact ⟨E, j, hR⟩

end GlobalTheory
