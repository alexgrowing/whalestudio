import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfRangeEq
import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelLattice
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetSharp

open Formalism.IndefR.Mult

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_ne_zero_of_ne {M : DSModel V S} {u : MMap M} (hu : u ≠ 0) : ∀ τ, ∃ w : M.sm τ, w ≠ 0 := by
  intro τ
  by_contra h
  push_neg at h
  exact hu (MultilinearMap.ext fun v => (u.map_coord_zero τ (h (v τ))).trans rfl)

theorem ipM_smul_measure_self (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {u : MMap M} {a : ℝ} (ha : 0 ≤ a)
    (hu : u ≠ 0) (h : ∃ c, IsMultIP M μ 𝓕 u u c) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 u u = (a : ℂ) * ipM M μ 𝓕 u u := by
  choose w hw using sm_ne_zero_of_ne hu
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hw τ (Submodule.coe_eq_zero.1 h)
  have h1 : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 u u ((a : ℂ) * ipM M μ 𝓕 u u) := by
    intro v v'
    obtain ⟨h1, h2⟩ := ipM_spec M μ 𝓕 u u h v v'
    refine ⟨?_, ?_⟩
    · unfold IntegrableOn at h1 ⊢
      rw [Measure.restrict_smul]
      exact h1.smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]
  exact hasPeterssonInner_unique M _ 𝓕 u u w hv0 (ipM_spec M _ 𝓕 u u ⟨_, h1⟩) h1

end Schur

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem norm_sq_rows (hP : Pins R F cG) (Z : ReadL R F X0 Y) (y : Fin ((s1Of R F).D) → D.what₂.LL) :
    ‖D.jEE (Z.eRR y)‖ ^ 2 =
      (RealDat.nP F.lv2 true)⁻¹ * ‖(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)‖ ^ 2 := by
  set z : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
    ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)) with hz
  have hzn : ‖(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)‖ = ‖z‖ := rfl
  rw [hzn]
  obtain ⟨hinj, -, hip⟩ := hP.char.base.models.HE
  set w := D.jEE (Z.eRR y) with hw
  have hT := Y.tied.sharp.ee w w
  have hJ := Z.jEE y
  have hE : ⟪w, w⟫_ℂ = ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 true)⁻¹ • R.ν0) R.fd0 (R.HE.e z) (R.HE.e z) := by
    rw [hT]
    show ipMT _ _ _ _ _ = _
    rw [ipMT, hJ]
    show ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 true)⁻¹ • R.ν0) R.fd0
      (PiTensorProduct.lift.symm (PiTensorProduct.lift (R.HE.e z))) (PiTensorProduct.lift.symm (PiTensorProduct.lift (R.HE.e z))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hip' : ⟪z, z⟫_ℂ = ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) := hip z z
  have ha : (0 : ℝ) ≤ (RealDat.nP F.lv2 true)⁻¹ := (inv_pos.2 (RealDat.nP_pos (F := F.lv2) true)).le
  by_cases hz0 : z = 0
  · have hu : R.HE.e z = 0 := by rw [hz0, map_zero]
    have hw0 : w = 0 := by
      apply Y.Ish.jE.injective
      rw [map_zero]
      apply Subtype.ext
      rw [hJ]
      show PiTensorProduct.lift (R.HE.e z) = 0
      rw [hu, map_zero]
    rw [hw0, hz0, norm_zero, norm_zero]
    ring
  · have hu : R.HE.e z ≠ 0 := fun h => hz0 (hinj (h.trans (map_zero _).symm))
    have hex : ∃ c, IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) c := by
      by_contra hno
      have h0 : ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) = 0 := by
        unfold ipM
        rw [dif_neg hno]
      exact hz0 (inner_self_eq_zero.1 (hip'.trans h0))
    rw [ipM_smul_measure_self (R.MY 0) R.ν0 R.fd0 ha hu hex, ← hip'] at hE
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ _ _ _ _ z, hE]
    exact Complex.re_ofReal_mul _ _

theorem majAt_rows_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR x) (Z.eRR y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hR := (complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim).rowHyp true
  have hn := hR.h4pos.2.2 true
  have hv0 := (pins_card_index_ranks D G Pl0 I0 T A3 Ks R F cG hP).2.2.2.2
  refine fun x y => GlobalTheory.Mem.RowSides.majAt_eq_of_normAt _ _ _ _ _ Z.eRR.toLinearMap (fun y => ?_) x y
  have hL : Formalism.HermitianLatticesTheory.normAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR y) = ‖D.jEE (Z.eRR y)‖ := by
    rw [hv0]; exact D.jEE_norm _
  have hr : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 y y =
      (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) *
        ⟪(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y), (R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)⟫_ℂ :=
    PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr true hR.h2 hn y y
  show Formalism.HermitianLatticesTheory.normAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR y) ^ 2 =
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 y ^ 2
  rw [hL, norm_sq_rows hP Z y]
  refine Eq.trans ?_ (Formalism.BasicNotions.normAt_sq_eq_majAt _ _ _ _).symm
  rw [hr, inner_self_eq_norm_sq_to_K, Complex.re_ofReal_mul]
  norm_cast

end GlobalTheory.Mem.R3.MetSharp
