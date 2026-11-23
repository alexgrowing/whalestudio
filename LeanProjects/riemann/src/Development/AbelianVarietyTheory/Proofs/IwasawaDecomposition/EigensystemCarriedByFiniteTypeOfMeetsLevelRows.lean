import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCarry

theorem inner_eq_zero_of_normal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : H →ₗ[ℂ] H) (hT : Commute T (LinearMap.adjoint T)) {a b : ℂ} (hab : a ≠ b) {x y : H}
    (hx : T x = a • x) (hy : T y = b • y) : ⟪x, y⟫_ℂ = 0 := by
  set S : H →ₗ[ℂ] H := T - b • LinearMap.id with hS
  have hSy : S y = 0 := by simp [hS, hy]
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd ℂ b) • LinearMap.id := by
    rw [hS, map_sub, LinearEquiv.map_smulₛₗ, LinearMap.adjoint_id]
  have hSc : Commute S (LinearMap.adjoint S) := by
    rw [hSadj, hS]
    have h1 : Commute T (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) := (Commute.one_right T).smul_right _
    have h2 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (LinearMap.adjoint T) := (Commute.one_left _).smul_left _
    have h3 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) :=
      ((Commute.one_left _).smul_left _).smul_right _
    exact (hT.sub_right h1).sub_left (h2.sub_right h3)
  have hSa : LinearMap.adjoint S y = 0 := by
    have h0 : ⟪LinearMap.adjoint S y, LinearMap.adjoint S y⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      have : S (LinearMap.adjoint S y) = LinearMap.adjoint S (S y) := by
        have := congrArg (fun f : H →ₗ[ℂ] H => f y) hSc.eq
        simpa [Module.End.mul_apply] using this
      rw [this, hSy, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 h0
  have hTa : LinearMap.adjoint T y = (starRingEnd ℂ b) • y := by
    have := hSa
    rw [hSadj, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have key : ⟪T x, y⟫_ℂ = ⟪x, LinearMap.adjoint T y⟫_ℂ := (LinearMap.adjoint_inner_right T x y).symm
  rw [hx, hTa, inner_smul_left, inner_smul_right] at key
  have hne : starRingEnd ℂ a ≠ starRingEnd ℂ b := fun h => hab ((starRingEnd ℂ).injective h)
  have : (starRingEnd ℂ a - starRingEnd ℂ b) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry

theorem twSub_iSup {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (V : I → Submodule ℂ E) :
    Tw.sub s (⨆ p, V p) = ⨆ p, Tw.sub s (V p) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun p x hx => Submodule.mem_iSup_of_mem (p := V) p hx)
  exact Submodule.iSup_induction V (motive := fun y => Tw.mk s y ∈ ⨆ p, Tw.sub s (V p)) hx
    (fun p y hy => Submodule.mem_iSup_of_mem p hy) (zero_mem _) fun y z hy hz => add_mem hy hz

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem carries_of_eq (R : RealDat3 D A3 Ks) (p : A3.fam3.base3.Ix) {c c' : Pl D.host.E → List ℤ → ℂ}
    (heq : R.EEc c' = R.EEc c) (h : R.Carries p c') : R.Carries p c := by
  have key : ∀ V W : Submodule ℂ R.HE.H, V = W →
      (V ≠ ⊥ ∧ V.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) →
      (W ≠ ⊥ ∧ W.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) := by
    rintro V W rfl hV; exact hV
  exact key _ _ heq h

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry

set_option maxHeartbeats 1000000 in

theorem carried : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (c : Pl D.host.E → List ℤ → ℂ) (b : Bool) (x : R.HE.H), x ≠ 0 → x ∈ R.EEc c → R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) → ∃ p, R.Carries p c := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost c b x hx0 hxc hxb
  by_contra hno
  push_neg at hno
  obtain ⟨hcore, hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hP.char
  obtain ⟨h, -, hN, -, hev, hchar⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 (hcore hHo.aux.ex)
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCu R.toRealDat) R.SF hSF

  have heig : ∀ c' (y : R.HE.H), y ∈ R.EEc c' → ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P →
      GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) y = c' P (dualLab d) • y := by
    intro c' y hy P d hG hL
    rw [hEEc c'] at hy
    rw [hev c' P hG (Finsupp.single d 1) y hy]
    congr 1
    simp [GlobalTheory.Hk3.evC, Finsupp.sum_single_index, hL]

  have horth : ∀ c', R.EEc c' ≠ R.EEc c → R.EEc c' ≤ (ℂ ∙ x)ᗮ := by
    intro c' hne y hy
    have hex : ∃ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ GlobalTheory.Hk3.IsLab (Yc D 0) P d ∧
        c' P (dualLab d) ≠ c P (dualLab d) := by
      by_contra hall
      push_neg at hall
      apply hne
      ext z
      constructor
      · intro hz
        rw [hEEc c]
        exact hchar c z fun P d hG hL => by rw [heig c' z hz P d hG hL, hall P d hG hL]
      · intro hz
        rw [hEEc c']
        exact hchar c' z fun P d hG hL => by rw [heig c z hz P d hG hL, hall P d hG hL]
    obtain ⟨P, d, hG, hL, hcc⟩ := hex
    have hT : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) := by
      rw [hN.2 P hG]
      exact hN.1 P P hG hG _ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := inner_eq_zero_of_normal _ hT hcc (heig c' y hy P d hG hL) (heig c x hxc P d hG hL)
    rw [← inner_conj_symm, this, map_zero]

  have hpart : ∀ p, R.EEp3 p ≤ (ℂ ∙ x)ᗮ := by
    intro p
    unfold RealDat3.EEp3
    refine iSup₂_le fun c' hc' => horth c' fun heq => hno p ?_
    exact carries_of_eq R p heq hc'

  have hxT : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈ (R.toCx3 F).EEl b := hxb
  rw [← (hHo.prim.sumE b).2] at hxT
  have hxS : x ∈ ⨆ p, R.EEp3 p := by
    have h1 : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
      rw [twSub_iSup]
      have hle : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤
          ⨆ p, Tw.sub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 p) := iSup_mono fun p => inf_le_left
      exact hle hxT
    exact h1
  have hself : x ∈ (ℂ ∙ x)ᗮ := (iSup_le hpart) hxS
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hself
  exact hx0 (inner_self_eq_zero.1 hself)

end GlobalTheory.Mem.R3.LabCarry
