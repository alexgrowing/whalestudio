import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypePartLeEigensystemPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointEigenMemISup
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.EigCarry

theorem exists_eq_of_mem_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ)
    (E : κ → Submodule ℂ M) (hE : ∀ k, ∀ y ∈ E k, ∀ i, op i y = χ k i • y) (ψ : ι → ℂ) (x : M) (hx0 : x ≠ 0)
    (hx : ∀ i, op i x = ψ i • x) (hmem : x ∈ ⨆ k, E k) : ∃ k, χ k = ψ := by
  first
  | (rename_i h_3 h_4; revert ι κ M h_3 h_4 op χ E hE ψ x hx0 hx hmem; exact @_root_.GlobalTheory.JointEigenSupremum.target)
  | exact @_root_.GlobalTheory.JointEigenSupremum.target
  | exact _root_.GlobalTheory.JointEigenSupremum.target
  | (apply _root_.GlobalTheory.JointEigenSupremum.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenSupremum.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenSupremum.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenSupremum.target ..)

theorem exists_part_eq {ι C H M : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup M] [Module ℂ M] (e : H →ₗ[ℂ] M)
    (op : ι → Module.End ℂ M) (χ : C → ι → ℂ) (N : Submodule ℂ M) (E : C → Submodule ℂ H)
    (hE : ∀ c y, y ∈ E c ↔ e y ∈ N ∧ ∀ i, op i (e y) = χ c i • e y) (S : C → Prop) (c : C) (x : H) (hx : x ∈ E c)
    (h0 : e x ≠ 0) (hs : x ∈ ⨆ (c' : C) (_ : S c'), E c') : ∃ c', S c' ∧ E c' = E c := by
  have hle : (⨆ (c' : C) (_ : S c'), E c') ≤ (⨆ k : {c' // S c'}, (E k.1).map e).comap e := by
    refine iSup₂_le fun c' hc' y hy => ?_
    exact (le_iSup (fun k : {c' // S c'} => (E k.1).map e) ⟨c', hc'⟩) ⟨y, hy, rfl⟩
  obtain ⟨k, hk⟩ := exists_eq_of_mem_iSup op (fun k : {c' // S c'} => χ k.1) (fun k => (E k.1).map e)
    (by rintro k _ ⟨y, hy, rfl⟩; exact ((hE _ y).1 hy).2) (χ c) (e x) h0 ((hE c x).1 hx).2 (hle hs)
  refine ⟨k.1, k.2, ?_⟩
  ext y
  rw [hE, hE]
  exact and_congr_right fun _ => forall_congr' fun q => by rw [congrFun hk q]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ssetF_base {R : RealDat3 D A3 Ks} {F : Face3 D A3} (hC : R.WeakCharacterisation F) : SsetF R.toRealDat A3.A.μ0 = R.SF := by
  have hL := hC.base.lev
  have hQ : R.Q A3.A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (hL.Q_ram A3.A.μ0 PP).2 (Or.inl hP) ?_
    rw [hL.xi_base]
    intro x hx
    rfl
  ext v
  rw [hC.inert.SF v]
  unfold SsetF
  rw [hQ]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => h ▸ rfl, fun h => HeightOneSpectrum.ext h⟩

abbrev RowOp (R : RealDat3 D A3 Ks) : Type :=
  {q : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Yc D 0)) //
    Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.SF q.1 q.2.1 q.2.2}

theorem mem_eEc_iff (R : RealDat3 D A3 Ks) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (x : R.HE.H) :
    x ∈ R.EEc c ↔ R.HE.e x ∈ Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) ∧
      ∀ q : RowOp R, heckeOn (R.MY 0) q.1.2.2 (R.HE.e x) = c q.1.1 (dualLab q.1.2.1) • R.HE.e x := by
  unfold RealDat3.EEc partDual partFull
  simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  exact and_congr_right fun _ => ⟨fun h q => h _ _ _ q.2, fun h P d S hS => h ⟨(P, d, S), hS⟩⟩

theorem carries_of_mem (R : RealDat3 D A3 Ks) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (x : R.HE.H)
    (hx : x ∈ R.EEc c) (h0 : R.HE.e x ≠ 0) (hs : x ∈ ⨆ p, R.EEp3 p) : ∃ p, R.Carries p c := by
  have hle : (⨆ p, R.EEp3 p) ≤ ⨆ (c') (_ : ∃ p, R.Carries p c'), R.EEc c' :=
    iSup_le fun p => iSup₂_le fun c' hc' =>
      le_iSup₂_of_le (f := fun c' (_ : ∃ p, R.Carries p c') => R.EEc c') c' ⟨p, hc'⟩ le_rfl
  obtain ⟨c', ⟨p, hp⟩, heq⟩ := exists_part_eq R.HE.e (fun q : RowOp R => heckeOn (R.MY 0) q.1.2.2)
    (fun c q => c q.1.1 (dualLab q.1.2.1)) _ R.EEc (mem_eEc_iff R) (fun c' => ∃ p, R.Carries p c') c x hx h0 (hle hs)
  exact ⟨p, heq ▸ hp.1, (Submodule.map_mono heq.ge).trans hp.2⟩

theorem mem_iSup_eEp3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool) (hP : (R.toCx3 F).PartsE b) (x : R.HE.H)
    (hx : R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)) : x ∈ ⨆ p, R.EEp3 p := by
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) x ∈ (R.toCx3 F).EEl b := hx
  rw [← hP.2] at h1
  have h2 : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤ Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
    refine iSup_le fun p => inf_le_left.trans fun y hy => ?_
    exact (le_iSup (fun p => R.EEp3 p) p) hy
  exact h2 h1

theorem carries_of_hasEig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c, HasEig R F Y π c → ∃ p, R.Carries p c := by
  intro _ _ _ hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds _ π c hc
  obtain ⟨hCore, hSF, hEE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hPins.char hHolds.aux.ex
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  unfold HasEig at hc
  rw [hμ, ssetF_base hPins.char] at hc
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT π)
  obtain ⟨U, hU, hU0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨x, hx, hxU⟩ := GlobalTheory.T.rowTypePart_le_eigensystemPart (s := 1) R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) R.SF hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2 _ _ c hc b U hU
  rw [← hEE] at hx
  refine carries_of_mem R c x hx (hxU ▸ hU0) (mem_iSup_eEp3 R F b (hHolds.prim.sumE b) x ?_)
  rw [hxU]
  exact hU.1

end GlobalTheory.Mem.EigCarry
