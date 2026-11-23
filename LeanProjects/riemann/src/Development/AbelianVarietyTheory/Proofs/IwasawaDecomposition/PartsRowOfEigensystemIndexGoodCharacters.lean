import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPsiOfStdFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtLeHPartOfCarries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtWLeHPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem partsRec_of_eig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd hP hH hHost hgen hLam
  have e1 := GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost hgen
  have e2 := GlobalTheory.Mem.EigCarry.carries_of_hasEig hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e3 := GlobalTheory.Mem.R3.IsotPart.isot_le_part hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e4 := GlobalTheory.Mem.R3.prt_le_hPart_of_carries hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e5 := GlobalTheory.Mem.R3.prtW_le_hPart hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have hc : Formalism.L2.Col.PairComm (A3.fam3.F.R A3.fam3.F.μ0).op := (hH.ok.ok2.what₂ A3.fam3.F.μ0).comm
  classical

  have hE : ∀ π, HasEig R F Y π (eigOfType R F Y π) := fun π => hasEig_eigOfType (e1 π)
  have hK : ∀ π, ∃ p, R.Carries p (eigOfType R F Y π) := fun π => e2 π _ (hE π)
  let Pi : Type := Set.range (eigOfType R F Y)
  have hPi : ∀ c : Pi, ∃ p, R.Carries p c.1 := by
    rintro ⟨c, π, rfl⟩
    exact hK π
  let labP : Pi → A3.fam3.base3.Ix := fun c => (hPi c).choose
  let E : EigIdx D Xd :=
    { Pi := Pi
      fin := Set.fintypeRange _
      dec := Classical.decEq _
      cOf := fun π => ⟨eigOfType R F Y π, π, rfl⟩
      lam_const := by
        intro j hj π π' e h1 h2 hcc
        have hc' : eigOfType R F Y π = eigOfType R F Y π' := congrArg Subtype.val hcc
        obtain ⟨p, hp⟩ := hK π
        have hp' : R.Carries p (eigOfType R F Y π') := hc' ▸ hp
        have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hk : k < D.R.m := by omega
        have a1 := hLam ⟨k, hk⟩ π p e h1 (e3 π _ p (hE π) hp ⟨k, hk⟩)
        have a2 := hLam ⟨k, hk⟩ π' p e h2 (e3 π' _ p (hE π') hp' ⟨k, hk⟩)
        exact a1.trans a2.symm }
  refine ⟨E, fun c => A3.fam3.toIx2 hc (labP c), Subtype.val, ?_⟩
  refine ⟨fun π => rfl, Subtype.val_injective, ?_, ?_⟩
  · intro π
    exact e4 π _ _ (hE π) (hPi _).choose_spec
  · intro i π
    have h5 := e5 π _ _ (hE π) (hPi (E.cOf π)).choose_spec i
    exact h5

end GlobalTheory.Mem.R3

end
