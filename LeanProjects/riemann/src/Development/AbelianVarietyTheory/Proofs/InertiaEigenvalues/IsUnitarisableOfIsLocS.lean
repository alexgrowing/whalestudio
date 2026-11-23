import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowSphSmall

open GlobalTheory.CuspRep.ParLaws GlobalTheory.LocLanglands

theorem locRec_unr_frobEig_le (hL : GlobalTheory.Published.LocalLanglandsGL) {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {n : ℕ} (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (hs : GlobalTheory.SmGL.IsSpherical σ.ρ)
    (hu : GlobalTheory.SmGL.IsUnitarisable σ.ρ) :
    (locRec hL h (cls σ)).unr ∧
      ∀ α ∈ (locRec hL h (cls σ)).frobEig, ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have H := isRec_locRec hL h
  have hunr : (locRec hL h (cls σ)).unr := (unr_iff H σ).2 hs
  refine ⟨hunr, ?_⟩
  obtain ⟨α, hα⟩ := exists_hasSatake_of_unr H hunr
  rw [rec_eq_diag H hα, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  have h1 := GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake E w n (GlobalTheory.SplitRead.Irr.ofIrrRep σ) α hα hu
  have h2 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n
      ((Finset.univ.val.map fun i => (α i : ℂ)).map (·⁻¹)) := by
    have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv _ _ _ _ h1
  intro b hb
  apply h2.norm_le
  simpa [Multiset.map_map, Function.comp_def] using hb

end GlobalTheory.RowSphSmall

section FormSec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

namespace GlobalTheory.RowSphSmall

set_option maxHeartbeats 1000000 in

theorem exists_form_rowRepR (hH : GlobalTheory.Published.HarishChandraFinite) (hC : GlobalTheory.Published.CuspRapidDecay) (D : D7) (G : Type) [Group G]
    [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : Pins R F cG) (σ : D.what₂.FT) :
    ∃ B : (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S → (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S → ℂ,
      (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) ∧ (∀ x y, B x y = starRingEnd ℂ (B y x)) ∧
      (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
      ∀ h (x y x' y' : (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S), (x' : GAf D.host.E D.R.r → ℂ) = NG.rt D.host.E D.R.r h x →
        (y' : GAf D.host.E D.R.r → ℂ) = NG.rt D.host.E D.R.r h y → B x' y' = B x y := by
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  have hne : isotIn (D := D) (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) (FinTyp.conjT π) ≠ ⊥ := by
    intro h
    apply hb
    unfold isotE isotL
    rw [h, inf_bot_eq]
  have hM := hP.char.base.models
  have hθ : IsInfFam R.θ := hM.inf
  have hSig : (Yc D 0).SigOK := D.sp.Y_sig 0
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  have hfd : ∀ j, j < D.R.m → (R.νY A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) (R.fdY A3.A.μ0 j) (R.νY A3.A.μ0 j) := by
    intro j hj
    by_cases h : j + 1 < D.R.m
    · have := hM.νY A3.A.μ0 j h
      exact ⟨this.1.1, this.2⟩
    · obtain rfl : j = D.R.m - 1 := by omega
      have := hM.νY' A3.A.μ0
      exact ⟨this.1.1, this.2⟩
  obtain ⟨hHaar, hFD⟩ := hfd 0 Y.hm
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MY 0) (θ := R.θ) (R.νY A3.A.μ0 0)
    (R.fdY A3.A.μ0 0) Y.PY hSA hSig hθ hHaar hFD
  obtain ⟨B', h1, h2, h3, h4⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r _ (actM Y.PY (R.MY 0))
    (Minf R.θ Y.PY (R.MY 0)) (ipM (R.MY 0) (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0)) hlin hherm hpos
    (fun h x hx => GlobalTheory.FinTypesRows.minf_stable Y.PY hcc h hx)
    (fun h x hx y hy => GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Yc D 0) _ R.θ (R.MY 0) D.R.r Y.PY (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0) hSA hSig hθ
      hHaar hFD h x hx y hy) (FinTyp.conjT π) hne
  exact GlobalTheory.RowLocalRows.form_of_conjT π B' h1 h2 h3 h4

end GlobalTheory.RowSphSmall
end FormSec

namespace GlobalTheory.RowSphSmall

theorem isUnitarisable_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.FinTyp L n)
    (B : π.S → π.S → ℂ) (hlin : ∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z)
    (hherm : ∀ x y, B x y = starRingEnd ℂ (B y x)) (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hinv : ∀ h (x y x' y' : π.S), (x' : Formalism.AUTREP.GAf L n → ℂ) = NG.rt L n h x →
      (y' : Formalism.AUTREP.GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y)
    (s : ReciprocityTheory.Aut.SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hτ : IsLocS π.S s τ) :
    GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  obtain ⟨i, T, -, -, hTi, hTm, hTe⟩ := hτ
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n s
  let t : τ.V → π.S := fun v => ⟨T v, hTm v⟩
  have tadd : ∀ v w, t (v + w) = t v + t w := fun v w => Subtype.ext (map_add T v w)
  have tsmul : ∀ (c : ℂ) v, t (c • v) = c • t v := fun c v => Subtype.ext (map_smul T c v)
  have hlin2 : ∀ y z : π.S, ∀ c : ℂ, B (y + c • z) = fun x => B y x + starRingEnd ℂ c * B z x := by
    intro y z c
    funext x
    rw [hherm, hlin, map_add, map_mul, ← hherm, ← hherm]
  have hadd1 : ∀ y z x : π.S, B (y + z) x = B y x + B z x := by
    intro y z x
    have := congrFun (hlin2 y z 1) x
    simpa using this
  have hsm1 : ∀ (c : ℂ) (z x : π.S), B (c • z) x = starRingEnd ℂ c * B z x := by
    intro c z x
    have h1 := congrFun (hlin2 0 z c) x
    have h0 : B 0 x = 0 := by
      have := hadd1 0 0 x
      simp only [add_zero] at this
      linear_combination -this
    simpa [h0] using h1
  have hadd2 : ∀ x y z : π.S, B x (y + z) = B x y + B x z := by
    intro x y z
    simpa using hlin x y z 1
  have hsm2 : ∀ (c : ℂ) (x z : π.S), B x (c • z) = c * B x z := by
    intro c x z
    have h1 := hlin x 0 z c
    have h0 : B x 0 = 0 := by
      have := hadd2 x 0 0
      simp only [add_zero] at this
      linear_combination -this
    simpa [h0] using h1
  let Bf : τ.V →ₗ[ℂ] τ.V →ₛₗ[starRingEnd ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => B (t w) (t v))
      (fun v v' w => by rw [tadd, hadd2])
      (fun c v w => by rw [tsmul, hsm2]; rfl)
      (fun v w w' => by rw [tadd, hadd1])
      (fun c v w => by rw [tsmul, hsm1]; rfl)
  refine ⟨Bf, ?_, ?_, ?_⟩
  · intro v w
    show B (t v) (t w) = starRingEnd ℂ (B (t w) (t v))
    exact hherm _ _
  · intro v hv
    show 0 < (B (t v) (t v)).re
    apply hpos
    intro h0
    apply hv
    apply hTi
    rw [map_zero]
    exact congrArg Subtype.val h0
  · intro g v w
    show B (t (τ.ρ g w)) (t (τ.ρ g v)) = B (t w) (t v)
    let g' := Matrix.GeneralLinearGroup.map i.symm.toRingHom g
    have hg : Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n (e g')) = g := by
      rw [he2]
      ext a b
      simp [g']
    have hx : ∀ a, T (τ.ρ g a) = NG.rt L n (e g') (T a) := by
      intro a
      rw [← hg]
      exact hTe (e g') (he1 g') a
    exact hinv (e g') (t w) (t v) (t (τ.ρ g w)) (t (τ.ρ g v)) (hx w) (hx v)

end GlobalTheory.RowSphSmall
