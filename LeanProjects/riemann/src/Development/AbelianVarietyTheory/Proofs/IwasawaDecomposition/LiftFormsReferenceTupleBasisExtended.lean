import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSLin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataDeterminedByValuesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

open Formalism.L2.Col

section LiftBasis

variable {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
  {S : GSD K} {S' : GSD L}

theorem gsdbc_lift_span (b : GSDBC ι S S') {κ : Type} [Fintype κ] (v : Module.Basis κ K S.EqFun) :
    ⊤ ≤ Submodule.span L (Set.range fun k => b.lift (v k)) := by
  obtain ⟨F⟩ := CoefFrame.nonempty ι
  intro φ _
  have h1 : Submodule.span L (Set.range b.lift) ≤ Submodule.span L (Set.range fun k => b.lift (v k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨ψ, rfl⟩
    rw [← v.sum_repr ψ, b.lift_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact h1 (b.mem_span_lift F φ)

theorem gsdbc_lift_li (b : GSDBC ι S S') {κ : Type} [Fintype κ] (v : Module.Basis κ K S.EqFun) :
    LinearIndependent L (fun k => b.lift (v k)) := by
  letI : Algebra K L := ι.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun q => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ L) q, eq_ratCast (algebraMap ℚ K) q, map_ratCast]
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let e := Module.finBasis K L
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hs : ∀ m, (∑ k, e.repr (c k) m • v k) = 0 := by
    intro m
    apply Subtype.ext
    funext d
    apply S.bV.ext_elem
    intro i
    have h0 := congrArg (fun x : S'.EqFun => b.bas.repr ((x : S'.D → S'.V) (b.eD.symm d)) i) hc
    rw [Submodule.coe_sum, Finset.sum_apply, map_sum, Finsupp.finset_sum_apply] at h0
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Finsupp.smul_apply, GSDBC.lift_apply, GSDBC.repr_j,
      Equiv.apply_symm_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, map_zero, Finsupp.zero_apply] at h0
    have h1 : (∑ k, S.bV.repr ((v k : S.D → S.V) d) i • c k) = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    have h2 := congrArg (fun x => e.repr x m) h1
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
      Finsupp.zero_apply] at h2
    rw [Submodule.coe_sum, Finset.sum_apply, map_sum, Finsupp.finset_sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply, map_zero, Finsupp.zero_apply]
    rw [← h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hz : ∀ m, e.repr (c k) m = 0 := fun m =>
    Fintype.linearIndependent_iff.1 v.linearIndependent _ (hs m) k
  rw [← e.sum_repr (c k)]
  simp [hz]

noncomputable def resLift (b : GSDBC ι S S') (hS : S.Ok) (hS' : S'.Ok) : (S.toCSD hS).Forms →+ (S'.toCSD hS').Forms where
  toFun x := S'.res hS' (b.lift ((S.res hS).symm x))
  map_zero' := by simp only [map_zero, b.lift_zero]
  map_add' x y := by simp only [map_add, b.lift_add]

theorem gsdbc_basis_of_read (b : GSDBC ι S S') {M M' : Type} [AddCommGroup M] [AddCommGroup M'] (Lm : M → M')
    {_ : Module K M} {_ : Module L M'} (r : M ≃ₗ[K] S.EqFun) (r' : M' ≃ₗ[L] S'.EqFun) (hL : ∀ x, r' (Lm x) = b.lift (r x))
    {κ : Type} [Fintype κ] (v : Module.Basis κ K M) :
    LinearIndependent L (fun k => Lm (v k)) ∧ ⊤ ≤ Submodule.span L (Set.range fun k => Lm (v k)) := by
  have hv : ∀ k, Lm (v k) = r'.symm (b.lift ((v.map r) k)) := fun k => by
    rw [Module.Basis.map_apply, ← hL, LinearEquiv.symm_apply_apply]
  simp only [hv]
  refine ⟨(gsdbc_lift_li b _).map' r'.symm.toLinearMap (LinearEquiv.ker _), ?_⟩
  have hr : (Set.range fun k => r'.symm (b.lift ((v.map r) k))) =
      r'.symm.toLinearMap '' Set.range fun k => b.lift ((v.map r) k) := by
    rw [← Set.range_comp]; rfl
  rw [hr, Submodule.span_image, eq_top_iff.2 (gsdbc_lift_span b _), Submodule.map_top, LinearEquiv.range]

end LiftBasis

end GlobalTheory.Mem.R3.DefLatBC

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.R3.DefLatBC.lift_basis_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → LinearIndependent (w'.st Z').toD7.what₂.LL (fun k => L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.basis k)) ∧ ⊤ ≤ Submodule.span (w'.st Z').toD7.what₂.LL (Set.range fun k => L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.basis k))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  have H1 := GlobalTheory.T.formsData_extendedData_baseChange_sameValues h1 h2 h3 h4 h5 h6 h7
  have H2 := GlobalTheory.T.formsLift_extendedData_determined_by_values h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and H1 H2) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf hP hpx Z hX Wt z g1 g2 g3 g4 Z' hX' g5 g6 g7 z' g8 g9 j j' hj φ hφ L hL hC
  beta_reduce at H
  clear H1 H2
  have Ha := H.1 B f T w hE hf hP hpx Z hX Wt z g1 g2 g3 g4 Z' hX' g5 g6 g7 z' g8 g9 j j' hj φ hφ
  cases Ha with
  | intro b hb =>
    exact GlobalTheory.Mem.R3.DefLatBC.gsdbc_basis_of_read b (fun x => L x) (Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm (Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (H.2 B f T w hE hf hP hpx Z hX Wt z g1 g2 g3 g4 Z' hX' g5 g6 g7 z' g8 g9 j j' hj φ hφ L hC b hb) _
