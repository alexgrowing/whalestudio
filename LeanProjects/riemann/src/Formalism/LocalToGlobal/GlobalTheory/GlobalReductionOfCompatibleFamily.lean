import Formalism.SharpRestriction.GlobalSchurBounds.LinkPk
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.HermitianColumns.StarConj
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfFlags
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
import Formalism.LocalToGlobal.GlobalTheory.PowFourLtCeilThresholdPrime
import Formalism.LocalToGlobal.GlobalTheory.PlacesP
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfHermitian

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.Lnk NumberField

structure GlobalObj (D : D7) where

  host : Formalism.L2.Host.HostTied D

  herm : Formalism.L2.Herm.FullTied D

  forms : ∀ u : D.what₂.Word, Formalism.L2.Forms.FormsTied D u

structure CurveObj (D : D7) where
  δ : ℂ
  delta_pow_twelve_eq_discr : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ
  χ : TaylorLogMetric.IdE D → ℂ
  chi : TaylorLogMetric.IsChi D χ
  e : TaylorLogMetric.FamE D
  M : IntermediateField ℚ ℂ
  [nf : NumberField M]
  eL : D.what₂.LL ≃+* M
  emb : ∀ y, ((eL y : M) : ℂ) = D.what₂.embLL y
  d : D.what₂.Tau → M
  gen : ∀ τ, TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {d τ}

attribute [instance] CurveObj.nf

structure GlobalObjF {eps : ℝ} (Fm : FamP eps) where
  T : ∀ x (i : Fm.Ix x), GlobalObj (Fm.D x i)
  K : ∀ x (i : Fm.Ix x), CurveObj (Fm.D x i)

structure CurveTies (D : D7) (K : CurveObj D) : Prop where
  om : ∀ τ (s : D.what₂.LL →+* ℂ), D.gx.Om τ s =
    (Real.pi * ‖conjOf K.eL s (K.d τ)‖ ^ 2 / TaylorLogMetric.area (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)))⁻¹
  thOne : ∀ s : D.what₂.LL →+* ℂ, ∃ G, IsTheta0 D.host.d (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)) G ∧
    D.gx.thOne s ^ 2 = normSq1 (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)) G
  thFree : ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (c : (D.mem u).C.cls i) (c' : (D.mem u).C.cls (i + 1)),
    ∃ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)),
      TaylorLogMetric.admitted D (D.R.N i) (D.R.N (i + 1)) L L' ∧ TaylorLogMetric.CoefIn D (K.e (D.R.N i) (D.R.N (i + 1)) L L') K.M ∧
      ∀ s : D.what₂.LL →+* ℂ,
        (D.fm u).thFree i s c c' ^ 2 = normConj D K.δ K.e K.M (conjOf K.eL s) (D.R.N i) (D.R.N (i + 1)) L L'

structure GlobalTiesF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) : Prop where
  real : ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i)
  curve : ∀ x (i : Fm.Ix x), CurveTies (Fm.D x i) (O.K x i)
  extra : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.L2.Herm.ExtraTied (O.T x i).herm (Fm.ex x hx i)

structure GlobalChoicesF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) : Prop where
  dataIn : ∀ x (i : Fm.Ix x), TaylorLogMetric.DataIn (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK (O.K x i).δ) (O.K x i).M
  kRat : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, flipTwoThree.adm7 (Fm.D x i)

structure CurveClaims (D : D7) (C : ℝ) (K : CurveObj D) : Prop where
  cl22 : Cl22 D C D.host.ccK K.δ K.χ K.e
  thPow : GL3Theta.thPow D D.host.ccK K.δ K.e

structure PendClaims (D : D7) : Prop where

  colVal : flipTwoThree.adm3 D → ∀ u, Nonempty (flipTwoThree.ColVal D u)

  UpDownIncidenceInverse : ∀ u, product_first_zeroth_parts.UpDownIncidenceInverse D u

  admT : ∀ u, product_first_zeroth_parts.admT D u

  br : ∀ u, ∃ P : product_first_zeroth_parts.Pend D u, product_first_zeroth_parts.ArchimedeanSignatureMatching P

structure GlobalClaimsF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) (C : ℝ) : Prop where
  curve : ∀ x (i : Fm.Ix x), CurveClaims (Fm.D x i) C (O.K x i)
  pend : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, PendClaims (Fm.D x i)

def GlobalTiedF {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ O : GlobalObjF Fm, GlobalTiesF O ∧ GlobalChoicesF O ∧ GlobalClaimsF O C

theorem CurveTies.omTied {D : D7} {K : CurveObj D} (h : CurveTies D K)
    (hD : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK K.δ) K.M) : OmegaCompatible D K.δ :=
  ⟨K.M, K.nf, K.eL, K.emb, hD, fun τ => ⟨K.d τ, K.gen τ, fun s => h.om τ s⟩⟩

theorem CurveTies.thTied {D : D7} {K : CurveObj D} (h : CurveTies D K)
    (hD : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK K.δ) K.M) : ThetaCompatible D K.δ K.e :=
  ⟨K.M, K.nf, K.eL, K.emb, hD, h.thOne, h.thFree⟩

theorem tiesF_of_ties {eps : ℝ} {Fm : FamP eps} {O : GlobalObjF Fm} (h : GlobalTiesF O) : StandardLattice.TiesF Fm :=
  ⟨fun x i => (h.real x i).vol.volTie, fun x i => (h.real x i).dsig⟩

theorem curveLinks_of {eps : ℝ} {Fm : FamP eps} {O : GlobalObjF Fm} {C : ℝ} (hT : GlobalTiesF O) (hK : GlobalChoicesF O)
    (hC : GlobalClaimsF O C) (x : ℝ) (i : Fm.Ix x) :
    (∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ)) ∧
    ThFree (Fm.D x i) ∧ ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C := by
  have h3 := (hT.curve x i).thTied (hK.dataIn x i)
  have h5 := theta_power_of_first_layer (hC.curve x i).thPow
  exact ⟨⟨_, (O.K x i).delta_pow_twelve_eq_discr, omLink_of_tied ((hT.curve x i).omTied (hK.dataIn x i))⟩, thFree_of_tied h3 h5,
    ⟨_, (O.K x i).delta_pow_twelve_eq_discr, _, (O.K x i).chi, _, (hC.curve x i).cl22,
      thLinkLe_of_tied h3 h5 (fun u j hj => (O.T x i).herm.base.cls_nonempty u j hj)⟩⟩

theorem hecke_compatibility_of_groups {eps : ℝ} {Fm : FamP eps} {O : GlobalObjF Fm} {C : ℝ} (hT : GlobalTiesF O) (hC : GlobalClaimsF O C)
    (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) : IncidenceTransportConditions (Fm.D x i) u := by
  have hs : SeenDef (Fm.D x i) (Formalism.L2.Herm.toErrX (O.T x i).herm) := (hT.extra x hx i).join.errX_eq ▸ (Fm.ex x hx i).err.seen
  have hP := hC.pend x hx i
  exact ⟨hP.UpDownIncidenceInverse u, hP.admT u, base_lattice_convention_of_flags _ hs u (base_lattice_convention_of_hermitian (O.T x i).herm u), hP.br u⟩

theorem linkIn_of {eps : ℝ} (Fm : FamP eps) (C3 C22 : ℝ) (O : GlobalObjF Fm) (hT : GlobalTiesF O) (hK : GlobalChoicesF O)
    (hC : GlobalClaimsF O C22) (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)
    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i)) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) :
    StandardLattice.TiesF Fm ∧
    (∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ)) ∧
    (∀ x (i : Fm.Ix x), ThFree (Fm.D x i)) ∧
    (∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C22) ∧
    flipTwoThree.admF7 Fm ∧
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) ∧
    (∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) := by
  have tVol : StandardLattice.TiesF Fm := tiesF_of_ties hT
  obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven
  have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by
    obtain ⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩ := h59a (Fm.D x i) (Fm.L x i).sc
    exact ⟨p1, p2, p3, p4, p5, p5c, p6, s59 x hx i, p8⟩
  have h24 := s24 ⟨hF3, StandardLattice.column_lemma_family_of_definite Fm 100 C₅ h59 (fun _ _ => gram0Def _)⟩ tVol
  have h4p : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev :=
    fun x hx i => (h24.2.2.2.2.2.1 x hx i).2.2.2.1
  obtain ⟨a0, hStab⟩ := flipTwoThree.stabiliser_family_of_column_lemma Fm 100 C₅ h59 h4p
  refine ⟨tVol, fun x i => (curveLinks_of hT hK hC x i).1, fun x i => (curveLinks_of hT hK hC x i).2.1,
    fun x i => (curveLinks_of hT hK hC x i).2.2, ⟨0, fun x _ hx i => hK.kRat x hx i⟩, ?_,
    ⟨Fm.x1 + 1, fun x hx i u => hecke_compatibility_of_groups hT hC x (by linarith) i u⟩⟩
  refine ⟨max a0 (Fm.x1 + 1), fun x hx i u => ?_⟩
  have h1 : Fm.x1 < x := by have := le_trans (le_max_right a0 (Fm.x1 + 1)) hx; linarith
  exact (hC.pend x h1 i).colVal (hStab x (le_trans (le_max_left _ _) hx) h1 i) u

theorem global_reduction_of_packets {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eL C3 crystallineComparison C22 : ℝ)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (heL : 0 ≤ eL) (hC0 : 1 ≤ C0)

    (O : GlobalObjF Fm)

    (hT : GlobalTiesF O)

    (hK : GlobalChoicesF O)

    (hC : GlobalClaimsF O C22)

    (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)

    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))
    (s22 : TaylorLogMetric.StatementFamilyConstant Fm C22) (s23 : flipTwoThree.KudlaFamilyStatement Fm) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) (s10 : product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison) :
    Fm.CoverAll → TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs eL := by
  intro hCov hTu hDG hCh hIn
  obtain ⟨tVol, tOm, tFree, tTh, t7, tCV, t10⟩ := linkIn_of Fm C3 C22 O hT hK hC hF3 s59 s24
  have provedFiveF : LocalQuadraticParts.SlopeLossFamily Fm eL := by
    obtain ⟨C5, c6, Cb, -, -, -, -, cTT, cBad, -⟩ := hCh
    exact Loss.slope_loss_lemma_family Fm Cb eL heL cTT cBad hIn.1 hCov
  obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven
  have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by
    obtain ⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩ := h59a (Fm.D x i) (Fm.L x i).sc
    exact ⟨p1, p2, p3, p4, p5, p5c, p6, s59 x hx i, p8⟩
  have h24 := s24 ⟨hF3, StandardLattice.column_lemma_family_of_definite Fm 100 C₅ h59 (fun _ _ => gram0Def _)⟩ tVol
  have h4p : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev :=
    fun x hx i => (h24.2.2.2.2.2.1 x hx i).2.2.2.1
  have h22 : TaylorLogMetric.ConclusionOnFamily Fm C22 := s22 (TaylorLogMetric.AdmF_of Fm (fun x i => UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _))
  have h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison := s10 (product_first_zeroth_parts.AdmF_of Fm C22 100 C₅ h22 h59 h4p t10)
  have provedFourF : LocalQuadraticParts.SlopeLemmaFamily Fm := Places.slope_lemma_link_form Fm Cabs CH C0 crystallineComparison (by linarith) h10 hTu hCh hIn
  exact linkGLOBAL_pk Fm Cabs CH C0 eL C3 crystallineComparison C22 hCabs hCH heL hC0 s59 s22 s23 s24 s10 provedFourF provedFiveF hF3 tVol
    tOm tFree tTh t7 (Places.settingF_of Fm hTu) tCV t10 hCov hTu hDG hCh hIn

theorem tiesF_of {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) : StandardLattice.TiesF Fm := by
  obtain ⟨O, hT, -, -⟩ := h
  exact tiesF_of_ties hT

theorem hecke_compatibility_beyond_threshold {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x)
    (u : (Fm.D x i).what₂.Word) : IncidenceTransportConditions (Fm.D x i) u := by
  obtain ⟨O, hT, -, hC⟩ := h
  exact hecke_compatibility_of_groups hT hC x hx i u

theorem GlobalTiedF.curveLinks {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) (x : ℝ) (i : Fm.Ix x) :
    (∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ)) ∧
    ThFree (Fm.D x i) ∧ ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C := by
  obtain ⟨O, hT, hK, hC⟩ := h
  exact curveLinks_of hT hK hC x i

theorem GlobalTiedF.kRat {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) : flipTwoThree.admF7 Fm := by
  obtain ⟨O, -, hK, -⟩ := h
  exact ⟨0, fun x _ hx i => hK.kRat x hx i⟩

theorem GlobalTiedF.colVal {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    flipTwoThree.adm3 (Fm.D x i) → ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) := by
  obtain ⟨O, -, -, hC⟩ := h
  exact (hC.pend x hx i).colVal

theorem GlobalTiedF.pend {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    flipTwoThree.adm7 (Fm.D x i) ∧ (flipTwoThree.adm3 (Fm.D x i) → ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) := by
  obtain ⟨O, -, hK, hC⟩ := h
  exact ⟨hK.kRat x hx i, (hC.pend x hx i).colVal⟩

theorem global_reduction_of_compatible_family {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eL C3 crystallineComparison C22 : ℝ)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (heL : 0 ≤ eL) (hC0 : 1 ≤ C0)
    (hT : GlobalTiedF Fm C22) (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)
    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))
    (s22 : TaylorLogMetric.StatementFamilyConstant Fm C22) (s23 : flipTwoThree.KudlaFamilyStatement Fm) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) (s10 : product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison) :
    Fm.CoverAll → TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs eL := by
  obtain ⟨O, a, b, c⟩ := hT
  exact global_reduction_of_packets Fm Cabs CH C0 eL C3 crystallineComparison C22 hCabs hCH heL hC0 O a b c hF3 s59 s22 s23 s24 s10

end Formalism.L2.GlobalTheoryTheory

end
