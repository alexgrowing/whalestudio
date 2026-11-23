import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfExhaustOfAvgCutoff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFibMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section eqv

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem psi_star_mul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : B.Mat k r) :
    star (psi k r z c x) * psi k r z c x = 1 := by
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (Complex.I * (((c * ell k r z x).re : ℝ) : ℂ)) +
      Complex.I * (((c * ell k r z x).re : ℝ) : ℂ) = 0 := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [h, Complex.exp_zero]

def oneP : B.SS k r := (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), (1 : B.Mat k r)))

theorem oneP_inSS (D : B.RealPlaceData k r Wp Wq) : D.inSS oneP :=
  ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one⟩

theorem sgs_oneP (g : B.Mat k r) : B.sgs oneP g = g := by
  show (1 : B.Mat k r)⁻¹ * (1 : B.Mat k r)⁻¹ * g * 1 * 1 = g
  simp

theorem eqv_of_FFl (D : B.RealPlaceData k r Wp Wq) (X : B.Mat k r → (Wq →L[ℂ] Wp))
    (hX : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z'))
    {p : B.SS k r} (hp : D.inSS p) {y : B.Mat k r} (hy : y ∈ JF.Om k r D.z D.z') :
    JF.xiP D p • B.rho D p X y = X y := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hnN : (Matrix.of p.1.2 : B.Mat k r)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv h2
  have mem : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hg.1, hg.2⟩
  have nlev : ∀ m ∈ Nset k r, m ∈ Q.Nlev k r 0 := fun m hm => ⟨hm, (Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 m).2 hm.1⟩
  have hyn : y * (Matrix.of p.2.2 : B.Mat k r) ∈ JF.Om k r D.z D.z' := by
    have := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D (p := (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), p.2.2)))
      ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h4⟩ hy
    have e : B.sgs (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), p.2.2)) y =
        y * (Matrix.of p.2.2 : B.Mat k r) := by
      show (1 : B.Mat k r)⁻¹ * (1 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) * 1 = _
      simp
    rwa [e] at this
  have hnyn : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) ∈ JF.Om k r D.z D.z' := by
    have := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D (p := (((1 : B.Mat k r), p.1.2), ((1 : B.Mat k r), p.2.2)))
      ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h2, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h4⟩ hy
    have e : B.sgs (((1 : B.Mat k r), p.1.2), ((1 : B.Mat k r), p.2.2)) y =
        (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) := by
      show (1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) * 1 = _
      simp
    rwa [e] at this
  obtain ⟨_, hL, hR, hU⟩ := hX
  have e1 : X ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r)) =
      (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) • X y := by
    rw [Matrix.mul_assoc, hL _ (mem _ hyn) _ (nlev _ hnN), hR _ (mem _ hy) _ (nlev _ h4), smul_smul]
  have e2 : X ((Matrix.of p.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r)) *
      (Matrix.of p.2.1 : B.Mat k r)) =
      (D.π (Matrix.of p.1.1 : B.Mat k r)⁻¹).comp ((X ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y *
        (Matrix.of p.2.2 : B.Mat k r))).comp (D.π' (Matrix.of p.2.1 : B.Mat k r))) :=
    hU _ (mem _ hnyn) _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3
  have hsgs : B.sgs p y = (Matrix.of p.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y *
      (Matrix.of p.2.2 : B.Mat k r)) * (Matrix.of p.2.1 : B.Mat k r) := by
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) *
      (Matrix.of p.2.1 : B.Mat k r) = _
    simp only [Matrix.mul_assoc]
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  have hπ : ∀ w, D.π (Matrix.of p.1.1 : B.Mat k r) (D.π (Matrix.of p.1.1 : B.Mat k r)⁻¹ w) = w := by
    intro w
    have := D.π_rep.2 _ h1 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1)
    rw [Matrix.mul_nonsing_inv _ hu1, D.π_rep.1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]; rfl
  have hπ' : ∀ w, D.π' (Matrix.of p.2.1 : B.Mat k r) (D.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹ w) = w := by
    intro w
    have := D.π'_rep.2 _ h3 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h3)
    rw [Matrix.mul_nonsing_inv _ hu3, D.π'_rep.1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]; rfl
  have hc : JF.xiP D p * (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ *
      psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) = 1 := by
    unfold JF.xiP
    have a1 := BesselUnipotentEquiv.star_psi_inv D.z cStd D.z_mem _ h2
    have a2 := psi_star_mul D.z cStd ((Matrix.of p.1.2 : B.Mat k r)⁻¹)
    have a3 := psi_star_mul D.z' cStd (Matrix.of p.2.2 : B.Mat k r)
    rw [a1] at a2
    calc psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2)) *
          (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r))
        = (psi k r D.z cStd (Matrix.of p.1.2) * psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹) *
          (star (psi k r D.z' cStd (Matrix.of p.2.2)) * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) := by ring
      _ = 1 := by rw [a2, a3, one_mul]
  unfold B.rho
  rw [hsgs, e2, e1]
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, hπ', hπ, smul_smul, hc, one_smul]

end eqv

theorem sAExh_of_avgCutoff (hA : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff) : SAExh := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v X hX Cs hCs hCsQ
  set Db := (T v).base with hDb
  have hplace : Q.IsPlace (D.parOf S v) Db.z Db.z' Db.π Db.π' := (hB.1.2.2.2.1.2 v).2.2.2.1
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r Db.z Db.z' := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hX' : X ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (Q.OmPlus S.G.k S.G.r Db.z Db.z') := by
    have := hX
    unfold smoothFormsPositiveCone at this
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v] at this
  obtain ⟨K', hK'c, hCsK', hK'Q⟩ := exists_compact_between hCs (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open Db.z Db.z')
    (fun x hx => hQ x (hCsQ hx))
  obtain ⟨φ, hφ, ⟨C, hCc, hCO, hCφ⟩, hint⟩ := hA S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C := by
    refine closure_minimal (fun g hg => ?_) hCc.isClosed
    by_contra hgC
    exact hg (by simp [hCφ g hgC])
  refine ⟨fun g => φ g • X g, interior K', isOpen_interior, hCsK', ?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus S.G.k S.G.r Db.z Db.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨Cᶜ, fun _ => 0, hCc.isClosed.isOpen_compl, fun h => hO (hCO h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hCφ g hg]
  · exact hCc.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]
    exact fun g hg => (hCO (hsuppC hg)).2
  · intro y hy
    have hgy : B.gq Db y ∈ JF.Om S.G.k S.G.r Db.z Db.z' :=
      Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db y (hQ y hy)
    have hJ : B.JF Db (fun g => φ g • X g) (B.gq Db y) =
        (∫ p, φ (B.sgs p (B.gq Db y)) ∂Db.μSS) • X (B.gq Db y) := by
      change ∫ p, JF.xiP Db p • B.rho Db p (fun g => φ g • X g) (B.gq Db y) ∂Db.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Db] with p hp
      have hr : B.rho Db p (fun g => φ g • X g) (B.gq Db y) =
          φ (B.sgs p (B.gq Db y)) • B.rho Db p X (B.gq Db y) := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, eqv_of_FFl Db X hX' hp hgy]
    refine ⟨fun hyU => ?_, fun h0 => ?_⟩
    · have h1 := hint oneP (oneP_inSS Db) y (interior_subset hyU)
      simp only [sgs_oneP] at h1
      rw [hJ, h1, one_smul]
    · rw [hJ, h0, smul_zero]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
