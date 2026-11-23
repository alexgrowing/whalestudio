import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SphericalVectorFixedLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeckeFrob
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem twisted_reciprocity_unramified_and_frobenius_eigenvalues_eq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {n : ℕ}
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (α : Fin n → ℂˣ) (hα : GlobalTheory.SmGL.HasSatake σ.ρ α) :
    ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (n : ℝ)) / 2)).unr ∧
    ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (n : ℝ)) / 2)).frobEig = twEig w α := by
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) hα]
  have hu : (GlobalTheory.WeilDeligne.WD.mk (GlobalTheory.WeilDeligne.WDRep.diag h fun i => (α i)⁻¹)).unr :=
    (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _)
  refine ⟨(GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 hu, ?_⟩
  rw [GlobalTheory.WeilDeligne.WD.frobEig_tw _ _ hu, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  simp [twEig]
theorem heckeSide_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {L : Type} [Field L] [NumberField L] [IsCMField L] {Ω : Type}
    [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω} {n : ℕ} (π : NG.AutRep L n) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (hu : IsUnif L s.v ϖ) (J : Subgroup (GAf L n))
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) (f : GAf L n → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) (c : ℕ → ℂ)
    (hc : ∀ k, 1 ≤ k → k ≤ n → NG.tN J s ϖ k f = c k • f) (hp : IsPlaceOver A (conjSplit s).w)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSplit s).w.adicCompletion L))) (hσ : IsLocS π.S (conjSplit s) σ) :
    ∃ α, GlobalTheory.SmGL.HasSatake σ.ρ α ∧ ∀ k, 1 ≤ k → k ≤ n →
      ((normV (conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k = (twEig (conjSplit s).w α).esymm k := by
  obtain ⟨i, T, hic, hcomp, hinj, hmem, heq⟩ := hσ
  have hf' := GlobalTheory.T.autRep_isotypic_splitPlace_localComponent L n π (conjSplit s) σ i T hinj hmem heq f hf
  obtain ⟨m, Tj, ej, hTj, hej, hsum⟩ := GlobalTheory.T.splitPlace_fixed_vector_sum_spherical_images L n π (conjSplit s) σ i hic hcomp f hf' hfix
  have hne : ∃ j, ej j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    rw [hsum]
    simp [h]
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := by
    obtain ⟨j, hj⟩ := hne
    exact (Submodule.ne_bot_iff _).2 ⟨ej j, hej j, hj⟩
  have hR := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL hp
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt hR ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hR σ).2 hsph)
  refine ⟨α, hα, fun k hk1 hk2 => ?_⟩
  have hfin := GlobalTheory.T.finite_heckeDoubleCoset_cosets_at_splitPlace L n s ϖ hu J hJ k
  have key : ((normV (conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k f =
      (twEig (conjSplit s).w α).esymm k • f := by
    conv_lhs => rw [hsum]
    rw [tN_sum J s ϖ k hfin, Finset.smul_sum, hsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ =>
      GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical L n s ϖ hu J hJ σ α hα i hic hcomp (Tj j) (hTj j) (ej j) (hej j) k hk1 hk2
  rw [hc k hk1 hk2, smul_smul] at key
  exact smul_left_injective ℂ hf0 key
theorem locPol_eq_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) → ∀ x, GlobalTheory.AutQuot.LocAt π w x →
    ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).unr ∧
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      (Multiset.map (fun α => X - Polynomial.C α)
        ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).frobEig).prod := by
  intro hL D π s w ϖ hcw hu J hJ f hf hf0 hfix c hc x hx
  have hw := conjSplit_w D s w hcw
  subst hw
  obtain ⟨σc, hσc, huniq⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV π (conjSplit s)
  obtain ⟨s', σ', h', hσ', hxe⟩ := hx
  have hh := huniq π s' h' σ' (NG.AutRep.iso_equivalence.refl π) hσ'
  have hxc : x = GlobalTheory.LocLanglands.cls σc := eq_of_heq (hxe.symm.trans (cls_heq h' σ' σc hh))
  subst hxc
  obtain ⟨α, hα, heig⟩ := _root_.GlobalTheory.HeckeFrob.heckeSide_alt hL π s ϖ hu J hJ f hf hf0 hfix c hc (D.nd.plOm.2 _) σc hσc
  obtain ⟨hun, hfe⟩ := _root_.GlobalTheory.HeckeFrob.twisted_reciprocity_unramified_and_frobenius_eigenvalues_eq hL (D.nd.plOm.2 _) σc α hα
  refine ⟨hun, ?_⟩
  rw [hfe, prod_eq_vieta D.R.nV _ (by simp [twEig])]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  rw [mul_assoc, heig k hk1 hk2]
end
end GlobalTheory.HeckeFrob
end
end
