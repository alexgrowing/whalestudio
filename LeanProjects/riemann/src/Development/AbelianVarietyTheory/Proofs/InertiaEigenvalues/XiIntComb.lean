import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralCoreSupLatticeCombinationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolysReachSmallFieldCoefficientFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.XiIntComb

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

def Good (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (u : ℂ)
    (P : PolF D (Wc D j).rank (Vc D j).rank) : Prop :=
  ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a,
    ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧
      (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a =
        ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k))

variable (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (u : ℂ)

theorem xi_eq_lin (Q : Finset (Pl D.host.E)) (M : ℕ) (P : PolF D (Wc D j).rank (Vc D j).rank) (a) :
    Y.Z.ρ.xi i j b D.nexp Q M h P a = xiLin Y.Z.ρ D.nexp i j b Q M h a P := rfl

theorem good_zero : Good Y i j b s h u 0 := by
  refine ⟨0, fun Q M _ _ a => ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, ?_⟩⟩
  rw [xi_eq_lin, map_zero, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]

theorem good_smul {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : Good Y i j b s h u P) (o : D.ntw.O i) :
    Good Y i j b s h u (Y.Z.ρ.eO i b o • P) := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨c, fun Q M hQ hs a => ?_⟩
  obtain ⟨n, o', m, hm, he⟩ := hc Q M hQ hs a
  refine ⟨n, fun k => o * o' k, m, hm, ?_⟩
  rw [xi_eq_lin, map_smul, smul_comm, ← xi_eq_lin, he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, map_mul]

theorem good_add {P P' : PolF D (Wc D j).rank (Vc D j).rank} (hP : Good Y i j b s h u P) (hP' : Good Y i j b s h u P') :
    Good Y i j b s h u (P + P') := by
  obtain ⟨c, hc⟩ := hP
  obtain ⟨c', hc'⟩ := hP'
  refine ⟨c + c', fun Q M hQ hs a => ?_⟩
  obtain ⟨n, o, m, hm, he⟩ := hc Q M hQ hs a
  obtain ⟨n', o', m', hm', he'⟩ := hc' Q M hQ hs a
  have hl : Y.Z.ρ.eO i b ((D.ntw.l i : ℕ) : D.ntw.O i) = ((D.ntw.l i : ℕ) : ℂ) := map_natCast _ _
  refine ⟨n + n', Fin.append (fun k => ((D.ntw.l i : ℕ) : D.ntw.O i) ^ c' * o k)
    (fun k => ((D.ntw.l i : ℕ) : D.ntw.O i) ^ c * o' k), Fin.append m m', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [Fin.append_left]; exact hm k
    · rw [Fin.append_right]; exact hm' k
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [xi_eq_lin, map_add, smul_add, ← xi_eq_lin, ← xi_eq_lin]
    congr 1
    · rw [show (((D.ntw.l i : ℕ) : ℂ) ^ (c + c') * u) = ((D.ntw.l i : ℕ) : ℂ) ^ c' * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) by ring,
        mul_smul, he, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, map_mul, map_pow, hl]
    · rw [show (((D.ntw.l i : ℕ) : ℂ) ^ (c + c') * u) = ((D.ntw.l i : ℕ) : ℂ) ^ c * (((D.ntw.l i : ℕ) : ℂ) ^ c' * u) by ring,
        mul_smul, he', Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, map_mul, map_pow, hl]

end GlobalTheory.XiIntComb

open GlobalTheory.XiIntComb in
theorem GlobalTheory.XiIntComb.xi_int_comb : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h P, Y.Z.ρ.IsDatum i j b s h P → ∃ (u : ℂ) (c : ℕ), u ≠ 0 ∧ ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hAR hSR hSI D X E Y hF hFP i hi j b s h P hd
  obtain ⟨u, hu0, hgen⟩ := GlobalTheory.T.thetaSeries_integral_core_supLattice_combination hAR hSR hSI D X E Y hF hFP i hi j b s h ⟨hd.split, hd.off, hd.fin, hd.supp, zero_mem _⟩
  have hB := Y.Z.good.base i j b
  have hm : ∀ τ, (Y.Z.ρ.B i j b).w.p τ + (Y.Z.ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ _ (Y.Z.ρ.B i j b).F.BS hB.wt hm
  have key : ∀ φ ∈ coefLatFn (Formalism.L2.Host.embLL0 D) (labLL0 D) (Y.Z.ρ.eO i b).range (Y.Z.ρ.B i j b).w.lam
      ((Y.Z.ρ.B i j b).latAt (finPt _ h)), ∃ P' ∈ (Y.Z.ρ.B i j b).valSpace,
        harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P' = φ ∧ Good Y i j b s h u P' := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := GlobalTheory.T.harmonic_polys_reach_small_field_coefficient_functions hAR hSR hSI D X E Y hF hFP i hi j b F
      exact ⟨P', h2, h3, hgen P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, good_zero Y i j b s h u⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, g1⟩ := h1
      obtain ⟨P₂, a2, rfl, g2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, good_add Y i j b s h u g1 g2⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, g1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨Y.Z.ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, good_smul Y i j b s h u g1 o⟩
  obtain ⟨P', h1, h2, ⟨c, hc⟩⟩ := key _ hd.mem.2
  obtain rfl : P = P' := sub_eq_zero.1 (hinj (P - P') (sub_mem hd.mem.1 h1) (by rw [map_sub, h2]; exact sub_self _))
  exact ⟨u, c, hu0, hc⟩
