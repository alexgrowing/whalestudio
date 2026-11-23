import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaDictionaryComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagNonempty
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link

open scoped LaurentSeries
open GlobalTheory.Toroidal GlobalTheory.FlatLine

theorem exists_cusp_of_isCuspSec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ la : AllWt.Weight S.Dw, (∀ τ, Antitone (la τ)) → ∀ f, IsCuspSec Φ k la f → ∃ g ∈ cuspOn (unf s) Z (wtOf S.Dw la 0), (Φ.C k).val g = f := by
  intro D A N j S κ s Φ k Z hZ la _ f hf
  classical
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by
    have := (CmDim.cm_dim D A).2.1
    omega
  have hpq : 1 ≤ S.Dw.p + S.Dw.q := by
    have := S.two_le
    have := S.rank_eq
    omega
  set ex : Ix S.Dw → ℤ := GlobalTheory.AllWt.exOf S.Dw la 0 with hexd
  have hex : ex none = 0 := rfl
  have hreg : ∀ i (y : (Φ.C i).Y.X), (Φ.C i).π y ∉ genBd s.T.Z →
      ((Φ.C i).LEx ex).RegularAt y (Pi.single (M := fun i => (Φ.C i).Y.Fn) k f i) := by
    intro i y _
    by_cases hi : i = k
    · subst hi
      rw [Pi.single_eq_same]
      exact Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf.1 y
    · rw [Pi.single_eq_of_ne hi]
      exact Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (Submodule.zero_mem _) y
  obtain ⟨g, ⟨hg, hgv⟩, -⟩ :=
    existsUnique_rule_of_regular _ _ _ _ _ _ _ _ _ _ κ.e _ _ _ Φ ex hex (Pi.single (M := fun i => (Φ.C i).Y.Fn) k f) hreg
  have hg' : idem Z * g ∈ GlobalTheory.AllWt.secZ s.Xo κ.c ex := by
    simpa using mul_mem_secZ (idem_mem_secZ Z) hg
  have hsupp : idem Z * g ∈ suppOn Z := mul_comm g (idem Z) ▸ mul_mem_suppOn g (idem_mem_suppOn Z)
  have hval : ∀ i, (Φ.C i).val (idem Z * g) = Pi.single (M := fun i => (Φ.C i).Y.Fn) k f i := by
    intro i
    have hmul : (Φ.C i).val (idem Z * g) = (Φ.C i).val (idem Z) * (Φ.C i).val g := by
      letI := (constF κ.e (Φ.C i).Y).toAlgebra
      exact evalAt_mul (K := κ.c.F) (fun S _ _ => FrPt s.Xo κ.c S) (fun φ y z => FrMap φ y z) (idem Z) g (Φ.C i).y0
    rw [hmul, hgv i]
    by_cases hi : i = k
    · subst hi
      have h1 : (Φ.C i).val (idem Z) = 1 := by
        letI := (constF κ.e (Φ.C i).Y).toAlgebra
        exact evR_idem hZ (FlagTan.fromTest_of_isLocalRing _)
      rw [h1, one_mul]
    · rw [Pi.single_eq_of_ne hi, mul_zero]
  have hvan : ∀ i, (Φ.C i).Y.vanishOn ((Φ.C i).LEx ex) ((Φ.C i).val (idem Z * g)) (Φ.C i).Ybd := by
    intro i
    rw [hval i]
    by_cases hi : i = k
    · subst hi
      rw [Pi.single_eq_same]
      exact hf.2
    · rw [Pi.single_eq_of_ne hi]
      intro y _
      exact CartierDiv.vanishesAt_iff.2 ⟨Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (Submodule.zero_mem _) y, fun h => h.ne_zero rfl⟩
  refine ⟨idem Z * g, ⟨?_, hsupp⟩, by rw [hval k, Pi.single_eq_same]⟩
  by_cases hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < S.Dw.mult τ →
      (wtOf S.Dw la 0).1 (τ, j') ≤ (wtOf S.Dw la 0).1 (τ, i)
  swap
  · have hex' : ∃ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < S.Dw.mult τ),
        (wtOf S.Dw la 0).1 (τ, m) < (wtOf S.Dw la 0).1 (τ, m + 1) := by
      by_contra hne
      push_neg at hne
      apply hdec
      intro τ i j' hij hj'
      revert hj'
      induction j', hij using Nat.le_induction with
      | base => intro _; exact le_refl _
      | succ n hn ih => intro hj'; exact (hne τ n hj').trans (ih (by omega))
    obtain ⟨τ, m, hm, hlt⟩ := hex'
    have h0 : idem Z * g = 0 := GlobalTheory.NonDomVanish.eq_zero_of_lt hg' τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt
    rw [h0]
    exact Submodule.zero_mem _
  refine GlobalTheory.AllWt.mem_cuspW.2 ⟨hg', fun σ hσ => holCusp_mem_holSub _ _ fun k' => ?_⟩
  have hU : Formalism.L2.PjFree.IsUnf (s.U σ) := (s.unf σ hσ).1
  have hsec : ((unf s σ).X k').IsSec (modelWt (unf s σ) (wtOf S.Dw la 0) k') (rdU (unf s σ) (idem Z * g) k') :=
    GlobalTheory.T.isSec_reading_decreasing_integer_exponents _ _ _ _ _ _ σ _ (unf s σ) (KitEx.key_nonempty s) hσ ((ThetaDictCompare.isUnf_toU _).2 hU) hpq _
      (even_wtOf la 0) hdec _ hg' k'
  refine GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ hsec (GlobalTheory.CuspFrom.isModerate _ hf1 hsec) fun ξ hξ x hx => ?_
  letI : Algebra κ.c.F ℂ⸨X⸩ := (GlobalTheory.ArcId.cstL.comp σ).toAlgebra
  have halg : ∀ t : κ.c.F, algebraMap κ.c.F ℂ⸨X⸩ t = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ t)) :=
    fun _ => rfl
  obtain ⟨y, T₀, s', d, hbd, hd, hw⟩ := GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence _ _ _ _ _ _ σ _ (s.U σ) halg hσ hU k' ξ hξ x hx _ _ s.T.Z
  have hc : (algebraMap (PowerSeries ℂ) ℂ⸨X⸩).comp ((PowerSeries.C (R := ℂ)).comp σ) = algebraMap κ.c.F ℂ⸨X⸩ :=
    RingHom.ext fun t => (halg t).symm
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.T.eigenframe_base_change_local_rings _ _ _ _ _ _ _ _ s.T.Z (GlobalTheory.T.exists_lieEigenspaceFrame_localRing_baseChange _ _ _ _ _ _ _ _ s.T.Z) _ κ.e _ _ _ Φ
    (PowerSeries ℂ) ℂ⸨X⸩ ((PowerSeries.C (R := ℂ)).comp σ) y ex (idem Z * g) hc hbd hex hg' hvan
  exact GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line _ _ _ _ _ ξ x s' d T₀ (fun m => (evR s.Xo κ.c (idem Z * g) y).coeff m) hsec
    (GlobalTheory.CuspFrom.freqNonneg _ hf1 hsec) hξ hx hd (fun m hm => by rw [hvl]; exact GlobalTheory.CuspFrom.coeff_eq_zero hv hm)
    fun w hw' => ⟨(hw w hw').1, (hw w hw').2 ex hex _ hg'⟩

end GlobalTheory.CovHt.Link

end
