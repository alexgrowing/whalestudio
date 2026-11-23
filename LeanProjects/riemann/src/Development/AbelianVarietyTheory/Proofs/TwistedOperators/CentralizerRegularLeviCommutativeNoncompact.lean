import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalUnitaryScalingWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeightsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPowArchProjNotMemOfEigenvalueTwoStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.LeviCent

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (extSub act)
open Matrix
open scoped TensorProduct

theorem nontrivial_AF (F : Type) [Field F] [NumberField F] : Nontrivial (AF F) := ⟨⟨0, 1, fun e => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact zero_ne_one ((map_zero (evInf F w)).symm.trans ((congrArg (evInf F w) e).trans (map_one _)))⟩⟩

theorem exists_aeval_of_mem_cent {D : D7} {V : HSp D} {γ : GF V} (hγ : IsRegSS γ.1.1) {g : GA D V}
    (hg : g ∈ cent (rat V γ)) :
    ∃ p : (AF D.host.F ⊗[D.host.F] D.host.E)[X],
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).1 = aeval (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (rat V γ)).1 p := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field γ.1.1 hγ
  refine GlobalTheory.Orb.exists_aeval_of_cyclic (v := inclR (AF D.host.F) ∘ v) ?_ ?_
  · change IsUnit (GlobalTheory.ClassParam.krylov (γ.1.1.map (inclR (AF D.host.F))) _).det
    rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hv).map _
  · have := congrArg (fun x => (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram x).1) (mem_cent.1 hg)
    simp only [map_mul, Units.val_mul] at this
    exact this

theorem mem_parab_of_mem_cent {D : D7} {V : HSp D} {γ : GF V} (hγ : IsRegSS γ.1.1) {g : GA D V}
    (hg : g ∈ cent (rat V γ)) (W : Submodule D.host.E V.V)
    (h : rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) W) :
    g ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) W := by
  set S := extSub (F := D.host.F) V (AF D.host.F) W
  have hs : ∀ y, y ∈ S ↔ act D.sp.cm V (rat V γ) y ∈ S := h
  set M := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (rat V γ)).1
  have hM : ∀ y ∈ S, M *ᵥ y ∈ S := fun y hy => (hs y).1 hy
  have hp : ∀ p : (AF D.host.F ⊗[D.host.F] D.host.E)[X], ∀ y ∈ S, aeval M p *ᵥ y ∈ S := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      intro y hy
      rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact Submodule.smul_mem _ a hy
    | add p q hp hq =>
      intro y hy
      rw [map_add, Matrix.add_mulVec]
      exact add_mem (hp y hy) (hq y hy)
    | monomial n a ih =>
      intro y hy
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec]
      exact ih _ (hM y hy)
  have key : ∀ g ∈ cent (rat V γ), ∀ y ∈ S, act D.sp.cm V g y ∈ S := by
    intro g hg y hy
    obtain ⟨p, e⟩ := exists_aeval_of_mem_cent hγ hg
    change (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).1 *ᵥ y ∈ S
    rw [e]
    exact hp p y hy
  exact fun y => ⟨key g hg y, fun hy => by
    have := key g⁻¹ (inv_mem hg) _ hy
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_inv] at this⟩

theorem exists_ne_zero_mem_sub {D : D7} {V : HSp D} (Φ : WittFrame V) {u : SV (wittIndex V)} (hu : u ≠ 0) :
    ∃ x ∈ Φ.sub u, x ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  have h1 := Φ.ef i i
  rw [if_pos rfl] at h1
  rcases h : u i with _ | _ | _
  · exact absurd h hi
  · refine ⟨Φ.f i, Submodule.subset_span (Or.inr ⟨i, h, rfl⟩), fun e => ?_⟩
    rw [e] at h1; simp [HSpace.hD] at h1
  · refine ⟨Φ.e i, Submodule.subset_span (Or.inl ⟨i, h, rfl⟩), fun e => ?_⟩
    rw [e] at h1; simp [HSpace.hD] at h1

theorem cent_levi (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))) (hP : IsPar P) (γ : GF V)
    (hγ : IsRegSS γ.1.1) (hl : rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P) :
    IsMulCommutative (cent (rat V γ)) ∧ cent (rat V γ) ≤ Φ.levi D.sp.cm (AF D.host.F) P ∧
      (P ≠ ∅ → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w))) := by
  have hl' : ∀ u ∈ P, rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u) ∧
      rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (-u)) := fun u hu =>
    Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hl u) hu)
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_, fun hne w hK => ?_⟩
  · obtain ⟨p, hp⟩ := exists_aeval_of_mem_cent hγ a.2
    obtain ⟨q, hq⟩ := exists_aeval_of_mem_cent hγ b.2
    apply GlobalTheory.AdelicU.matHom_injective (AF D.host.F) D.sp.cm.sig V.gram
    apply Units.ext
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul, hp, hq]
    rw [← map_mul, ← map_mul, mul_comm]
  · refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mem_parab_of_mem_cent hγ hg _ (hl' u hu).1
    · exact mem_parab_of_mem_cent hγ hg _ (hl' u hu).2
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hu0 : u ≠ 0 := fun e => hP.1 (e ▸ hu)
    have := nontrivial_AF D.host.F
    have hi : rat V γ⁻¹ ∈ Φ.levi D.sp.cm (AF D.host.F) P := by rw [map_inv]; exact inv_mem hl
    have hi' := Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hi u) hu)
    have h1 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 (hl' u hu).1
    have h2 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 (hl' u hu).2
    have h3 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 hi'.1
    have h4 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 hi'.2
    obtain ⟨g, g1, g2, g3⟩ := GlobalTheory.T.exists_rationalUnitary_scaling_wittFrame D V Φ u
    have hc : Commute g γ := GlobalTheory.T.commute_of_wittFrame_weights D V Φ u γ g 2 h1 h2 h3 h4 g1 g2 g3
    obtain ⟨x, hxu, hx0⟩ := exists_ne_zero_mem_sub Φ hu0
    obtain ⟨n, hn⟩ := GlobalTheory.T.exists_pow_archProj_not_mem_of_eigenvalue_two D V g x hx0 (g1 x hxu) w _ hK
    exact hn (mem_cent.2 (((hc.pow_left n).map (rat V)).map (projArch D.sp.cm.sig V.gram w)).eq)

end GlobalTheory.LeviCent
