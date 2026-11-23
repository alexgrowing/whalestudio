import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDominantWeightCuspSectionsNoCommonZeroStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanFamily

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_cuspA_of_lastPos : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos (T.Q.Dw j) a →
    4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n →
    Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤
      Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j a n : Set (T.R j))) := by
  intro D T h j hj σ hσ a n hdom hlast hn
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    a n hdom hlast hn
    (fun k => h.chiTriv j hj σ hσ a n hdom k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hI
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let _ : Algebra K ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨κ.comp (Ideal.Quotient.mkₐ K M), fun x hx => ?_⟩
  show κ (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]

theorem evR_of_frMap {D : D7} (T : CoreJ D) (h : LawsJ T) {j : ℕ} (hj : Formalism.L2.Pj.InR D j) (f : T.R j)
    (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (p : TRing T.Q.c.F) (ψ : p.R →ₐ[T.Q.c.F] S)
    (y : FrPt (T.Q.Xo j) T.Q.c p.R) (z : FrPt (T.Q.Xo j) T.Q.c S) (hz : FrMap ψ y z) :
    evR (T.Q.Xo j) T.Q.c f z = ψ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) z :=
    ⟨p, ψ, y, hz⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact h.evalWD j hj f hf S _ p _ ψ _ y z hT.choose_spec.choose_spec.choose_spec hz

set_option maxHeartbeats 1000000 in

theorem exists_family : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom b m ∧ (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) ∧ (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) ∧ ∀ P ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n), ∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  intro D T h j hj σ hσ a n hdom
  obtain ⟨b, m, hbm, hlast, hm, hnz⟩ := GlobalTheory.T.exists_dominantWeight_cuspSections_noCommonZero D T h j hj σ hσ
  haveI : FiniteDimensional T.Q.c.F (T.cuspA j b m) := h.cuspFD j hj b m hbm
  haveI : Module.Free T.Q.c.F (T.cuspA j b m) := Module.Free.of_divisionRing _ _
  let B := Module.finBasis T.Q.c.F (T.cuspA j b m)
  have hsec : ∀ i, (B i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c b m := fun i => cusp_le_sec _ _ _ _ _ (B i).2
  refine ⟨b, m, _, fun i => (B i : T.R j), hbm, hsec, ?_, ?_⟩
  · intro p y
    by_contra hne
    have hL := (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1
    obtain ⟨ψ, hψ⟩ := exists_complex_point σ _ hne
    obtain ⟨z, hz⟩ := hL.bc p.R (CAt σ) ψ y
    have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (B i : T.R j) z = 0 := fun i => by
      rw [evR_of_frMap T h hj _ (hsec i).1 p ψ y z hz]
      exact hψ _ (Ideal.subset_span ⟨i, rfl⟩)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨k, x, t, ht⟩ := (h.unf j hj σ hσ).2.2.1 z
    have hx0 : ∀ i, rdU (T.U j σ) (B i : T.R j) k x.1 = 0 := fun i => by
      have hw := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hsec i) t _ z ht
      rw [hz0 i] at hw
      have hu : wchar (ex (T.Q.Dw j) b m) t ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (t c).ne_zero
      have h0 := (mul_eq_zero.1 hw.symm).resolve_left hu
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2]
      exact congrArg toC h0
    let ev : FDSec (T.U j σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k x.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hall : ∀ f ∈ T.cuspA j b m, rdU (T.U j σ) f k x.1 = 0 := by
      intro f hf
      have key : ∀ g : T.cuspA j b m, g ∈ Submodule.span T.Q.c.F (Set.range B) →
          rdU (T.U j σ) (g : T.R j) k x.1 = 0 := by
        intro g0 hg0
        induction hg0 using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨i, rfl⟩ := hg
          exact hx0 i
        | zero => rw [Submodule.coe_zero, map_zero]; rfl
        | add g g' _ _ hg hg' =>
          rw [Submodule.coe_add, map_add, Pi.add_apply, Pi.add_apply, hg, hg', add_zero]
        | smul c g _ hg =>
          rw [Submodule.coe_smul, map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hg, smul_zero]
      exact key ⟨f, hf⟩ (B.mem_span _)
    have hle : Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j b m : Set (T.R j))) ≤ LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hall f hf
    obtain ⟨P, hP, hPx⟩ := hnz k x.1 x.2
    exact hPx (hle (holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ b m hbm hlast hm hP))
  · intro P hP i
    have hrd : rdU (T.U j σ) (B i : T.R j) ∈ holSub (T.U j σ).X (laU (T.U j σ) b m) :=
      ((mem_cusp _ _ _ _ _ _).1 (B i).2).2 σ hσ
    have hdab : Dom (a + b) (n + m) := ⟨fun τ => (hdom.1 τ).add (hbm.1 τ), hdom.2.add hbm.2⟩
    have hprod : P * rdU (T.U j σ) (B i : T.R j) ∈
        Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (a + b) (n + m)) := by
      refine ⟨?_, fun k x hx => by simp [hP.2 k x hx]⟩
      have hP1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hP.1
      have hr1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hrd
      refine (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).2 fun k => ?_
      rw [show laU (T.U j σ) (a + b) (n + m) k = laU (T.U j σ) a n k + laU (T.U j σ) b m k from
        GlobalTheory.CuspProduct.laU_add (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) a b n m hdom.2 hbm.2 k]
      exact (siegelSpaceAlgebra_holds (E := D.host.E) D.R.r _ _ _ 0).2.1 _ (hP1 k) _ (hr1 k).1
    have hlast' : LastPos (T.Q.Dw j) (a + b) := fun τ hτ hm0 =>
      lt_of_lt_of_le (hlast τ hτ hm0) (by simp)
    have hs := holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ (a + b) (n + m) hdab hlast' (by omega) hprod
    exact Submodule.span_mono (Set.image_mono (cusp_le_sec _ _ _ _ _)) hs

end GlobalTheory.SpanFamily
