import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSubquotFiniteSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperSubquotientFinite

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem chartRing_fg (I : Chart x) : (chartRing S x I).FG := by
  classical
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine ⟨Finset.univ.image (fun l => x l / x i) ∪ I.1.image (fun j => x i / x j), ?_⟩
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    intro a ha
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
      Set.mem_range, Set.mem_image, Finset.mem_coe] at ha
    rcases ha with ⟨l, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X S l, isHomogeneous_X S i, by simp⟩
    · exact ⟨X i, X j, 1, X_mem_monos hj, isHomogeneous_X S i, isHomogeneous_X S j, by simp⟩
  · rintro a ⟨f, s, e, hs, hf, hse, rfl⟩
    set T := Algebra.adjoin S ((Finset.univ.image (fun l => x l / x i) ∪
      I.1.image (fun j => x i / x j) : Finset Ω) : Set Ω) with hT
    have h1 : aeval x f / x i ^ e ∈ T := by
      have hc : aeval x f / x i ^ e ∈ chartRing S x (singleChart hxi) :=
        ⟨f, X i ^ e, e, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) e, hf,
          isHomogeneous_X_pow _ _, by simp⟩
      refine Algebra.adjoin_mono ?_ (mem_ampleBase_of_mem_chartRing hxi hc)
      rintro _ ⟨l, rfl⟩
      simp
    have h2 : ∀ s ∈ monos (S := S) I.1, ∃ e', s.IsHomogeneous e' ∧ x i ^ e' / aeval x s ∈ T := by
      intro s hs
      induction hs using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨j, hj, rfl⟩ := ha
        refine ⟨1, isHomogeneous_X S j, ?_⟩
        rw [aeval_X, pow_one]
        exact Algebra.subset_adjoin (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
          Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨j, hj, rfl⟩)
      | one => exact ⟨0, isHomogeneous_one _ _, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨ea, ha1, ha2⟩ := ha
        obtain ⟨eb, hb1, hb2⟩ := hb
        refine ⟨ea + eb, ha1.mul hb1, ?_⟩
        rw [map_mul, pow_add, mul_div_mul_comm]
        exact T.mul_mem ha2 hb2
    obtain ⟨e', hse', h2'⟩ := h2 s hs
    have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos I hs
    have hs0' : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)
    obtain rfl : e = e' := hse.inj_right hse' hs0'
    have hxe : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    have : aeval x f / aeval x s = (aeval x f / x i ^ e) * (x i ^ e / aeval x s) := by
      field_simp
    rw [this]
    exact T.mul_mem h1 h2'

theorem isNoetherianRing_chart [IsNoetherianRing S] (I : Chart x) : IsNoetherianRing (chartRing S x I) := by
  have : Algebra.FiniteType S (chartRing S x I) := ⟨(Subalgebra.fg_top _).mpr (chartRing_fg I)⟩
  exact Algebra.FiniteType.isNoetherianRing S _

end SnapperSubquotientFinite

set_option maxHeartbeats 1000000 in
open SnapperQuotientAdditivity SnapperSubquotientFinite in

theorem SnapperSubquotFinite.proof (hfin : SnapperFinite.Statement.{u, v, w}) :
    SnapperSubquotFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F F₁ F₂ hfg h1 h21 i
  have hfg1 : ∀ I, (F₁.sub I).FG := fun I => by
    have := isNoetherianRing_chart (S := k) I
    exact (hfg I).of_le (h1 I)
  have hfg2 : ∀ I, (F₂.sub I).FG := fun I => by
    have := isNoetherianRing_chart (S := k) I
    exact (hfg I).of_le ((h21 I).trans (h1 I))

  have hH : ∀ (G : SubFamily k x E), (∀ I, (G.sub I).FG) → ∀ j,
      FiniteDimensional k (Cech.Hdeg (fun I : Chart x => (G.sub I : Type v)) (fun _ => ⊤)
        G.toSubSystem.res j) := by
    intro G hG j
    have h := hfin k Ω N x E G hG 0 Fin.elim0 Fin.elim0 0 j
    change FiniteDimensional k ((G.toSubSystem.twist (twistSys k x 0)).H j) at h
    rw [SubSystem.twist_twistSys_zero] at h
    have : FiniteDimensional k (Cech.H (fun I : Chart x => (G.sub I : Type v)) G.toSubSystem.res j) := h
    exact (hdegTopEquiv _ _ j).symm.finiteDimensional
  have hdd := CechDSq.proof (N + 1) (support x) k (fun I : Chart x => (F₁.sub I : Type v))
    F₁.toSubSystem.res (fun _ _ _ _ _ => LinearMap.ext fun _ => rfl)
  let φ : ∀ I : Chart x, F₂.sub I →ₗ[k] F₁.sub I := fun I =>
    { toFun := fun y => ⟨y, h21 I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ψ : ∀ I : Chart x, F₁.sub I →ₗ[k] F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I :=
    fun I => (SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I).mkQ
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => (F₂.sub I : Type v)) (B := fun I : Chart x => (F₁.sub I : Type v))
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)
    (ρA := F₂.toSubSystem.res) (ρB := F₁.toSubSystem.res)
    (ρC := SubSystem.quotRes F₁.toSubSystem F₂.toSubSystem)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤) (φ := φ) (ψ := ψ)
  have L1 := L (fun _ _ _ _ => rfl)
  have L2 := L1 (fun _ _ _ _ => rfl)
  have L3 := L2 (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
  have L4 := L3 (fun I a b hab => Subtype.ext (congrArg (fun z : F₁.sub I => (z : E)) hab))
  have L5 := L4 (fun I y => (Submodule.Quotient.mk_eq_zero _).2 y.2)
  have L6 := L5 (fun I m _ hm => ⟨⟨m, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)).1 hm⟩, Submodule.mem_top, rfl⟩)
  have L7 := L6 (fun I z _ => (Submodule.Quotient.mk_surjective _ z).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L8 := L7 (fun _ _ _ _ _ => Submodule.mem_top)
  have liftZP_newton := L8 hdd
  obtain ⟨δ, hgδ, -⟩ := (liftZP_newton.2 i).2
  have := hH F₁ hfg1 i
  have := hH F₂ hfg2 (i + 1)
  have hC := Module.Finite.of_exact (f := Cech.mapHdeg _ _ ψ _ _ i) (g := δ.rangeRestrict)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict]; exact LinearMap.exact_iff.1 hgδ))
    δ.surjective_rangeRestrict
  exact (hdegTopEquiv _ _ i).finiteDimensional

end

end GroundTheory.Heights₂.Heights.Kleiman
