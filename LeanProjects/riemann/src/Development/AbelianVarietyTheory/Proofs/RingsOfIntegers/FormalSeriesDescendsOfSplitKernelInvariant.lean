import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowSpanXLeSpanFormalModuleMatrixStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteBasisPowerSeriesSubstFiniteColength
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InvariantsAndTraceFiniteFreeDomainEndomorphisms
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalMatrixKernelFiniteNcardEqRankStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLawsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupTranslateAutomorphismAndMatrixKernelStatement

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem mem_range_of_invariant (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] (Φ : A →+* R)
    (r : ℕ) (b : Fin r → R) (hb : ∀ f, ∃! cf : Fin r → A, f = ∑ i, Φ (cf i) * b i)
    {J : Type} (S : Set J) (hS : S.Finite) (hc : S.ncard = r) (g : J → R → R)
    (hg : ∀ α ∈ S, ∃ ψ : R →+* R, ∀ f, g α f = ψ f) (hfix : ∀ α ∈ S, ∀ a, g α (Φ a) = Φ a)
    (hinj : ∀ α ∈ S, ∀ β ∈ S, (∀ f, g α f = g β f) → α = β) (x : R) (hx : ∀ α ∈ S, g α x = x) :
    ∃ a, x = Φ a := by
  classical
  let _ : Algebra A R := Φ.toAlgebra
  have hsm : ∀ (a : A) (y : R), a • y = Φ a * y := fun a y => rfl
  have hli : LinearIndependent A b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    have h0 := (hb 0).unique (y₁ := c) (y₂ := 0) (by simpa [hsm] using hc0.symm) (by simp)
    intro i
    rw [h0]; rfl
  have hsp : ⊤ ≤ Submodule.span A (Set.range b) := by
    intro f _
    obtain ⟨c, hc, -⟩ := hb f
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => (hsm (c i) (b i)) ▸
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bs : Module.Basis (Fin r) A R := Module.Basis.mk hli hsp
  have : Module.Free A R := Module.Free.of_basis bs
  have : Module.Finite A R := Module.Finite.of_basis bs
  have hr : Module.finrank A R = r := by rw [Module.finrank_eq_card_basis bs, Fintype.card_fin]
  choose ψ hψ using hg
  let G : S → (R →ₐ[A] R) := fun α =>
    { ψ α.1 α.2 with
      commutes' := fun a => by
        have := hfix α.1 α.2 a
        rw [hψ α.1 α.2] at this
        exact this }
  have hG : ∀ (α : S) f, G α f = g α.1 f := fun α f => (hψ α.1 α.2 f).symm
  have hGi : Function.Injective G := fun α β h =>
    Subtype.ext (hinj _ α.2 _ β.2 fun f => by rw [← hG, ← hG, h])
  have : Fintype S := hS.fintype
  have hcard : (Finset.univ.image G).card = Module.finrank A R := by
    rw [Finset.card_image_of_injective _ hGi, hr, ← hc, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  obtain ⟨a, ha⟩ := (GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank A R _ hcard).1 x (by
    intro g0 hg0
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hg0
    rw [hG, hx _ α.2])
  exact ⟨a, ha.symm⟩

theorem descends_of_invariant : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (q q' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → q' * q = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → jacM B q ≠ 0 → SplitKer B q → ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → ∃ f', f = pullM B q f' := by
  intro V _ _ _ _ _ d O _ _ B hB n q q' N hN hq hj hs f hf
  have h0 : ∀ b i, MvPowerSeries.constantCoeff (matV B q (fun j => pt V (n := n) d j) b i) = 0 :=
    (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n 0 q q 0 0 (fun b i => by simp) (fun b i => by simp)).2.2.2.2.2.1
  set φ : Fin n × Fin d → MvPowerSeries (Fin n × Fin d) V :=
    fun s => matV B q (fun j => pt V (n := n) d j) s.1 s.2 with hφ
  have hφ0 : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0 := fun s => h0 s.1 s.2
  obtain ⟨⟨Ψ, -, hΨ⟩, -, hsub, -⟩ := GlobalTheory.PlaceInt.evC_spec V (Fin n × Fin d) (Fin n × Fin d) (Fin n × Fin d) φ
    (fun s => by rw [hφ0]; exact Ideal.zero_mem _)
  have hp : ∀ a, pullM B q a = Ψ a := fun a => hΨ a
  have hs' : ∀ a, MvPowerSeries.subst φ a = Ψ a := fun a => (hsub hφ0 a).symm.trans (hΨ a)
  obtain ⟨r, b, hr, hb⟩ := GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient V (Fin n × Fin d) φ hφ0 (GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n q q' N hN hq)
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.formalMatrixKernel_finite_ncard_eq_rank V d O B hB n q q' N hN hq hj hs
  have : IsDomain (MvPowerSeries (Fin n × Fin d) V) := NoZeroDivisors.to_isDomain _
  have hsh := (GlobalTheory.T.formalGroupTranslate_automorphism_and_matrixKernel V d O B n q).2.2
  obtain ⟨a, ha⟩ := mem_range_of_invariant (MvPowerSeries (Fin n × Fin d) V) (MvPowerSeries (Fin n × Fin d) V)
    (Ψ : MvPowerSeries (Fin n × Fin d) V →+* MvPowerSeries (Fin n × Fin d) V) r b
    (fun f => by simpa only [hs', RingHom.coe_coe] using hb f) (kerM B q) hfin (hcard.trans hr) (shift B.G.F)
    (fun α hα => by
      obtain ⟨ψ, hψ⟩ := (hsh α α hα.1 hα.1).1
      exact ⟨ψ.toRingEquiv.toRingHom, hψ⟩)
    (fun α hα a => by
      have := (hsh α α hα.1 hα.1).2.1.1 hα a
      rw [hp] at this
      exact this)
    (fun α hα β hβ h => (hsh α β hα.1 hβ.1).2.2.1 h) f hf
  exact ⟨a, ha.trans (hp a).symm⟩

end GlobalTheory.PlaceInt
