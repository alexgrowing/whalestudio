import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubquotientJacquetModuleOfSupercuspidalSupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetProUnipotentRadicalFixedVectorsLiftStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.DepthZeroPass

theorem fixed_ne_bot_of_isSubquotient {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (hρ : IsSmooth ρ) (h : IsSubquotient τ ρ)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (hτ : fixed τ H ≠ ⊥) : fixed ρ H ≠ ⊥ := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hτ
  obtain ⟨u, rfl⟩ := hf w
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : V) = v} := by
      ext g
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hρ v
  obtain ⟨v, hv, hfv⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun g hg => by
    have h1 := mem_fixed.1 hw g hg
    show f (S.toRepresentation g u) = f u
    exact (f.isIntertwining _ _ g u).trans h1
  refine (Submodule.ne_bot_iff _).2 ⟨(v : V), mem_fixed.2 fun g hg => ?_, ?_⟩
  · have := mem_fixed.1 hv g hg
    exact congrArg Subtype.val this
  · intro h0
    apply hw0
    have hv0 : v = 0 := Subtype.ext h0
    have hfv' : f v = f u := hfv
    rw [← hfv', hv0, map_zero]

theorem fixed_piTensor_ne_bot {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (H : ∀ a, Subgroup (Γ a)) (h : ∀ a, fixed (ρ a) (H a) ≠ ⊥) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ H) ≠ ⊥ := by
  choose v hv hv0 using fun a => (Submodule.ne_bot_iff _).1 (h a)
  choose l hl using fun a => Module.Projective.exists_dual_eq_one ℂ (hv0 a)
  refine (Submodule.ne_bot_iff _).2 ⟨PiTensorProduct.tprod ℂ v, mem_fixed.2 fun g hg => ?_, fun h0 => ?_⟩
  · rw [piTensor_tprod]
    congr 1
    funext a
    exact mem_fixed.1 (hv a) (g a) (hg a trivial)
  · have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
    simp [hl] at this

theorem isCompact_leviKOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] :
    IsCompact (leviKOne k m : Set (Levi k m)) := by
  rw [leviKOne, Subgroup.coe_pi]
  exact isCompact_univ_pi fun a => levelPre_bot (k := k) (n := m a) ▸ isCompact_levelPre ⊥

theorem depthZeroInduction : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInduction := by
  intro hG hBZ hZ k _ _ _ _ _ x s hs hfix
  obtain ⟨r, u, e, hu, hsq⟩ := GlobalTheory.T.exists_subquotient_jacquetModule_of_supercuspidalSupport hG hBZ hZ k x s hs
  have hxs : IsSmooth x.rep := x.2.rep.smooth
  have h1 : fixed (piTensor fun a => (u a).rep) (leviKOne k fun a => Fin (u a).1) ≠ ⊥ :=
    fixed_piTensor_ne_bot _ _ fun a => hfix _ (hu a)
  have h2 := fixed_ne_bot_of_isSubquotient (isSmooth_jac e hxs) hsq isCompact_leviKOne h1
  obtain ⟨y, hy1, hy0⟩ := (Submodule.ne_bot_iff _).1 h2
  have hy2 : y ∈ fixed (jacU e x.rep) (leviKOne k fun a => Fin (u a).1) := mem_fixed.2 fun g hg => by
    have h3 := mem_fixed.1 hy1 g hg
    have h4 : deltaHalf k (fun a => Fin (u a).1) g = 1 :=
      deltaHalf_of_mem_leviK fun a _ => StepData.KOne_le_KO (hg a trivial)
    simpa [jac, twist_apply, h4] using h3
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.T.jacquet_proUnipotentRadical_fixed_vectors_lift k e x.rep ((hBZ k).1 _ _ x.rep hxs x.2.rep.irr) y hy2
  refine (Submodule.ne_bot_iff _).2 ⟨v, mem_fixed.2 fun g hg => mem_fixed.1 hv g (KOne_le_proRad e hg), ?_⟩
  rintro rfl
  exact hy0 rfl

end GlobalTheory.DepthZeroPass

end
