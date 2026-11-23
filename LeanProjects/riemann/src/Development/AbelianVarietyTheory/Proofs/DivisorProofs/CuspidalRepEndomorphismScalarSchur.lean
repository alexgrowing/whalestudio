import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.Published

namespace GlobalTheory.CuspSchur

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def imgPart (π : CuspSub E a) (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (w : W) : Submodule ℂ π.V where
  carrier := {ψ | (∀ k ∈ L, π.op (.fin k) ψ = ψ) ∧
    ∃ T : W →ₗ[ℂ] π.V, (∀ k v, T (ρ k v) = π.op (.cpt k) (T v)) ∧ T w = ψ}
  add_mem' := by
    rintro x y ⟨h1, T, h2, rfl⟩ ⟨h3, T', h4, rfl⟩
    exact ⟨fun k hk => by rw [map_add, h1 k hk, h3 k hk], T + T', fun k v => by simp [h2, h4], rfl⟩
  zero_mem' := ⟨fun _ _ => map_zero _, 0, fun _ _ => by simp, rfl⟩
  smul_mem' := by
    rintro c x ⟨h1, T, h2, rfl⟩
    exact ⟨fun k hk => by rw [map_smul, h1 k hk], c • T, fun k v => by simp [h2], rfl⟩

theorem finiteDimensional_imgPart (π : CuspSub E a) {L : Subgroup (GL (Fin a) (Af E))}
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (Kinf E a) W} (hρ : AutFin.IsContRep ρ) (w : W) :
    FiniteDimensional ℂ (imgPart π L ρ w) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ π.V, cap τ u φ = c • φ := fun τ u =>
    π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := GlobalTheory.automorphicFormsFiniteGL E a L hL W ρ hρ c
  refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ (imgPart π L ρ w).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms L ρ c))
    fun v => Submodule.subset_span ⟨(π.cusp _ v.1.2).1, fun k hk => congrArg Subtype.val (v.2.1 k hk), fun g => ?_,
      fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  obtain ⟨T, hT, e⟩ := v.2.2
  have h := AutFinGL.type_of_map ρ (π.V.subtype ∘ₗ T) (fun k w => congrArg Subtype.val (hT k w)) w g
  rw [LinearMap.comp_apply, e] at h
  exact h

theorem schur : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (x : CuspSub E a)
    (f : x.V →ₗ[ℂ] x.V), (∀ o φ, f (x.op o φ) = x.op o (f φ)) → ∃ c : ℂ, ∀ φ, f φ = c • φ := by
  intro E _ _ _ a π f hf
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hL : IsOpen (LocEx.stab π.finPart ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) := π.isSmooth_finPart _
  have : FiniteDimensional ℂ (LocEx.orbSpan φ) := (π.cusp φ hφ).1.kfin
  have hSV : LocEx.orbSpan φ ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact π.stable (.cpt k) φ hφ)
  let w : LocEx.orbSpan φ := ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩
  let U := imgPart π (LocEx.stab π.finPart ⟨φ, hφ⟩) (sub (cptRep E a) _ (LocEx.orbSpan_stable φ)) w
  have : FiniteDimensional ℂ U := finiteDimensional_imgPart π hL (LocEx.isContRep_sub _ _) w
  have hφU : (⟨φ, hφ⟩ : π.V) ∈ U := ⟨fun k hk => hk, Submodule.inclusion hSV, fun _ _ => rfl, rfl⟩
  have hfU : ∀ v ∈ U, f v ∈ U := by
    rintro _ ⟨h1, T, h2, rfl⟩
    exact ⟨fun k hk => by rw [← hf, h1 k hk], f ∘ₗ T, fun k v => by simp [h2, hf], rfl⟩
  have : Nontrivial U := ⟨⟨⟨_, hφU⟩, 0, fun e => h0 (congrArg (fun z : U => z.1.1) e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrict hfU)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv1 : f v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases π.irred ((Module.End.eigenspace f c).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨y, hy, rfl⟩
    refine ⟨π.op o y, Module.End.mem_eigenspace_iff.2 ?_, rfl⟩
    rw [hf, Module.End.mem_eigenspace_iff.1 hy, map_smul]) with h1 | h1
  · have h2 : v.1.1 ∈ (Module.End.eigenspace f c).map π.V.subtype := ⟨v.1, Module.End.mem_eigenspace_iff.2 hv1, rfl⟩
    rw [h1] at h2
    exact absurd (Subtype.ext (Subtype.ext ((Submodule.mem_bot ℂ).1 h2))) hv.2
  · intro ψ
    obtain ⟨y, hy, e⟩ : ψ.1 ∈ (Module.End.eigenspace f c).map π.V.subtype := h1.symm ▸ ψ.2
    obtain rfl : y = ψ := Subtype.ext e
    exact Module.End.mem_eigenspace_iff.1 hy

end GlobalTheory.CuspSchur

end
