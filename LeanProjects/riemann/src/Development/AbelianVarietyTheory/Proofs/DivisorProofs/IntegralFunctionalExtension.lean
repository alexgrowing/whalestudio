import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem integral_form_extend_of_saturated : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type)
    [CommRing O] [Algebra O C] (X : Type) [AddCommGroup X] [Module C X] [Module O X]
    [IsScalarTower O C X] (L : Submodule O X) (S : Submodule C X) (f : X →ₗ[C] C), v.Integers O →
    L.FG → (∀ x ∈ L, x ∈ S → f x ∈ (algebraMap O C).range) →
    ∃ F : X →ₗ[C] C, (∀ x ∈ L, F x ∈ (algebraMap O C).range) ∧ ∀ x ∈ L, x ∈ S → F x = f x := by
  intro C _ v O _ _ X _ _ _ _ L S f hv hfg hf
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : Module.Finite O L := Module.Finite.iff_fg.2 hfg
  let P : Submodule O L := (S.restrictScalars O).comap L.subtype
  let q : X →ₗ[O] X ⧸ S := (S.mkQ).restrictScalars O
  have hPq : P ≤ LinearMap.ker (q ∘ₗ L.subtype) := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero S).2 hx
  let ι : (L ⧸ P) →ₗ[O] X ⧸ S := P.liftQ (q ∘ₗ L.subtype) hPq
  have hιker : LinearMap.ker ι = ⊥ := by
    apply Submodule.ker_liftQ_eq_bot
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero S).1 hx
  have hιinj : Function.Injective ι := LinearMap.ker_eq_bot.1 hιker
  have hfree : Module.Free O (L ⧸ P) := by
    have : Module.Flat O (L ⧸ P) := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff y).1 hy
      have ha0 : (a : O) ≠ 0 := nonZeroDivisors.ne_zero a.2
      have h1 : (a : O) • ι y = 0 := by rw [← map_smul, Submonoid.smul_def] at *; rw [ha, map_zero]
      rw [← algebraMap_smul C (a : O) (ι y)] at h1
      have h2 : ι y = 0 := (smul_eq_zero.1 h1).resolve_left (by simpa using ha0)
      exact hιinj (by rw [h2, map_zero])
    exact Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O (L ⧸ P)
  have hliO : LinearIndependent O (ι ∘ b) := b.linearIndependent.map' ι hιker
  have hliC : LinearIndependent C (ι ∘ b) := (LinearIndependent.iff_fractionRing O C).1 hliO
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ (LinearMap.id) (Submodule.mkQ_surjective P)
  have hs' : ∀ y, P.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  have key : ∀ y, S.mkQ ((s y : L) : X) = ι y := by
    intro y
    conv_rhs => rw [← hs' y]
    rfl
  let g0 := (Module.Basis.span hliC).constr C (fun i => f ((s (b i) : L) : X))
  obtain ⟨h, hh⟩ := LinearMap.exists_extend g0
  have hhb : ∀ i, h (ι (b i)) = f ((s (b i) : L) : X) := by
    intro i
    have e1 : (⟨ι (b i), Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span C (Set.range (ι ∘ b))) =
        Module.Basis.span hliC i := by
      apply Subtype.ext; rw [Module.Basis.span_apply]; rfl
    have := LinearMap.congr_fun hh (Module.Basis.span hliC i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, g0, Module.Basis.constr_basis] at this
    rw [← this, ← e1]
  let F : X →ₗ[C] C := f - h ∘ₗ S.mkQ
  have hFS : ∀ x ∈ S, F x = f x := by
    intro x hx
    simp [F, (Submodule.Quotient.mk_eq_zero S).2 hx]
  refine ⟨F, ?_, fun x _ hx => hFS x hx⟩
  let G : (L ⧸ P) →ₗ[O] C := (F.restrictScalars O) ∘ₗ L.subtype ∘ₗ s
  have hG : G = 0 := by
    apply b.ext
    intro i
    simp only [G, F, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.sub_apply,
      Submodule.subtype_apply, LinearMap.zero_apply]
    rw [key, hhb, sub_self]
  intro x hx
  let xL : L := ⟨x, hx⟩
  let y := P.mkQ xL
  have hmem : ((xL - s y : L) : X) ∈ S := by
    have : P.mkQ (xL - s y) = 0 := by rw [map_sub, hs', sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hsplit : x = ((xL - s y : L) : X) + ((s y : L) : X) := by simp [xL]
  have hGy : F ((s y : L) : X) = 0 := LinearMap.congr_fun hG y
  rw [hsplit, map_add, hGy, add_zero, hFS _ hmem]
  exact hf _ (Submodule.coe_mem _) hmem

end GlobalTheory
