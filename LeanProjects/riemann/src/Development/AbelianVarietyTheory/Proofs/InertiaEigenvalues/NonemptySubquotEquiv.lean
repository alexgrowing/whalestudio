import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocEulerScalars

theorem nonempty_subquot_equiv {R R' X : Type*} [Ring R] [Ring R'] [AddCommGroup X] [Module R X]
    [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    Nonempty ((Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype)) := by
  refine ⟨Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => ?_⟩
  change (B.comap Z.subtype).quotientRel a b ↔
    (B'.comap Z'.subtype).quotientRel (Equiv.subtypeEquivRight hZ a) (Equiv.subtypeEquivRight hZ b)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap]
  exact hB _

theorem localEulerChar_above : LocalFiniteness → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation Λ (Dec (F := F) A) M), (∀ m : M, l • m = 0) → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ContAction ρ → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ ReciprocityTheory.Gal.locDeg v := by
  intro hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ A v ρ hl hA hv hc

  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule fun m => by rw [pow_one]; exact hl m
  let ρ' : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M := zmodRep (l ^ 1) ρ
  have hc' : ContAction ρ' := hc

  have hd : ∀ c : Dec (F := F) A → M, d1 ρ c = d1 ρ' c := fun c => by
    funext p
    obtain ⟨g, h⟩ := p
    rw [d1_apply, d1_apply]
    rfl
  have hZ1 : ∀ f, f ∈ Z1 ρ ↔ f ∈ Z1 ρ' := fun f => by
    rw [mem_Z1_iff_cocycle, mem_Z1_iff_cocycle]
    exact Iff.rfl
  have hB1 : ∀ f, f ∈ B1 ρ ↔ f ∈ B1 ρ' := fun f => by
    rw [mem_coboundaries1, mem_coboundaries1]
    exact Iff.rfl
  have hZ2 : ∀ f, f ∈ Z2 ρ ↔ f ∈ Z2 ρ' := fun f => by
    rw [mem_cocycles2, mem_cocycles2]
    exact Iff.rfl
  have hB2 : ∀ f, f ∈ B2 ρ ↔ f ∈ B2 ρ' := fun f => by
    rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]
    simp only [hd]
  obtain ⟨e1⟩ := nonempty_subquot_equiv (Z1 ρ) (B1 ρ) (Z1 ρ') (B1 ρ') hZ1 hB1
  obtain ⟨e2⟩ := nonempty_subquot_equiv (Z2 ρ) (B2 ρ) (Z2 ρ') (B2 ρ') hZ2 hB2
  have c1 : Nat.card (H1 ρ) = Nat.card (H1 ρ') := Nat.card_congr e1
  have c2 : Nat.card (H2 ρ) = Nat.card (H2 ρ') := Nat.card_congr e2

  obtain ⟨-, h1, h2, -⟩ := hF F Ω l 1 M A ρ' v Nat.one_pos hA hc'
  have hχ := (hE F Ω l 1 M A ρ' v Nat.one_pos hA hc').1 hv
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [c1, c2]
  convert hχ using 3

  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

end GlobalTheory.LocEulerScalars
