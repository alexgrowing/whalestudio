import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul : ∀ {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] {N : Type} [AddCommGroup N] [Module B N] [Module E N] [IsScalarTower E B N] [Module.Finite E N] (χ : G →* Bˣ) (ε : G →* Eˣ) (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ∀ δ : B, Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) = Ideal.span {δ} → finrank E ↥(H0dual ε ρ) = finrank E ↥(LinearMap.ker ((LinearMap.lsmul B N δ).restrictScalars E)) := by
  intro G E B _ _ _ _ _ N _ _ _ _ _ χ ε ρ hρ δ hδ
  set L := (LinearMap.lsmul B N δ).restrictScalars E with hL
  have key : H0dual ε ρ = (LinearMap.range L).dualAnnihilator := by
    ext f
    have hmem : f ∈ H0dual ε ρ ↔ ∀ (g : G) (x : N), f (ρ g x) = (ε g : E) * f x := by
      unfold H0dual
      exact Iff.rfl
    rw [hmem, Submodule.mem_dualAnnihilator]
    let S : Ideal B :=
      { carrier := {b | ∀ x : N, f (b • x) = 0}
        add_mem' := fun {a b} ha hb x => by
          simp only [Set.mem_setOf_eq] at ha hb
          rw [add_smul, map_add, ha x, hb x, add_zero]
        zero_mem' := fun x => by simp
        smul_mem' := fun c b hb x => by
          simp only [Set.mem_setOf_eq] at hb
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb _ }
    have hS : ∀ b, b ∈ S ↔ ∀ x : N, f (b • x) = 0 := fun b => Iff.rfl
    have hgen : ∀ g, (∀ x, f (ρ g x) = (ε g : E) * f x) ↔
        ((χ g : B) - algebraMap E B (ε g)) ∈ S := by
      intro g
      rw [hS]
      refine forall_congr' fun x => ?_
      rw [hρ, sub_smul, map_sub, algebraMap_smul, f.map_smul (ε g : E) x, smul_eq_mul, sub_eq_zero]
    constructor
    · intro h
      have hle : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) ≤ S := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        exact (hgen g).1 (h g)
      rw [hδ] at hle
      have hd : δ ∈ S := hle (Ideal.subset_span rfl)
      rintro _ ⟨x, rfl⟩
      exact hd x
    · intro h g
      rw [hgen]
      have hd : δ ∈ S := fun x => h _ ⟨x, rfl⟩
      have hle : Ideal.span {δ} ≤ S := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hd
      rw [← hδ] at hle
      exact hle (Ideal.subset_span ⟨g, rfl⟩)
  rw [key]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range L)
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  omega
