import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwiningGlOfUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroMapEqZeroOfWeightNe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InitMinorNeZeroOfStrictMono
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankLeFinrankDirectSumBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankIntertwiningMapDirectSum

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem branchesAlong_of_irreducible {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N) (lam : DomWeight N)
    (hirr : ∀ mu : DomWeight n, (smallRep ι mu).IsIrreducible)
    (hz : ∀ mu nu : DomWeight n, mu ≠ nu → ∀ φ : (smallRep ι mu).IntertwiningMap (smallRep ι nu), φ = 0) :
    BranchesAlong ι h lam := by
  classical
  have iso : Nonempty ((sumRep ι h lam).Equiv (resRep ι h lam)) := by
    refine GlobalTheory.nonempty_directSum_equiv_of_finrank_le ℂ H (Below h lam) _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1) _
      (fun mu => hirr mu.1) (fun i j hij => hz i.1 j.1 fun e => hij (Subtype.ext e)) (fun mu => ?_) (GlobalTheory.Branching.finrank_le_finrank_directSum_below n N h lam)
    obtain ⟨φ, hφ⟩ := GlobalTheory.Branching.exists_intertwining_ne_zero n N h lam mu.1 mu.2
    refine ⟨⟨φ.toLinearMap, fun y => φ.isIntertwining' (ι y)⟩, fun e => hφ ?_⟩
    have e' := congrArg Representation.IntertwiningMap.toLinearMap e
    exact Representation.IntertwiningMap.ext e'
  refine ⟨iso, fun mu => ?_⟩
  letI : Fintype (Below h lam) := Fintype.ofFinite _
  have hm := (GlobalTheory.IntertwinerSum.finrank_intertwiningMap_directSum ℂ H (Below h lam) _ _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1)
    (smallRep ι mu) (resRep ι h lam) iso).1
  have h0 : ∀ nu : DomWeight n, mu ≠ nu →
      Module.finrank ℂ ((smallRep ι mu).IntertwiningMap (smallRep ι nu)) = 0 := fun nu hne => by
    have : Subsingleton ((smallRep ι mu).IntertwiningMap (smallRep ι nu)) :=
      ⟨fun a b => (hz mu nu hne a).trans (hz mu nu hne b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  refine ⟨fun hI => ?_, fun hI => ?_⟩
  · unfold mult
    rw [hm, Finset.sum_eq_single (⟨mu, hI⟩ : Below h lam)]
    · have := hirr mu
      exact Representation.IsIrreducible.finrank_intertwiningMap_self _
    · intro b _ hb
      exact h0 b.1 fun e => hb (Subtype.ext e.symm)
    · simp
  · unfold mult
    rw [hm]
    exact Finset.sum_eq_zero fun b _ => h0 b.1 fun e => hI (e ▸ b.2)

theorem intertwining_unitary_eq_zero (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu)) : φ = 0 := by
  have := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  obtain ⟨f, hf, h0⟩ := GlobalTheory.Branching.exists_ne_zero_map_eq_zero_of_weight_ne n mu nu hne
    ⟨φ.toLinearMap, fun g => LinearMap.ext fun f => GlobalTheory.Branching.intertwining_gl_of_unitary n mu nu φ g f⟩
  refine (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_left fun hi => hf (hi ?_)
  rw [map_zero]; exact h0

theorem isIrreducible_smallRep_id (n : ℕ) (mu : DomWeight n) : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IsIrreducible := by
  have hU := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  let r : Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu) → Subrepresentation (smallRep (unitaryIncl n) mu) :=
    fun S => ⟨S.toSubmodule, fun u _ hv => S.apply_mem_toSubmodule (unitaryIncl n u) hv⟩
  have hnt : Nontrivial (Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (r S) with e | e
  · have e' := congrArg Subrepresentation.toSubmodule e
    exact Or.inl (Subrepresentation.ext e')
  · have e' := congrArg Subrepresentation.toSubmodule e
    exact Or.inr (Subrepresentation.ext e')

theorem intertwining_id_eq_zero (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IntertwiningMap (smallRep (MonoidHom.id (GL (Fin n) ℂ)) nu)) :
    φ = 0 := by
  have := intertwining_unitary_eq_zero n mu nu hne ⟨φ.toLinearMap, fun u => φ.isIntertwining' (unitaryIncl n u)⟩
  have e' := congrArg Representation.IntertwiningMap.toLinearMap this
  exact Representation.IntertwiningMap.ext e'

theorem branchesAlong_all (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    BranchesAlong (MonoidHom.id (GL (Fin n) ℂ)) h lam ∧ BranchesAlong (unitaryIncl n) h lam :=
  ⟨branchesAlong_of_irreducible _ h lam (isIrreducible_smallRep_id n) (intertwining_id_eq_zero n),
    branchesAlong_of_irreducible _ h lam (isIrreducible_smallRep_unitary n) (intertwining_unitary_eq_zero n)⟩

instance finite_cointertwining {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N)
    (lam : DomWeight N) (mu : DomWeight n) :
    FiniteDimensional ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) := by
  let L : (resRep ι h lam).IntertwiningMap (smallRep ι mu) →ₗ[ℂ] (nablaSq ℂ N lam →ₗ[ℂ] nablaSq ℂ n mu) :=
    { toFun := fun f => f.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective L fun _ _ e => Representation.IntertwiningMap.ext e

theorem comult_of_irreducible {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N)
    (lam : DomWeight N) (hirr : ∀ mu : DomWeight n, (smallRep ι mu).IsIrreducible)
    (hz : ∀ mu nu : DomWeight n, mu ≠ nu → ∀ φ : (smallRep ι mu).IntertwiningMap (smallRep ι nu), φ = 0)
    (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) = 0) := by
  classical
  have iso := (branchesAlong_of_irreducible ι h lam hirr hz).1
  letI : Fintype (Below h lam) := Fintype.ofFinite _
  have hm := (GlobalTheory.IntertwinerSum.finrank_intertwiningMap_directSum ℂ H (Below h lam) _ _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1)
    (smallRep ι mu) (resRep ι h lam) iso).2
  have h0 : ∀ nu : DomWeight n, nu ≠ mu →
      Module.finrank ℂ ((smallRep ι nu).IntertwiningMap (smallRep ι mu)) = 0 := fun nu hne => by
    have : Subsingleton ((smallRep ι nu).IntertwiningMap (smallRep ι mu)) :=
      ⟨fun a b => (hz nu mu hne a).trans (hz nu mu hne b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  refine ⟨fun hI => ?_, fun hI => ?_⟩
  · rw [hm, Finset.sum_eq_single (⟨mu, hI⟩ : Below h lam)]
    · have := hirr mu
      exact Representation.IsIrreducible.finrank_intertwiningMap_self _
    · intro b _ hb
      exact h0 b.1 fun e => hb (Subtype.ext e)
    · simp
  · rw [hm]
    exact Finset.sum_eq_zero fun b _ => h0 b.1 fun e => hI (e ▸ b.2)

theorem comult_id (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
        (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
        (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) = 0) :=
  comult_of_irreducible _ h lam (isIrreducible_smallRep_id n) (intertwining_id_eq_zero n) mu

theorem comult_unitary (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep (unitaryIncl n) h lam).IntertwiningMap
        (smallRep (unitaryIncl n) mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep (unitaryIncl n) h lam).IntertwiningMap
        (smallRep (unitaryIncl n) mu)) = 0) :=
  comult_of_irreducible _ h lam (isIrreducible_smallRep_unitary n) (intertwining_unitary_eq_zero n) mu

end GlobalTheory.Branching

namespace GlobalTheory.Published

theorem weylBranching_holds : WeylBranching := fun n N h _ lam => GlobalTheory.Branching.branchesAlong_all n N h lam

end GlobalTheory.Published
