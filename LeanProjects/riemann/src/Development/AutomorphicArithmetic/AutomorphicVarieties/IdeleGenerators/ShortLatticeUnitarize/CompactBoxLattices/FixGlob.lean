import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc UpperTheory.V.Af.GlobalFixedVectors Matrix

private theorem mem_Kc {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} :
    k ∈ Kc c ↔ ∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := by
  simp [Kc, Subgroup.mem_iInf]

private theorem entry_Kc {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) (i j : Fin 2) :
    k i j ∈ UpperTheory.V.Af.Ohat F := by
  refine mem_Ohat.2 fun w => ?_
  obtain ⟨g, -, hg⟩ := mem_Kc.1 hk w
  have e := congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) hg
  change ((g i j : w.adicCompletionIntegers F) : w.adicCompletion F) = pLoc F w (k i j) at e
  rw [← e]
  exact (g i j).2

private theorem Kc_le {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) : k ∈ KLev F 2 1 := by
  let A : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F) := fun i j => ⟨k i j, entry_Kc hk i j⟩
  let B : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F) := fun i j => ⟨(k⁻¹ : GF F) i j, entry_Kc (inv_mem hk) i j⟩
  have hA : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix A = k.val := rfl
  have hB : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix B = (k⁻¹ : GF F).val := rfl
  have hinj : Function.Injective ((UpperTheory.V.Af.Ohat F).subtype.mapMatrix (m := Fin 2)) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_, ?_⟩
  · rw [map_mul, map_one, hA, hB, Units.mul_inv]
  · rw [map_mul, map_one, hA, hB, Units.inv_mul]
  · haveI : Subsingleton (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(UpperTheory.V.Af.Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · exact Units.ext hA

theorem UpperTheory.V.Sd.Wc.fixGlob :
    UpperTheory.V.Sd.Wc.FixGlob := by
  classical
  intro F _ _ V _ _ ρ hρ c x hc
  have key : ∀ S : Finset (Pl F),
      (∀ k ∈ KAway 2 1 S, k ∈ Kc c → ρ k x = x) → (∀ k ∈ KAway 2 1 ∅, k ∈ Kc c → ρ k x = x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      intro h
      refine ih fun k hk hl => ?_
      rw [mem_Kc] at hl
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 1 (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hc w _ (hl w)
      have h4 := h _ h2 (mem_Kc.2 fun v => by
        by_cases hv : v = w
        · subst hv; simp [pLoc_locGL]
        · simpa [pLoc_locGL_of_ne hv] using hl v)
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) ((hρ x).mem_nhds (by simp))
  intro k hk
  exact key S (fun k hk _ => hS hk) k (mem_KAway.2 ⟨Kc_le hk, by simp⟩) hk
