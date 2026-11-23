import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem frob_ne_one {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hp : (Module.finrank F F').Prime) (hs : ∀ z, s z = z ^ Nat.card F) :
    s ≠ 1 := by
  rintro rfl
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Fintype F' := Fintype.ofFinite F'
  have hcard : Nat.card F' = Nat.card F ^ Module.finrank F F' := Module.natCard_eq_pow_finrank
  have hq : 1 < Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at hs hq hcard
  have hne : (X ^ q - X : F'[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F' hq
  have hdeg : (X ^ q - X : F'[X]).natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq F' hq
  have hsub : (Finset.univ : Finset F') ⊆ (X ^ q - X : F'[X]).roots.toFinset := by
    intro z _
    rw [Multiset.mem_toFinset, mem_roots hne]
    have := hs z
    simp only [AlgEquiv.one_apply] at this
    simp [IsRoot, ← this]
  have h1 : Nat.card F' ≤ q := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ Multiset.card (X ^ q - X : F'[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ q - X : F'[X]).natDegree := card_roots' _
      _ = q := hdeg
  rw [hcard] at h1
  have h2 : q ^ 2 ≤ q ^ Module.finrank F F' := Nat.pow_le_pow_right (by omega) hp.two_le
  nlinarith

theorem UpperTheory.Gal.InertialTypesAlt.killsNil :
    KillsAll → KillsOn fun a => a.D = [] := by
  intro h F F' _ _ _ _ s hp hs ι θ hθ a hD hok hq
  obtain ⟨q, D, L⟩ := a
  simp only at hD hq
  subst hD
  subst hq
  have key := h F F' s hp (frob_ne_one s hp hs) ι θ hθ L (fun p hp' => hok.2.2 p hp') (deg L) rfl
  have hrk : (⟨Nat.card F, [], L⟩ : Lbl).rk = deg L := by
    have h0 : GlobalTheory.Shin.deg ([] : List (ℕ × ℕ)) = 0 := rfl
    simp [Lbl.rk, h0]
  rw [hrk]
  simpa [Lbl.lift, JD_nil] using key
