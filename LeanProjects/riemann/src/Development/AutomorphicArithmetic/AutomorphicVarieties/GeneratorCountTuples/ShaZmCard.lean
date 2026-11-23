import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ShaFrom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardHomQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

theorem UpperTheory.V.K.shaZmCard :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l), IsTotallyComplex L → Nat.card (ShaZm D 1 0) ≤ classNumber L := by
  intro l hl L Ω _ _ _ _ _ D hL
  obtain ⟨hinj, hmap⟩ := UpperTheory.V.Kum.shaZm L Ω l D 1 (Or.inr (nrRealPlaces_eq_zero_iff.2 hL))
  obtain ⟨ι, hι, -⟩ := zmodToQZ l 1
  have hc := UpperTheory.V.Kum.cardHomQZ l (Additive (ClassGroup (𝓞 L)))
  have hf : Finite (Additive (ClassGroup (𝓞 L)) →+ QZ l) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.out.ne_zero)
  let f : ClDual L l (ZMod (l ^ 1)) (ZMod (l ^ 1)) → (Additive (ClassGroup (𝓞 L)) →+ QZ l) := fun θ =>
    AddMonoidHom.mk' (fun c => ι (θ.1 c.toMul)) fun a b => by rw [toMul_add, θ.2.1, map_add]
  have hfi : Function.Injective f := fun a b h =>
    Subtype.ext (funext fun c => hι (DFunLike.congr_fun h (Additive.ofMul c)))
  have hfin : Finite (ClDual L l (ZMod (l ^ 1)) (ZMod (l ^ 1))) := Finite.of_injective f hfi
  have h1 : Nat.card (ShaZm D 1 0) = Nat.card ((ShaZm D 1 0).map (resZm D 1)) :=
    Nat.card_congr (Submodule.equivMapOfInjective _ hinj _).toEquiv
  have h2 : Nat.card ((ClDual L l (ZMod (l ^ 1)) (ZMod (l ^ 1))).map
      (LinearMap.funLeft (ZMod (l ^ 1)) (ZMod (l ^ 1)) (artCl L Ω))) ≤ Nat.card (ClDual L l (ZMod (l ^ 1)) (ZMod (l ^ 1))) :=
    Nat.card_le_card_of_surjective _ (LinearMap.submoduleMap_surjective _ _)
  have h3 := Nat.card_le_card_of_injective f hfi
  have h4 : l ^ (Nat.card (Additive (ClassGroup (𝓞 L)))).factorization l ≤ Nat.card (Additive (ClassGroup (𝓞 L))) :=
    Nat.ordProj_le l Nat.card_pos.ne'
  have h5 : Nat.card (Additive (ClassGroup (𝓞 L))) = classNumber L := by
    rw [classNumber, ← Nat.card_eq_fintype_card]; rfl
  rw [h1, hmap]
  omega
