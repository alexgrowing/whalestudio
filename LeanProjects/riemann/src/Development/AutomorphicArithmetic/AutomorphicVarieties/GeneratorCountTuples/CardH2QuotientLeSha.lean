import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.CardAbove

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

theorem UpperTheory.V.K.card_H2_quotient_le_sha :
    GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l) (e : ℤ), IsTotallyComplex L → let n := e + 1; Nat.card (H2 (zlTw D n) ⧸ lpow l (H2 (zlTw D n)) 1) ≤ Nat.card (Sha1 (zd D n 1) (locFam D.S D.A) (continuous_locFam D.S D.A)) * l ^ Module.finrank ℚ L := by
  intro hP hF hT l hl L Ω _ _ _ _ _ D e hc
  classical
  have hcase : PTCase L l := Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 hc)
  have hS := fun r hr => (finite_level D e hP hcase r hr).2.1
  have h3 := (finite_level D e hP hcase 1 one_pos).2.2
  have hg := (global_lim D e hF hT hS h3).2 1
  intro n
  have : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have hfd : Finite (TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) := DFunLike.finite _
  have hcd : Nat.card (TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) = l :=
    (GlobalTheory.T.card_dual_zmod_module_eq_card (l ^ 1) (ZMod (l ^ 1))).trans ((Nat.card_zmod _).trans (pow_one l))
  have hfin := fun v => (local_zr hF hT D (e + 1) v 1 one_pos).2.1
  have hloc : ∀ v : D.S, Nat.card (H2 ((zr D (e + 1) 1).comp (locFam D.S D.A v))) ≤ l := fun v => by
    rw [(local_zr hF hT D (e + 1) v 1 one_pos).2.2.2]
    refine le_trans ?_ hcd.le
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hpi : Nat.card (∀ v : D.S, H2 ((zr D (e + 1) 1).comp (locFam D.S D.A v))) ≤
      l ^ Module.finrank ℚ L := by
    rw [Nat.card_pi]
    refine le_trans (Finset.prod_le_pow_card _ _ l fun v _ => hloc v) ?_
    refine Nat.pow_le_pow_right hl.out.pos ?_
    rw [Finset.card_univ, Fintype.card_coe]
    exact UpperTheory.V.LDataCardLeFinrank.cardAbove L Ω l D
  have hker : LinearMap.ker (GlobalTheory.Published.PoitouTate.loc2 D.S D.A (zr D (e + 1) 1)) =
      Sha2 (zr D (e + 1) 1) (locFam D.S D.A) (continuous_locFam D.S D.A) := by
    rw [GlobalTheory.Published.PoitouTate.loc2, LinearMap.ker_pi]; rfl
  refine (card_quot_lpow 1 _ hg.1 hg.2).le.trans ?_
  rw [Submodule.card_eq_card_quotient_mul_card
    (LinearMap.ker (GlobalTheory.Published.PoitouTate.loc2 D.S D.A (zr D (e + 1) 1))),
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv, hker, ← (hS 1 one_pos).1.2.2.2]
  first
  | exact Nat.mul_le_mul_left _ (le_trans (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective) hpi)
  | (rw [mul_comm]; exact Nat.mul_le_mul_left _ (le_trans (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective) hpi))
