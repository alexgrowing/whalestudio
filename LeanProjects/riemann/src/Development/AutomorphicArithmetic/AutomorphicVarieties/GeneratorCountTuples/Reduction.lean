import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardRed
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TensCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.ChiTriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.ShaDualCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.ShaZmCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardH2QuotientLeSha
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.PrimeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumGens
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumT
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumFin

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit
open scoped TensorProduct

namespace UpperTheory.V.K

private theorem tensCard' (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H] [inst : Module ℤ H]
    [Finite (AddCommGroup.torsion H)] (Y : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] H)) [Finite Y] :
    Nat.card Y ≤ Nat.card (AddCommGroup.torsion H) := by
  obtain rfl : inst = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  exact tensCard l H Y

section

variable (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
  {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (D : LData L Ω l) (hL : IsTotallyComplex L) (hμ : HasMuQ l L)

include hP hF hT hL hμ

theorem card_mod_le (e : ℤ) :
    Nat.card (H2 (zlTw D (e + 1)) ⧸ lpow l (H2 (zlTw D (e + 1))) 1) ≤ classNumber L * l ^ Module.finrank ℚ L := by
  have h := card_H2_quotient_le_sha hP hF hT l L Ω D e hL
  dsimp only at h
  rw [shaDualCard l L Ω D (e + 1) (chiTriv l L Ω D hμ)] at h
  exact h.trans (Nat.mul_le_mul_right _ (shaZmCard l L Ω D hL))

theorem generators (e : ℤ) :
    Real.log (Nat.card (H2 (zlTw D (e + 1)) ⧸ lpow l (H2 (zlTw D (e + 1))) 1)) ≤
      4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) * Real.log l :=
  numGens l L _ (card_mod_le hP hF hT D hL hμ e)

theorem reduction (hK : KBridge) (e : ℕ) (he : 1 ≤ e) [Finite (torsHGL L (4 * e + 4) (2 * e))] :
    Finite (H2 (zlTw D ((e : ℤ) + 1))) ∧
      Real.log (Nat.card (H2 (zlTw D ((e : ℤ) + 1)))) ≤
        4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) * ((2 * (e : ℝ)) * (2 * (e : ℝ) + 3)) *
          Real.log ((Module.finrank ℚ L : ℝ) + 1) + Real.log (Nat.card (torsHGL L (4 * e + 4) (2 * e))) := by
  obtain ⟨K, _, _, _, p, h, hp, hh⟩ := hK l L Ω D hL hμ e he
  have hfin : Finite (H2 (zlTw D ((e : ℤ) + 1))) := Finite.of_surjective p hp
  refine ⟨hfin, ?_⟩
  have hr : Finite (LinearMap.range h) := Finite.of_surjective h.rangeRestrict h.surjective_rangeRestrict
  have h1 := (cardRed l K _ _ p h _ hp hh).trans
    (Nat.mul_le_mul_left _ (tensCard' l (HGL L (4 * e + 4) (2 * e)) (LinearMap.range h)))
  have hg := generators hP hF hT D hL hμ (e : ℤ)
  have hq : Finite (H2 (zlTw D ((e : ℤ) + 1)) ⧸ lpow l (H2 (zlTw D ((e : ℤ) + 1))) 1) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  set a := Nat.card (H2 (zlTw D ((e : ℤ) + 1)) ⧸ lpow l (H2 (zlTw D ((e : ℤ) + 1))) 1) with ha
  set b := Nat.card (torsHGL L (4 * e + 4) (2 * e)) with hb
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (Nat.card_pos : 0 < a)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (Nat.card_pos : 0 < b)
  have hx0 : (0 : ℝ) < Nat.card (H2 (zlTw D ((e : ℤ) + 1))) := Nat.cast_pos.2 Nat.card_pos
  have h2 : Real.log (Nat.card (H2 (zlTw D ((e : ℤ) + 1)))) ≤ cOne (2 * e) * Real.log a + Real.log b := by
    rw [← Real.log_pow, ← Real.log_mul (by positivity) hb0.ne']
    exact Real.log_le_log hx0 (by exact_mod_cast h1)
  have hc : (cOne (2 * e) : ℝ) ≤ (2 * (e : ℝ)) * (2 * (e : ℝ) + 3) := by exact_mod_cast cOne_le (2 * e)
  have hl : Real.log l ≤ Real.log ((Module.finrank ℚ L : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast (Fact.out : l.Prime).pos) (by exact_mod_cast primeLe l L hμ)
  have hD : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 (discr_ne_zero L)
  have hlog : 0 ≤ Real.log (2 * ((discr L).natAbs : ℝ)) := Real.log_nonneg (by linarith)
  have hn : 0 ≤ Real.log ((Module.finrank ℚ L : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have h3 : Real.log a ≤ 4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) *
      Real.log ((Module.finrank ℚ L : ℝ) + 1) := hg.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  have h4 := mul_le_mul hc h3 (Real.log_natCast_nonneg a) (by positivity)
  linarith

end

theorem TorsBound.pow {C : ℝ} (h : TorsBound C) : ∃ C', TorsBoundPow C' := by
  obtain ⟨C', H⟩ := numT C
  exact ⟨C', fun L _ _ hL e he => ⟨(h L hL e he).1, (h L hL e he).2.trans
    (H e _ _ he Module.finrank_pos (Int.natAbs_pos.2 (discr_ne_zero L)))⟩⟩

theorem lemmaK_of (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) (hK : KBridge)
    (h : ∃ C, TorsBoundPow C) : ∃ CK : ℝ, 0 < CK ∧ LemmaK CK := by
  obtain ⟨C, h⟩ := h
  obtain ⟨CK, h0, H⟩ := numFin C
  refine ⟨CK, h0, fun l _ L Ω _ _ _ _ _ D hL hμ e he => ?_⟩
  obtain ⟨hf, hb⟩ := h L hL e he
  obtain ⟨h1, h2⟩ := reduction hP hF hT D hL hμ hK e he
  refine ⟨h1, h2.trans (le_trans ?_ (H e _ _ he Module.finrank_pos (Int.natAbs_pos.2 (discr_ne_zero L))))⟩
  gcongr

end UpperTheory.V.K

end
