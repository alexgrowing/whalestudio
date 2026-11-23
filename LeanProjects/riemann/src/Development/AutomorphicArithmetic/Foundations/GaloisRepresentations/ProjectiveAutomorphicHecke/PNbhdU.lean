import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhdU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private noncomputable def th {w : Plc E} (hw : IsSplitAt w) : GLw n w →* GLw n (cj w) :=
  (cLoc (cj w)).comp ((finU E n).subtype.comp (locF hw))

private theorem continuous_th {w : Plc E} (hw : IsSplitAt w) : Continuous (th (n := n) hw) :=
  (GlobalTheory.BCT.GlobLev.continuous_cLoc (cj w)).comp
    ((continuous_subtype_val (p := (· ∈ locU n w))).comp (locE hw).symm.continuous)

private theorem cLoc_cj_eq {w : Plc E} (hw : IsSplitAt w) (u : finU E n) :
    cLoc (cj w) u.1 = th hw (cLoc w u.1) :=
  GlobalTheory.LocInj.cLoc_conj_eq w u.1 (locF hw (cLoc w u.1)).1 (cLoc_locF hw _).symm

private theorem cj_cj (w : Plc E) : cj (cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w

private theorem exists_lt (α : Type) : ∃ lt : α → α → Prop, (∀ a b, a ≠ b → lt a b ∨ lt b a) ∧ ∀ a b, lt a b → ¬ lt b a := by
  obtain ⟨_, _⟩ := exists_wellOrder α
  exact ⟨(· < ·), fun a b h => lt_or_gt_of_ne h, fun a b h => lt_asymm h⟩

private def Top (lt : Plc E → Plc E → Prop) (Up : Plc E → Prop) (w₀ w : Plc E) : Prop :=
  Up w ∧ (Up (cj w) → w = w₀ ∨ (cj w ≠ w₀ ∧ lt w (cj w)))

private theorem top_or {lt : Plc E → Plc E → Prop} (h1 : ∀ a b, a ≠ b → lt a b ∨ lt b a) {Up : Plc E → Prop} (w₀ : Plc E)
    {w : Plc E} (hne : cj w ≠ w) (hup : Up w ∨ Up (cj w)) : Top lt Up w₀ w ∨ Top lt Up w₀ (cj w) := by
  by_cases ha : Up w
  · by_cases hb : Up (cj w)
    · by_cases e : w = w₀
      · exact Or.inl ⟨ha, fun _ => Or.inl e⟩
      · by_cases e' : cj w = w₀
        · exact Or.inr ⟨hb, fun _ => Or.inl e'⟩
        · rcases h1 w (cj w) hne.symm with h | h
          · exact Or.inl ⟨ha, fun _ => Or.inr ⟨e', h⟩⟩
          · exact Or.inr ⟨hb, fun _ => Or.inr ⟨by rwa [cj_cj], by rwa [cj_cj]⟩⟩
    · exact Or.inl ⟨ha, fun h => absurd h hb⟩
  · have hb := hup.resolve_left ha
    exact Or.inr ⟨hb, fun h => absurd (by rwa [cj_cj] at h) ha⟩

private theorem not_both {lt : Plc E → Plc E → Prop} (h2 : ∀ a b, lt a b → ¬ lt b a) {Up : Plc E → Prop} {w₀ w : Plc E}
    (hne : cj w ≠ w) (ha : Top lt Up w₀ w) (hb : Top lt Up w₀ (cj w)) : False := by
  have hb2 := hb.2 (by rw [cj_cj]; exact ha.1)
  rw [cj_cj] at hb2
  rcases ha.2 hb.1 with e | ⟨e, h⟩
  · rcases hb2 with e' | ⟨e', _⟩
    · exact hne (e'.trans e.symm)
    · exact e' e
  · rcases hb2 with e' | ⟨_, h'⟩
    · exact e e'
    · exact h2 _ _ h h'

end UpperTheory.Gal.CertificateRingHomMap.PNbhdU

open UpperTheory.Gal.CertificateRingHomMap.PNbhdU in
theorem UpperTheory.Gal.CertificateRingHomMap.pNbhdU_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.NbhdU := by
  intro h2 hI hL _ E _ _ _ n O hO Up hUp w₀ hw₀ hu₀
  obtain ⟨S₀, K₀, hK₀, hS₀⟩ := h2 E n O hO
  obtain ⟨lt, hlt1, hlt2⟩ := exists_lt (Plc E)
  have hne : ∀ w : Plc E, IsSplitAt w → cj w ≠ w := fun w hw => (hL E n w hw).2.2.1
  have hsp : ∀ w : Plc E, IsSplitAt w → IsSplitAt (cj w) := fun w hw => (hL E n w hw).2.2.2.1
  let T : Finset (Plc E) := insert w₀ (S₀ ∪ S₀.image (fun w => cj w))
  let S : Finset (Plc E) := T.filter (fun w => IsSplitAt w → Top lt Up w₀ w)
  let Kw : ∀ w : Plc E, Subgroup (GLw n w) := fun w =>
    if hw : IsSplitAt w then K₀ w ⊓ (K₀ (cj w)).comap (th hw) else K₀ w
  have hKle : ∀ w, Kw w ≤ K₀ w := by
    intro w
    by_cases hw : IsSplitAt w
    · simp only [Kw, dif_pos hw]; exact inf_le_left
    · simp only [Kw, dif_neg hw]; exact le_rfl
  have hKopen : ∀ w, IsOpen (Kw w : Set (GLw n w)) := by
    intro w
    by_cases hw : IsSplitAt w
    · simp only [Kw, dif_pos hw, Subgroup.coe_inf, Subgroup.coe_comap]
      exact (hK₀ w).1.inter ((hK₀ (cj w)).1.preimage (continuous_th hw))
    · simp only [Kw, dif_neg hw]; exact (hK₀ w).1
  have hKKGL : ∀ w, Kw w ≤ GlobalTheory.LFun.KGL w n := fun w => (hKle w).trans (hK₀ w).2
  have hmemS : ∀ w, w ∈ T → (IsSplitAt w → Top lt Up w₀ w) → w ∈ S := fun w h h' => Finset.mem_filter.2 ⟨h, h'⟩
  refine ⟨S, Kw, ⟨?_, fun w _ => hKopen w, fun w _ => ?_, fun w _ _ => hKKGL w, fun w hw hs => ?_⟩, ?_⟩
  · exact hmemS _ (Finset.mem_insert_self _ _) fun _ => ⟨hu₀, fun _ => Or.inl rfl⟩
  · exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen (Kw w) (hKopen w)) (hKKGL w)
  · have hw' := (Finset.mem_filter.1 hw).2 hs
    exact ⟨hw'.1, fun hc => not_both hlt2 (hne w hs) hw' ((Finset.mem_filter.1 hc).2 (hsp w hs))⟩
  · intro u hu
    obtain ⟨hz, hS, hout⟩ := mem_lev.1 hu
    have hint : ∀ w, cLoc w u.1 ∈ GlobalTheory.LFun.KGL w n := by
      intro w
      by_cases h1 : w ∈ S
      · exact hKKGL w (hS w h1)
      · by_cases h2 : cj w ∈ S
        · have h3 := hI E n (ofU u) (cj w) hz (hKKGL _ (hS _ h2))
          have key : ∀ v : Plc E, v = w → comp v (ofU u) ∈ GlobalTheory.LFun.KGL v n → cLoc w u.1 ∈ GlobalTheory.LFun.KGL w n := by
            rintro v rfl h; exact h
          exact key _ (cj_cj w) h3
        · exact hout w h1 h2
    refine hS₀ u hint fun w hw => ?_
    have hT : w ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_left _ hw)
    by_cases hs : IsSplitAt w
    · by_cases ht : Top lt Up w₀ w
      · exact hKle w (hS w (hmemS w hT fun _ => ht))
      · have ht' := (top_or hlt1 w₀ (hne w hs) (hUp w hs)).resolve_left ht
        have hT' : cj w ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))
        have h3 := hS (cj w) (hmemS _ hT' fun _ => ht')
        simp only [Kw, dif_pos (hsp w hs)] at h3
        have h4 : th (hsp w hs) (cLoc (cj w) u.1) ∈ K₀ (cj (cj w)) := (Subgroup.mem_inf.1 h3).2
        rw [← cLoc_cj_eq (hsp w hs) u] at h4
        have key : ∀ v : Plc E, v = w → cLoc v u.1 ∈ K₀ v → cLoc w u.1 ∈ K₀ w := by
          rintro v rfl h; exact h
        exact key _ (cj_cj w) h4
    · exact hKle w (hS w (hmemS w hT fun h => absurd h hs))
