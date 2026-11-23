import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SpreadRestrict

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X}

theorem surj_conj {B : Type} [CommGroup B] (χ : G D.host.E N.Om →* B) (hA : AntiHom X.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring N.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring N.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := X.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, X.cc (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E N.Om)) x).symm
  have hs' : ∀ x, X.cc.symm (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, X.cc (X.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, X.cc.symm x = X.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap X.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine X.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap X.cc.symm.toRingHom).comap X.cc.symm.toRingHom = A := by
    ext y
    show X.cc.symm (X.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem sign_eq_one (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {S : Finset (Pl D.host.E)} {M : ℕ}
    {P v : Pl D.host.E} (hP : P ∈ S) (hv : v ∈ S) (hc : IsConjPl D.host P v) (hPa : P ∈ admissibleConjugatePairPlaces X i S M) :
    (((Y.delU_conj i S M P hP v hv hc).choose : ℤ) : ZMod (X.l i ^ M)) = 1 := by
  classical
  have hs := (Y.delU_conj i S M P hP v hv hc).choose_spec
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := conj_mem_admissibleConjugatePairPlaces hPa hc
  obtain ⟨-, P', -, -, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPa
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm.2 P (by simp)
  have hDel : GlobalTheory.GalChar.IsDel D.host X.cc (X.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    have hsP : ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
      obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
      exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact surj_conj χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host X.cc (X.l i) ⟨χ, hDel⟩
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
  obtain ⟨σ, -, hσ⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd 1)
  have e := hs σ
  rw [delU_on hY σ ⟨v, hv⟩ hva, delU_on hY σ ⟨P, hP⟩ hPa] at e
  simp only at e
  rw [GlobalTheory.GalChar.pair_eq hc, hσ, toAdd_ofAdd, mul_one] at e
  exact e.symm

theorem spread_conj (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {M : ℕ} {ch : Set (Pl D.host.E)} (hch : IsChoice ch)
    {S : Finset (Pl D.host.E)} (hS : admissibleConjugatePairPlaces X i S M = S) (x : ↥(half ch (admissibleConjugatePairPlaces X i S M)) → ZMod (X.l i ^ M))
    {v P : Pl D.host.E} (hvS : v ∈ S) (hvc : v ∉ ch) (hvP : IsConjPl D.host v P)
    (hPh : P ∈ half ch (admissibleConjugatePairPlaces X i S M)) :
    spread Y i S M ch x ⟨v, hvS⟩ = x ⟨P, hPh⟩ := by
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := by rw [hS]; exact hvS
  have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
  have hPv := GlobalTheory.GalChar.isConjPl_symm hvP
  have hPaa : P ∈ admissibleConjugatePairPlaces X i (admissibleConjugatePairPlaces X i S M) M := by
    simp only [hS]
    rw [← hS]
    exact (mem_half.1 hPh).1
  rw [spread_apply, Finset.sum_eq_single ⟨P, hPh⟩, weight, if_neg hne, dif_pos ⟨hva, hPv⟩, sign_eq_one hY _ _ hPv hPaa,
    one_mul]
  · intro P' _ h'
    rw [weight, if_neg fun e : v = P'.1 => hvc (e ▸ (mem_half.1 P'.2).2), dif_neg fun h => h' (Subtype.ext
      (GlobalTheory.GalChar.isConjPl_unique (GlobalTheory.GalChar.isConjPl_symm h.2) hvP)), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem spread_restrict : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  intro D N X Y hY i M ch hch Q Q' hQQ hQ hQ' hsub c v hv
  by_cases hc : v ∈ ch
  · have h1 : v ∈ half ch (admissibleConjugatePairPlaces X i Q M) := mem_half.2 ⟨by rw [hQ]; exact hQQ hv, hc⟩
    have h2 : v ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨by rw [hQ']; exact hv, hc⟩
    rw [spread_of_mem Y i Q M hch c ⟨v, hQQ hv⟩ h1, spread_of_mem Y i Q' M hch _ ⟨v, hv⟩ h2]
  · have hva : v ∈ admissibleConjugatePairPlaces X i Q' M := by rw [hQ']; exact hv
    obtain ⟨-, P, -, hvP, -⟩ := mem_admissibleConjugatePairPlaces_iff.1 hva
    have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
    have hPc : P ∈ ch := by
      by_contra h
      exact hc ((hch.pair _ _ hvP hne).2 h)
    have hPa' : P ∈ admissibleConjugatePairPlaces X i Q' M := conj_mem_admissibleConjugatePairPlaces hva hvP
    have hPh' : P ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨hPa', hPc⟩
    rw [spread_conj hY hch hQ c (hQQ hv) hc hvP (hsub P hPh'), spread_conj hY hch hQ' _ hv hc hvP hPh']

end GlobalTheory.SpreadRestrict

end
