import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Loc

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem le_locS (S : Submonoid R) (L : Submodule R W) : L ≤ Formalism.HermitianLatticesTheory.locS S L := fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

theorem locS_mono (S : Submonoid R) {L M : Submodule R W} (h : L ≤ M) :
    Formalism.HermitianLatticesTheory.locS S L ≤ Formalism.HermitianLatticesTheory.locS S M := fun x ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩

theorem locS_idem (S : Submonoid R) (L : Submodule R W) :
    Formalism.HermitianLatticesTheory.locS S (Formalism.HermitianLatticesTheory.locS S L) = Formalism.HermitianLatticesTheory.locS S L := by
  apply le_antisymm
  · rintro x ⟨s, hs, t, ht, hx⟩
    refine ⟨t * s, S.mul_mem ht hs, ?_⟩
    rw [mul_smul]
    exact hx
  · exact le_locS S _

theorem locS_eq_of (S : Submonoid R) {L M : Submodule R W} (h1 : L ≤ Formalism.HermitianLatticesTheory.locS S M)
    (h2 : M ≤ Formalism.HermitianLatticesTheory.locS S L) : Formalism.HermitianLatticesTheory.locS S L = Formalism.HermitianLatticesTheory.locS S M := by
  apply le_antisymm
  · calc Formalism.HermitianLatticesTheory.locS S L ≤ Formalism.HermitianLatticesTheory.locS S (Formalism.HermitianLatticesTheory.locS S M) := locS_mono S h1
      _ = Formalism.HermitianLatticesTheory.locS S M := locS_idem S M
  · calc Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S (Formalism.HermitianLatticesTheory.locS S L) := locS_mono S h2
      _ = Formalism.HermitianLatticesTheory.locS S L := locS_idem S L

theorem iInf_localization_eq [IsDedekindDomain R] (hR : ¬ IsField R) (L : Submodule R W) :
    (⨅ P : HeightOneSpectrum R, haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) = L := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_iInf] at hx
    by_contra hxL
    let I : Ideal R := L.comap (LinearMap.toSpanSingleton R W x)
    have hI : I ≠ ⊤ := by
      intro h
      apply hxL
      have h1 : (1 : R) ∈ I := h ▸ Submodule.mem_top
      simpa [I] using h1
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
    have hM0 : M ≠ ⊥ := by
      intro h
      apply hR
      rw [h] at hM
      exact Ring.isField_iff_maximal_bot.2 hM
    obtain ⟨s, hs, hsx⟩ := hx ⟨M, hM.isPrime, hM0⟩
    exact hs (hIM (by simpa [I] using hsx))
  · exact le_iInf fun P => le_locS _ L

end Loc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def JdS (D : Formalism.BasicNotions.D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

def GDiffPrime : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (P : HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
    ∃ s ∈ JdS D, s ∉ P.asIdeal

theorem differentIdealPowers_eq_inv (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) :
    ∃ k : ℕ, differentIdealPowers D i = ((((JdS D) ^ k : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine ⟨0, ?_⟩
    rw [differentIdealPowers, Fin.snoc_last, pow_zero, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, inv_one]
  · refine ⟨D.R.rS - (a : ℕ), ?_⟩
    have hcast : ((D.R.rS : ℤ) - (a : ℕ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
      have := a.isLt
      omega
    rw [differentIdealPowers, Fin.snoc_castSucc, hcast, zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
    rfl

theorem JdS_pow_ne_zero (D : Formalism.BasicNotions.D7) (k : ℕ) :
    ((((JdS D) ^ k : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, ← Ideal.zero_eq_bot]
  apply pow_ne_zero
  rw [Ideal.zero_eq_bot, JdS, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
  exact differentIdeal_ne_bot

theorem one_mem_aa (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) (o : 𝓞 D.host.E) :
    (o : D.host.E) ∈ differentIdealPowers D i := by
  obtain ⟨k, hk⟩ := differentIdealPowers_eq_inv D i
  rw [hk, FractionalIdeal.mem_inv_iff (JdS_pow_ne_zero D k)]
  intro y hy
  obtain ⟨a, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  exact (FractionalIdeal.mem_one_iff _).2 ⟨o * a, by rw [map_mul]⟩

theorem clear_aa (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) (s : 𝓞 D.host.E) (hs : s ∈ JdS D) :
    ∃ k : ℕ, ∀ c ∈ differentIdealPowers D i, ∃ o : 𝓞 D.host.E, (o : D.host.E) = ((s ^ k : 𝓞 D.host.E) : D.host.E) * c := by
  obtain ⟨k, hk⟩ := differentIdealPowers_eq_inv D i
  refine ⟨k, fun c hc => ?_⟩
  rw [hk, FractionalIdeal.mem_inv_iff (JdS_pow_ne_zero D k)] at hc
  have hsk : ((s ^ k : 𝓞 D.host.E) : D.host.E) ∈
      ((JdS D ^ k : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨s ^ k, Ideal.pow_mem_pow hs k, rfl⟩
  have h1 := hc _ hsk
  rw [mul_comm] at h1
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  exact ⟨o, ho⟩

theorem smul_O_E {D : Formalism.BasicNotions.D7} (o : 𝓞 D.host.E) (v : (VS D).V) : o • v = ((o : D.host.E)) • v := (algebraMap_smul D.host.E o v).symm

theorem mem_pb {D : Formalism.BasicNotions.D7} {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (i : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (c : D.host.E) (hc : c ∈ Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) :
    c • flagDifferenceVectors D F0 F' i ∈ pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) := Submodule.subset_span ⟨i, c, hc, rfl⟩

theorem loc_g (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (P : HeightOneSpectrum (𝓞 D.host.E)) (s : 𝓞 D.host.E) (hsJ : s ∈ JdS D) (hsP : s ∉ P.asIdeal) :
    haveI := P.isPrime
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))) := by
  haveI := P.isPrime
  apply locS_eq_of
  · refine (Submodule.span_le.mpr ?_).trans (le_locS _ _)
    rintro v (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · have := mem_pb F0 F' (Sum.inl a) _ (one_mem_aa D a 1)
      simpa [flagDifferenceVectors] using this
    · have := mem_pb F0 F' (Sum.inr b) _ (one_mem_aa D b 1)
      simpa [flagDifferenceVectors] using this
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨i, c, hc, rfl⟩
    have hc' : c ∈ Sum.elim (differentIdealPowers D) (differentIdealPowers D) i := hc
    obtain ⟨k, hk⟩ := clear_aa D (Sum.elim id id i) s hsJ
    have hc2 : c ∈ differentIdealPowers D (Sum.elim id id i) := by rcases i with a | a <;> exact hc'
    obtain ⟨o, ho⟩ := hk c hc2
    refine ⟨s ^ k, fun h => hsP (P.isPrime.mem_of_pow_mem k h), ?_⟩
    rw [smul_O_E, smul_smul, ← ho, ← smul_O_E]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rcases i with a | b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b, rfl⟩

theorem gS_ne_zero' (D : Formalism.BasicNotions.D7) : ((gS D : D.host.E)) ≠ 0 := by
  have h : gS D ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  exact_mod_cast h

theorem aa_castSucc (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) :
    differentIdealPowers D (Fin.castSucc a) = ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) := by
  rw [differentIdealPowers, Fin.snoc_castSucc]

theorem aa_last (D : Formalism.BasicNotions.D7) : differentIdealPowers D (Fin.last D.R.rS) = 1 := by
  rw [differentIdealPowers, Fin.snoc_last]

theorem mem_UUS_fvec (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (a : Fin (D.R.rS + 1)) (c : D.host.E) (hc : c ∈ differentIdealPowers D a) :
    c • F0.fvec a ∈ UUS D F0 F' ∧ c • F'.fl.fvec a ∈ UUS D F0 F' := by
  induction a using Fin.lastCases with
  | last =>
    rw [aa_last, FractionalIdeal.mem_one_iff] at hc
    obtain ⟨o, rfl⟩ := hc
    simp only [FlagG.fvec, Fin.snoc_last]
    rw [← smul_O_E, ← smul_O_E]
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _))))
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _))
  | cast a =>
    rw [aa_castSucc] at hc
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.subset_span ⟨a, c, hc, rfl⟩)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, c, hc, rfl⟩))

theorem UUS_le_pb (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') : UUS D F0 F' ≤ pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) := by
  have hg := gS_ne_zero' D
  have key : ∀ (a : Fin (D.R.rS + 1)) (c : D.host.E), c ∈ differentIdealPowers D a →
      c • F0.fvec a ∈ pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) ∧
      c • F'.fl.fvec a ∈ pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) := by
    intro a c hc
    refine ⟨mem_pb F0 F' (Sum.inl a) c hc, ?_⟩
    have hgc : ((gS D : D.host.E)) * c ∈ differentIdealPowers D a := by
      have := Submodule.smul_mem (differentIdealPowers D a : Submodule (𝓞 D.host.E) D.host.E) ((gS D : ℕ) : 𝓞 D.host.E) hc
      rwa [Algebra.smul_def, map_natCast] at this
    have e : c • F'.fl.fvec a = (((gS D : D.host.E)) * c) • flagDifferenceVectors D F0 F' (Sum.inr a) + c • flagDifferenceVectors D F0 F' (Sum.inl a) := by
      simp only [flagDifferenceVectors, Sum.elim_inr, Sum.elim_inl]
      have hgc' : (((gS D : D.host.E)) * c) • (((gS D : D.host.E))⁻¹ • (F'.fl.fvec a - F0.fvec a)) =
          c • (F'.fl.fvec a - F0.fvec a) := by
        rw [smul_smul]
        congr 1
        field_simp
      rw [hgc', smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (mem_pb F0 F' (Sum.inr a) _ hgc) (mem_pb F0 F' (Sum.inl a) c hc)
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨a, c, hc, rfl⟩
    have := (key (Fin.castSucc a) c (by rw [aa_castSucc]; exact hc)).1
    simpa [FlagG.fvec] using this
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have := (key (Fin.last _) 1 (by simpa using one_mem_aa D (Fin.last D.R.rS) 1)).1
    simpa [FlagG.fvec] using this
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨a, c, hc, rfl⟩
    have := (key (Fin.castSucc a) c (by rw [aa_castSucc]; exact hc)).2
    simpa [FlagG.fvec] using this
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have := (key (Fin.last _) 1 (by simpa using one_mem_aa D (Fin.last D.R.rS) 1)).2
    simpa [FlagG.fvec] using this

theorem loc_ng (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    haveI := P.isPrime
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))) := by
  haveI := P.isPrime
  have hg := gS_ne_zero' D
  apply locS_eq_of
  · exact (UUS_le_pb D F0 F').trans (le_locS _ _)
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨i, c, hc, rfl⟩
    rcases i with a | b
    · exact le_locS _ _ (mem_UUS_fvec D F0 F' a c hc).1
    · refine ⟨((gS D : ℕ) : 𝓞 D.host.E), hP, ?_⟩
      have e : ((gS D : ℕ) : 𝓞 D.host.E) • (c • flagDifferenceVectors D F0 F' (Sum.inr b)) = c • F'.fl.fvec b - c • F0.fvec b := by
        rw [smul_O_E]
        simp only [flagDifferenceVectors, Sum.elim_inr, smul_smul]
        push_cast
        rw [← smul_sub]
        congr 1
        field_simp
      rw [e]
      exact Submodule.sub_mem _ (mem_UUS_fvec D F0 F' b c hc).2 (mem_UUS_fvec D F0 F' b c hc).1

open Classical in
theorem mmPseudo_of (hg : GDiffPrime) : MMPseudo := by
  intro D u u' _ F0 what₂ _ Z F' _ _ _ _
  have hP : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (haveI := P.isPrime
       if ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal then Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F')
       else Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F')) =
      (haveI := P.isPrime
       Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)))) := by
    intro P
    split_ifs with h
    · obtain ⟨s, hsJ, hsP⟩ := hg D P h
      exact loc_g D F0 F' P s hsJ hsP
    · exact loc_ng D F0 F' P h
  unfold MMof
  rw [iInf_congr hP]
  exact iInf_localization_eq (NumberField.RingOfIntegers.not_isField D.host.E) _

theorem congruence_prime_different : GDiffPrime := by
  intro D P hP
  haveI := P.isPrime
  have hg : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    apply P.isPrime.mem_or_mem
    unfold gS at hP
    exact_mod_cast hP
  have key : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ s ∈ JdS D, s ∉ P.asIdeal := by
    intro i hi
    set n := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F), ?_, ?_⟩
    · exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem _)
    · intro hn
      rw [map_natCast] at hn
      have hc := (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.coprime_gi (D := D) i).cast (R := 𝓞 D.host.E)
      obtain ⟨a, b, hab⟩ := hc
      have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
        rw [← hab]
        exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hi)
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  rcases hg with h | h
  · exact key 0 h
  · exact key 1 h

theorem mass_pseudo_basis : MMPseudo := mmPseudo_of congruence_prime_different

end PI.UnitaryGroupMassFormula.CntFormula.R6
