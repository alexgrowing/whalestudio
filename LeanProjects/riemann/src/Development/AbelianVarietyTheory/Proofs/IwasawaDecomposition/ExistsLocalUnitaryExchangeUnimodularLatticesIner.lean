import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartanExchangeUnimodularInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmodulePatchAtPrimeIsLatticeLocPStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameAtOfLocalizationEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationHermitianDualEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimePowSmulLeOfLocalizationsEqAwayStatement

noncomputable section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.InertExchange

theorem exchange : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)),
  conjPrime₂ P = P → (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) →
  ∀ (X Z : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E X → Submodule.IsLattice E Z →
    IsUnimodular (hStd E n) X → IsUnimodular (hStd E n) Z →
    (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Z) →
    ∃ σ : Submodule (𝓞 E) (Sp E n) → Submodule (𝓞 E) (Sp E n), σ X = Z ∧ σ Z = X ∧
      (∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) →
        Submodule.IsLattice E (σ Y) ∧ IsUnimodular (hStd E n) (σ Y) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X (σ Y)) ∧
      (∀ Y' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') →
        ∃ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
          (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) ∧ σ Y = Y') ∧
      (∀ Y Y' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) → Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') → σ Y = σ Y' → Y = Y') ∧
      ∀ (s : List ℕ) (Y Y' : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) → Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') →
        (IsInertNbr P.asIdeal s (σ Y) (σ Y') ↔ IsInertNbr P.asIdeal s Y Y') := by
  intro E _ _ _ n P hP hin X Z hXl hZl hXu hZu hXZ
  obtain ⟨g, hg, hgX, hgZ⟩ := GlobalTheory.T.cartan_exchange_unimodular_inert_prime n P hP hin X Z hXl hZl hXu hZu hXZ
  have hcc : ∀ Q : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ Q) = Q := fun Q => by
    apply HeightOneSpectrum.ext
    ext r
    change cO E (cO E r) ∈ Q.asIdeal ↔ r ∈ Q.asIdeal
    rw [cO_cO]
  have locg : ∀ (h : Sp E n ≃ₗ[E] Sp E n) (Q : HeightOneSpectrum (𝓞 E)) (M N : Submodule (𝓞 E) (Sp E n)),
      localization₂ Q.asIdeal M = localization₂ Q.asIdeal N → localization₂ Q.asIdeal (gmap h M) = localization₂ Q.asIdeal (gmap h N) := by
    intro h Q M N e
    ext x
    rw [mem_localization_gmap, mem_localization_gmap, e]
  have locg_inv : ∀ (h : Sp E n ≃ₗ[E] Sp E n) (Q : HeightOneSpectrum (𝓞 E)) (M N : Submodule (𝓞 E) (Sp E n)),
      localization₂ Q.asIdeal (gmap h M) = localization₂ Q.asIdeal (gmap h N) → localization₂ Q.asIdeal M = localization₂ Q.asIdeal N := by
    intro h Q M N e
    ext x
    have h1 := (mem_localization_gmap Q h M (h x)).symm
    have h2 := (mem_localization_gmap Q h N (h x)).symm
    simp only [LinearEquiv.symm_apply_apply] at h1 h2
    rw [h1, h2, e]
  have ginv : ∀ M : Submodule (𝓞 E) (Sp E n), gmap g⁻¹ (gmap g M) = M := by
    intro M
    ext x
    rw [mem_gmap, mem_gmap]
    have e : g⁻¹ = g.symm := rfl
    rw [e, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  have hginv : g⁻¹ ∈ UF E n := inv_mem hg
  have unimodG : ∀ (h : Sp E n ≃ₗ[E] Sp E n), h ∈ UF E n → ∀ M : Submodule (𝓞 E) (Sp E n),
      IsUnimodular (hStd E n) M → IsUnimodular (hStd E n) (gmap h M) := by
    intro h hh M hM
    have hM' : dual (hStd E n) M = M := hM
    show dual (hStd E n) (gmap h M) = gmap h M
    rw [dual_gmap h hh, hM']
  have unimod : ∀ A B C : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E A → Submodule.IsLattice E B →
      Submodule.IsLattice E C → IsUnimodular (hStd E n) B → IsUnimodular (hStd E n) C →
      localization₂ P.asIdeal A = localization₂ P.asIdeal B → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal C) →
      IsUnimodular (hStd E n) A := by
    intro A B C hA hB hC hBu hCu hAP hAQ
    have hBu' : dual (hStd E n) B = B := hBu
    have hCu' : dual (hStd E n) C = C := hCu
    show dual (hStd E n) A = A
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    by_cases hQ : Q = P
    · rw [hQ]
      have h1 : localization₂ (conjPrime₂ P).asIdeal A = localization₂ (conjPrime₂ P).asIdeal B := by rw [hP]; exact hAP
      rw [GlobalTheory.T.localization_hermitianDual_eq P A B hA hB h1, hBu', hAP]
    · have hQ' : conjPrime₂ Q ≠ P := fun h => hQ (by rw [← hcc Q, h, hP])
      rw [GlobalTheory.T.localization_hermitianDual_eq Q A C hA hC (hAQ _ hQ'), hCu', hAQ Q hQ]
  have locσ : ∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → ∀ Q : HeightOneSpectrum (𝓞 E),
      localization₂ Q.asIdeal (patchAt P (gmap g Y) Y) = localization₂ Q.asIdeal (if Q = P then gmap g Y else Y) :=
    fun Y hY => (GlobalTheory.T.submodulePatchAtPrime_isLattice_locP P (gmap g Y) Y (gmap_lattice g Y hY) hY).2
  have latσ : ∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y →
      Submodule.IsLattice E (patchAt P (gmap g Y) Y) :=
    fun Y hY => (GlobalTheory.T.submodulePatchAtPrime_isLattice_locP P (gmap g Y) Y (gmap_lattice g Y hY) hY).1
  refine ⟨fun Y => patchAt P (gmap g Y) Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show patchAt P (gmap g X) X = Z
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    rw [locσ X hXl Q]
    split_ifs with hQ
    · rw [hQ]; exact hgX.localization_eq.symm
    · exact (hXZ Q hQ).localization_eq.symm
  · show patchAt P (gmap g Z) Z = X
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    rw [locσ Z hZl Q]
    split_ifs with hQ
    · rw [hQ]; exact hgZ.localization_eq.symm
    · exact (hXZ Q hQ).localization_eq
  · intro Y hYl hYu hYS
    show Submodule.IsLattice E (patchAt P (gmap g Y) Y) ∧ IsUnimodular (hStd E n) (patchAt P (gmap g Y) Y) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X (patchAt P (gmap g Y) Y)
    refine ⟨latσ Y hYl, ?_, ?_⟩
    · refine unimod _ (gmap g Y) X (latσ Y hYl) (gmap_lattice g Y hYl) hXl (unimodG g hg Y hYu) hXu ?_ ?_
      · rw [locσ Y hYl P, if_pos rfl]
      · intro Q hQ
        rw [locσ Y hYl Q, if_neg hQ]
        exact (hYS Q hQ).localization_eq
    · intro Q hQ
      apply GlobalTheory.T.sameAt_of_localization_eq Q X _ hXl (latσ Y hYl)
      rw [locσ Y hYl Q, if_neg hQ]
      exact (hYS Q hQ).localization_eq.symm
  · intro Y' hl' hu' hS'
    obtain ⟨hYl, hYloc⟩ := GlobalTheory.T.submodulePatchAtPrime_isLattice_locP P (gmap g⁻¹ Y') Y' (gmap_lattice _ _ hl') hl'
    refine ⟨patchAt P (gmap g⁻¹ Y') Y', hYl, ?_, ?_, ?_⟩
    · refine unimod _ (gmap g⁻¹ Y') Y' hYl (gmap_lattice _ _ hl') hl' (unimodG _ hginv Y' hu') hu' ?_ ?_
      · rw [hYloc P, if_pos rfl]
      · intro Q hQ
        rw [hYloc Q, if_neg hQ]
    · intro Q hQ
      apply GlobalTheory.T.sameAt_of_localization_eq Q X _ hXl hYl
      rw [hYloc Q, if_neg hQ]
      exact (hS' Q hQ).localization_eq.symm
    · show patchAt P (gmap g (patchAt P (gmap g⁻¹ Y') Y')) (patchAt P (gmap g⁻¹ Y') Y') = Y'
      apply Formalism.L2.DIV.eq_of_forall_localized_eq
      intro Q
      rw [locσ _ hYl Q]
      split_ifs with hQ
      · rw [hQ]
        ext x
        rw [mem_localization_gmap, hYloc P, if_pos rfl, mem_localization_gmap]
        have e : g⁻¹ = g.symm := rfl
        rw [e, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
      · rw [hYloc Q, if_neg hQ]
  · intro Y Y' hYl hYu hYS hY'l hY'u hY'S he
    have he' : patchAt P (gmap g Y) Y = patchAt P (gmap g Y') Y' := he
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    by_cases hQ : Q = P
    · rw [hQ]
      apply locg_inv g P
      have h1 := congrArg (localization₂ P.asIdeal) he'
      rw [locσ Y hYl P, locσ Y' hY'l P, if_pos rfl, if_pos rfl] at h1
      exact h1
    · rw [(hYS Q hQ).localization_eq, (hY'S Q hQ).localization_eq]
  · intro s Y Y' hYl hYu hYS hY'l hY'u hY'S
    show IsInertNbr P.asIdeal s (patchAt P (gmap g Y) Y) (patchAt P (gmap g Y') Y') ↔ IsInertNbr P.asIdeal s Y Y'
    have hAl := gmap_lattice g Y hYl
    have hBl := gmap_lattice g Y' hY'l
    have hAA' := GlobalTheory.T.sameAt_of_localization_eq P (gmap g Y) _ hAl (latσ Y hYl) (by rw [locσ Y hYl P, if_pos rfl])
    have hBB' := GlobalTheory.T.sameAt_of_localization_eq P (gmap g Y') _ hBl (latσ Y' hY'l) (by rw [locσ Y' hY'l P, if_pos rfl])
    have hAB : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal (gmap g Y) = localization₂ Q.asIdeal (gmap g Y') :=
      fun Q hQ => locg g Q Y Y' ((hYS Q hQ).localization_eq.trans (hY'S Q hQ).localization_eq.symm)
    have hA'B' : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P →
        localization₂ Q.asIdeal (patchAt P (gmap g Y) Y) = localization₂ Q.asIdeal (patchAt P (gmap g Y') Y') := by
      intro Q hQ
      rw [locσ Y hYl Q, locσ Y' hY'l Q, if_neg hQ, if_neg hQ, (hYS Q hQ).localization_eq, (hY'S Q hQ).localization_eq]
    obtain ⟨k1, hk1, hk1'⟩ := GlobalTheory.T.exists_prime_pow_smul_le_of_localizations_eq_away P _ _ hAl hBl hAB
    obtain ⟨k2, hk2, hk2'⟩ := GlobalTheory.T.exists_prime_pow_smul_le_of_localizations_eq_away P _ _ (latσ Y hYl) (latσ Y' hY'l) hA'B'
    obtain ⟨a, ha, a', ha', h1, h2⟩ := hAA'
    obtain ⟨b, hb, b', hb', h3, h4⟩ := hBB'
    have hα0 : a * a' * b * b' ∉ P.asIdeal :=
      Formalism.L2.DIV.lc_mul_notMem P (Formalism.L2.DIV.lc_mul_notMem P (Formalism.L2.DIV.lc_mul_notMem P ha ha') hb) hb'
    obtain ⟨t, p, hp, e⟩ := P.isMaximal.exists_inv hα0
    have hgeom := geom_sum_mul p (k1 + k2)
    have hgd : t * (∑ i ∈ Finset.range (k1 + k2), p ^ i) * (a * a' * b * b') + p ^ (k1 + k2) = 1 := by
      linear_combination (∑ i ∈ Finset.range (k1 + k2), p ^ i) * e - hgeom
    have hδ : p ^ (k1 + k2) ∈ P.asIdeal ^ (k1 + k2) := Ideal.pow_mem_pow hp _
    set S := ∑ i ∈ Finset.range (k1 + k2), p ^ i
    have rAA' : HiRel (t * S * (a * a' * b * b')) (gmap g Y) (patchAt P (gmap g Y) Y) := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * b * b') • (a' • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h2 x hx)
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a' * b * b') • (a • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h1 x hx)
    have rBB' : HiRel (t * S * (a * a' * b * b')) (gmap g Y') (patchAt P (gmap g Y') Y') := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * a' * b) • (b' • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h4 x hx)
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * a' * b') • (b • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h3 x hx)
    have le1 : P.asIdeal ^ (k1 + k2) ≤ P.asIdeal ^ k1 := Ideal.pow_le_pow_right (by omega)
    have le2 : P.asIdeal ^ (k1 + k2) ≤ P.asIdeal ^ k2 := Ideal.pow_le_pow_right (by omega)
    have rAB : HiRel (p ^ (k1 + k2)) (gmap g Y) (gmap g Y') :=
      HiRel.of_ideal ((Submodule.smul_mono_left le1).trans hk1) ((Submodule.smul_mono_left le1).trans hk1') hδ
    have rA'B' : HiRel (p ^ (k1 + k2)) (patchAt P (gmap g Y) Y) (patchAt P (gmap g Y') Y') :=
      HiRel.of_ideal ((Submodule.smul_mono_left le2).trans hk2) ((Submodule.smul_mono_left le2).trans hk2') hδ
    constructor
    · intro h
      have h5 := isInertNbr_par hgd rAA'.symm rBB'.symm rA'B' rAB h
      have h6 := h5.gmap g⁻¹
      rwa [ginv, ginv] at h6
    · intro h
      exact isInertNbr_par hgd rAA' rBB' rAB rA'B' (h.gmap g)

end GlobalTheory.InertExchange
