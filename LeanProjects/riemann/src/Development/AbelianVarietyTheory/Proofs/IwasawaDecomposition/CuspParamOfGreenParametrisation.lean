import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteFieldStatement

noncomputable section

open CategoryTheory Polynomial Formalism.L2.NT

namespace GlobalTheory.GreenParam

open GlobalTheory.GLq GlobalTheory.GLq.LabelUnique Formalism.IrreducibleCountingLemmas.TYPES

variable {g : ℕ} [Fact g.Prime]

def datum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : LabelDatum g where
  teich := t
  teich_inj := ht
  gen := ζ
  gen_order d hd := (hζ d hd).1
  gen_norm d e hd he := (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

theorem mem_rootsBar_of_aeval {P : (ZMod g)[X]} (hP : P ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : aeval x P = 0) : x ∈ Formalism.CyclotomicNorms.rootsBar P := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots (Polynomial.map_ne_zero hP), IsRoot, Polynomial.eval_map, ← aeval_def]
  exact hx

theorem isPrimeLab_iff (d : ℕ) (P : (ZMod g)[X]) :
    IsPrimeLab d P ↔ P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, ?_, h4⟩
    rintro rfl
    exact h3 (by simp)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, fun h0 => h3 ?_, h4⟩
    have hd : (X : (ZMod g)[X]) ∣ P := X_dvd_iff.2 h0
    exact (eq_of_monic_of_associated monic_X h1 (irreducible_X.associated_of_dvd h2 hd)).symm

theorem isPrimeLab_charpoly {d : ℕ} (y : Gn g d) (hy : Irreducible (y : Mt g d).charpoly) :
    IsPrimeLab d (y : Mt g d).charpoly := by
  refine ⟨Matrix.charpoly_monic _, hy, fun h0 => ?_, by simp [Matrix.charpoly_natDegree_eq_dim]⟩
  have hdet := Matrix.det_eq_sign_charpoly_coeff (y : Mt g d)
  rw [h0, mul_zero] at hdet
  exact (Matrix.isUnits_det_units y).ne_zero hdet

theorem exists_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {z : Formalism.CyclotomicNorms.Fbar g}
    (hz : z ^ (g ^ d - 1) = 1) : ∃ m : ℕ, L.gen d ^ m = z := by
  have h1 : 1 < g ^ d := Nat.one_lt_pow hd.ne' (Fact.out : g.Prime).one_lt
  haveI : NeZero (g ^ d - 1) := ⟨by omega⟩
  have hp : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := by
    rw [← L.gen_order d hd]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨m, -, hm⟩ := hp.eq_pow_of_pow_eq_one hz
  exact ⟨m, hm⟩

theorem sum_thetaOf (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {P : (ZMod g)[X]} (hP : IsPrimeLab d P)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar P) (m : ℕ) :
    ∑ i ∈ Finset.range d, thetaOf L d x ((L.gen d ^ m) ^ (g ^ i)) =
      ∑ i ∈ Finset.range d, L.teich x ^ (m * g ^ i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, pow_sub_one_eq_one hP hx, map_one]
  rw [← pow_mul, thetaOf_gen_pow L d hd x hw]

theorem hasCuspLabel_iff (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) {d : ℕ} (V : FDRep ℂ (GL (Fin d) (ZMod g)))
    (hV : IsCusp (fun x => V.character x)) (P : (ZMod g)[X]) :
    HasCuspLabel (convC t ht ζ hζ) V P ↔ IsCuspOf (datum t ht ζ hζ) P (fun x => V.character x) := by
  have hd : 0 < d := hV.1
  unfold HasCuspLabel
  simp only [Fintype.card_fin, ZMod.card]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hP : IsPrimeLab d P := (isPrimeLab_iff d P).2 ⟨h1, h2, h3, h4⟩
    refine ⟨hP, hV, fun x hx y hy z hz => ?_⟩
    have hy' := isPrimeLab_charpoly y hy
    obtain ⟨m, rfl⟩ := exists_gen_pow (datum t ht ζ hζ) hd (pow_sub_one_eq_one hy' hz)
    rw [sum_thetaOf _ hd hP hx]
    exact h5 x (aeval_eq_zero_of_mem h1.ne_zero hx) y hy _ (aeval_eq_zero_of_mem hy.ne_zero hz) m rfl
  · rintro ⟨hP, -, h5⟩
    obtain ⟨h1, h2, h3, h4⟩ := (isPrimeLab_iff d P).1 hP
    refine ⟨h1, h2, h3, h4, fun x hx y hy z hz m hm => ?_⟩
    have hx' := mem_rootsBar_of_aeval h1.ne_zero hx
    have h := h5 x hx' y hy z (mem_rootsBar_of_aeval hy.ne_zero hz)
    have hm' : (datum t ht ζ hζ).gen d ^ m = z := hm
    rw [← hm', sum_thetaOf _ hd hP hx'] at h
    exact h

theorem nonempty_iso_of_character {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Fintype.card_pos.ne')
  have h1 := FDRep.char_orthonormal V W
  have h2 := FDRep.char_orthonormal V V
  rw [← h, h2, if_pos ⟨Iso.refl V⟩] at h1
  by_contra h3
  rw [if_neg h3] at h1
  exact one_ne_zero h1

theorem cuspParam_of_green : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g)
    (hζ : IsGenSys ζ), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam (ZMod g) (convC t ht ζ hζ) := by
  intro hG g _ t ht ζ hζ d hd
  obtain ⟨τ, hτ, -, hall⟩ := hG g (datum t ht ζ hζ) d hd
  have huniq := GlobalTheory.GLq.LabelUniqueAll.label_eq (datum t ht ζ hζ) d
  refine ⟨fun V hs hc => ?_, fun P h1 h2 h3 h4 => ?_, fun V W P hs hc hs' hc' hP hP' => ?_⟩
  · have hV := (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc
    obtain ⟨Q, hQ, hVQ⟩ := hall _ hV
    refine ⟨⟨Q, ?_, fun P hP => ?_⟩, ?_⟩
    · refine (hasCuspLabel_iff t ht ζ hζ V hV Q).2 ?_
      rw [hVQ]; exact (hτ Q hQ).1
    · refine huniq P Q _ ((hasCuspLabel_iff t ht ζ hζ V hV P).1 hP) ?_
      rw [hVQ]; exact (hτ Q hQ).1
    · have h1 : V.character 1 = τ Q 1 := congrFun hVQ 1
      rw [FDRep.char_one, (hτ Q hQ).2] at h1
      simp only [q, ZMod.card]
      exact_mod_cast h1
  · have hP : IsPrimeLab d P := (isPrimeLab_iff d P).2 ⟨h1, h2, h3, h4⟩
    have hc := (hτ P hP).1
    obtain ⟨V, hs, hVχ⟩ := hc.2.1.2.1
    have he : (fun x => V.character x) = τ P := funext hVχ
    have hV : IsCusp (fun x => V.character x) := he ▸ hc.2.1
    exact ⟨V, hs, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).1 hV, (hasCuspLabel_iff t ht ζ hζ V hV P).2 (he ▸ hc)⟩
  · have hV := (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc
    have hW := (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d W hd hs').2 hc'
    obtain ⟨Q, hQ, hVQ⟩ := hall _ hV
    obtain ⟨Q', hQ', hWQ⟩ := hall _ hW
    have e1 : P = Q := huniq P Q _ ((hasCuspLabel_iff t ht ζ hζ V hV P).1 hP) (hVQ ▸ (hτ Q hQ).1)
    have e2 : P = Q' := huniq P Q' _ ((hasCuspLabel_iff t ht ζ hζ W hW P).1 hP') (hWQ ▸ (hτ Q' hQ').1)
    refine nonempty_iso_of_character V W ?_
    exact hVQ.trans ((e1.symm.trans e2) ▸ hWQ.symm)

end GlobalTheory.GreenParam
