import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.QNF

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

theorem toLin'_nfMat_eq_sum_nfGen {E : Type} [Field E] [NumberField E] [StarRing E] (q n c : ℕ) (e : Fin c → ℤ) (z : Fin n → E)
    (y : Fin (n + c) → E) :
    Matrix.toLin' (nfMat n c (q : E) e z) y =
      Loc.inX E n c (fun a => y (Fin.castAdd c a)) + ∑ i, y (Fin.natAdd n i) • nfGen q n c e z i := by
  funext p
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Pi.add_apply, Finset.sum_apply]
  congr 1
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · simp [nfMat, Loc.inX]
    · have : ∀ a : Fin n, Fin.natAdd n b ≠ Fin.castAdd c a := fun a h => by
        have := congrArg Fin.val h
        simp at this; omega
      simp [nfMat, Loc.inX, this]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · have h1 : Fin.castAdd c a ≠ Fin.natAdd n i := fun h => by
        have := congrArg Fin.val h
        simp at this; omega
      have h2 : ¬ (a.1 = n + i.1) := by omega
      by_cases hi : i.1 = 0
      · have h0 : ∀ h, (⟨0, h⟩ : Fin c) = i := fun h => Fin.ext hi.symm
        have h3 : ¬ (a.1 = n) := by omega
        simp [nfMat, nfGen, Loc.inX, Loc.eN, h1, h3, hi, h0]
        ring
      · simp [nfMat, nfGen, Loc.eN, h1, h2, hi]
    · by_cases hb : b = i
      · subst hb
        simp [nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, mul_comm]
      · have : ¬ (b.1 = i.1) := fun h => hb (Fin.ext h)
        simp [nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, hb, this]

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem image_lamYat_nfMat {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (e : Fin (cOf R j) → ℤ)
    (z : Fin (R.N j) → X.E) :
    (Matrix.toLin' (nfMat (R.N j) (cOf R j) ((qOf P : ℕ) : X.E) e z)) ''
        (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = nfLat P (R.N j) (cOf R j) e z := by
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_lamYat hP, nfLat, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun a => x (Fin.castAdd _ a), (mem_localization_standardLattice _ _).2 fun a => hx _, fun b => x (Fin.natAdd _ b),
      fun b => hx _, toLin'_nfMat_eq_sum_nfGen _ _ _ _ _ _⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    refine ⟨Fin.addCases (motive := fun _ => X.E) l s, fun p => ?_, ?_⟩
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) p
      · simpa using (mem_localization_standardLattice _ _).1 hl a
      · simpa using hs b
    · rw [toLin'_nfMat_eq_sum_nfGen]
      simp

theorem pad_mem_lamYat_iff {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (z : Fin (R.N j) → X.E) :
    (fun l : Fin (R.N j + cOf R j) => if h : l.1 < R.N j then z ⟨l.1, h⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ↔
      z ∈ stdAt X.E (R.N j) P := by
  rw [mem_lamYat hP]
  constructor
  · intro h
    refine (mem_localization_standardLattice _ _).2 fun a => ?_
    simpa using h (Fin.castAdd _ a)
  · intro h l
    by_cases hl : l.1 < R.N j
    · simpa [hl] using (mem_localization_standardLattice _ _).1 h ⟨l.1, hl⟩
    · simpa [hl] using (mem_lamYat (R := R) (j := j) hP 0).1 (zero_mem _) l

theorem nf_iff_matNF : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs →
    ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h ↔ GlobalTheory.QNF.MatNF Pr R j P h := by
  intro X Pr R j P hP h
  unfold NF MatNF
  refine exists_congr fun e => exists_congr fun z => and_congr_right fun _ => and_congr (pad_mem_lamYat_iff hP z).symm ?_
  rw [← image_lamYat_nfMat hP]
  refine Iff.trans ?_ SetLike.ext'_iff.symm
  rw [Submodule.map_coe, Submodule.map_coe]
  rfl

end GlobalTheory.QNF

end
