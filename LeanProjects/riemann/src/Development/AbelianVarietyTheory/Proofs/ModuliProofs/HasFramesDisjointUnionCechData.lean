import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in

theorem lin_of_isEmpty {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} [hT : IsEmpty T'.left]
    (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) (c : Fin n → Γ(T'.left, ⊤))
    (s : LB.Sec (LPow G L (N : ℤ) T')) : Lin G L N h b c s := by
  intro z
  exact isEmptyElim ((fst T' G).left z)

theorem isEmpty_of_eq_bot {Z : Scheme.{0}} {U : Z.Opens} (h : U = ⊥) : IsEmpty U.toScheme := by
  subst h
  exact ⟨fun x => by simpa using x.2⟩

theorem subsingleton_sections_of_isEmpty {X : Scheme.{0}} [IsEmpty X] : Subsingleton Γ(X, ⊤) := by
  refine CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)
  ext x
  exact isEmptyElim x

open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in

theorem trans_of_inf_eq_bot {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) {n : ℕ} (r s : ℤ) {U V : Z.Opens}
    (hUV : U ⊓ V = ⊥) (thU : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk U.ι)))
    (thV : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk V.ι)))
    (bU : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))) (bV : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk V.ι)))
    (g : Γ(Z, U ⊓ V)) :
    ∃ (c : Γ((U ⊓ V).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((U ⊓ V).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => thU) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        (fun _ : Fin 1 => thV) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => bU k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        bV (fun k' => M.val k k') t) ∧
    (U ⊓ V).topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val := by
  have hE : IsEmpty (U ⊓ V).toScheme := isEmpty_of_eq_bot hUV
  have := subsingleton_sections_of_isEmpty (X := (U ⊓ V).toScheme)
  have sec : ∀ M : ℕ, LB.Sec (LPow G L (M : ℤ) (Over.mk (U ⊓ V).ι)) := fun M =>
    { f := fun _ => 0
      compat := fun _ _ => fn_ext fun y _ => (hE.false ((fst (Over.mk (U ⊓ V).ι) G).left y)).elim }
  refine ⟨1, 1, ⟨sec 1, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _⟩,
    fun k => ⟨sec N, lin_of_isEmpty (hT := hE) G L N _ _ _ _, lin_of_isEmpty (hT := hE) G L N _ _ _ _⟩,
    Subsingleton.elim _ _⟩

theorem hasFrames_sumLB : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  intro Z G L N A B n r s hAB hA hB
  obtain ⟨thA, bA, hAt, hAb⟩ := hA
  obtain ⟨thB, bB, hBt, hBb⟩ := hB
  refine ⟨fun | .inl i => thA i | .inr j => thB j, fun | .inl i => bA i | .inr j => bB j, ?_, ?_⟩
  · rintro (i | i) (j | j)
    · exact hAt i j
    · exact trans_of_inf_eq_bot G L N r s (hAB i j) (thA i) (thB j) (bA i) (bB j) _
    · exact trans_of_inf_eq_bot G L N r s (by rw [inf_comm]; exact hAB j i) (thB i) (thA j) (bB i) (bA j) _
    · exact hBt i j
  · rintro (i | i) W _ _ _ hW χ hχ
    · exact hAb i W hW χ hχ
    · exact hBb i W hW χ hχ

end GlobalTheory.ModelSum
