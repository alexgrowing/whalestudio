import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ModelSum

theorem image_inf_le {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (U V : Z'.Opens) :
    f ''ᵁ U ⊓ f ''ᵁ V ≤ f ''ᵁ (U ⊓ V) := by

  rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
  obtain rfl : b = a := f.isOpenEmbedding.injective hba
  exact ⟨b, ⟨ha, hb⟩, rfl⟩

def pushLB {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') : LB Z :=
  ⟨A.ι, fun i => f ''ᵁ A.U i, fun i j => res (image_inf_le f (A.U i) (A.U j))
    (Units.map (f.appIso (A.U i ⊓ A.U j)).inv.hom.toMonoidHom (A.g i j))⟩

def sumLB {Z : Scheme.{0}} (A B : LB Z) : LB Z :=
  ⟨A.ι ⊕ B.ι, Sum.elim A.U B.U, fun p q => match p, q with
    | .inl i, .inl j => A.g i j
    | .inr i, .inr j => B.g i j
    | .inl _, .inr _ => 1
    | .inr _, .inl _ => 1⟩

def AmpleFam {Z : Scheme.{0}} (A : LB Z) : Prop :=
  ∀ z : Z, ∃ (d : ℕ) (s : H0 A d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)

def HasFrames {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n : ℕ) (r s : ℤ) : Prop :=
  ∃ (th : ∀ i : A.ι, LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk (A.U i).ι)))
    (b : ∀ i : A.ι, Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (A.U i).ι))),
  (∀ i j : A.ι, ∃ (c : Γ((A.U i ⊓ A.U j).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((A.U i ⊓ A.U j).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => th i) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (fun _ : Fin 1 => th j) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => b i k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (b j) (fun k' => M.val k k') t) ∧
    (A.U i ⊓ A.U j).topIso.inv.hom (A.g i j).val = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val) ∧
  ∀ (i : A.ι) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ χ : Sp W ⟶ (A.U i).toScheme,
    Set.range (jK W ≫ χ ≫ (A.U i).ι) ⊆ abLocus G →
    BasisAlong G L 1 (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (fun _ : Fin 1 => th i) ∧
    BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (b i)

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

theorem hasFrames_of_ampFrames (F : AmpFrames G L N) : HasFrames G L N F.A F.n F.r F.s := by
  refine ⟨F.th, F.b, ?_, ?_⟩
  · intro i j
    exact F.trans i j
  · intro i W _ _ _ hW χ hχ
    exact F.trait i W hW χ hχ

theorem exists_ampFrames {A : LB Z} {n : ℕ} {r s : ℤ} (hA : A.IsLB) (ha : AmpleFam A) (h : HasFrames G L N A n r s) :
    ∃ F : AmpFrames G L N, F.A = A ∧ F.n = n ∧ F.r = r ∧ F.s = s := by

  obtain ⟨th, b, htr, htrait⟩ := h
  exact ⟨⟨A, hA, ha, n, th, b, r, s, htr, htrait⟩, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ModelSum

end
