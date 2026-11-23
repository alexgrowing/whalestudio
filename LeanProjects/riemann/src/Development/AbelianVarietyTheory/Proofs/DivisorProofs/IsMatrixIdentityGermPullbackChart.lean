import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem pullbackGerm_finset_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {K : Type} (s : Finset K)
    (a : K → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem isMat_germ : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB R _ t A' B' _ _ φA' φB' Φ' c h
  obtain ⟨ψA, ψB, α, h1, h2, -, -, hch⟩ := h
  refine ⟨ψA, ψB, h1, h2, ?_⟩
  intro Z e z pM q hM hA
  have hz : e z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q) := by
    refine ⟨?_, ?_⟩
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hM i
      simpa using this
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hA i
      simpa using this
  refine ⟨gm e z _ (α.s (pM, q)), fun j => ?_⟩
  have E := congrArg (gs e z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q))) (hch j (pM, q))
  erw [gs_mul _ _ _ hz] at E
  erw [gs_unit _ _ _ hz, pullbackGerm_finset_sum _ _ _ hz, gs_appLE _ _ _ _ _ _ hz] at E
  refine E.trans (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  erw [gs_mul _ _ _ hz, gs_appLE _ _ _ _ _ _ hz, gs_appLE _ _ _ _ _ _ hz]
  rfl

end GlobalTheory.HomFixMat
