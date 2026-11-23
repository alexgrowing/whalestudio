import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepOfAffineTestsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHomsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixGlob

open TopologicalSpace in

theorem lc_props {Rg : Type} [CommRing Rg] [IsNoetherianRing Rg] {N : ℕ} {X H : Scheme.{0}}
    (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (i : H ⟶ X) [IsClosedImmersion c] [IsOpenImmersion i] :
    QuasiCompact (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    IsSeparated (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    LocallyOfFiniteType (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
  refine ⟨?_, inferInstance, ?_⟩
  · have h1 : NoetherianSpace (Sp (MvPolynomial (Fin N) Rg)) :=
      inferInstanceAs (NoetherianSpace (PrimeSpectrum (MvPolynomial (Fin N) Rg)))
    have h2 : NoetherianSpace H :=
      ((i ≫ c).isEmbedding).isInducing.noetherianSpace
    exact (quasiCompact_iff_compactSpace _).2 inferInstance
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      show (algebraMap Rg (MvPolynomial (Fin N) Rg)).FiniteType
      exact RingHom.finiteType_algebraMap.2 inferInstance
    infer_instance

theorem exists_homFixRep_of_secBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨N, X, c, H, i, AH, _, BH, _, φA, φB, Φ, hc, hi, pA, pB, hΦ, hiso, hrep⟩ :=
    GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs Rg A B L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨q1, q2, q3⟩ := lc_props c i
  exact ⟨HomFixRep.mk H (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))))
    AH BH φA φB pA pB Φ hΦ hiso (GlobalTheory.T.homFixedPullbackRep_of_affineTests _ A B L M hL hM H _ AH BH φA φB Φ pA pB hrep), q1, q2, q3⟩

end GlobalTheory.HomFixGlob
