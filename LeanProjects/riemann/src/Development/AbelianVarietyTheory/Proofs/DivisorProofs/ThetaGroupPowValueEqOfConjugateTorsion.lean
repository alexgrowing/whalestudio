import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateL
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaPowConj

theorem prod_telescope {U : Type} [CommGroup U] (F G : ℕ → U) (n : ℕ) :
    ∏ i ∈ Finset.range n, (F i * G i * (F (i + 1))⁻¹) = F 0 * (∏ i ∈ Finset.range n, G i) * (F n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    group

theorem val_powGen_transport : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  intro S S' A A' _ _ L L' T T' f k N θ θ' Ψ hT hN H Z q z J J' hJ hJ'
  rw [GlobalTheory.ConjPull.val_thetaPow θ N (q ≫ f) z hJ, GlobalTheory.ConjPull.val_thetaPow θ' N q z hJ']
  have step : ∀ i ∈ Finset.range N,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        ((q ≫ f) ≫ (translT A (θ.pt ^ i)).left) z J =
      Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k *
        val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J' *
        (Ψ (q ≫ (translT A' (θ'.pt ^ (i + 1))).left) z J J' ^ k)⁻¹ := by
    intro i _
    have e1 : (q ≫ f) ≫ (translT A (θ.pt ^ i)).left = (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ f := by
      rw [Category.assoc, hT i, Category.assoc]
    have e2 : (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ (translT A' θ'.pt).left =
        q ≫ (translT A' (θ'.pt ^ (i + 1))).left := by
      rw [Category.assoc, ← Over.comp_left, GlobalTheory.PullMove.translT_mul, pow_succ']
    rw [e1, H Z _ z J J' hJ hJ', e2]
  rw [Finset.prod_congr rfl step,
    prod_telescope (fun i => Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k)
      (fun i => val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J')]
  simp only [hN, pow_zero]
  rw [mul_comm, ← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.ThetaPowConj
