import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfield
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsOneTraitWeilPairingBijectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsTraitCompatibleLevelsMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointMulLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionLabelingGaloisConjugateAlgClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelingsEqOfThetaPointPairingsOrderNStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaLevels

variable {R : Type} [CommRing R] [IsDomain R]

def galPt {A : PolAV (Sp (FractionRing R))} (σ : Kb R →ₐ[FractionRing R] Kb R) (y : TFK (R := R) (Kb R) ⟶ A.A) :
    TFK (R := R) (Kb R) ⟶ A.A :=
  Over.homMk (spMap σ.toRingHom ≫ y.left) (by
    rw [Category.assoc, Over.w y]
    show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R))) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) σ.comp_algebraMap)

theorem conj_eq_of_pow_eq_one [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hT : OneTrait D.toPre A lab) {n : ℕ} (hn : 1 ≤ n)
    (hnK : (n : Kb R) ≠ 0) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (hQ : ∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p')
    (hA : ∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ n = 1 → spMap σ.toRingHom ≫ y.left = y.left)
    {M d : ℕ} (hd : 1 ≤ d) (hM : M = n * d) (x₂ : QkPt D.toPre (Kb R) M → (TFK (R := R) (Kb R) ⟶ A.A))
    (hx₂ : ∀ p p', QkExt σ.toRingHom p p' → (x₂ p').left = spMap σ.toRingHom ≫ (lab M p).left)
    (h₂ : LabTors D.toPre A M x₂) (p' : QkPt D.toPre (Kb R) M) (hp' : lab M p' ^ n = 1) : x₂ p' = lab M p' := by
  subst hM
  have hnd : 1 ≤ n * d := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have T₁ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT n hn
  have T₂ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT (n * d) hnd
  obtain ⟨r, hr⟩ := T₁.1 _ hp'
  obtain ⟨q, hqy, hqg⟩ := GlobalTheory.T.exists_levelPoint_mul_level R D (Kb R) n d r
  have hq : lab (n * d) q = lab n r := GlobalTheory.T.torsionLabels_trait_compatible_levels_mul R hR D A lab hT n d hn hd r q hqy hqg
  have hqp : QkPt.Equiv D.toPre (Kb R) q p' := (T₂.2.2.1 q p').1 (hq.trans hr)
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom σ.comp_algebraMap hnK r
  obtain ⟨q₀, hq₀y, hq₀g⟩ := GlobalTheory.T.exists_levelPoint_mul_level R D (Kb R) n d r₀
  have hq₀ : QkExt σ.toRingHom q₀ q := by
    obtain ⟨y, g, e⟩ := q
    obtain ⟨y₀, g₀, e₀⟩ := q₀
    dsimp only at hqy hqg hq₀y hq₀g
    subst hqg hq₀g hqy hq₀y
    exact ⟨congrArg (d • ·) hr₀.1, hr₀.2.1, hr₀.2.2⟩
  have e₂ := hx₂ q₀ q hq₀
  rw [GlobalTheory.T.torsionLabels_trait_compatible_levels_mul R hR D A lab hT n d hn hd r₀ q₀ hq₀y hq₀g, (T₁.2.2.1 r₀ r).2 (hQ r₀ r hr₀), hr, hA _ hp'] at e₂
  exact ((h₂.2.2.1 q p').2 hqp).symm.trans (Over.OverMorphism.ext e₂)

end GlobalTheory.Mum.ThetaLevels

open GlobalTheory.Mum.ThetaLevels in

theorem GlobalTheory.Mum.thetaLevels_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, (∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p') ∧ ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left) → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ v : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → Kb R, IsThetaPt A (n ^ i) (lab ((n ^ i) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p') → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left := by
  intro R _ _ _ hR n hn ho hu D A lab hT hG
  have hch : CharZero R := hR.2
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ j₀ * (n ^ 2) ^ 2 := by
    refine ⟨((n ^ 2) ^ 2) ^ A.g * A.g.factorial, ?_⟩
    have h1 : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ (((n ^ 2) ^ 2) ^ A.g * A.g.factorial) :=
      Nat.lt_pow_self hn.one_lt
    have h2 : 1 ≤ (n ^ 2) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)
    exact lt_of_lt_of_le h1 (Nat.le_mul_of_pos_right _ h2)
  refine ⟨j₀ + 4, fun i hi v hv hc σ p p' hpp' => ?_⟩
  have hmj : n ^ i = n ^ (i - 4) * (n ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hbound : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < (n ^ i) := by
    rw [hmj]
    exact lt_of_lt_of_le hj₀ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn.pos (by omega)))
  have hF : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have hKc : CharZero (Kb R) := charZero_of_injective_algebraMap (algebraMap (FractionRing R) (Kb R)).injective
  have hMK : (((n ^ i) ^ 2 : ℕ) : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hn.ne_zero))
  choose pre hpre using fun p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) =>
    GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom σ.comp_algebraMap hMK p'
  let x₂ : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A) := fun q => galPt σ (lab ((n ^ i) ^ 2) (pre q))
  have hx₂ : ∀ q q', QkExt σ.toRingHom q q' → (x₂ q').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) q).left := fun q q' h => by
    show spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) (pre q')).left = _
    rw [GlobalTheory.QkClosure.qkExt_inj σ.toRingHom σ.comp_algebraMap (hpre q') h]
  have hM1 : 1 ≤ (n ^ i) ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero _ hn.ne_zero))
  have H₁ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT ((n ^ i) ^ 2) hM1
  have H₂ := GlobalTheory.T.isTorsionLabeling_galoisConjugate_algClosure R hR D A σ ((n ^ i) ^ 2) hM1 (lab ((n ^ i) ^ 2)) x₂ H₁ hx₂
  have Hn : ∀ q, lab ((n ^ i) ^ 2) q ^ n = 1 → x₂ q = lab ((n ^ i) ^ 2) q := fun q hq =>
    conj_eq_of_pow_eq_one hR D A lab hT hn.one_lt.le (Nat.cast_ne_zero.2 hn.ne_zero) σ (hG σ).1 (hG σ).2
      (d := n ^ (2 * i - 1)) (Nat.one_le_pow _ _ hn.pos)
      (by rw [← pow_mul, ← pow_succ']; congr 1; omega) x₂ hx₂ H₂ q hq
  obtain ⟨c, hc'⟩ := hc σ
  have h₁ := GlobalTheory.ThetaDescentLevel.isThetaPt_reindex hv pre
  have h₂ := GlobalTheory.T.thetaPoint_conj_algClosure_automorphism R A (n ^ i) σ _ (fun q => lab ((n ^ i) ^ 2) (pre q)) x₂ (fun q => v (pre q)) (fun q => rfl) h₁
  have h₃ : IsThetaPt A (n ^ i) x₂ (fun q => GlobalTheory.Ex.fnOf (v q)) :=
    GlobalTheory.Ex.ThetaDescent.isThetaPt_unit_mul A (n ^ i) x₂ _ _ (GlobalTheory.Ex.fnOf ((c⁻¹ : (Kb R)ˣ) : Kb R))
      ((Units.isUnit c⁻¹).map _) (fun q => by
        unfold GlobalTheory.Ex.fnOf
        rw [← map_mul, hc' _ _ (hpre q), ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]) h₂
  have key := GlobalTheory.T.torsionLabelings_eq_of_thetaPoint_pairings_order_n R D.toPre A n (i - 4) (n ^ i) hn ho hmj hbound (lab ((n ^ i) ^ 2)) x₂ H₁ H₂ Hn v hv h₃ p'
  rw [← key]
  exact hx₂ p p' hpp'
