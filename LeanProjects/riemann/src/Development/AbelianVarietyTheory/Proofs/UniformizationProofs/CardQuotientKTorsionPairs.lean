import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_eq_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (hk : k ≠ 0)
    (hd : ∀ y : D.X, ∃ g : GtPtF D F, k • g = iota hB F y) :
    Nat.card (Quot (QkPt.Equiv D F (k := k))) = k ^ D.rank * Nat.card {g : GtPtF D F // k • g = 0} := by
  choose r hr using hd
  let K : AddSubgroup D.X := (nsmulAddMonoidHom k : D.X →+ D.X).range
  have hK : Nat.card (D.X ⧸ K) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  let f : (D.X ⧸ K) × {g : GtPtF D F // k • g = 0} → Quot (QkPt.Equiv D F (k := k)) := fun x =>
    Quot.mk _ (qkMk hB x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
  rw [← hK, ← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · rintro ⟨c, t⟩ ⟨c', t'⟩ h
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
    simp only [qkMk_y, qkMk_g] at hy hg
    obtain rfl : c = c' := by
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
      exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
    have hz : z = 0 := by
      have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
      exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk)
    rw [hz, map_zero, add_zero, add_right_inj] at hg
    exact Prod.ext rfl (Subtype.ext hg.symm)
  · rintro ⟨p⟩
    obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D.X ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    have hy : (QuotientAddGroup.mk p.y : D.X ⧸ K).out = p.y + k • z := by
      rw [show k • z = _ from hz, add_neg_cancel_left]
    refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota hB F z - r (QuotientAddGroup.mk p.y : D.X ⧸ K).out, ?_⟩,
      (Quot.sound ((equiv_iff hB _ _).2 ⟨z, hy, ?_⟩)).symm⟩
    · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul hB, map_add, map_nsmul, sub_self]
    · exact add_sub_cancel _ _

theorem card_qk : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → Nat.card (Quot (QkPt.Equiv D.toPre F (k := k))) = k ^ (2 * (D.toPre.rank + D.toPre.P.g)) := by
  intro hL R _ _ _ I hA D F _ _ _ k hk
  have : IsNoetherianRing R := hA.1
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL.1 hL.2.1 R D.toPre F k (Nat.cast_ne_zero.2 (by omega))).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  have h₂ := (gt_onto_divisible_kernel hL R I hA D F).2.1 k hk
  rw [card_qk_eq_mul D.tau_bimult (by omega) fun y => (h₂ _).imp fun _ e => ((isNsmul_iff_eq _ _ _).1 e).symm, h₁,
    ← pow_add]
  congr 1
  ring

end GlobalTheory.UT
end
