import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WpQTrivRight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.SympQ

theorem qEq_one_of_wp {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (nd : ∀ b : N.A, b ^ k = 1 → (∀ b', b' ^ k = 1 → N.weil k b b' = 1) → b = 1) (p : N.QT k)
    (hp : ∀ p', N.wp p p' = 1) : N.QEq p 1 := by
  have hk0 : k ≠ 0 := fun h => hk (by rw [h, Nat.cast_zero])
  have h3 : ∀ y : N.X, ∃ p : N.QT k, p.1.1.toAdd = y := fun y => by
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨g, -, h⟩ := QStr.root_over N hk0 (N.io y) b hb
    exact ⟨⟨(Multiplicative.ofAdd y, g), h⟩, rfl⟩
  obtain ⟨p₀, hq, h1, hb⟩ := (QStr.orth_iff N hk nd p).1 fun p' _ => hp p'
  have : p₀ = 1 := by
    refine Subtype.ext (Prod.ext h1 (NumD.Gt.ext hb (funext fun χ => ?_)))
    obtain ⟨p', rfl⟩ := h3 χ
    rw [← (WpPairing.wp_pairing C N _ p₀ p' p').2.2.2.2.2.1 h1 hb, ← WpPairing.wp_congr_left N hq p', hp p']
    rfl
  rwa [this] at hq

theorem wpQ_nondeg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → ∀ x : GlobalTheory.SympQ.Qq N n, (∀ y, GlobalTheory.SympQ.wpQ N n x y = 1) → x = 1 := by
  intro R _ _ _ hR D F _ _ _ N ν n hn x hx
  obtain ⟨⟨h1, h2, h3, h4⟩, hc⟩ := hR
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have : CharZero F := by
    have : CharZero (FractionRing R) := inferInstance
    exact charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h0 : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨hW, -⟩ := GlobalTheory.ThetaInValues.brUth_of_laws hL R D.toPre D.psi_even D.tau_bimult F N ν
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  induction x using QuotientGroup.induction_on with
  | H p =>
    have hq : N.QEq p 1 := by
      refine qEq_one_of_wp N h0 (fun a => ?_) (fun b hb h => ?_) p fun p' => hx (QuotientGroup.mk p')
      · obtain ⟨y, hy⟩ := GlobalTheory.ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA a) hn
        exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
      · refine ν.eA.map_eq_one_iff.1 (GlobalTheory.ThetaRep.eq_one_of_weilIs hL D.toPre.P (jFK (R := R) F ≫ jK R) h0 _
          ((tor _ _).2 hb) fun y hy => ?_)
        obtain ⟨b', rfl⟩ := ν.eA.surjective y
        have hb' := (tor _ _).1 hy
        have := hW n hn b b' hb hb'
        rwa [h b' hb', show unitOn (1 : Fˣ) = 1 from map_one (Units.map _)] at this
    exact (qEq_iff_mk_eq N p 1).1 hq

end GlobalTheory.SympQ
