import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem unitOn_bijective (R : Type) [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.toMulEquiv).bijective

theorem unitOn_mul' {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v :=
  map_mul _ u v

theorem unitOn_one' {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 :=
  map_one _

theorem exists_weil_function : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)), ∃ e : ℕ → Pts A.A → Pts A.A → Cˣ, ∀ k : ℕ, 1 ≤ k → (∀ z s : Pts A.A, z ^ k = 1 → s ^ k = 1 → ∀ w : Cˣ, Out.WeilIs A.A A.L (k : ℤ) z s (unitOn w) ↔ w = e k z s) ∧ (∀ z z' s : Pts A.A, z ^ k = 1 → z' ^ k = 1 → s ^ k = 1 → e k (z * z') s = e k z s * e k z' s ∧ e k s (z * z') = e k s z * e k s z') ∧ (∀ (l : ℕ) (z s : Pts A.A), 1 ≤ l → z ^ k = 1 → s ^ (k * l) = 1 → e (k * l) z s = e k z (s ^ l)) ∧ ∀ κ : Pts A.A → Cˣ, (∀ z z', z ^ k = 1 → z' ^ k = 1 → κ (z * z') = κ z * κ z') → ∃! s : Pts A.A, s ^ k = 1 ∧ ∀ z, z ^ k = 1 → e k z s = κ z := by
  intro C _ _ _ A
  classical
  have hW : Out.WeilSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.1
  have hP : Out.CharPairSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb := unitOn_bijective C
  have hex : ∀ (k : ℕ) (z s : Pts A.A), ∃ c : Cˣ, z ^ k = 1 → s ^ k = 1 →
      ∀ w : Cˣ, Out.WeilIs A.A A.L (k : ℤ) z s (unitOn w) ↔ w = c := by
    intro k z s
    by_cases h : z ^ k = 1 ∧ s ^ k = 1
    · obtain ⟨c, hc, hu⟩ := (hW _ A k _).1 z s h.1 h.2
      obtain ⟨c', rfl⟩ := hb.2 c
      exact ⟨c', fun _ _ w => ⟨fun hw => hb.1 (hu _ hw), fun hw => hw ▸ hc⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose e he using hex
  have hself : ∀ (k : ℕ) (z s : Pts A.A), z ^ k = 1 → s ^ k = 1 →
      Out.WeilIs A.A A.L (k : ℤ) z s (unitOn (e k z s)) := fun k z s hz hs => (he k z s hz hs _).2 rfl
  have hmk : ∀ (k : ℕ) (z z' : Pts A.A), z ^ k = 1 → z' ^ k = 1 → (z * z') ^ k = 1 := fun k z z' hz hz' => by
    rw [mul_pow, hz, hz', _root_.one_mul]
  have hl : ∀ (k : ℕ) (z z' s : Pts A.A), z ^ k = 1 → z' ^ k = 1 → s ^ k = 1 →
      e k (z * z') s = e k z s * e k z' s := by
    intro k z z' s hz hz' hs
    refine ((he k _ s (hmk k z z' hz hz') hs _).1 ?_).symm
    rw [unitOn_mul']
    exact (hW _ A k _).2.1 _ _ _ _ _ (hself k z s hz hs) (hself k z' s hz' hs)
  have halt : ∀ (k : ℕ) (z : Pts A.A), z ^ k = 1 → e k z z = 1 := by
    intro k z hz
    refine ((he k z z hz hz _).1 ?_).symm
    rw [unitOn_one']
    exact (hW _ A k _).2.2.1 z hz
  have hskew : ∀ (k : ℕ) (z s : Pts A.A), z ^ k = 1 → s ^ k = 1 → e k z s = (e k s z)⁻¹ := by
    intro k z s hz hs
    refine ((he k z s hz hs _).1 ?_).symm
    have h := GlobalTheory.CommPairing.weilIs_symm A.isLB (hself k s z hs hz)
    rwa [show (unitOn (e k s z))⁻¹ = unitOn (e k s z)⁻¹ from (map_inv _ _).symm] at h
  have hr : ∀ (k : ℕ) (z z' s : Pts A.A), z ^ k = 1 → z' ^ k = 1 → s ^ k = 1 →
      e k s (z * z') = e k s z * e k s z' := by
    intro k z z' s hz hz' hs
    rw [hskew k s _ hs (hmk k z z' hz hz'), hl k z z' s hz hz' hs, hskew k s z hs hz, hskew k s z' hs hz',
      mul_inv]
  refine ⟨e, fun k hk => ⟨he k, fun z z' s hz hz' hs => ⟨hl k z z' s hz hz' hs, hr k z z' s hz hz' hs⟩, ?_, ?_⟩⟩
  · intro l z s hl1 hz hs
    have hz' : z ^ (k * l) = 1 := by rw [pow_mul, hz, one_pow]
    have hs' : (s ^ l) ^ k = 1 := by rw [← pow_mul, mul_comm, hs]
    have hu : IsUnit ((k * l : ℕ) : Γ((Over.mk (𝟙 (Sp C)) : Over (Sp C)).left, ⊤)) := by
      have h0 : IsUnit ((k * l : ℕ) : C) := by
        refine IsUnit.mk0 _ ?_
        exact_mod_cast (Nat.mul_pos hk hl1).ne'
      have := h0.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
      rwa [map_natCast] at this
    have h1 := ((hW _ A k _).2.2.2 l s z _ hu hs hz).2 (hself k _ z hs' hz)
    have h2 := (he (k * l) s z hs hz' _).1 (by exact_mod_cast h1)
    rw [hskew _ z s hz' hs, hskew _ z _ hz hs', h2]
  · intro κ hκ
    have hkC : (k : C) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    obtain ⟨b, ⟨hb1, hb2⟩, hbu⟩ := hP C A k hkC (fun x => unitOn (κ x.1)) (fun x y => by
      change unitOn (κ (x.1 * y.1)) = _
      rw [hκ _ _ x.2 y.2, unitOn_mul'])
    refine ⟨b, ⟨hb1, fun z hz => ((he k z b hz hb1 _).1 (hb2 ⟨z, hz⟩)).symm⟩, fun s hs => hbu s ⟨hs.1, fun x => ?_⟩⟩
    exact (he k x.1 s x.2 hs.1 _).2 (hs.2 x.1 x.2).symm

end GlobalTheory.ChTor
