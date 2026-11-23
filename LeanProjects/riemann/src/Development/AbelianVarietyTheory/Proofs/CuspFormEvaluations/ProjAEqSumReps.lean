import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VacMean

open GlobalTheory.SW.TensVac GlobalTheory.SW.TensLat

theorem projA_eq_sum_reps {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E}
    {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)} (hA : Good X w A) (hA' : Good X w A')
    {v : TF n g} (hv : IsVac X bas w A' v) {R : Finset (Matrix (Fin n) (Fin r) E)}
    (hR : ∀ y ∈ R, y ∈ A) (hR' : ∀ y ∈ A, ∃! y' ∈ R, y - y' ∈ A') :
    projA X bas w A v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v := by
  have hfix : ∀ y, epsW X w y • heisG X bas y v = v ↔ y ∈ A' := by
    refine fun y => ⟨fun h => ?_, hv.2.2 y⟩
    by_contra hy
    have := hA'.ip_eq_zero idx hs hn hv hy
    rw [h, hv.2.1] at this
    exact one_ne_zero this
  have hiff : ∀ a ∈ A, ∀ b ∈ A, epsW X w a • heisG X bas a v = epsW X w b • heisG X bas b v ↔
      b - a ∈ A' := by
    intro a ha b hb
    rw [← neg_add_eq_sub, ← hfix, ← hA.rho_rho idx hs hn (A.neg_mem ha) hb hv.1]
    constructor
    · intro h
      rw [← h, hA.rho_rho idx hs hn (A.neg_mem ha) ha hv.1, neg_add_cancel,
        rho_zero idx hs hn hv.1]
    · intro h
      conv_lhs => rw [← h]
      rw [hA.rho_rho idx hs hn ha (A.neg_mem ha) (rho_sb idx hs hn b hv.1), add_neg_cancel,
        rho_zero idx hs hn (rho_sb idx hs hn b hv.1)]
  have hinj : Set.InjOn (fun y => epsW X w y • heisG X bas y v) R := fun a ha b hb h =>
    (hR' b (hR b hb)).unique ⟨ha, (hiff a (hR a ha) b (hR b hb)).1 h⟩
      ⟨hb, by rw [sub_self]; exact A'.zero_mem⟩
  have himg : (fun y => epsW X w y • heisG X bas y v) '' A =
      (fun y => epsW X w y • heisG X bas y v) '' R := by
    refine Set.Subset.antisymm ?_ (Set.image_mono fun y hy => hR y hy)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', ⟨h1, h2⟩, -⟩ := hR' y hy
    exact ⟨y', h1, (hiff y' (hR y' h1) y hy).2 h2⟩
  rw [projA, himg, finsum_mem_image hinj, finsum_mem_coe_finset, hinj.ncard_image,
    Set.ncard_coe_finset]

theorem vac_proj_mean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∃ R : Finset (Matrix (Fin n) (Fin r) E), (∀ y ∈ R, y ∈ tens Λ L) ∧ (∀ y ∈ tens Λ L, ∃! y', y' ∈ R ∧ ∀ b, y b - y' b ∈ L) ∧ R.card = ((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup) ^ r ∧ 0 < R.card ∧ projA X bas (w : E) (tens Λ L) v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X (w : E) y • heisG X bas y v := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn w hw L hL Λ hΛ v hv
  have good (Λ) (hΛ : Λ ∈ Vset E n 1) : Good X (w : E) (tens Λ L) :=
    ⟨tens_fg hΛ hL.1, tens_selfDual hΛ hL, fun y hy => epsW_semichar hΛ hL w.isIntegral_coe hw hy⟩
  have hS := GlobalTheory.SW.Base.stdL_mem_Vset (E := E) n 1
  have hidx := (tens_selfDual_semichar_index E r X g bas idx n hs hn w w.isIntegral_coe hw L hL 1
    Λ hΛ).2.2.2.2.2 _ hS
  obtain ⟨v', hv', -⟩ := (good Λ hΛ).vac hs
  have hne : (tens (stdL E n) L).relIndex (tens Λ L) ≠ 0 := by
    intro h
    have := (good Λ hΛ).overlap idx hs hn (good _ hS) hv' hv
    rw [h] at this
    simp at this
  obtain ⟨R, hR, hR'⟩ := TensorLat.exists_reps_of_relIndex_ne_zero hne
  have hc := TensorLat.card_eq_relIndex_of_reps hR hR'
  refine ⟨R, hR, fun y hy => ?_, hc.trans hidx, hc ▸ Nat.pos_of_ne_zero hne,
    projA_eq_sum_reps idx hs hn (good Λ hΛ) (good _ hS) hv hR hR'⟩
  have := hR' y hy
  simp only [mem_tens_stdL] at this
  exact this

end GlobalTheory.Dict.VacMean
