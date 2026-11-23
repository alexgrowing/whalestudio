import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnivPairing

theorem weilIs_pow_eq_one (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  obtain ⟨hex, hmul, -, -⟩ := hW S P k T
  obtain ⟨c₁, hc₁, hu⟩ := hex 1 y (one_pow k) hy
  have h₂ := hmul 1 1 y c₁ c₁ hc₁ hc₁
  rw [_root_.mul_one] at h₂
  obtain rfl : c₁ = 1 := mul_eq_left.1 (hu _ h₂)
  have hpow : ∀ j : ℕ, WeilIs P.A P.L k (x ^ j) y (c ^ j) := fun j => by
    induction j with
    | zero => rw [pow_zero, pow_zero]; exact hc₁
    | succ j ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ _ ih hc
  have h := hpow k
  rw [hx] at h
  exact hu _ h

theorem isNilpotent_of_geometric {B : Type} [CommRing B] {b : B}
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ b = 0) : IsNilpotent b := by
  refine nilpotent_iff_mem_prime.2 fun J hJ => ?_
  have e := h (AlgebraicClosure (FractionRing (B ⧸ J)))
    (((algebraMap (FractionRing (B ⧸ J)) _).comp (algebraMap (B ⧸ J) (FractionRing (B ⧸ J)))).comp
      (Ideal.Quotient.mk J))
  rw [RingHom.comp_apply, RingHom.comp_apply, map_eq_zero,
    map_eq_zero_iff _ (IsFractionRing.injective (B ⧸ J) _)] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e

theorem eq_one_of_geometric (B : Type) [CommRing B] (u : B) (k : ℕ) (hk : IsUnit (k : B)) (hu : u ^ k = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) : u = 1 := by
  have hn : IsNilpotent ((∑ i ∈ Finset.range k, u ^ i) - k) := isNilpotent_of_geometric fun K _ _ χ => by
    simp [h K χ]
  have hs : IsUnit (∑ i ∈ Finset.range k, u ^ i) := by
    have := hn.isUnit_add_right_of_commute hk (Commute.all _ _)
    rwa [sub_add_cancel] at this
  have e := geom_sum_mul u k
  rw [hu, sub_self] at e
  exact sub_eq_zero.1 (hs.mul_right_eq_zero.1 e)

theorem weilIs_univ_pull_exists_unique : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), 0 < N → (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (x y : T ⟶ Xo.univ.t.G) (e : Γ(T.left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom e)) ∧ (∀ (T : Over Xo.X) (x y : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → ∃ e : Γ(T.left, ⊤)ˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e ∧ e ^ (N ^ 2) = 1 ∧ ∀ e', WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e' → e' = e) ∧ ∀ (B : Type) [CommRing B] (u : B) (k : ℕ), IsUnit (k : B) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) → u = 1 := by
  intro hL E _ _ _ H Dw l Xo N _
  have := UnivPol.isLocallyNoetherian Xo
  refine ⟨fun T T' h x y e _ _ he => ?_, fun T x y hx hy => ?_, eq_one_of_geometric⟩
  · exact CommPairing.weilIs_pull hL.globalFns (UnivPol.pol Xo).isAb (UnivPol.pol Xo).isLB h he
  · rw [← Nat.cast_pow]
    obtain ⟨e, he, hu⟩ := (hL.weil Xo.X (UnivPol.pol Xo) (N ^ 2) T).1 x y hx hy
    exact ⟨e, he, weilIs_pow_eq_one hL.weil (UnivPol.pol Xo) (N ^ 2) x y hx hy e he, hu⟩

end GlobalTheory.UnivPairing
