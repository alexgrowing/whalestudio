import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def TWStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen → ∀ ζ : F, ζ ≠ 0 →
      ∃ c : ℚ, ∀ s t s' : Fam D.toPre F k, PhiRel D.toPre F k p w s t → Fam.IsSmul D.toPre F ζ t s' →
        ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' (r + c)

namespace PeriodicValuation

theorem all_of_periodic {P : ℚ → Prop} (hmono : ∀ r r' : ℚ, r' ≤ r → P r → P r') {d : ℚ} (hd : d ≠ 0)
    (hper : ∀ r, P r ↔ P (r + d)) (r₁ r₂ : ℚ) (h : P r₁) : P r₂ := by
  have he : ∀ r, P r → P (r + |d|) := by
    intro r hr
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · rw [abs_of_neg hneg]
      have h1 : P (r - d) := (hper (r - d)).2 (by rwa [sub_add_cancel])
      simpa [sub_eq_add_neg] using h1
    · rw [abs_of_pos hpos]
      exact (hper r).1 hr
  have hn : ∀ k : ℕ, P (r₁ + k * |d|) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have h2 := he _ ih
      convert h2 using 1
      push_cast
      ring
  have hpos : 0 < |d| := abs_pos.2 hd
  obtain ⟨k, hk⟩ := exists_nat_gt ((r₂ - r₁) / |d|)
  rw [div_lt_iff₀ hpos] at hk
  exact hmono _ _ (by linarith) (hn k)

end PeriodicValuation

open PeriodicValuation

theorem galois_fixed_adelic_matrices_descend (hL : Laws) (hTW : TWStatement) : FiniteOrderValuationInvariance := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk p w hw ζ hζ hfin s t s' hst hts' r
  obtain ⟨c, hc⟩ := hTW V ϖ hϖ D Q hQ F v hv k hk p w hw ζ hζ
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hL.globalFns V (maximalIdeal V) D F k hk p w hw
  obtain ⟨M, hM1, hM⟩ := hfin
  let step : Fam D.toPre F k → Fam D.toPre F k := fun x => ζ • Φ x
  have hsm : ∀ x : Fam D.toPre F k, Fam.IsSmul D.toPre F ζ (Φ x) (step x) := fun x α j => rfl
  have hstep : ∀ x r, NuGe D Q F v k x r ↔ NuGe D Q F v k (step x) (r + c) := fun x r =>
    hc x (Φ x) (step x) ((hΦ x (Φ x)).2 rfl) (hsm x) r
  have hsame : ∀ x y : Fam D.toPre F k, (∀ α j, (x.s α).f j = (y.s α).f j) →
      ∀ r, NuGe D Q F v k x r ↔ NuGe D Q F v k y r := by
    intro x y hxy r
    simp only [NuGe, VGe, hxy]
  have hiter : ∀ n : ℕ, ∀ r, NuGe D Q F v k s r ↔ NuGe D Q F v k (step^[n] s) (r + n * c) := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [ih r, Function.iterate_succ_apply', hstep (step^[n] s) (r + n * c)]
      have e : r + n * c + c = r + ((n + 1 : ℕ) : ℚ) * c := by push_cast; ring
      rw [e]
  have hret : ∀ α j, ((step^[M] s).s α).f j = (s.s α).f j := by
    refine hM (fun i => step^[i.val] s) (fun i => Φ (step^[i.val] s)) fun i => ⟨?_, ?_⟩
    · exact (hΦ _ _).2 rfl
    · intro α j
      show ((step^[i.val + 1] s).s α).f j = _
      rw [Function.iterate_succ_apply']
      exact hsm _ α j
  have hper : ∀ r, NuGe D Q F v k s r ↔ NuGe D Q F v k s (r + M * c) := fun r =>
    (hiter M r).trans (hsame _ _ hret _)
  by_cases hc0 : c = 0
  · have h := hc s t s' hst hts' r
    rwa [hc0, add_zero] at h
  · have hd : (M : ℚ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast (by omega : M ≠ 0)) hc0
    have hmono : ∀ r r' : ℚ, r' ≤ r → NuGe D Q F v k s r → NuGe D Q F v k s r' :=
      fun r r' h hp => NuGe.mono (h := hp) (hr := h)
    constructor
    · intro h
      have h1 : NuGe D Q F v k s (r - c) := all_of_periodic hmono hd hper r (r - c) h
      have h2 := (hc s t s' hst hts' (r - c)).1 h1
      rwa [sub_add_cancel] at h2
    · intro h
      have h1 : NuGe D Q F v k s (r - c) :=
        (hc s t s' hst hts' (r - c)).2 (by rwa [sub_add_cancel])
      exact all_of_periodic hmono hd hper (r - c) r h1

end ReciprocityTheory.ChartRestriction.G.DVR
