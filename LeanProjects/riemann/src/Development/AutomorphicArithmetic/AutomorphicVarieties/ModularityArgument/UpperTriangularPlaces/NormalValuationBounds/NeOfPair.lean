import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.BarFacts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

open private spl_bar from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit

namespace UpperTheory.V.Keep

private theorem pairs (e : ℕ) (he : 2 ≤ e) (i j : Fin 4)
    (h : (![e + 1, e, 1, 0] : Fin 4 → ℕ) i = (![e + 1, e, 1, 0] : Fin 4 → ℕ) j + 1) :
    (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 1 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega

private theorem ne_of_pair {k : Type} [Field k] (x : k) (hx : x ≠ 1) (i j : Fin 4)
    (h : (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 1 ∧ j = 2)) :
    (![x, 1, x, 1] : Fin 4 → k) i ≠ (![x, 1, x, 1] : Fin 4 → k) j := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hx, Ne.symm hx]

private theorem exp_step {M : Type} [CommGroup M] (a b c : M) (m n : ℕ) (hc : ¬ IsOfFinOrder c)
    (h : a = b * c) (ha : a ^ 2 = c ^ (2 * (m : ℤ))) (hb : b ^ 2 = c ^ (2 * (n : ℤ))) : m = n + 1 := by
  have hinj := injective_zpow_iff_not_isOfFinOrder.2 hc
  have key : c ^ (2 * (m : ℤ)) = c ^ (2 * ((n : ℤ) + 1)) := by
    rw [← ha, h, mul_pow, hb, ← zpow_natCast c 2, ← zpow_add]
    congr 1
  have := hinj key
  omega

private theorem res_step {l : ℕ} [Fact l.Prime] (c : Coef l) (a b d : c.Oˣ) (x y : PadicAlgCl l)
    (hx : ‖x - ((a : c.O) : PadicAlgCl l)‖ < 1) (hy : ‖y - ((b : c.O) : PadicAlgCl l)‖ < 1)
    (e : x = y * ((d : c.O) : PadicAlgCl l)) :
    residue c.O (a : c.O) = residue c.O (b : c.O) * residue c.O (d : c.O) := by
  set z : c.O := (a : c.O) - (b : c.O) * (d : c.O) with hz
  have hnorm : ‖((z : c.O) : PadicAlgCl l)‖ < 1 := by
    have hd := GlobalTheory.CoefCoord.norm_unit c d
    have hsplit : ((z : c.O) : PadicAlgCl l) =
        -(x - ((a : c.O) : PadicAlgCl l)) + (y - ((b : c.O) : PadicAlgCl l)) * ((d : c.O) : PadicAlgCl l) := by
      rw [hz, e]
      push_cast
      ring
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rwa [norm_neg]
    · rw [norm_mul, hd, mul_one]
      exact hy
  have hmem : z ∈ maximalIdeal c.O := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := GlobalTheory.CoefCoord.norm_unit c hu.unit
    simp only [IsUnit.unit_spec] at this
    rw [this] at hnorm
    exact lt_irrefl _ hnorm
  have h0 : residue c.O z = 0 := (residue_eq_zero_iff _).2 hmem
  rw [hz, map_sub, map_mul, sub_eq_zero] at h0
  exact h0

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem bar_chi (D : Raw Ω c) (hD : D.Good) (pr : Bool) (g : G ℚ Ω) (hp : Raw.bar D.Psi g = 1) (i : Fin 4) :
    Raw.bar (chi D pr i) g = (![Raw.bar D.ξ g, 1, Raw.bar D.ξ g, 1] : Fin 4 → ResidueField c.O) i := by
  obtain ⟨-, -, hal, hth, -⟩ := barFacts D hD
  have h1 : Raw.bar (1 : G ℚ Ω →* c.Oˣ) g = 1 := by
    simp [Raw.bar]
  have hth' : Raw.bar D.th g = Raw.bar D.ξ g := by
    rw [hth, hp, mul_one]
  cases pr <;> fin_cases i <;> simp [chi, lab, Raw.ps, hal g, hth', hp, h1]

end

theorem unlF : UnlF := by
  intro hinf Ω _ _ _ l _ c D T hD hT hLoc r A hA κ hord i j heq
  obtain ⟨-, -, -, -, -, hrbar, hrb, -⟩ := barFacts D hD
  have hstep : ∀ s : Dec (F := T.F) A, κ i s = κ j s * cycBar T.F Ω l s.1 := by
    intro s
    rw [heq]
    rfl
  have hres : ∀ s : Dec (F := T.F) A, Raw.bar (chi D T.pr i) (resQ T.F s.1) =
      Raw.bar (chi D T.pr j) (resQ T.F s.1) * Raw.bar (chiO ℚ Ω l c.O) (resQ T.F s.1) := by
    intro s
    have h2 := congrArg Units.val (hstep s)
    rw [Units.val_mul] at h2
    exact res_step c _ _ _ _ _ (hord.red i s) (hord.red j s) h2
  rcases hLoc A hA with ⟨g, hgI, hom⟩ | ⟨g, hgD, hom, hps, hal⟩
  · obtain ⟨hξ, hΨ⟩ := (hrbar _).1 (hT.ineL A hA g hgI)
    have e1 := hres ⟨g, Ine_le_Dec A hgI⟩
    have hall : ∀ k, (![Raw.bar D.ξ (resQ T.F g), 1, Raw.bar D.ξ (resQ T.F g), 1] : Fin 4 → ResidueField c.O) k = 1 := by
      intro k
      fin_cases k
      · exact hξ
      · rfl
      · exact hξ
      · rfl
    rw [bar_chi D hD T.pr _ hΨ, bar_chi D hD T.pr _ hΨ, hall, hall, one_mul, ← hD.om_bar] at e1
    exact hom e1.symm
  · have hΨ : Raw.bar D.Psi (resQ T.F g) = 1 := by
      rw [hrb] at hps
      cases h : T.pr <;> simp [wPs, h] at hps <;> exact hps
    have hξ : Raw.bar D.ξ (resQ T.F g) ≠ 1 := by
      rw [hrb] at hal
      simpa [wAl] using hal
    obtain ⟨U, hU, hw⟩ := hord.wts
    obtain ⟨s, hs, hc⟩ := hinf T.F Ω l A hA U hU
    let sD : Dec (F := T.F) A := ⟨s, Ine_le_Dec A (Subgroup.mem_inf.1 hs).2⟩
    have hnum : D.wts4 i = D.wts4 j + 1 :=
      exp_step _ _ _ _ _ hc (hstep sD) (hw i sD hs) (hw j sD hs)
    have hp := pairs D.e hD.two_le i j hnum
    have e1 := hres ⟨g, hgD⟩
    rw [bar_chi D hD T.pr _ hΨ, bar_chi D hD T.pr _ hΨ, ← hD.om_bar, hom, mul_one] at e1
    exact ne_of_pair _ hξ i j hp e1

end UpperTheory.V.Keep
