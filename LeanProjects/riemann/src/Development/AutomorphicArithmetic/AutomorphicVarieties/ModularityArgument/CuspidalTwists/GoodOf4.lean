import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.DefsBad
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Cu

private theorem gd_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hq : A.valuation (q : Ω) < 1) : ¬ A.valuation (p : Ω) < 1 := fun hp => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hv : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have h1 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv a)) hp
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv b)) hq
  have h2 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem gd_rb {D : Raw Ω c} (T : Tower D) (g : G T.F Ω) :
    T.rb wAl g = residue c.O (D.al (resQ T.F g) : c.O) := by
  have e : chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹ = D.al (resQ T.F g) := by
    generalize resQ T.F g = s
    cases T.pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]
  show residue c.O (((chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
    (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : c.Oˣ) : c.O) = _
  rw [zpow_one, zpow_zero, mul_one, e]

private theorem gd_al (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.ξ g = 1) :
    residue c.O (D.al g : c.O) = 1 := by
  have e : D.al g * D.om g = chiO ℚ Ω l c.O g := by
    simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, hg, mul_one, inv_mul_cancel_right]
  have e2 := congrArg (fun u : c.Oˣ => residue c.O (u : c.O)) e
  simp only [Units.val_mul, map_mul] at e2
  have e3 : residue c.O (D.om g : c.O) = residue c.O (chiO ℚ Ω l c.O g : c.O) := hD.om_bar g
  rw [← e3] at e2
  have hu : IsUnit (residue c.O (D.om g : c.O)) := (D.om g).isUnit.map _
  exact (mul_eq_right₀ hu.ne_zero).1 e2

private theorem gd_rbar (D : Raw Ω c) (g : G ℚ Ω) (h : D.rbar g = 1) : residue c.O (D.al g : c.O) = 1 := by
  have key : D.rbar g 2 2 = residue c.O (Matrix.diagonal (fun i => (D.ps i g : c.O)) 2 2) := rfl
  rw [h, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at key
  exact key.symm

private theorem gd_up {F : IntermediateField ℚ Ω} {g : G ℚ Ω} (hg : g ∈ F.fixingSubgroup) : ∃ g' : G F Ω, resQ F g' = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => (F.mem_fixingSubgroup_iff g).1 hg x.1 x.2, rfl⟩

end

theorem UpperTheory.V.Cu.goodOf4 :
    UpperTheory.V.Cu.GoodOf4 := by
  intro Ω _ _ _ l _ c D T₀ T hD hT K' hS hoff w θ hw hsp hθ k g0 ρ c₁ h ρ₁ x hM p hp
  have hK : ∀ g : G T₀.F Ω, residue c.O (D.al (resQ T₀.F g) : c.O) = 1 → resQ T₀.F g ∈ K'.fixingSubgroup := by
    intro g hg
    by_contra hn
    have := (UpperTheory.V.Ws.P1.coefRes c).2.1
    exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq (ResidueField c.O) l]; exact hD.l_odd)
      ((hoff g hn).symm.trans ((gd_rb T₀ g).trans hg))
  by_cases hpS : p ∈ D.S
  · exact Or.inl (hS p hpS)
  by_cases hpw : p = w
  · subst hpw
    refine Or.inl fun A hA g hg => ?_
    obtain ⟨⟨h1, h2⟩, -⟩ := hsp A hA hg
    obtain ⟨g', rfl⟩ := gd_up h1
    exact hK g' (gd_rbar D _ h2)
  refine Or.inr ⟨fun e => hpS (e ▸ hD.l_mem), fun A hA s hs => ?_⟩
  have hAS : Raw.Away D.S A := fun q hq =>
    gd_val A ((Nat.coprime_primes (hD.S_prime q hq) hp).2 fun e => hpS (e ▸ hq)) hA
  have hAw : Raw.Away {w} A := fun q hq => by
    rw [Finset.mem_singleton.1 hq]
    exact gd_val A ((Nat.coprime_primes hw hp).2 fun e => hpw e.symm) hA
  have hI : resQ T.L s ∈ Ine (F := ℚ) A := ⟨hs.1, hs.2⟩
  have hξ : D.ξ (resQ T.L s) = 1 := hD.xi_unr A hAS hI
  have hψ : D.ψ (resQ T.L s) = 1 := hD.psi_unr A hAS hI
  have hres : resQ T₀.F (resLe (hT.le.trans T.F_le) s) = resQ T.L s := AlgEquiv.ext fun _ => rfl
  refine ⟨?_, ?_⟩
  · rw [← hres]
    exact hK _ (by rw [hres]; exact gd_al D hD _ hξ)
  · have hφ : phi D T₀.pr (resQ T.L s) = 1 := by
      generalize resQ T.L s = g at hξ hψ
      unfold phi
      split_ifs <;> simp [hξ, hψ]
    have h1 := hM.away A (hAS l hD.l_mem) _ hI hφ (hθ A hAw hI)
    obtain ⟨u, hu⟩ := hM.iso
    have h2 := hu (resQ T.L s)
    have h3 : (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits (resQ T.L s) = 1 := by
      refine Units.ext ?_
      show (ρ₁ (resQ T.L s)).map (algebraMap c₁.O (PadicAlgCl l)) = 1
      rw [h1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [h3] at h2
    have h4 : ρ (resQ T.L s) = u⁻¹ * (u * ρ (resQ T.L s) * u⁻¹) * u := by group
    rw [h4, ← h2, mul_one, inv_mul_cancel]
