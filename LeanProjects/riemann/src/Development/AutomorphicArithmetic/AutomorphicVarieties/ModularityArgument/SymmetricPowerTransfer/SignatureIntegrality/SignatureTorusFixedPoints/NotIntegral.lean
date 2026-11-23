import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.EUInvApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem index_comap {G G' : Type} [Group G] [Group G'] (e : G →* G') (he : Function.Surjective e)
    {A B : Subgroup G'} (h : A.relIndex B ≠ 0) : (A.comap e).relIndex (B.comap e) ≠ 0 := Subgroup.relIndex_comap_ne_zero e h

private theorem J_index {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (V : Lev k) (n : ℕ) : (V.J n).relIndex (KO k (Fin n)) ≠ 0 :=
  fun h0 => GlAx.Kc_index (k := k) (n := n) (V.c + 1) le_rfl (Subgroup.relIndex_eq_zero_of_le_left (kc_le V) h0)

private theorem not_integral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] [Algebra O k] (hO : IsInts k O) {a : kˣ} (ha : valuation k (a : k) < 1) :
    ¬ IsIntegral O ((a : k) + (a⁻¹ : kˣ)) := by
  intro hint
  have hv : Valuation.Integers (valuation k) O :=
    { hom_inj := hO.inj
      map_le_one := fun x => (hO.range _).1 ⟨x, rfl⟩
      exists_of_le_one := fun r hr => (hO.range r).2 hr }
  have h1 : valuation k ((a : k) + ((a⁻¹ : kˣ) : k)) ≤ 1 := hv.isIntegral_iff_v_le_one.mp hint
  have hprod : valuation k ((a⁻¹ : kˣ) : k) * valuation k (a : k) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hsub : ((a⁻¹ : kˣ) : k) = ((a : k) + ((a⁻¹ : kˣ) : k)) - a := by ring
  have h2 : valuation k ((a⁻¹ : kˣ) : k) ≤ 1 := by
    rw [hsub]
    exact (Valuation.map_sub _ _ _).trans (max_le h1 ha.le)
  exact (mul_lt_of_le_one_of_lt h2 ha).ne hprod

theorem UpperTheory.V.Z.Sym.Sig.okLev :
    UpperTheory.V.Z.Sym.Sig.OkLev := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry _ χ _
  obtain ⟨hU, -, hKU, -⟩ := eU_facts k O hO h2 Δ s hs hs0
  obtain ⟨hD, hKD, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  obtain ⟨f1, f2, f3, -, -, f6⟩ := finFacts k V
  have hpos : V.H.relIndex V.H2 ≠ 0 := fun h0 => f1 (by
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ f3 f2, h0, zero_mul])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hKU]; exact Subgroup.comap_mono (f6 3).2.2.2
  · rw [← hKU]; exact index_comap _ hU.2 (J_index V 3)
  · rw [← hKD]; exact Subgroup.comap_mono (f6 2).2.2.2
  · rw [← hKD]; exact index_comap _ hD.2 (J_index V 2)
  · change 0 < (V.H.relIndex (Uo k) : ℝ) * (V.H.relIndex V.H2 : ℝ)
    have a1 : 0 < V.H.relIndex (Uo k) := Nat.pos_of_ne_zero f1
    have a2 : 0 < V.H.relIndex V.H2 := Nat.pos_of_ne_zero hpos
    positivity
  · change 0 < (V.H.relIndex (Uo k) : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero f1
  · rintro t ht τ ⟨h, hh, rfl⟩
    have ht' : valuation k (t : k) < valuation k (unif k : k) ^ 2 := ht
    have hu : valuation k (unif k : k) < 1 := by rw [GlAx.unif_spec]; exact uniformizer_lt_one
    have ha : valuation k ((t * h : kˣ) : k) < 1 := by
      have e : valuation k (h : k) = 1 := V.H_le hh
      rw [Units.val_mul, map_mul, e, mul_one]
      exact ht'.trans (pow_lt_one₀ zero_le' hu two_ne_zero)
    refine ⟨⟨((t * h : kˣ) : k) - ((t * h)⁻¹ : kˣ), ?_⟩, not_integral hO ha⟩
    have e : ((t * h : kˣ) : k) * ((t * h)⁻¹ : kˣ) = 1 := Units.mul_inv _
    linear_combination (4 : k) * e

end
