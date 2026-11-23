import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixStableLineLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixFlagExists

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Matrix Pointwise

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem ex_lift (k₀ : IntermediateField ℚ Ω) {g : G ℚ Ω} (hg : g ∈ k₀.fixingSubgroup) :
    ∃ h : G k₀ Ω, resQ k₀ h = g :=
  ⟨{ g.toRingEquiv with commutes' := fun x => hg x }, rfl⟩

private theorem res_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup :=
  fun x => g.commutes x

private theorem val_comap (A : ValuationSubring Ω) (t : G ℚ Ω) (y : Ω) :
    (A.comap (t : Ω →+* Ω)).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, map_eq_zero_iff _ t.injective]
  rfl

private theorem dec_conj {A : ValuationSubring Ω} (t : G ℚ Ω) {s : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A) :
    t⁻¹ * s * t ∈ Dec (F := ℚ) (A.comap (t : Ω →+* Ω)) := by
  rw [← Subgroup.inv_mem_iff, mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
  show t (t⁻¹ (s (t x))) ∈ A ↔ t x ∈ A
  rw [mul_inv_apply, apply_mem_iff_of_mem_Dec hs]

private theorem ine_conj {A : ValuationSubring Ω} (t : G ℚ Ω) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    t⁻¹ * s * t ∈ Ine (F := ℚ) (A.comap (t : Ω →+* Ω)) := by
  refine ⟨dec_conj t hs.1, fun x hx => ?_⟩
  rw [val_comap, map_sub]
  show A.valuation (t (t⁻¹ (s (t x))) - t x) < 1
  rw [mul_inv_apply]
  refine hs.2 _ ?_
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  exact hx

private theorem norm_of_cong {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  have h' : ‖(a : Qbar l) - b‖ < ‖(b : Qbar l)‖ := hb ▸ h
  have e := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h'.ne
  rw [sub_add_cancel, max_eq_right h'.le] at e
  rw [e, hb]

private theorem pull (k₀ : IntermediateField ℚ Ω) [NumberField k₀] {S : Type} (r : G k₀ Ω →* GL (Fin 2) (Qbar l))
    {m : Fin 2 → ℤ} {ψ : Fin 2 → G k₀ Ω →* (Qbar l)ˣ} {B : ValuationSubring Ω} (hO : OrdAt r m ψ B) (h : S → G k₀ Ω)
    (hD : ∀ s, resQ k₀ (h s) ∈ Dec (F := ℚ) B) :
    ∃ κ : Fin 2 → S → (Qbar l)ˣ, S2.Flag (fun s => r (h s)) κ ∧
      (∀ i s, resQ k₀ (h s) ∈ Ine (F := ℚ) B → κ i s = cycBar ℚ Ω l (resQ k₀ (h s)) ^ m i) ∧ ∀ i s, Cong (κ i s) (ψ i (h s)) := by
  obtain ⟨κ, ⟨g, hg⟩, h2, h3⟩ := hO
  refine ⟨fun i s => κ i ⟨h s, hD s⟩, ⟨g, fun s => ⟨(hg ⟨h s, hD s⟩).1 1 0 (by decide), (hg ⟨h s, hD s⟩).2⟩⟩,
    fun i s hs => h2 i ⟨h s, hD s⟩ ⟨hD s, hs.2⟩, fun i s => h3 i ⟨h s, hD s⟩⟩

end

theorem UpperTheory.induced_flag_condition :
    UpperTheory.V.Sd.S2.IndFlag := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H
  refine ⟨![(k : ℤ) + t, k, 0, -(t : ℤ)], ?_, fun A hA => ?_⟩
  · have := H.dat.hk
    have := H.dat.ht
    intro i
    fin_cases i <;> simp <;> omega
  have hA' : (A.comap (resQ T.F T.g0 : Ω →+* Ω)).valuation (l : Ω) < 1 := by
    rw [val_comap, map_natCast]
    exact hA
  have hD : ∀ s : Dec (F := T.F) A, resQ T.F s ∈ Dec (F := ℚ) A := fun s => s.2
  choose h hh using fun s : Dec (F := T.F) A => ex_lift k₀ (H.hyp.spl A hA (hD s))
  choose h' hh' using fun s : Dec (F := T.F) A => ex_lift k₀ (H.hyp.spl _ hA' (dec_conj (resQ T.F T.g0) (hD s)))
  have hcomm : ∀ (χ : G ℚ Ω →* (Qbar l)ˣ) s, χ (resQ k₀ (h' s)) = χ (resQ T.F s) := fun χ s => by
    rw [hh', map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  have hne : ∃ s : Dec (F := T.F) A, ¬ Cong (up D.ξ (resQ T.F s)) 1 := by
    obtain ⟨g, hg, hg4⟩ := H.hyp.two.bigL A hA
    refine ⟨⟨g, hg⟩, fun hc => hg4 ?_⟩
    have := (H.chars.al g 1).2 (by rwa [pow_one])
    rw [pow_one] at this
    rw [this, one_pow]
  have hR : ∀ s, Rib (r (h s)) (up D.ξ (resQ T.F s)) := fun s => by
    have := H.rib (h s) (hh s ▸ res_mem T.F s)
    rwa [hh] at this
  have hR' : ∀ s, Rib (r (h' s)) (up D.ξ (resQ T.F s)) := fun s => by
    have := H.rib (h' s) (by
      rw [hh', ← map_inv, ← map_mul, ← map_mul]
      exact res_mem T.F _)
    rwa [hcomm] at this
  have hmix : ∀ s : Dec (F := T.F) A, (R (resQ T.F s) : M4 (Qbar l)) = mix (β / α) (r (h s)) (r (h' s)) := fun s => by
    rw [← hh s]
    exact H.mix.on _ _ (by rw [hh, hh'])
  have hγ : ‖((β / α : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    rw [Units.val_div_eq_div_val, norm_div, norm_of_cong H.α_cong (H.chars.unit _ _),
      norm_of_cong H.β_cong (H.chars.unit _ _), div_one]
  have hI : ∀ s : Dec (F := T.F) A, (s : G T.F Ω) ∈ Ine (F := T.F) A → resQ T.F s ∈ Ine (F := ℚ) A :=
    fun s hs => ⟨hD s, hs.2⟩
  have hdet : ∀ {M : GL (Fin 2) (Qbar l)} {a b : (Qbar l)ˣ}, Matrix.GeneralLinearGroup.det M = a * b →
      (M : Matrix (Fin 2) (Fin 2) (Qbar l)).det = a * b := fun e => congrArg Units.val e
  rcases H.dat.above A _ hA _ H.chars.out (fun y => (Iff.rfl : _ ↔ y ∈ A.comap (resQ T.F T.g0 : Ω →+* Ω))) with ⟨o, o'⟩ | ⟨o, o'⟩
  all_goals
    obtain ⟨κ, f, i1, c1⟩ := pull k₀ r o h fun s => hh s ▸ hD s
    obtain ⟨κ', f', i2, c2⟩ := pull k₀ r o' h' fun s => hh' s ▸ dec_conj _ (hD s)
    obtain ⟨d1, u1, w1⟩ := UpperTheory.mix_stable_line_local l _ _ _ κ hne hR f
    obtain ⟨d2, u2, w2⟩ := UpperTheory.mix_stable_line_local l _ _ _ κ' hne hR' f'
    have j1 := fun i s hs => i1 i s (hh s ▸ hI s hs)
    have j2 := fun i s hs => i2 i s (hh' s ▸ ine_conj _ (hI s hs))
    simp only [hh, hcomm] at j1 j2
    have c10 := c1 0
    have c11 := c1 1
    have c20 := c2 0
    have c21 := c2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.comp_apply, MonoidHom.one_apply, hh, hcomm] at c10 c11 c20 c21
  · obtain ⟨u, hu, eu⟩ := u1 c10
    obtain ⟨w, hw, ew⟩ := w2 c20
    obtain ⟨n, hn, hf⟩ := (UpperTheory.mix_flag_exists l H.hyp.good.l_odd _ u w hγ hu hw).1
    refine ⟨n, hn, fun s hs => ?_⟩
    obtain ⟨g1, g2⟩ := hf _ _ _ _ _ _ (Units.ne_zero _) (Units.ne_zero _) (eu ⟨s, hs⟩) (ew ⟨s, hs⟩) (hdet (d1 _)) (hdet (d2 _))
    rw [← hmix] at g1 g2
    refine ⟨g1, fun i => ?_⟩
    rw [g2]
    fin_cases i
    · exact ⟨c10 _, fun hs' => congrArg Units.val (j1 0 _ hs')⟩
    · exact ⟨c20 _, fun hs' => congrArg Units.val (j2 0 _ hs')⟩
    · exact ⟨c21 _, fun hs' => congrArg Units.val (j2 1 _ hs')⟩
    · exact ⟨c11 _, fun hs' => congrArg Units.val (j1 1 _ hs')⟩
  · obtain ⟨u, hu, eu⟩ := u2 c20
    obtain ⟨w, hw, ew⟩ := w1 c10
    obtain ⟨n, hn, hf⟩ := (UpperTheory.mix_flag_exists l H.hyp.good.l_odd _ u w hγ hu hw).2
    refine ⟨n, hn, fun s hs => ?_⟩
    obtain ⟨g1, g2⟩ := hf _ _ _ _ _ _ (Units.ne_zero _) (Units.ne_zero _) (ew ⟨s, hs⟩) (eu ⟨s, hs⟩) (hdet (d1 _)) (hdet (d2 _))
    rw [← hmix] at g1 g2
    refine ⟨g1, fun i => ?_⟩
    rw [g2]
    fin_cases i
    · exact ⟨c20 _, fun hs' => congrArg Units.val (j2 0 _ hs')⟩
    · exact ⟨c10 _, fun hs' => congrArg Units.val (j1 0 _ hs')⟩
    · exact ⟨c11 _, fun hs' => congrArg Units.val (j1 1 _ hs')⟩
    · exact ⟨c21 _, fun hs' => congrArg Units.val (j2 1 _ hs')⟩
