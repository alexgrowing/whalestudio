import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Chain.map_eq_one_iff {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (a : O →+* k)
    (ha : ∀ x ∈ maximalIdeal O, a x = 0) (x : O) : a x = 1 ↔ residue O x = 1 := by
  constructor
  · intro h
    rw [← sub_eq_zero, ← map_one (residue O), ← map_sub, residue_eq_zero_iff]
    by_contra hm
    have hu := (IsLocalRing.notMem_maximalIdeal.mp hm).map a
    rw [map_sub, h, map_one, sub_self] at hu
    exact not_isUnit_zero hu
  · intro h
    have hm : x - 1 ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, map_sub, h, map_one, sub_self]
    have := ha _ hm
    rwa [map_sub, map_one, sub_eq_zero] at this

private theorem UpperTheory.V.Ws.Chain.roots_wt : ∀ w ∈ roots, ∃ i j : Fin 4, i ≠ j ∧
    ((w = wt 0 j ∧ i = 0) ∨ (w = wt i 0 ∧ j = 0) ∨ (w = wt 1 2 ∧ i = 1 ∧ j = 2) ∨ (w = wt 2 1 ∧ i = 2 ∧ j = 1)) := by
  decide

private theorem UpperTheory.V.Ws.Chain.rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    rw [← h, mul_comm (Φ.χ 0 g), mul_inv_cancel_right]
  have e : ∀ k : Fin 4, Φ.χ k g = ![Φ.χ 0 g, Φ.χ 1 g, Φ.χ 2 g, Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹] k := by
    intro k
    fin_cases k <;> simp [hd]
  have key : ∀ k : Fin 4, Φ.χ k g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ *
      (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ lamW k * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ muW k := by
    intro k
    rw [e k]
    generalize Φ.χ 0 g = x at *
    generalize Φ.χ 1 g = y at *
    generalize Φ.χ 2 g = z at *
    fin_cases k <;> simp [lamW, muW] <;> group
  have hrt : Φ.rt (wt i j) g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW i - lamW j) *
      (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW i - muW j) := rfl
  rw [hrt, key i, key j]
  generalize Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ = d
  generalize Φ.χ 0 g * (Φ.χ 1 g)⁻¹ = u
  generalize Φ.χ 0 g * (Φ.χ 2 g)⁻¹ = v
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  rw [sub_smul, sub_smul]
  abel

theorem UpperTheory.V.Ws.Chain.rtFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Ok → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) →
      (∀ w ∈ roots, a ((frQ D T.pr (resQ T.F T.g0)).rt w (resQ T.F T.g0)) ≠ 1) ∧
      ∀ w g, a ((T.fr ∅).rt w g) = 1 ↔ T.rb w g = 1 := by
  intro Ω _ _ _ l _ c D hD T hT k _ a ha
  have rel : ∀ (pr : Bool) (s : G ℚ Ω), chi D pr 0 s * chi D pr 3 s = chi D pr 1 s * chi D pr 2 s := by
    intro pr s
    cases pr <;> simp [chi, lab, Raw.ps, Raw.th, Raw.al, Raw.Psi, UpperTheory.V.Chr.Psi] <;> ac_rfl
  refine ⟨?_, fun w g => UpperTheory.V.Ws.Chain.map_eq_one_iff a ha _⟩
  intro w hw h1
  have hw' : ∃ i j : Fin 4, i ≠ j ∧ w = wt i j := by
    obtain ⟨i, j, hij, h⟩ := UpperTheory.V.Ws.Chain.roots_wt w hw
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> exact ⟨_, _, hij, rfl⟩
  obtain ⟨i, j, hij, rfl⟩ := hw'
  have key : (frQ D T.pr (resQ T.F T.g0)).rt (wt i j) (resQ T.F T.g0) * chi D T.pr j (resQ T.F T.g0) =
      chi D T.pr i (resQ T.F T.g0) :=
    UpperTheory.V.Ws.Chain.rt_wt (frQ D T.pr (resQ T.F T.g0)) (resQ T.F T.g0) (rel T.pr _) i j
  have hr : residue c.O ↑((frQ D T.pr (resQ T.F T.g0)).rt (wt i j) (resQ T.F T.g0)) = 1 :=
    (UpperTheory.V.Ws.Chain.map_eq_one_iff a ha _).1 h1
  apply hT.dist i j hij
  show residue c.O ↑(chi D T.pr i (resQ T.F T.g0)) = residue c.O ↑(chi D T.pr j (resQ T.F T.g0))
  rw [← key, Units.val_mul, map_mul, hr, one_mul]
