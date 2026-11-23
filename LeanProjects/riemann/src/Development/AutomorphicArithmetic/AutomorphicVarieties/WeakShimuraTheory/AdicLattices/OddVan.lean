import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.LocVanK
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

private theorem ov_red {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (red : O →+* k)
    (hred : ∀ a ∈ maximalIdeal O, red a = 0) {a b : O} (h : red a = red b) : residue O a = residue O b := by
  rw [← sub_eq_zero, ← map_sub] at h
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  by_contra hn
  exact ((IsLocalRing.notMem_maximalIdeal.1 hn).map red).ne_zero h

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)

private theorem ov_rt (pr : Bool) (g0 : G ℚ Ω) {w : ℤ × ℤ} (hw : w ∈ oddRoots) :
    (frQ D pr g0).rt w ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹] := by
  have e : ∀ w g, (frQ D pr g0).rt w g = D.al g ^ w.1 * (if pr then (D.Psi g)⁻¹ else D.Psi g) ^ w.2 := fun w g => by
    cases pr <;> simp [Fr.rt, frQ, chi, lab, Raw.ps, Raw.th, mul_assoc, mul_right_comm (D.al g) (D.Psi g)]
  have a1 : (frQ D pr g0).rt wAl = D.al := MonoidHom.ext fun g => by simp [e, wAl]
  have a2 : (frQ D pr g0).rt (-wAl) = D.al⁻¹ := MonoidHom.ext fun g => by simp [e, wAl]
  have a3 : (frQ D pr g0).rt wBe = if pr then D.th⁻¹ else D.be :=
    MonoidHom.ext fun g => by cases pr <;> simp [e, wBe, Raw.be, Raw.th, mul_comm]
  have a4 : (frQ D pr g0).rt (-wBe) = if pr then D.th else D.be⁻¹ :=
    MonoidHom.ext fun g => by cases pr <;> simp [e, wBe, Raw.be, Raw.th, mul_comm]
  have a5 : (frQ D pr g0).rt wTh = if pr then D.be⁻¹ else D.th :=
    MonoidHom.ext fun g => by cases pr <;> simp [e, wTh, Raw.be, Raw.th, mul_comm]
  have a6 : (frQ D pr g0).rt (-wTh) = if pr then D.be else D.th⁻¹ :=
    MonoidHom.ext fun g => by cases pr <;> simp [e, wTh, Raw.be, Raw.th, mul_comm]
  simp only [oddRoots, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [a1]
  · simp [a2]
  · rw [a3]; cases pr <;> simp
  · rw [a4]; cases pr <;> simp
  · rw [a5]; cases pr <;> simp
  · rw [a6]; cases pr <;> simp

private theorem ov_ij {γ : G ℚ Ω →* c.Oˣ} (hγ : γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹]) :
    ∃ i j, lamW i ≠ lamW j ∧ ∀ g, γ g * D.ps j g = D.ps i g := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 3, by decide, fun g => by simp [Raw.ps]⟩
  · exact ⟨1, 2, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
  · exact ⟨0, 3, by decide, fun g => by simp [Raw.ps]⟩
  · exact ⟨3, 2, by decide, fun g => by simp [Raw.ps]⟩
  · exact ⟨2, 1, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
  · exact ⟨3, 0, by decide, fun g => by simp [Raw.ps]⟩

private theorem ov_lab (pr : Bool) (i : Fin 4) : lab pr (lab pr i) = i := by
  revert pr i; decide

end

theorem UpperTheory.V.Ws.Lat.oddVan :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → UpperTheory.V.Loc.LocalPublishedTheorems → ∀ (k : Type) [Field k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) →
      ∀ (pr : Bool) (g0 : G ℚ Ω), (∀ i j, i ≠ j → Raw.bar (chi D pr i) g0 ≠ Raw.bar (chi D pr j) g0) → OddVan (frQ D pr g0) red := by
  intro Ω _ _ _ l _ c D hD hP k _ red hred pr g0 hd w hw z hz m hm
  have hγ := ov_rt D pr g0 hw
  obtain ⟨hlc, hco, hN, h0⟩ := hz
  have hw0 : w ≠ 0 := by rintro rfl; revert hw; decide
  unfold Fr.LocTriv at hm
  generalize (frQ D pr g0).rt w = γ at hγ hco hm
  obtain ⟨i, j, hij, hq⟩ := ov_ij D hγ
  have key : ∀ g, Raw.bar (D.ps i) g ≠ Raw.bar (D.ps j) g → ∀ x : k, red (γ g : c.O) * x - x = 0 → x = 0 := by
    intro g hg x hx
    by_contra hx0
    have h1 : red (γ g : c.O) = 1 := mul_right_cancel₀ hx0 (by rw [one_mul]; exact sub_eq_zero.1 hx)
    refine hg (ov_red red hred ?_)
    rw [← hq g, Units.val_mul, map_mul, h1, one_mul]
  obtain ⟨n, hn⟩ := xvanExt D hD k red hred γ hγ z hlc hco (fun A hA g hg h1 => hN g (.inl ⟨A, hA, hg, h1⟩)) fun v hv => by
    rcases Finset.mem_insert.1 hv with rfl | hv'
    · exact ⟨-m (), fun g hg => (hm () g hg).trans (by ring)⟩
    · obtain ⟨x, hx⟩ := locVanK D hD hP k red hred γ hγ v hv' (fun g => z g) (hlc.comp_continuous continuous_subtype_val)
        fun g h => hco g h
      exact ⟨x, fun g hg => hx ⟨g, hg⟩⟩
  have hg0 : Raw.bar (D.ps i) g0 ≠ Raw.bar (D.ps j) g0 := by
    have := hd (lab pr i) (lab pr j) fun e => hij (by rw [← ov_lab pr i, e, ov_lab])
    rwa [chi, chi, ov_lab, ov_lab] at this
  have hn0 : n = 0 := key g0 hg0 n ((hn g0).symm.trans (h0 hw0))
  have hz0 : z = 0 := funext fun g => by rw [hn, hn0, mul_zero, sub_zero]; rfl
  obtain ⟨hσ, -, hne⟩ := (facts D hD).2.1 l (Finset.mem_insert_self _ _)
  refine ⟨hz0, funext fun v => key _ (hne i j hij) _ ?_⟩
  have := hm v _ hσ
  rw [hz0] at this
  rw [← neg_sub, ← this]
  exact neg_zero
