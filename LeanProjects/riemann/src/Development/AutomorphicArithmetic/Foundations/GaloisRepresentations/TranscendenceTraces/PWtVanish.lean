import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtVanish_of :
    Isolate → WtPt → PtEx → PtLift → FibFin → WtVanish := by
  intro hIso hPt hEx hLift hFin Z S p _ w hw D hD hzero
  funext Ω _ _ z
  show w Ω z = 0
  obtain ⟨A, W, v, hEt, hW, hvW, hvz, huniq⟩ := hIso p (pt z)
  haveI : IsFinite A.r := A.finite
  classical
  let φ : A.V → ℤ := fun y => if y ∈ W then 1 else 0
  have hφ : IsLocallyConstant φ := by
    refine IsLocallyConstant.iff_isOpen_fiber.2 ?_
    intro n
    by_cases h1 : n = 1
    · subst h1
      convert hW.isOpen using 1
      ext y
      by_cases hy : y ∈ W <;> simp [φ, hy]
    · by_cases h0 : n = 0
      · subst h0
        convert hW.compl.isOpen using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy]
      · convert isOpen_empty using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy] <;> omega
  obtain ⟨ψ, hψ, hψeq⟩ := hw A φ hφ
  have hsum : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      ψ (A.r v) = w Ω z * ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    rw [← hx1, hψeq Ω1 x1, mul_finsum_mem]
    apply finsum_mem_congr rfl
    intro z' hz'
    have hz'' : z' ≫ A.r = x1 := hz'
    by_cases hW' : pt z' ∈ W
    · have hr : A.r (pt z') = A.r v := by
        rw [← pt_comp, hz'']
        exact hx1
      have hv : pt z' = v := huniq _ hW' hr
      have hwz : w Ω1 (z' ≫ A.v) = w Ω z :=
        hPt p w hw Ω1 Ω (z' ≫ A.v) z (by rw [pt_comp, hv, hvz])
      simp [φ, hW', hwz]
    · simp [φ, hW']
  have hpos : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      0 < ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    obtain ⟨z1, hz1, hpz1⟩ := hLift A.r Ω1 x1 v hx1.symm
    have hf := hFin A.r Ω1 x1
    rw [finsum_mem_eq_finite_toFinset_sum _ hf]
    have hmem : z1 ∈ hf.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hz1
    calc (0:ℤ) < φ (pt z1) := by simp [φ, hpz1, hvW]
      _ ≤ _ := Finset.single_le_sum (f := fun z' => φ (pt z'))
          (fun i _ => by by_cases hi : pt i ∈ W <;> simp [φ, hi]) hmem
  obtain ⟨Ω0, _, _, x0, hx0⟩ := hEx A.U (A.r v)
  have hO : IsOpen (ψ ⁻¹' {ψ (A.r v)}) := hψ.isOpen_fiber _
  have hopen := A.u.isOpenMap _ hO
  obtain ⟨y, ⟨u1, hu1, rfl⟩, hyD⟩ :=
    hD.inter_open_nonempty _ hopen ⟨A.u (A.r v), A.r v, rfl, rfl⟩
  obtain ⟨Ω2, _, _, x2, hx2⟩ := hEx A.U u1
  have hψ1 : ψ u1 = 0 := by
    rw [← hx2, hψeq Ω2 x2]
    apply finsum_mem_of_eqOn_zero
    intro z' hz'
    have hz'' : z' ≫ A.r = x2 := hz'
    have hw0 : w Ω2 (z' ≫ A.v) = 0 := by
      apply hzero Ω2
      have hc : (z' ≫ A.v) ≫ p = x2 ≫ A.u := by
        rw [Category.assoc, A.pb.w, ← Category.assoc, hz'']
      rw [hc, pt_comp, hx2]
      exact hyD
    simp [hw0]
  have hu1' : ψ u1 = ψ (A.r v) := hu1
  have h1 := hsum Ω0 x0 hx0
  have h2 := hpos Ω0 x0 hx0
  rw [← hu1', hψ1] at h1
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h h2.ne'
