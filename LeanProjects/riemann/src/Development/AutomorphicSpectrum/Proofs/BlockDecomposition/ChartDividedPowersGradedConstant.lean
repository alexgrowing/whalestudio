import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFil

section Rings

variable {R B : Type} [CommRing R] [CommRing B] {I : Ideal R} {J : Ideal B}

theorem dividedPowerFiltration_anti (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') : pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

theorem one_mem_pdP_zero (δ : DividedPowers J) : (1 : B) ∈ pdP δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem mul_mem_map (γ : DividedPowers I) (i : R →+* B) (r r' : ℕ) {x y : B}
    (hx : x ∈ (pdP γ r).map i) (hy : y ∈ (pdP γ r').map i) : x * y ∈ (pdP γ (r + r')).map i := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul] at h
  exact Ideal.map_mono (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le γ r r') h

theorem dpow_mem_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ (pdP γ n).map i := by
  have h0 : ∀ y ∈ J, δ.dpow 0 y ∈ (pdP γ 0).map i := fun y hy => by
    rw [δ.dpow_zero hy, ← map_one i]
    exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
  rw [hJ] at hx
  revert n
  refine Submodule.span_induction (p := fun x _ => ∀ n, δ.dpow n x ∈ (pdP γ n).map i) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩ n
    rw [hi.2 a ha]
    exact Ideal.mem_map_of_mem i (GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ n ha)
  · intro n
    by_cases hn : n = 0
    · subst hn
      exact h0 0 J.zero_mem
    · rw [δ.dpow_eval_zero hn]
      exact Ideal.zero_mem _
  · intro y z hy hz ihy ihz n
    have hy' : y ∈ J := hJ ▸ hy
    have hz' : z ∈ J := hJ ▸ hz
    rw [δ.dpow_add hy' hz']
    refine Ideal.sum_mem _ fun ab hab => ?_
    have e : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    rw [← e]
    exact mul_mem_map γ i _ _ (ihy _) (ihz _)
  · intro a y hy ihy n
    have hy' : y ∈ J := hJ ▸ hy
    rw [smul_eq_mul, δ.dpow_mul hy']
    exact Ideal.mul_mem_left _ _ (ihy n)

theorem dividedPowerFiltration_eq_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) (r : ℕ) : pdP δ r = (pdP γ r).map i := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map hi r hx)
  rintro _ ⟨l, hl, hr, rfl⟩
  have key : ∀ l : List (ℕ × B), (∀ q ∈ l, q.2 ∈ J) →
      (l.map fun q => δ.dpow q.1 q.2).prod ∈ (pdP γ (l.map Prod.fst).sum).map i := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [← map_one i]
      exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
    | cons a t ih =>
      intro h
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact mul_mem_map γ i _ _ (dpow_mem_map γ δ i hi hJ (h a (by simp)) _)
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
  exact Ideal.map_mono (dividedPowerFiltration_anti γ hr) (key l hl)

end Rings

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

theorem sub_mem_J (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (z : c.D.B) : f.φ z - g.φ z ∈ T.J := by
  obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
  have e := (hu _ f.pt).trans (hu _ g.pt).symm
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun e (Ideal.Quotient.mk _ z))

theorem sub_mem_pdP (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (n : ℕ) {x : c.D.B} (hx : x ∈ (pdP γ n).map c.D.i) : f.φ x - g.φ x ∈ pdP T.δ (n + 1) := by
  refine Submodule.span_induction (p := fun x _ => f.φ x - g.φ x ∈ pdP T.δ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, -, rfl⟩
    have e : f.φ (c.D.i a) - g.φ (c.D.i a) = 0 := by rw [f.comm, g.comm, sub_self]
    rw [e]
    exact Ideal.zero_mem _
  · rw [map_zero, map_zero, sub_zero]
    exact Ideal.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hy hz
  · intro a y hy ih
    have e : f.φ (a • y) - g.φ (a • y) = f.φ a * (f.φ y - g.φ y) + (f.φ a - g.φ a) * g.φ y := by
      rw [smul_eq_mul, map_mul, map_mul]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h1 : f.φ a - g.φ a ∈ pdP T.δ 1 := T.J_le_pdPow_one (sub_mem_J c hT f g a)
    have hm : (pdP γ n).map c.D.i ≤ pdP c.D.δ n :=
      Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map c.D.compat n hx
    have hy' : y ∈ pdP c.D.δ n := hm hy
    have h2 : g.φ y ∈ pdP T.δ n := dividedPowerFiltration_map g.dp n hy'
    have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ 1 n (Ideal.mul_mem_mul h1 h2)
    rwa [add_comm 1 n] at h3

theorem chart_grConst : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  intro O R _ _ I γ p X q κ V d c h Q hQ hD
  have h1 : ∀ r, c.D.pdPow r = (pdP γ r).map c.D.i := fun r =>
    dividedPowerFiltration_eq_map γ c.D.δ c.D.i c.D.compat c.J_eq r
  refine ⟨h1, ?_⟩
  intro n T σ σ' x hx
  have hx' : (show c.D.B from x) ∈ c.D.pdPow ((n : ℤ).toNat) := hx
  rw [Int.toNat_natCast, h1] at hx'
  change _ ∈ T.obj.pdPow (((n : ℤ) + 1).toNat)
  have e : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [e]
  exact sub_mem_pdP c (hQ _ T.property) σ.hom σ'.hom n hx'

end GlobalTheory.CompanionTheory.ChartFil
