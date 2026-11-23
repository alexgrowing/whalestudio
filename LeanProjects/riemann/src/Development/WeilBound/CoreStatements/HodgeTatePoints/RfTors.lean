import Development.WeilBound.CoreStatements.HodgeTatePoints.LiftComul
import Development.WeilBound.CoreStatements.HodgeTatePoints.RfHopf
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)}

theorem pt_zero (hpt : IsTorsPts G p pt) : pt 0 = 1 := by
  have h := hpt.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_nsmul (hpt : IsTorsPts G p pt) (n : ℕ) (x : N) : pt (n • x) = pt x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, pt_zero hpt]
  | succ n ih => rw [succ_nsmul, hpt.add, ih, pow_succ]

theorem exists_pts (T : TorsRep G p) (hpt : IsTorsPts G p pt) :
    ∃ φ : N → (T.A →ₐ[R] R), ∀ x, spMap (φ x) ≫ T.y = pt x := by
  choose φ hφ using fun x => (T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)).exists
  exact ⟨φ, hφ⟩

omit [AddCommGroup N] in
theorem mem_torsFun {C : Type} [Field C] [Algebra R C] (T : TorsRep G p)
    {φ : N → (T.A →ₐ[R] R)} (hφ : ∀ x, spMap (φ x) ≫ T.y = pt x) (g : N → C) :
    g ∈ torsFun C T pt ↔ ∃ a : T.A, g = fun x => algebraMap R C (φ x a) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun x => ha x _ (hφ x)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun x ψ h => ?_⟩
    rw [tors_ext T (h.trans (hφ x).symm)]

omit [AddCommGroup N] in
theorem mem_vanIdeal (T : TorsRep G p) {φ : N → (T.A →ₐ[R] R)}
    (hφ : ∀ x, spMap (φ x) ≫ T.y = pt x) (K : Set N) (a : T.A) :
    a ∈ vanIdeal T pt K ↔ ∀ k ∈ K, φ k a = 0 := by
  constructor
  · exact fun h k hk => h k hk _ (hφ k)
  · intro h k hk ψ e
    rw [tors_ext T (e.trans (hφ k).symm)]
    exact h k hk

end

theorem tors_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  intro p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt
  obtain ⟨Δ, ε, s, hΔ, -, -, h1, h2, h3, h4, h5⟩ := tors_alg R p G T
  obtain ⟨φ, hφ⟩ := exists_pts T hpt
  have hsurj : ∀ ψ : T.A →ₐ[R] R, ∃ x, spMap ψ ≫ T.y = pt x := fun ψ =>
    ((hpt.range _).1 (tors_pow T ψ)).imp fun _ h => h.symm
  have hbij : Function.Bijective φ :=
    ⟨fun x y h => hpt.inj (by rw [← hφ, ← hφ, h]),
      fun ψ => (hsurj ψ).imp fun x h => tors_ext T ((hφ x).trans h.symm)⟩
  let : Bialgebra R T.A := Bialgebra.ofAlgHom Δ ε h1 h2 h3
  let : HopfAlgebra R T.A := HopfAlgebra.ofAlgHom s h4 (by
    change AlgHom.comp _ Δ = AlgHom.comp _ ε
    rw [← h4]
    conv_lhs => rw [← h5, ← AlgHom.comp_assoc]
    congr 1
    ext <;> simp)
  have : Coalgebra.IsCocomm R T.A := ⟨congr(($h5).toLinearMap)⟩
  have := T.fin
  have := T.free
  obtain ⟨hsep, -, AA, hAA⟩ := hopfalg p C v R hv hp T.A N φ hbij (fun x y a => by
    have : φ (x + y) = (Algebra.TensorProduct.lift (φ x) (φ y) (fun _ _ => Commute.all _ _)).comp Δ := by
      apply tors_ext T
      rw [lift_comul T Δ hΔ, Algebra.TensorProduct.lift_comp_includeLeft,
        show (Algebra.TensorProduct.lift (φ x) (φ y) (fun _ _ => Commute.all _ _)).comp
          Algebra.TensorProduct.includeRight = φ y by ext; simp, hφ, hφ, hφ, hpt.add]
    rw [this]
    rfl)
  refine ⟨⟨AA, ?_⟩, fun a ha => hsep a fun x => ha _, fun x => ?_, hsurj, fun x => hpt.inj ?_⟩
  · ext g
    rw [hAA, mem_torsFun T hφ]
  · exact T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)
  · rw [pt_nsmul hpt, pt_zero hpt]
    exact (hpt.range _).2 ⟨x, rfl⟩

end PositivityTheory.HtPt.Rf
