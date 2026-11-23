import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem formIntegral {p : ℕ} [Fact p.Prime] {D : Datum p}
    (F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D)) (e : D.La → D.La → ℤ)
    (hF : ∀ x y, F (inAf D x) (inAf D y) = (e x y : AfP p))
    {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : IsIntAf (F v w) := by
  have ez : ∀ (a : AfP p) (x : D.La), a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = a • inAf D x := by
    intro a x
    rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have hgen : ∀ (a : AfP p) (x : D.La), IsIntAf a → ∀ w ∈ LaHat D, IsIntAf (F (a • inAf D x) w) := by
    intro a x ha w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      rw [ez, map_smul, map_smul, LinearMap.smul_apply, hF, smul_eq_mul, smul_eq_mul]
      exact isInt_mul ha' (isInt_mul ha (isInt_intCast _))
    | zero => rw [map_zero]; exact isIntAf_zero
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact isIntAf_add h₁ h₂
    | neg w _ h => rw [map_neg]; exact isIntAf_neg h
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [ez]
    exact hgen a x ha w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact isIntAf_zero
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact isIntAf_add h₁ h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

theorem UpperTheory.form_scalar_of_adelic_endo_preserving_lattice :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} (F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D)) (e : D.La → D.La → ℤ),
        (∀ x y, F (inAf D x) (inAf D y) = (e x y : AfP p)) →
        ∀ (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, A v ∈ LaHat D) → ∀ (gs : ℕ → D.La →+ D.La),
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (gs n x) + n • w) →
        ∀ (nu : ℕ → ℤ) (c : AfP p), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : AfP p, IsIntAf b ∧ c = (nu n : AfP p) + n • b) →
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ e (gs n x) (gs n y) - nu n * (2 * D.EF x y)) →
        ∀ v w, F (A v) (A w) = (2 * c) * formAf D v w := by
  intro p _ D F e hF A _ gs hA nu c hc hsim
  have key : ∀ x x', F (A (inAf D x)) (A (inAf D x')) = (2 * c) * formAf D (inAf D x) (inAf D x') := by
    intro x x'
    have := zero p (F (A (inAf D x)) (A (inAf D x')) - (2 * c) * formAf D (inAf D x) (inAf D x'))
      fun n hn hnp => by
      obtain ⟨w, hw, e₁⟩ := hA n hn hnp x
      obtain ⟨w', hw', e₂⟩ := hA n hn hnp x'
      obtain ⟨β, hβ, eβ⟩ := hc n hn hnp
      obtain ⟨k, hk⟩ := hsim n hn hnp x x'
      refine ⟨(k : AfP p) + F (inAf D (gs n x)) w' + F w (inAf D (gs n x')) +
        n • F w w' - (2 : ℤ) * β * (D.EF x x' : AfP p), ?_, ?_⟩
      · exact isInt_sub (isInt_add (isInt_add (isInt_add (isInt_intCast k)
          (formIntegral F e hF (inAf_mem D _) hw')) (formIntegral F e hF hw (inAf_mem D _)))
          (isInt_nsmul (formIntegral F e hF hw hw') n))
          (isInt_mul (isInt_mul (isInt_intCast 2) hβ) (isInt_intCast _))
      · have hk' := congrArg (Int.cast : ℤ → AfP p) hk
        push_cast at hk'
        rw [e₁, e₂, eβ]
        simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, form_inAf, hF, nsmul_eq_mul]
        push_cast
        linear_combination hk'
    exact sub_eq_zero.1 this
  have e2 := bilinear_ext_adelic_inclusion D (f := F.compl₁₂ A A) (g := (2 * c) • formAf D) fun x x' => by
    simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul]; exact key x x'
  intro v w
  have := LinearMap.congr_fun₂ e2 v w
  simpa using this
