import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

theorem UpperTheory.primeToP_isogeny_of_adelic_endo_preserving_lattice :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {D' : PLat D.O D.inv} (ψ : D'.La ≃+ D.La) (T : VQ D ≃ₗ[ℚ] VQ D) {j : D'.La →+ VQ D},
        (∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u) → (∀ (c : D.O) u, j (c • u) = actQ D c (j u)) →
        ∀ {f : ℕ → D.La →+ D'.La}, (∀ n : ℕ, 0 < n → n.Coprime p → ∀ (c : D.O) a, ∃ e, f n (c • a) = c • f n a + n • e) →
        ∀ (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, A v ∈ LaHat D) →
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (ψ (f n x)) + n • w) → ∀ b : D.O,
        (T.toLinearMap.baseChange (AfP p)) * A * (actQ D b).baseChange (AfP p) =
          (actQ D b).baseChange (AfP p) * ((T.toLinearMap.baseChange (AfP p)) * A) := by
  intro p _ D D' ψ T j hj hjc f hf A hAL hA b
  let Cq : VQ D →ₗ[ℚ] VQ D := T.symm.toLinearMap ∘ₗ actQ D b ∘ₗ T.toLinearMap
  let Cc : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := Cq.baseChange (AfP p)
  have hC1 : ∀ u, Cq ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = (1 : ℚ) ⊗ₜ[ℤ] ψ (b • u) := by
    intro u
    have h : T ((1 : ℚ) ⊗ₜ[ℤ] ψ (b • u)) = actQ D b (T ((1 : ℚ) ⊗ₜ[ℤ] ψ u)) := by
      rw [hj, hj, hjc]
    change T.symm (actQ D b (T ((1 : ℚ) ⊗ₜ[ℤ] ψ u))) = _
    rw [← h, T.symm_apply_apply]
  have hCt : ∀ (a : AfP p) (u : D'.La), Cc (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ u)) =
      a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ (b • u)) := by
    intro a u
    change Cq.baseChange (AfP p) _ = _
    rw [LinearMap.baseChange_tmul, hC1]
  have hCin : ∀ u, Cc (inAf D (ψ u)) = inAf D (ψ (b • u)) := fun u => hCt 1 u
  have hCL : ∀ v ∈ LaHat D, Cc v ∈ LaHat D := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      obtain ⟨u, rfl⟩ := ψ.surjective x
      rw [hCt]
      exact AddSubgroup.subset_closure ⟨a, ψ (b • u), ha, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have hAC : A * (actQ D b).baseChange (AfP p) = Cc * A := by
    refine ext_inAf D fun x => ?_
    have := modZero D ((A * (actQ D b).baseChange (AfP p)) (inAf D x) - (Cc * A) (inAf D x)) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := hA n hn hc (b • x)
      obtain ⟨w', hw', e'⟩ := hA n hn hc x
      obtain ⟨z, hz⟩ := hf n hn hc b x
      refine ⟨inAf D (ψ z) + w - Cc w', sub_mem (add_mem (inAf_mem D _) hw) (hCL _ hw'), ?_⟩
      rw [Module.End.mul_apply, Module.End.mul_apply, bc_inAf, e, hz, e', map_add, map_add, hCin, map_nsmul,
        map_nsmul, inAf_add, inAf_nsmul]
      simp only [smul_add, smul_sub]; abel
    exact sub_eq_zero.1 this
  have hTC : (T.toLinearMap.baseChange (AfP p)) * Cc =
      (actQ D b).baseChange (AfP p) * (T.toLinearMap.baseChange (AfP p)) := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      change T.toLinearMap.baseChange (AfP p) (Cq.baseChange (AfP p) (a ⊗ₜ[ℚ] m)) =
        (actQ D b).baseChange (AfP p) (T.toLinearMap.baseChange (AfP p) (a ⊗ₜ[ℚ] m))
      simp only [LinearMap.baseChange_tmul]
      congr 1
      change T (T.symm (actQ D b (T m))) = actQ D b (T m)
      exact T.apply_symm_apply _
  rw [_root_.mul_assoc, hAC, ← _root_.mul_assoc, hTC, _root_.mul_assoc]
