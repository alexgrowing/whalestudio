import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitMain
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRatUnitFactorizationFiniteAdelesAwayP
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.DenCoprimeIffOfMulPrimeToPRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast
import Development.AbelianVarietyTheory.Definitions.Divisors.MemUQptsStarCIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem actOn_comm {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (y : AfP p ⊗[ℚ] G.C) (c : D.O) :
    actOn L.rep (AfP p) y * (actQ D c).baseChange (AfP p) = (actQ D c).baseChange (AfP p) * actOn L.rep (AfP p) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, add_mul, mul_add, hu, hv]
  | tmul a d =>
    have h : L.rep d * actQ D c = actQ D c * L.rep d := (L.rep_range _).1 ⟨d, rfl⟩ c
    have h2 := congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) h
    rw [map_mul, map_mul] at h2
    rw [GlobalTheory.LKGeo.MultScale.actOn_tmul, smul_mul_assoc, mul_smul_comm]
    exact congrArg (a • ·) h2

private theorem EFQ_adj {p : ℕ} [Fact p.Prime] (D : Datum p) (c : D.O) (u w : VQ D) :
    D.EF.baseChange ℚ (actQ D c u) w = D.EF.baseChange ℚ u (actQ D (D.inv c) w) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add, h, h']
    | tmul q' y =>
      rw [UpperTheory.Gal.W2.Wit.actQ_tmul, UpperTheory.Gal.W2.Wit.actQ_tmul]
      have e := D.EFQ_tmul q q' (c • x) y
      have e' := D.EFQ_tmul q q' x (D.inv c • y)
      rw [Datum.EFQ] at e e'
      rw [e, e', D.adj]; rfl

theorem UpperTheory.Gal.W2.witOfAd_of :
    UpperTheory.Gal.W2.RdForm → UpperTheory.Gal.W2.RdDense → UpperTheory.Gal.W2.RdAct → UpperTheory.Gal.W2.WitOfAd := by
  intro hForm hDense _ p _ D G L B N hN hNp h₁ M hM hs
  obtain ⟨s, hs0, hperf⟩ := hs
  obtain ⟨c, hc⟩ := hForm p D G L B h₁
  obtain ⟨s₁, ε, a, b, hs₁, hε, hε', hsc, ha, hb, hap, hbp, hab⟩ := UpperTheory.exists_rat_unit_factorization_finiteAdelesAwayP p c s hs0
  let x := trivX B
  let T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)
  let S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁
  have hST : S * T = 1 := by
    have e1 : actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have e2 : L.actG h₁ * L.actG h₁⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    change (actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁) *
      (L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)) = 1
    rw [_root_.mul_assoc, ← _root_.mul_assoc (L.actG h₁), e2, _root_.one_mul, e1]
  have hcomm : ∀ c' : D.O, T * (actQ D c').baseChange (AfP p) = (actQ D c').baseChange (AfP p) * T := by
    intro c'
    change (L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)) * _ =
      _ * (L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C))
    rw [_root_.mul_assoc, actOn_comm, ← _root_.mul_assoc, KNLevel.actG_eq, actOn_comm, _root_.mul_assoc]
  let Bq : LinearMap.BilinForm ℚ (VQ D) := (D.EF.baseChange ℚ).comp (L.rep ((B.β⁻¹ : G.Cˣ) : G.C)) LinearMap.id
  have hBq : ∀ u w, Bq u w = formB L B.β u w := fun u w => rfl
  have hsh : sh G ((B.β⁻¹ : G.Cˣ) : G.C) = ((B.β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G (B.β : G.C) * sh G ((B.β⁻¹ : G.Cˣ) : G.C) = 1 := by
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    rw [B.sym] at h1
    calc sh G ((B.β⁻¹ : G.Cˣ) : G.C)
        = ((B.β⁻¹ : G.Cˣ) : G.C) * ((B.β : G.C) * sh G ((B.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
      _ = _ := by rw [h1, _root_.mul_one]
  have halt : ∀ u, Bq u u = 0 := by
    intro u
    have h1 : Bq u u = D.EF.baseChange ℚ u (L.rep ((B.β⁻¹ : G.Cˣ) : G.C) u) := by
      have := L.adj ((B.β⁻¹ : G.Cˣ) : G.C) u u
      rw [hsh] at this
      exact this
    have h2 : D.EF.baseChange ℚ u (L.rep ((B.β⁻¹ : G.Cˣ) : G.C) u) = - Bq u u :=
      D.EFQ_swap (L.rep ((B.β⁻¹ : G.Cˣ) : G.C) u) u
    linarith
  have hnd : ∀ u, (∀ w, Bq u w = 0) → u = 0 := by
    intro u h
    have h1 : L.rep ((B.β⁻¹ : G.Cˣ) : G.C) u = 0 := D.eq_zero_of_EFQ h
    have h2 : L.rep (B.β : G.C) (L.rep ((B.β⁻¹ : G.Cˣ) : G.C) u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one]; rfl
    rw [← h2, h1, map_zero]
  have hadj : ∀ (c' : D.O) u w, Bq (actQ D c' u) w = Bq u (actQ D (D.inv c') w) := by
    intro c' u w
    have h : L.rep ((B.β⁻¹ : G.Cˣ) : G.C) * actQ D c' = actQ D c' * L.rep ((B.β⁻¹ : G.Cˣ) : G.C) :=
      (L.rep_range _).1 ⟨_, rfl⟩ c'
    have h2 := congrArg (fun f : Module.End ℚ (VQ D) => f u) h
    change D.EF.baseChange ℚ (L.rep ((B.β⁻¹ : G.Cˣ) : G.C) (actQ D c' u)) w = _
    change L.rep ((B.β⁻¹ : G.Cˣ) : G.C) (actQ D c' u) = actQ D c' (L.rep ((B.β⁻¹ : G.Cˣ) : G.C) u) at h2
    rw [h2, EFQ_adj]; rfl
  let X : UpperTheory.Gal.W2.Wit.Sys D :=
    { T := T, S := S, ST := hST, comm := hcomm, B := Bq, alt := halt, nondeg := hnd, adj := hadj, M := M, hM := hM,
      s := s₁, s_pos := hs₁
      perf := fun w => by
        rw [hperf w]
        exact forall₂_congr fun u _ => (UpperTheory.den_coprime_iff_of_mul_prime_to_p_ratio p s s₁ a b ha hb hap hbp hab _).symm
      ε := ε, ε_int := hε, ε_inv := hε'
      form := fun u w => by
        have h := hc u w
        change (D.EF.baseChange ℚ).baseChange (AfP p) (T ((1 : AfP p) ⊗ₜ u)) (T ((1 : AfP p) ⊗ₜ w)) = _ at h
        rw [h, map_mul, hsc, hBq]; ring
      dense := fun n hn z => hDense p D G L x h₁ n hn z }
  obtain ⟨D', t, j, hCls, hinj, hlin, hspan, hform, hco1, hco2, hloc⟩ := X.main N hN hNp
  exact ⟨D', t, j, hCls, ⟨hinj, hlin, hspan, 2 * s₁, by positivity, hform⟩, ⟨hco1, hco2⟩, hloc⟩
