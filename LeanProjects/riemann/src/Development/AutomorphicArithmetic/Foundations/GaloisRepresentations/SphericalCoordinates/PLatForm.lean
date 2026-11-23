import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem nsmul_canc {V : Type} [AddCommGroup V] [Module ℚ V] {a : ℕ} (ha : a ≠ 0) {x y : V}
    (h : a • x = a • y) : x = y := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h' : (a : ℚ) • x = (a : ℚ) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h
  exact (smul_right_injective V ha') h'

private theorem ext_lin {Λ V V' : Type} [AddCommGroup Λ] [AddCommGroup V] [AddCommGroup V'] [Module ℚ V]
    [Module ℚ V'] (j : Λ →+ V) (hj : Function.Injective j)
    (hs : ∀ v, ∃ (m : ℕ) (u : Λ), m ≠ 0 ∧ m • v = j u) (f : Λ →+ V') :
    ∃ A : V →ₗ[ℚ] V', ∀ u, A (j u) = f u := by
  choose m u hm hu using hs
  let g : V → V' := fun v => ((m v : ℚ))⁻¹ • f (u v)
  have hg : ∀ v, m v • g v = f (u v) := by
    intro v
    have h0 : (m v : ℚ) ≠ 0 := by exact_mod_cast hm v
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have key : ∀ (a : ℕ) (x : Λ) (v : V), a ≠ 0 → a • v = j x → a • g v = f x := by
    intro a x v ha hx
    have e : m v • x = a • u v := by
      apply hj
      rw [map_nsmul, map_nsmul, ← hx, ← hu v, smul_comm]
    apply nsmul_canc (hm v)
    rw [smul_comm, hg, ← map_nsmul, ← map_nsmul, e]
  have hadd : ∀ v₁ v₂, g (v₁ + v₂) = g v₁ + g v₂ := by
    intro v₁ v₂
    have h12 : m v₁ * m v₂ ≠ 0 := mul_ne_zero (hm _) (hm _)
    apply nsmul_canc h12
    rw [key (m v₁ * m v₂) (m v₂ • u v₁ + m v₁ • u v₂) (v₁ + v₂) h12 ?_]
    · rw [map_add, map_nsmul, map_nsmul, smul_add, ← hg v₁, ← hg v₂, smul_smul, smul_smul, mul_comm (m v₂),
        mul_comm (m v₁) (m v₂)]
    · rw [map_add, map_nsmul, map_nsmul, ← hu v₁, ← hu v₂, smul_add, smul_smul, smul_smul, mul_comm (m v₂)]
  refine ⟨(AddMonoidHom.mk' g hadd).toRatLinearMap, fun x => ?_⟩
  show g (j x) = f x
  have h1 : (1 : ℕ) • g (j x) = f x := key 1 x (j x) one_ne_zero (one_nsmul _)
  simpa using h1

theorem UpperTheory.Gal.W2.latForm_of :
    UpperTheory.Gal.W2.LatForm := by
  intro p _ D G L β β' D' D'' j j'' hP hP'' w m hm hw
  obtain ⟨hj, hjO, hjs, s₀, hs₀, hjF⟩ := hP
  obtain ⟨hj2, hjO2, hjs2, s₂, hs₂, hjF2⟩ := hP''
  obtain ⟨A, hA⟩ := ext_lin j'' hj2 hjs2 (j.comp w.toAddMonoidHom)
  replace hA : ∀ u, A (j'' u) = j (w u) := hA
  haveI := D.finLa
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun v hv => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    have h1 : j (w u) = 0 := by rw [← hA, ← hu, map_nsmul, hv, smul_zero]
    have h2 : w u = 0 := hj (by rw [h1, map_zero])
    have h3 : u = 0 := by
      refine D''.nondeg u fun u' => ?_
      have := hw u u'
      rw [h2] at this
      simp only [map_zero, LinearMap.zero_apply] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h hm.ne'
      · exact h
    apply nsmul_canc ha
    rw [hu, h3, map_zero, smul_zero]
  let Ae := LinearEquiv.ofInjectiveEndo A hAinj
  let B : Module.End ℚ (VQ D) := (Ae.symm : VQ D →ₗ[ℚ] VQ D)
  have hAB : A * B = 1 := LinearEquiv.ofInjectiveEndo_right_inv A hAinj
  have hBA : B * A = 1 := LinearEquiv.ofInjectiveEndo_left_inv A hAinj
  have hcomm : ∀ b, A * actQ D b = actQ D b * A := by
    intro b
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    apply nsmul_canc ha
    show a • A (actQ D b v) = a • actQ D b (A v)
    calc a • A (actQ D b v) = A (actQ D b (a • v)) := by rw [map_nsmul, map_nsmul]
      _ = A (j'' (b • u)) := by rw [hu, hjO2]
      _ = j (w (b • u)) := hA _
      _ = j (b • w u) := by rw [map_smul]
      _ = actQ D b (j (w u)) := hjO _ _
      _ = actQ D b (A (a • v)) := by rw [hu, hA]
      _ = a • actQ D b (A v) := by rw [map_nsmul, map_nsmul]
  have hBcomm : ∀ b, B * actQ D b = actQ D b * B := by
    intro b
    calc B * actQ D b = B * actQ D b * (A * B) := by rw [hAB, _root_.mul_one]
      _ = B * (actQ D b * A) * B := by simp only [_root_.mul_assoc]
      _ = B * (A * actQ D b) * B := by rw [hcomm]
      _ = (B * A) * actQ D b * B := by simp only [_root_.mul_assoc]
      _ = actQ D b * B := by rw [hBA, _root_.one_mul]
  obtain ⟨x, hx⟩ := (L.rep_range A).2 hcomm
  obtain ⟨x', hx'⟩ := (L.rep_range B).2 hBcomm
  have hxx' : x * x' = 1 := L.rep_inj (by rw [map_mul, hx, hx', hAB, map_one])
  have hx'x : x' * x = 1 := L.rep_inj (by rw [map_mul, hx, hx', hBA, map_one])
  let y : G.Cˣ := ⟨x, x', hxx', hx'x⟩
  have hform : ∀ v v', s₀ * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) (A v') =
      (m : ℚ) * s₂ * D.EF.baseChange ℚ (L.rep ((β'⁻¹ : G.Cˣ) : G.C) v) v' := by
    intro v v'
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    obtain ⟨b, u', hb, hu'⟩ := hjs2 v'
    have e1 := hjF (w u) (w u')
    have e2 := hjF2 u u'
    have e3 : ((D'.EF (w u) (w u') : ℤ) : ℚ) = (m : ℚ) * (D''.EF u u' : ℤ) := by
      rw [hw u u']; push_cast; ring
    unfold formB at e1 e2
    rw [← hA, ← hA, ← hu, ← hu', map_nsmul, map_nsmul, map_nsmul] at e1
    rw [← hu, ← hu', map_nsmul] at e2
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at e1 e2
    have hab : (a : ℚ) * b ≠ 0 := mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hb)
    apply mul_left_cancel₀ hab
    linear_combination -e1 + e3 + (m : ℚ) * e2
  have hnd : ∀ a : VQ D, (∀ v, D.EF.baseChange ℚ a v = 0) → a = 0 := by
    intro a ha
    obtain ⟨c, u, hc, hu⟩ := hjs (L.rep (β : G.C) a)
    have hinv : ∀ z : VQ D, L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (β : G.C) z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    have hu0 : u = 0 := by
      refine D'.nondeg u fun u' => ?_
      have e := hjF u u'
      unfold formB at e
      rw [← hu, map_nsmul, hinv] at e
      simp only [map_nsmul, LinearMap.smul_apply, ha, smul_zero, mul_zero] at e
      exact_mod_cast e
    have h0 : c • L.rep (β : G.C) a = c • (0 : VQ D) := by rw [hu, hu0, map_zero, smul_zero]
    have := nsmul_canc hc h0
    rw [← hinv a, this, map_zero]
  set r : ℚ := (m : ℚ) * s₂ / s₀ with hr
  have hr0 : 0 < r := by
    have : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hs₀' : s₀ ≠ 0 := hs₀.ne'
  have hshsh : sh G (sh G x) = x := G.star_star x
  have hkey : sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x = algebraMap ℚ G.C r * ((β'⁻¹ : G.Cˣ) : G.C) := by
    apply L.rep_inj
    refine LinearMap.ext fun v => ?_
    rw [← sub_eq_zero]
    refine hnd _ fun v' => ?_
    have e := hform v v'
    have e2 := L.adj (sh G x) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) v'
    rw [hshsh, hx] at e2
    simp only [map_mul, Module.End.mul_apply, hx, AlgHom.commutes, Module.algebraMap_end_apply,
      map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [e2, hr]
    field_simp
    linear_combination e
  refine ⟨y, Units.mk0 r hr0.ne', hr0, ?_, fun u => ?_⟩
  · show x * (β' : G.C) * sh G x = algebraMap ℚ G.C r * (β : G.C)
    have h1 : x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) = r • x := by
      calc x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x)
          = x * (β' : G.C) * (sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x) := by simp only [_root_.mul_assoc]
        _ = r • (x * ((β' : G.C) * ((β'⁻¹ : G.Cˣ) : G.C))) := by
            rw [hkey, ← Algebra.smul_def, mul_smul_comm, _root_.mul_assoc]
        _ = r • x := by rw [Units.mul_inv, _root_.mul_one]
    calc x * (β' : G.C) * sh G x
        = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * (x * x') * (β : G.C)) := by
          rw [hxx', _root_.mul_one, Units.inv_mul, _root_.mul_one]
      _ = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) * (x' * (β : G.C)) := by
          simp only [_root_.mul_assoc]
      _ = r • (x * x' * (β : G.C)) := by rw [h1, smul_mul_assoc, _root_.mul_assoc]
      _ = algebraMap ℚ G.C r * (β : G.C) := by rw [hxx', _root_.one_mul, Algebra.smul_def]
  · show j (w u) = L.rep x (j'' u)
    rw [hx, hA]
