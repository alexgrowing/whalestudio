import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PrimeToPIsogenyOfAdelicEndoPreservingLattice
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.FormScalarOfAdelicEndoPreservingLattice
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsUnitTrivOfSimilitudeFactor
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.OneTmulMemCompletedLatticeIff
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRationalEquivOfIsPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

open GlobalTheory.AdelicSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private theorem sys_lim {D' : PLat D.O D.inv} (ψ : D'.La ≃+ D.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ} (hw : IsWit D' f nu) :
    ∃ A A' : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), A * A' = 1 ∧ A' * A = 1 ∧ (∀ v ∈ LaHat D, A v ∈ LaHat D) ∧
      (∀ v ∈ LaHat D, A' v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (ψ (f n x)) + n • w := by
  set g : ℕ → D.La →+ D.La := fun n => (ψ : D'.La →+ D.La).comp (f n) with hg
  have hgv : ∀ n x, g n x = ψ (f n x) := fun _ _ => rfl
  have htw : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z := by
    intro n m hn hm hc x
    obtain ⟨e, he⟩ := (hw.1 n m hn hm hc).2 x
    exact ⟨ψ e, by rw [hgv, hgv, he, map_add, map_nsmul]⟩
  have hsurj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z := by
    intro n hn hc x
    obtain ⟨-, -, -, h4, -⟩ := hw.2 n hn hc
    obtain ⟨a, e, he⟩ := h4 (ψ.symm x)
    refine ⟨a, -ψ e, ?_⟩
    have : x = ψ (f n a) + n • ψ e := by
      rw [← map_nsmul, ← map_add, ← he, AddEquiv.apply_symm_apply]
    rw [hgv, this, smul_neg]; abel
  have hinj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w := by
    intro n hn hc x z h
    obtain ⟨-, -, h3, -, -⟩ := hw.2 n hn hc
    refine (h3 x).1 ⟨ψ.symm z, ?_⟩
    apply ψ.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply, ← hgv, h]
  obtain ⟨g', htw', hgg', hg'g⟩ := invSys D g htw hsurj hinj
  obtain ⟨h₀, h₀L, h₀c⟩ := modLim D g htw
  obtain ⟨h₁, h₁L, h₁c⟩ := modLim D g' htw'
  have inv_of : ∀ (f₀ f₁ : ℕ → D.La →+ D.La) (k₀ k₁ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)),
      (∀ v ∈ LaHat D, k₀ v ∈ LaHat D) →
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, k₀ (inAf D x) = inAf D (f₀ n x) + n • w) →
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, k₁ (inAf D x) = inAf D (f₁ n x) + n • w) →
      (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, f₀ n (f₁ n x) = x + n • z) → k₀ * k₁ = 1 := by
    intro f₀ f₁ k₀ k₁ hk₀L hk₀ hk₁ hf
    refine ext_inAf D fun x => ?_
    have := modZero D ((k₀ * k₁) (inAf D x) - inAf D x) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := hk₁ n hn hc x
      obtain ⟨w', hw', e'⟩ := hk₀ n hn hc (f₁ n x)
      obtain ⟨z, hz⟩ := hf n hn hc x
      refine ⟨inAf D z + w' + k₀ w, add_mem (add_mem (inAf_mem D z) hw') (hk₀L w hw), ?_⟩
      rw [Module.End.mul_apply, e, map_add, e', hz, inAf_add, inAf_nsmul, map_nsmul]
      simp only [smul_add]; abel
    rw [Module.End.one_apply]; exact sub_eq_zero.1 this
  exact ⟨h₀, h₁, inv_of g g' h₀ h₁ h₀L h₀c h₁c hgg', inv_of g' g h₁ h₀ h₁L h₁c h₀c hg'g, h₀L, h₁L, h₀c⟩

private theorem exists_unit_lim {nu : ℕ → ℤ}
    (ht : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ nu (n * m) - nu n)
    (hc : ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (nu n) (n : ℤ)) :
    ∃ c : (AfP p)ˣ, ∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : AfP p, IsIntAf b ∧ (c : AfP p) = (nu n : AfP p) + n • b := by
  obtain ⟨c, hcI, hcl⟩ := lim p nu ht
  obtain ⟨c', hcc'⟩ := unit p c (fun n => (nu n % n).toNat) fun n hn hnp => by
    obtain ⟨β, hβ, e⟩ := hcl n hn hnp
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnn : 0 ≤ nu n % n := Int.emod_nonneg _ hn'
    have hcast : (((nu n % n).toNat : ℕ) : ℤ) = nu n % n := Int.toNat_of_nonneg hnn
    have h3 := congrArg (Int.cast : ℤ → AfP p) hcast
    rw [Int.cast_natCast] at h3
    have hdiv : nu n = (nu n % n) + n * (nu n / n) := (Int.emod_add_mul_ediv _ _).symm
    refine ⟨?_, (β + ((nu n / n : ℤ) : AfP p)), isInt_add hβ (isInt_intCast _), ?_⟩
    · have hcop := hc n hn hnp
      have h2 : IsCoprime (nu n % n) (n : ℤ) := by
        rw [Int.emod_def]
        simpa [sub_eq_add_neg, mul_comm] using (IsCoprime.add_mul_left_left hcop (-(nu n / n)))
      rw [← hcast] at h2
      exact Nat.isCoprime_iff_coprime.1 h2
    · have e2 : (nu n : AfP p) = (((nu n % n).toNat : ℕ) : AfP p) + (n : AfP p) * ((nu n / n : ℤ) : AfP p) := by
        have h4 := congrArg (Int.cast : ℤ → AfP p) hdiv
        rw [Int.cast_add, Int.cast_mul, ← h3, Int.cast_natCast] at h4
        exact h4
      rw [e, e2, nsmul_eq_mul, nsmul_eq_mul, mul_add]; ring
  exact ⟨⟨c, c', hcc', by rw [mul_comm]; exact hcc'⟩, hcl⟩

private theorem bc_inv (T : VQ D ≃ₗ[ℚ] VQ D) :
    T.toLinearMap.baseChange (AfP p) * T.symm.toLinearMap.baseChange (AfP p) = 1 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]

private theorem actOn_inC (L : Link D G) (c : G.C) (u : VQ D) :
    actOn L.rep (AfP p) (inC G (AfP p) c) ((1 : AfP p) ⊗ₜ[ℚ] u) = (1 : AfP p) ⊗ₜ[ℚ] L.rep c u := by
  have h : inC G (AfP p) c = (1 : AfP p) ⊗ₜ[ℚ] c := rfl
  have h2 : ∀ a : AfP p, actOn L.rep (AfP p) (a ⊗ₜ[ℚ] c) = a • (L.rep c).baseChange (AfP p) := by
    intro a
    simp [actOn, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
    rfl
  rw [h, h2]
  simp

private theorem form_one (u w : VQ D) :
    formAf D ((1 : AfP p) ⊗ₜ[ℚ] u) ((1 : AfP p) ⊗ₜ[ℚ] w) = algebraMap ℚ (AfP p) (D.EF.baseChange ℚ u w) := by
  simp [formAf, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

private theorem cong_iff {A A' : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)} (h : A * A' = 1)
    (hAL : ∀ v ∈ LaHat D, A v ∈ LaHat D) (hA'L : ∀ v ∈ LaHat D, A' v ∈ LaHat D) (z : AfP p ⊗[ℚ] VQ D) :
    A' z ∈ LaHat D ↔ z ∈ LaHat D := by
  refine ⟨fun hz => ?_, hA'L z⟩
  have := hAL _ hz
  rwa [← Module.End.mul_apply, h, Module.End.one_apply] at this

theorem adCore_of : AdCore := by
  intro p _ D G L β D' j hj f nu hw
  obtain ⟨ψ, T, hT⟩ := UpperTheory.exists_rational_equiv_of_isPlace L hj
  obtain ⟨A, A', hAA', hA'A, hAL, hA'L, hAc⟩ := sys_lim ψ hw
  obtain ⟨c, hc⟩ := exists_unit_lim (fun n m a b d => (hw.1 n m a b d).1) (fun n a b => (hw.2 n a b).1)
  obtain ⟨-, hjO, -, s, hs, hsF⟩ := hj
  set Tb := T.toLinearMap.baseChange (AfP p) with hTb
  set Tb' := T.symm.toLinearMap.baseChange (AfP p) with hTb'
  have hTv : ∀ z, Tb ((1 : AfP p) ⊗ₜ[ℚ] z) = (1 : AfP p) ⊗ₜ[ℚ] T z := fun z => by simp [hTb]
  have hTv' : ∀ z, Tb' ((1 : AfP p) ⊗ₜ[ℚ] z) = (1 : AfP p) ⊗ₜ[ℚ] T.symm z := fun z => by simp [hTb']
  have hTT' : Tb * Tb' = 1 := bc_inv T
  have hT'T : Tb' * Tb = 1 := by simpa using bc_inv T.symm
  have gg' : (Tb * A) * (A' * Tb') = 1 := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc A, hAA', _root_.one_mul, hTT']
  have g'g : (A' * Tb') * (Tb * A) = 1 := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc Tb', hT'T, _root_.one_mul, hA'A]
  have c0 : ∀ b : D.O, (Tb * A) * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * (Tb * A) :=
    UpperTheory.primeToP_isogeny_of_adelic_endo_preserving_lattice ψ T hT hjO (fun n a b => (hw.2 n a b).2.1) A hAL hAc
  have c1 : ∀ b : D.O, (A' * Tb') * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * (A' * Tb') := by
    intro b
    calc (A' * Tb') * (actQ D b).baseChange (AfP p)
        = (A' * Tb') * ((actQ D b).baseChange (AfP p) * ((Tb * A) * (A' * Tb'))) := by rw [gg', _root_.mul_one]
      _ = (A' * Tb') * ((Tb * A) * (actQ D b).baseChange (AfP p)) * (A' * Tb') := by
          rw [c0 b]; simp only [_root_.mul_assoc]
      _ = _ := by rw [← _root_.mul_assoc (A' * Tb'), g'g, _root_.one_mul]
  obtain ⟨y, hy⟩ := comm L (Tb * A) c0
  obtain ⟨y', hy'⟩ := comm L (A' * Tb') c1
  have yy' : y * y' = 1 := inj L (by rw [map_mul, hy, hy', gg', map_one])
  have y'y : y' * y = 1 := inj L (by rw [map_mul, hy, hy', g'g, map_one])
  have hform : ∀ v w, algebraMap ℚ (AfP p) s * formAf D (actOn L.rep (AfP p) (inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C))
      (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w) = (2 * (c : AfP p)) * formAf D v w := by
    set B := actOn L.rep (AfP p) (inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C)) with hB
    set F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
      algebraMap ℚ (AfP p) s • (formAf D).compl₁₂ (B * Tb) Tb with hFdef
    have hFv : ∀ v w, F v w = algebraMap ℚ (AfP p) s * formAf D (B (Tb v)) (Tb w) := fun v w => by
      simp only [hFdef, LinearMap.smul_apply, LinearMap.compl₁₂_apply, Module.End.mul_apply, Algebra.smul_def]
      rfl
    have key := UpperTheory.form_scalar_of_adelic_endo_preserving_lattice F (fun x x' => D'.EF (ψ.symm x) (ψ.symm x')) (fun x x' => by
        have h1 : ∀ x, Tb (inAf D x) = (1 : AfP p) ⊗ₜ[ℚ] j (ψ.symm x) := fun x => by
          rw [inAf, hTv, ← hT, ψ.apply_symm_apply]
        rw [hFv, h1, h1, hB, actOn_inC, form_one]
        show _ = ((D'.EF (ψ.symm x) (ψ.symm x') : ℤ) : AfP p)
        have h2 := hsF (ψ.symm x) (ψ.symm x')
        rw [← map_mul]
        have h3 : s * (D.EF.baseChange ℚ) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j (ψ.symm x))) (j (ψ.symm x')) =
            ((D'.EF (ψ.symm x) (ψ.symm x') : ℤ) : ℚ) := h2.symm
        rw [h3, map_intCast])
      A hAL (fun n => (ψ : D'.La →+ D.La).comp (f n)) hAc nu c hc (fun n hn hnp x x' => by
        obtain ⟨-, -, -, -, h5⟩ := hw.2 n hn hnp
        simpa using h5 x x')
    intro v w
    have h1 := key v w
    rw [hFv] at h1
    rw [hy]
    exact h1
  obtain ⟨t, ht⟩ := UpperTheory.exists_unit_triv_of_similitude_factor L β y y' y'y yy' s hs c hform
  have hrd : ∀ w, rd L ⟨y', y, y'y, yy'⟩ 1 w = A' ((1 : AfP p) ⊗ₜ[ℚ] T.symm w) := by
    intro w
    simp only [rd, inv_one, map_one, Module.End.one_apply, hy']
    rw [Module.End.mul_apply, hTv']
  refine ⟨⟨y', y, y'y, yy'⟩, t, ht, fun n hn hnp => ⟨fun w => ?_, fun a => ?_⟩⟩
  · rw [hrd, cong_iff hAA' hAL hA'L, UpperTheory.one_tmul_mem_completedLattice_iff]
    constructor
    · rintro ⟨r, u, h⟩
      refine ⟨r, ψ u, ?_⟩
      apply T.injective
      rw [map_nsmul, T.apply_symm_apply, h, hT]
    · rintro ⟨r, x, h⟩
      refine ⟨r, ψ.symm x, ?_⟩
      rw [← hT, ψ.apply_symm_apply, ← h, map_nsmul, T.apply_symm_apply]
  · obtain ⟨w, hwL, e⟩ := hAc n hn hnp a
    refine ⟨-(A' w), neg_mem (hA'L w hwL), ?_⟩
    have h1 : T.symm (j (f n a)) = (1 : ℚ) ⊗ₜ[ℤ] ψ (f n a) := by rw [← hT, T.symm_apply_apply]
    have h2 : (1 : AfP p) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ (f n a)) = A (inAf D a) - n • w := by
      rw [e, add_sub_cancel_right]; rfl
    rw [hrd, h1, h2, map_sub, map_nsmul, ← Module.End.mul_apply, hA'A, Module.End.one_apply, smul_neg, sub_eq_add_neg]

end UpperTheory.Gal.W2
