import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.ExistsContDiffEventuallyEq

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

private theorem exists_conj_diag {k : Type} [Field k] (N : GL (Fin 3) k) (μ : Fin 3 → kˣ)
    (hμ : Function.Injective μ) (hroot : ∀ i, ((N : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot (μ i : k)) :
    ∃ g : GL (Fin 3) k, N = g * diagT k (Fin 3) μ * g⁻¹ :=
  UpperTheory.V.Lib.Small.conj_of_roots (fun i => (μ i : k)) (fun _ _ e => hμ (Units.ext e)) N _ (GlobalTheory.SmGL.val_diagT k μ) hroot

private theorem diag_of_comm {k : Type} [Field k] (μ : Fin 3 → kˣ) (hμ : Function.Injective μ)
    (e : GL (Fin 3) k) (h : e * diagT k (Fin 3) μ = diagT k (Fin 3) μ * e) :
    ∃ u : Fin 3 → kˣ, e = diagT k (Fin 3) u := by
  have hoff : ∀ i j, i ≠ j → (e : Matrix (Fin 3) (Fin 3) k) i j = 0 := by
    intro i j hij
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M i j) (congrArg Units.val h)
    simp only [Units.val_mul, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : (μ j : k) ≠ μ i := fun h' => hij (hμ (Units.ext h')).symm
    have h3 : (e : Matrix (Fin 3) (Fin 3) k) i j * ((μ j : k) - μ i) = 0 := by
      rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 h2)
  have hdiag : (e : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal fun i => (e : Matrix (Fin 3) (Fin 3) k) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (e : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 e.isUnit).ne_zero
  have hne : ∀ i, (e : Matrix (Fin 3) (Fin 3) k) i i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩
  rw [val_diagT]
  simpa using hdiag

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.normalG :
    UpperTheory.V.Z.Sym.Sig.NormalG := by
  intro k _ _ _ _
  obtain ⟨-, -, hd, hθ, hΦ, hi, hc⟩ := thFacts k (Lev.iw k)
  obtain hP := (thFacts k (Lev.iw k)).1
  have ht : ∀ u : GL (Fin 3) k, th' k u = Phi k * th k 3 u * (Phi k)⁻¹ := fun u => rfl
  have hprod : ∀ x y z : kˣ, dg ![x, y, z] * th' k (dg ![x, y, z]) = dg ![x / z, 1, z / x] := by
    intro x y z
    rw [hd, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [div_eq_mul_inv, mul_comm]
  refine ⟨fun g₀ x y z => ?_, fun δ a ha hch => ?_⟩
  · rw [← hprod x y z, ht]
    simp only [map_mul, map_inv, hθ, hΦ]
    group
  · have ha0 : (a : k) ≠ 0 := a.ne_zero
    have hgt : 1 < valuation k ((a⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 ha0))).2 ha
    have h1 : (a : k) ≠ 1 := fun h => by rw [h, map_one] at ha; exact lt_irrefl _ ha
    have h2 : ((a⁻¹ : kˣ) : k) ≠ 1 := fun h => by rw [h, map_one] at hgt; exact lt_irrefl _ hgt
    have h3 : (a : k) ≠ ((a⁻¹ : kˣ) : k) := fun h => by
      rw [← h] at hgt; exact lt_asymm ha hgt
    have hμ : Function.Injective (![a, 1, a⁻¹] : Fin 3 → kˣ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (exfalso
           have hij' := congrArg Units.val hij
           simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Units.val_one] at hij'
           first
             | exact h1 hij' | exact h1 hij'.symm | exact h2 hij' | exact h2 hij'.symm
             | exact h3 hij' | exact h3 hij'.symm)
    have hroot : ∀ i, (((δ * th k 3 δ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot
        (((![a, 1, a⁻¹] : Fin 3 → kˣ) i : kˣ) : k) := by
      intro i
      rw [hch]
      fin_cases i <;> simp [Polynomial.IsRoot]
    obtain ⟨g₀, hN⟩ := exists_conj_diag (δ * th k 3 δ) _ hμ hroot
    set n : GL (Fin 3) k := dg ![a, 1, a⁻¹] with hn
    set e : GL (Fin 3) k := g₀⁻¹ * δ * th k 3 g₀ * (Phi k)⁻¹ with he
    have hen : e * th' k e = n := by
      have : e * th' k e = g₀⁻¹ * (δ * th k 3 δ) * g₀ := by
        rw [ht, he]
        simp only [map_mul, map_inv, hθ, hΦ, inv_inv]
        group
      rw [this, hN]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      try rfl
    have hfix : th' k n = n := by
      rw [hn, hd]
      simp
    have hne : th' k e * e = n := by
      have := congrArg (th' k) hen
      rwa [map_mul, hP.invol, hfix] at this
    have hcomm : e * n = n * e := by
      nth_rewrite 1 [← hne]
      nth_rewrite 1 [← hen]
      group
    obtain ⟨u, hu⟩ := diag_of_comm _ hμ e hcomm
    have hu' : u = ![u 0, u 1, u 2] := by
      funext i; fin_cases i <;> rfl
    refine ⟨g₀, u 0, u 1, u 2, ?_, ?_⟩
    · have : dg ![u 0, u 1, u 2] = e := by rw [hu]; exact congrArg _ hu'.symm
      rw [this, he]
      group
    · have h4 : dg ![u 0 / u 2, 1, u 2 / u 0] = n := by
        rw [← hprod, ← hu' , ← hen, hu]
      have h5 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 0) (congrArg Units.val h4)
      simp only [hn, dg, val_diagT] at h5
      simpa [Units.ext_iff] using h5

end
