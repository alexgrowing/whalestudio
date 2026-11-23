import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TorAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartGraded
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem count_weights_eq_local_dims (w : Fin 12 → ℤ) (h : ∀ j, Nat.card {i // w i = j} ≤ locDims j) (j : ℤ) :
    Nat.card {i // w i = j} = locDims j := by
  classical
  have hc : ∀ j, Nat.card {i // w i = j} = (Finset.univ.filter fun i => w i = j).card := fun j => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hm : ∀ i, w i ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := fun i => by
    by_contra hn
    have h1 := h (w i)
    have h2 : 0 < Nat.card {k // w k = w i} := by
      haveI : Nonempty {k // w k = w i} := ⟨⟨i, rfl⟩⟩
      exact Nat.card_pos
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [locDims, hn, if_false] at h1
    omega
  have hs := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := ({-2, -1, 0, 1, 2} : Finset ℤ)) (f := w)
    (fun i _ => hm i)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hs
  simp only [← hc, Finset.card_univ, Fintype.card_fin] at hs
  have a1 : _ ≤ 1 := h (-2)
  have a2 : _ ≤ 2 := h (-1)
  have a3 : _ ≤ 3 := h 0
  have a4 : _ ≤ 4 := h 1
  have a5 : _ ≤ 2 := h 2
  have a6 := h j
  unfold locDims at a6 ⊢
  split_ifs at a6 ⊢ with b1 b2 b3 b4 b5
  all_goals (try subst_vars); omega

theorem UpperTheory.V.Loc.rtChart :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∃ (w : Fin 12 → ℤ) (φ : U.R →ₐ[O] MvPowerSeries (Fin 12) E), UpperTheory.V.Loc.IsCompl (D.It U) x φ ∧ (∀ j, Nat.card {i // w i = j} = locDims j) ∧ ∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart E w (wt a b) := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx
  obtain ⟨-, φ₀, h₀⟩ := UpperTheory.V.Loc.rtCompl hP D U E x hx
  obtain ⟨t, θ, ht, hθx, hθI, hθ⟩ := torAut hP D U x hx
  let e : GQ l × Fin 3 × Fin 3 → U.R := fun s =>
    (U.r.hom s.1).mat s.2.1 s.2.2 - algebraMap O U.R (x ((U.r.hom s.1).mat s.2.1 s.2.2))
  haveI : IsCO O (DualNumber O) := co_sqz O O O fun _ => rfl
  obtain ⟨u, hu⟩ := chartSpan 12 (D.It U) x φ₀ _ e h₀ (fun f f' h => by
    obtain ⟨F, -, hF⟩ := (U.rep (DualNumber O)).2 (U.r.map f') trivial
    refine (hF f ?_).trans (hF f' rfl).symm
    refine GLift.ext (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl)
    ext1 a b
    have := h (g, a, b)
    simp only [e, map_sub, AlgHom.commutes, sub_left_inj] at this
    exact this)
  obtain ⟨φ, hφ, hz⟩ := chartChange 12 (D.It U) x φ₀ (fun i => e (u i)) h₀ (fun i => by simp [e]) hu
  have hxe : ∀ g a b, x ((U.r.hom g).mat a b) = (r0 D.η D.Ψ g).mat a b := fun g a b =>
    congrArg (fun r : GQ l →* GG 3 O => (r g).mat a b) hx
  let w : Fin 12 → ℤ := fun i => wt (u i).2.1 (u i).2.2
  have hgr := chartGraded 12 (D.It U) x φ (fun i => e (u i)) w θ t hφ hz hθx hθI ht (fun i => by
    simp only [e, w, map_sub, AlgHom.commutes, hθ, mul_sub]
    congr 1
    by_cases hab : (u i).2.1 = (u i).2.2
    · simp [hab, wt]
    · rw [hxe, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab]
      simp)
  have hg : ∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart E w (wt a b) := fun g a b => hgr _ _ (hθ g a b)
  refine ⟨w, φ, hφ, count_weights_eq_local_dims w (chartCount hP D U E x hx 12 w φ u hφ hg fun i j => ?_), hg⟩
  have h1 := hz i
  simp only [e, map_sub, AlgHom.commutes, sub_eq_iff_eq_add] at h1
  rw [h1, map_add, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, if_neg (by simp), add_zero,
    MvPowerSeries.coeff_X]
  simp [Finsupp.single_left_inj, eq_comm]
