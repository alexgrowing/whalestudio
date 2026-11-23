import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsC2AtOfIsPotential

noncomputable section

open MvPolynomial ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace RealGeo

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def lineCoef : Option (Ψ × Fin N) → Option (Ψ × Fin N) → ℤ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some r, some p => Cmp.rootCoef r p

omit [DecidableEq Ψ] in

theorem line_smooth (M : RootModel Ψ N) (o : Option (Ψ × Fin N)) : IsSmoothHerm (M.line 1 o) := by
  cases o with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth 1 r

theorem geoMono_word (hI : PB.Inputs) (M : RootModel Ψ N) {J : Ideal (MRing M.ι)}
    (R : AnLogRes M.P J (dimFl Ψ N)) (w : Fin (dimFl Ψ N) → Option (Ψ × Fin N)) :
    M.geoMono (∑ j, Finsupp.single (w j) 1) =
      mInt R.A (fun j => potOf R (M.line 1 (w j))) (fun _ => 1) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ (∑ j, Finsupp.single (w j) (1 : ℕ)) none) := by
  classical
  have hdeg : (∑ j, Finsupp.single (w j) (1 : ℕ)).degree = dimFl Ψ N := by
    rw [map_sum]
    simp [Finsupp.degree_single]
  have hms : Finsupp.toMultiset (∑ j, Finsupp.single (w j) (1 : ℕ)) = Multiset.map w Finset.univ.val := by
    rw [Finsupp.toMultiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [Finset.sum_eq_multiset_sum]
    have e : (fun i => ({w i} : Multiset (Option (Ψ × Fin N)))) = (fun p => {p}) ∘ w := rfl
    rw [e, ← Multiset.map_map, Multiset.sum_map_singleton]
  obtain ⟨ρ, hρ⟩ := GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.exists_perm_toList w
  have hML : monoLines (M.line 1) (∑ j, Finsupp.single (w j) (1 : ℕ)) (dimFl Ψ N) =
      (fun i => M.line 1 (w i)) ∘ ρ := by
    funext k
    have hk : (k : ℕ) < (Multiset.map w Finset.univ.val).toList.length := by
      have := k.2
      simp [Multiset.length_toList]
    unfold monoLines
    rw [hms, dif_pos hk, hρ k hk]
    rfl
  unfold RootModel.geoMono
  rw [if_pos hdeg, hML]
  congr 1
  refine (ptsIntegral_one_eq_mInt hI.resExists resBridge R M.arith (L := (fun i => M.line 1 (w i)) ∘ ρ)
    (fun j => line_smooth M _)).trans ?_
  exact mIntSymm R.A (fun j => potOf R (M.line 1 (w j))) ρ _

omit [DecidableEq Ψ] in

theorem geoFun_pow (M : RootModel Ψ N) (a : Option (Ψ × Fin N) → ℝ) :
    M.geoFun ((∑ o, C (a o) * X o) ^ dimFl Ψ N) =
      ∑ w : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
        (∏ j, a (w j)) * M.geoMono (∑ j, Finsupp.single (w j) 1) := by
  classical
  have h1 : (∑ o, C (a o) * X o : RPA Ψ N) ^ dimFl Ψ N =
      ∑ w : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
        (∏ j, a (w j)) • monomial (∑ j, Finsupp.single (w j) 1) (1 : ℝ) := by
    have h0 : (∑ o, C (a o) * X o : RPA Ψ N) ^ dimFl Ψ N =
        ∏ _j : Fin (dimFl Ψ N), ∑ o, C (a o) * X o := by simp
    rw [h0, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.prod_mul_distrib, monomial_sum_one, smul_eq_C_mul, map_prod]
    rfl
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  have : (monomial (∑ j, Finsupp.single (w j) 1) (1 : ℝ) : RPA Ψ N) =
      basisMonomials (Option (Ψ × Fin N)) ℝ (∑ j, Finsupp.single (w j) 1) := by
    rw [coe_basisMonomials]
  rw [this, RootModel.geoFun, Module.Basis.constr_basis]

omit [DecidableEq Ψ] in

theorem linA_eq (lam : Wt Ψ N) (s : ℝ) :
    linA lam s = ∑ o : Option (Ψ × Fin N), C (o.elim s fun r => -lam r.1 r.2) * X o := by
  simp only [linA, toA, linRoot, map_neg, map_sum, map_mul, rename_C, rename_X, Fintype.sum_option,
    Option.elim, neg_mul, Finset.sum_neg_distrib]
  rw [add_comm]

theorem xdeg_eq {M : RootModel Ψ N} {S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))} {n : ℕ} (R : RealTie M S n)
    (r : Ψ × Fin N) (k : M.K) :
    M.xdeg r k = (if h : 0 < (r.2 : ℕ) then
      (R.Re.ref (some (r.1, ⟨(r.2 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) r.2.isLt⟩))).a k else 0) -
        (R.Re.ref (some r)).a k := by
  obtain ⟨τ, i⟩ := r
  dsimp only
  have hY : ∀ l : Fin N, (R.Re.ref (some (τ, l))).a k = -∑ m ∈ Finset.Iic l, M.xdeg (τ, m) k := fun l => by
    rw [R.fund_deg τ l]
    simp [Finset.sum_apply]
  split_ifs with h
  · have hI : Finset.Iic i = insert i (Finset.Iic (⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin N)) := by
      ext l
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    have hn : i ∉ Finset.Iic (⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin N) := by
      simp only [Finset.mem_Iic, Fin.le_def]
      omega
    simp only [hY]
    rw [hI, Finset.sum_insert hn]
    ring
  · have hI : Finset.Iic i = {i} := by
      ext l
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    simp only [hY]
    rw [hI, Finset.sum_singleton]
    ring

theorem line_deg {M : RootModel Ψ N} {S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))} {n : ℕ} (R : RealTie M S n)
    (o : Option (Ψ × Fin N)) : (M.line 1 o).a = (PB.combLine R.Re.ref (lineCoef o)).a := by
  funext k
  rw [PB.combLine_a, Fintype.sum_option]
  cases o with
  | none =>
    simp only [lineCoef, one_mul, zero_mul, Finset.sum_const_zero, add_zero, R.ref_none.1]
    rfl
  | some r =>
    simp only [lineCoef, zero_mul, zero_add]
    rw [Cmp.sum_rootCoef_mul r fun p => (R.Re.ref (some p)).a k]
    show (M.x 1 r).a k = _
    rw [M.x_deg, xdeg_eq R r k]

omit [DecidableEq Ψ] in

theorem prod_coef (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) (w : Fin (dimFl Ψ N) → Option (Ψ × Fin N)) :
    ∏ j, M.coef lam s (w j) =
      (∏ j, (w j).elim s fun r => -lam r.1 r.2) / (M.kA : ℝ) ^ (∑ j, Finsupp.single (w j) (1 : ℕ)) none := by
  classical
  have h1 : ∀ j, M.coef lam s (w j) = ((w j).elim s fun r => -lam r.1 r.2) *
      ((M.kA : ℝ)⁻¹) ^ (Finsupp.single (w j) (1 : ℕ)) none := fun j => by
    cases h : w j with
    | none => simp [RootModel.coef, div_eq_mul_inv]
    | some r => simp [RootModel.coef]
  simp only [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.finset_sum_apply]
  rw [inv_pow, div_eq_mul_inv]

theorem sum_coef_lineCoef (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) (a : Option (Ψ × Fin N)) :
    ∑ o, M.coef lam s o * (lineCoef o a : ℝ) = PB.gapS (fun x => lam x.1 x.2) (s / M.kA) a := by
  rw [Fintype.sum_option]
  cases a with
  | none => simp [lineCoef, RootModel.coef, PB.gapS]
  | some p =>
    simp only [lineCoef, RootModel.coef, PB.gapS, Option.elim, Int.cast_zero, mul_zero, zero_add]
    exact Cmp.sum_neg_mul_rootCoef (fun x : Ψ × Fin N => lam x.1 x.2) p

end RealGeo

theorem geoFun_linA_pow_of_realTie : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N)
    (S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))) (n : ℕ) (R : RealTie M S n) (lam : Wt Ψ N) (s : ℝ),
    (n : ℝ) * M.geoFun (linA lam s ^ dimFl Ψ N) =
      eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) S.degPoly := by
  intro hI _ _ Ψ _ _ N M S n R lam s
  classical
  have hδ : (M.δ : ℝ) = n * R.Re.deg := by exact_mod_cast R.δ_eq
  have hδ0 : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  have hn0 : (n : ℝ) ≠ 0 := fun h => hδ0 (by rw [hδ, h, zero_mul])
  have hd0 : (R.Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 R.Re.deg_pos.ne'
  have hk0 : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.kA_pos.ne'
  have hT : ∀ w : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
      M.geoMono (∑ j, Finsupp.single (w j) 1) =
        (∑ v : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
          (∏ i, (RealGeo.lineCoef (w i) (v i) : ℝ)) * (R.Re.deg * S.degNum v)) /
          ((M.δ : ℝ) * (M.kA : ℝ) ^ (∑ j, Finsupp.single (w j) (1 : ℕ)) none) := by
    intro w
    rw [RealGeo.geoMono_word hI M R.Re.R w, ← Cmp.mInt_combLine_eq R.Re fun j => RealGeo.lineCoef (w j)]
    congr 1
    exact Cmp.mInt_potOf_eq_of_deg R.Re.R (fun j => RealGeo.line_smooth M _)
      (fun j => Cmp.isSmoothHerm_combLine R.Re.ref_smooth _) fun j => RealGeo.line_deg R _
  have heval : eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) S.degPoly =
      ∑ v, S.degNum v * ∏ j, PB.gapS (fun x => lam x.1 x.2) (s / M.kA) (v j) := by
    simp [PB.AnSys.degPoly, PB.formPoly]
  have hg : ∀ v : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
      ∏ j, PB.gapS (fun x => lam x.1 x.2) (s / M.kA) (v j) =
        ∑ w : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
          (∏ j, M.coef lam s (w j)) * ∏ j, (RealGeo.lineCoef (w j) (v j) : ℝ) := by
    intro v
    simp_rw [← RealGeo.sum_coef_lineCoef]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun w _ => Finset.prod_mul_distrib
  rw [RealGeo.linA_eq, RealGeo.geoFun_pow, heval, Finset.mul_sum]
  calc _ = ∑ w : Fin (dimFl Ψ N) → Option (Ψ × Fin N), ∑ v : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
          S.degNum v * ((∏ j, M.coef lam s (w j)) * ∏ j, (RealGeo.lineCoef (w j) (v j) : ℝ)) :=
        Finset.sum_congr rfl fun w _ => by
          rw [hT, RealGeo.prod_coef, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [hδ]
          have hp : (M.kA : ℝ) ^ (∑ j, Finsupp.single (w j) (1 : ℕ)) none ≠ 0 := pow_ne_zero _ hk0
          field_simp
    _ = ∑ v : Fin (dimFl Ψ N) → Option (Ψ × Fin N), ∑ w : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
          S.degNum v * ((∏ j, M.coef lam s (w j)) * ∏ j, (RealGeo.lineCoef (w j) (v j) : ℝ)) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hg, Finset.mul_sum]

end GlobalTheory.CompanionTheory.Ar.Top
