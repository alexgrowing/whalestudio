import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpAct
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ActLin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ExpTieAlg

variable {S : Type} [CommRing S]

abbrev fam1 {τ : Type} {d : ℕ} (χ : Fin d → MvPowerSeries τ S) : Fin 1 × Fin d → MvPowerSeries τ S := fun p => χ p.2

theorem has_subst_family_of_const {τ : Type} {d : ℕ} {χ : Fin d → MvPowerSeries τ S} (h : ∀ j, constantCoeff (χ j) = 0) :
    HasSubst (fam1 χ) := hasSubst0 fun p => h p.2

theorem eval_single_eq_subst {n d : ℕ} (χ : Pt S n d) (g : PS S 1 d) : ev (n := n) ![χ] g = subst (fam1 χ) g := by
  unfold ev
  congr 1
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i
  rfl

theorem subst_family_comp {τ : Type} {d : ℕ} {χ : Fin d → MvPowerSeries τ S} {ψ : Pt S 1 d}
    (hχ : ∀ j, constantCoeff (χ j) = 0) (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : PS S 1 d) :
    subst (fam1 χ) (subst (fam1 ψ) g) = subst (fam1 fun j => subst (fam1 χ) (ψ j)) g :=
  subst_comp_subst_apply (has_subst_family_of_const hψ) (has_subst_family_of_const hχ) g

open Formalism.FG.SolveVAux in

theorem coeff_single_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (a : σ → MvPowerSeries τ S) (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ S) (t : τ) :
    coeff (Finsupp.single t 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hlow : ∀ s, Low 1 (a s) := fun s => (low_one_iff _).2 (ha s)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun s : σ => Finsupp.single s 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.prod_single_index (h := fun (s : σ) (e : ℕ) => a s ^ e) (pow_zero _), pow_one, smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single t 1) (e.prod fun s n => a s ^ n) = 0 := by
      rcases Nat.lt_or_ge e.degree 2 with hd | hd
      · rcases Nat.lt_or_ge e.degree 1 with hd1 | hd1
        · have he0 : e = 0 := by
            have : e.degree = 0 := by omega
            exact (Finsupp.degree_eq_zero_iff e).1 this
          rw [he0, Finsupp.prod_zero_index, coeff_one, if_neg]
          exact Finsupp.single_ne_zero.2 one_ne_zero
        · obtain ⟨p, rfl⟩ := degree_eq_one e (by omega)
          exact absurd (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ p))) hne
      · have hl := low_P hlow e
        exact hl _ (by rw [Finsupp.degree_single]; omega)
    rw [hz, smul_zero]

open Formalism.FG.SolveVAux in

theorem eq_linear {N : ℕ} (g : MvPowerSeries (Fin 1 × Fin N) S)
    (h : ∀ n : Fin 1 × Fin N →₀ ℕ, n.degree ≠ 1 → coeff n g = 0) :
    g = ∑ q, C (coeff (Finsupp.single ((0 : Fin 1), q) 1) g) * X ((0 : Fin 1), q) := by
  classical
  ext n
  rw [map_sum]
  by_cases hn : n.degree = 1
  · obtain ⟨⟨i, q⟩, rfl⟩ := degree_eq_one n hn
    fin_cases i
    rw [Finset.sum_eq_single q]
    · simp [coeff_X]
    · intro b _ hb
      rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
      intro e
      apply hb
      have := Finsupp.single_left_injective one_ne_zero e
      simp only [Prod.mk.injEq] at this
      exact this.2.symm
    · simp
  · rw [h n hn]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
    rintro rfl
    exact hn (by simp [Finsupp.degree_single])

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ExpTieAlg ExpActPf
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem expAct_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type}
    [CommRing S] [Algebra ℚ S] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : IsExpOf B.G.F uvec φ) (a : O) (cA : Lt1 Dw → S)
    (hE : ∀ (ℓ : Lt1 Dw) (i : Fin d), ∑ j, dLin (B.A.act a) i j * uvec ℓ j = cA ℓ * uvec ℓ i) (j : Fin d) :
    subst (fam1 φ) (B.A.act a j) =
      subst (fun q : Fin 1 × Fin (dL Dw) => cA ((ltIdx Dw).symm q.2) • (X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S))
        (φ j) := by
  classical
  obtain ⟨ℓ, hℓ0, hℓ1, hℓadd⟩ := LogPf.logSt S d B.G
  obtain ⟨ε, hinv, -⟩ := formal_exp_law S d B.G ℓ hℓ0 hℓ1 hℓadd
  have hφ0 := hφ.const
  have hA0 : ∀ i, constantCoeff (B.A.act a i) = 0 := B.A.const a
  have hF0 : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  set w : Fin (dL Dw) → Fin d → S := fun q i => uvec ((ltIdx Dw).symm q) i with hw
  have hlin : ∀ q i, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ i) = w q i := by
    intro q i
    have := hφ.lin ((ltIdx Dw).symm q) i
    simpa [w] using this
  have hGF : B.G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1) = B.G.F := by
    funext i
    show ev (n := 2) ![pt S d 0, pt S d 1] (B.G.F i) = B.G.F i
    unfold ev
    have : (fun p : Fin 2 × Fin d => (![pt S d 0, pt S d 1] : Fin 2 → Pt S 2 d) p.1 p.2) = X := by
      funext p; rcases p with ⟨b, i⟩; fin_cases b <;> rfl
    rw [this, subst_self]; rfl

  have hBs : HasSubst (fun r : Fin 1 × Fin (dL Dw) =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst0 fun r => by simp
  have hA2 : HasSubst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) :=
    hasSubst0 fun p => constantCoeff_subst_eq_zero (hasSubst_cpy _) (fun r => by simp [cpy]) (hφ0 p.2)
  have hadd : ∀ i, ev (n := 2) ![pt S (dL Dw) 0 + pt S (dL Dw) 1] (subst (fam1 φ) (ℓ i)) =
      ev (n := 2) ![pt S (dL Dw) 0] (subst (fam1 φ) (ℓ i)) + ev (n := 2) ![pt S (dL Dw) 1] (subst (fam1 φ) (ℓ i)) := by
    intro i
    rw [eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst]
    have hl : subst (fam1 B.G.F) (ℓ i) =
        subst (fam1 (pt S (n := 2) d 0)) (ℓ i) + subst (fam1 (pt S (n := 2) d 1)) (ℓ i) := by
      have := congrFun hℓadd i
      simp only [comp1, Pi.add_apply, eval_single_eq_subst, hGF] at this
      exact this
    have e1 : subst (fam1 (pt S (dL Dw) 0 + pt S (dL Dw) 1)) (subst (fam1 φ) (ℓ i)) =
        subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (subst (fam1 B.G.F) (ℓ i)) := by
      rw [subst_comp_subst_apply (has_subst_family_of_const hφ0) (hasSubst0 fun r => by simp [pt]),
        subst_comp_subst_apply (has_subst_family_of_const hF0) hA2]
      congr 1
      funext p
      exact (hφ.hom p.2).symm
    rw [e1, hl, subst_add hA2, subst_comp_subst_apply (has_subst_family_of_const (fun j => by simp [pt])) hA2,
      subst_comp_subst_apply (has_subst_family_of_const (fun j => by simp [pt])) hA2,
      subst_comp_subst_apply (has_subst_family_of_const hφ0) (hasSubst0 fun r => by simp [pt]),
      subst_comp_subst_apply (has_subst_family_of_const hφ0) (hasSubst0 fun r => by simp [pt])]
    congr 1 <;> congr 1 <;> funext p <;> (simp only [pt, fam1, subst_X hA2]; rfl)

  have hlam : ∀ i, subst (fam1 φ) (ℓ i) = ∑ q, C (w q i) * X ((0 : Fin 1), q) := by
    intro i
    have h1 := addition_linear S (dL Dw) (subst (fam1 φ) (ℓ i)) (hadd i)
    rw [eq_linear _ h1]
    apply Finset.sum_congr rfl
    intro q _
    congr 2
    rw [coeff_single_subst (fam1 φ) (fun p => hφ0 p.2) (ℓ i) ((0 : Fin 1), q), Fintype.sum_prod_type,
      Fin.sum_univ_one]
    have hd : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) (ℓ i) = (1 : Matrix (Fin d) (Fin d) S) i k := by
      intro k; rw [← hℓ1]; rfl
    simp only [fam1, hlin, hd, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]

  have hε0 : ∀ i, constantCoeff (ε i) = 0 := hinv.1
  have hεℓ : ∀ k, subst (fam1 ℓ) (ε k) = X ((0 : Fin 1), k) := by
    intro k
    have := congrFun hinv.2.2.1 k
    simpa [comp1, eval_single_eq_subst, pt] using this
  have hact := action_linear S d O B ℓ ε hℓ0 hℓ1 hℓadd hinv a
  have hcε : ∀ k, constantCoeff (subst (fam1 ε) (B.A.act a k)) = 0 := fun k => by
    rw [const_subst0 (a := fam1 ε) (fun p => hε0 p.2)]; exact hA0 k
  have hℓA : ∀ i, subst (fam1 (B.A.act a)) (ℓ i) = ∑ k, C (dLin (B.A.act a) i k) * ℓ k := by
    intro i
    have hAk : ∀ k, B.A.act a k = subst (fam1 ℓ) (subst (fam1 ε) (B.A.act a k)) := by
      intro k
      rw [subst_family_comp hℓ0 hε0]
      have h2 : (fam1 fun j => subst (fam1 ℓ) (ε j)) = (X : Fin 1 × Fin d → PS S 1 d) := by
        funext p; rcases p with ⟨i, j⟩; fin_cases i; exact hεℓ j
      rw [h2, subst_self]; rfl
    have hi := hact i
    have hcomp : comp1 (B.A.act a) ε = fun k => subst (fam1 ε) (B.A.act a k) := by
      funext k; exact eval_single_eq_subst _ _
    rw [comp1, eval_single_eq_subst, hcomp] at hi
    calc subst (fam1 (B.A.act a)) (ℓ i)
        = subst (fam1 fun k => subst (fam1 ℓ) (subst (fam1 ε) (B.A.act a k))) (ℓ i) := by
          congr 1; funext p; exact hAk p.2
      _ = subst (fam1 ℓ) (subst (fam1 fun k => subst (fam1 ε) (B.A.act a k)) (ℓ i)) :=
          (subst_family_comp hℓ0 hcε _).symm
      _ = subst (fam1 ℓ) (∑ k, C (dLin (B.A.act a) i k) * X ((0 : Fin 1), k)) := by rw [hi]
      _ = ∑ k, C (dLin (B.A.act a) i k) * ℓ k := by
          rw [subst_sum' (has_subst_family_of_const hℓ0)]
          apply Finset.sum_congr rfl
          intro k _
          rw [subst_mul (has_subst_family_of_const hℓ0), subst_C, subst_X (has_subst_family_of_const hℓ0)]

  set D : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun q => cA ((ltIdx Dw).symm q.2) • (X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) with hDdef
  have hD : HasSubst D := hasSubst0 fun q => by simp [D]
  have hP0 : ∀ k, constantCoeff (subst (fam1 φ) (B.A.act a k)) = 0 := fun k => by
    rw [const_subst0 (a := fam1 φ) (fun p => hφ0 p.2)]; exact hA0 k
  have hQ0 : ∀ k, constantCoeff (subst D (φ k)) = 0 := fun k =>
    constantCoeff_subst_eq_zero hD (fun q => by simp [D]) (hφ0 k)
  have hLP : ∀ i, subst (fam1 fun k => subst (fam1 φ) (B.A.act a k)) (ℓ i) =
      ∑ q, C (cA ((ltIdx Dw).symm q) * w q i) * X ((0 : Fin 1), q) := by
    intro i
    rw [← subst_family_comp hφ0 hA0, hℓA i, subst_sum' (has_subst_family_of_const hφ0)]
    simp_rw [subst_mul (has_subst_family_of_const hφ0), subst_C, hlam, Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    have := hE ((ltIdx Dw).symm q) i
    simpa [w] using this
  have hLQ : ∀ i, subst (fam1 fun k => subst D (φ k)) (ℓ i) =
      ∑ q, C (cA ((ltIdx Dw).symm q) * w q i) * X ((0 : Fin 1), q) := by
    intro i
    rw [show (fam1 fun k => subst D (φ k)) = fun s => subst D (fam1 φ s) from rfl,
      ← subst_comp_subst_apply (has_subst_family_of_const hφ0) hD, hlam i, subst_sum' hD]
    apply Finset.sum_congr rfl
    intro q _
    rw [subst_mul hD, subst_C, subst_X hD]
    simp only [D, smul_eq_C_mul, map_mul]
    ring

  have hX : ∀ (P : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), (∀ k, constantCoeff (P k) = 0) →
      P j = subst (fam1 fun i => subst (fam1 P) (ℓ i)) (ε j) := by
    intro P hP
    rw [← subst_family_comp hP hℓ0, hεℓ j, subst_X (has_subst_family_of_const hP)]
  rw [hX _ hP0, hX _ hQ0]
  congr 1
  funext p
  exact (hLP p.2).trans (hLQ p.2).symm

theorem expActOf_of_eig (hE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S]
    [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin C.d),
    ∑ j, dLin (C.B.A.act a) i j * C.uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i) : ExpActOfSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hφ a j
  exact expAct_core C.B C.uvec φ hφ a (fun ℓ => algebraMap c.F S (embK c ℓ.1 a))
    (fun ℓ i => hE E H Dw l Xo c S y C a ℓ i) j

end Formalism.MainNotions.ModuliIntegralCharts.H1
