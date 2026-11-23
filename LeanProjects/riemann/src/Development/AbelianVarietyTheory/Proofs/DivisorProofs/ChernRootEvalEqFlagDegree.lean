import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmChernRootsMulFibrePoint
import Formalism.DegreeFormula.PointDegree.PermExpInj
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagAlternation

open GlobalTheory.GoodMetric

def topExp (ι : Type) [Fintype ι] (N : ℕ) : Root (fun _ : ι => N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => N - 1 - (x.2 : ℕ)

theorem coeff_rename_equiv {α β : Type} (e : α ≃ β) (p : MvPolynomial α ℝ) (d : β →₀ ℕ) :
    coeff d (rename e p) = coeff (Finsupp.equivMapDomain e.symm d) p := by
  have hd : d = Finsupp.mapDomain e (Finsupp.equivMapDomain e.symm d) := by
    rw [Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
    simp
  conv_lhs => rw [hd]
  exact coeff_rename_mapDomain _ e.injective _ _

theorem coeff_mul_of_isHomogeneous {σ : Type} (P A : MvPolynomial σ ℝ) (d : σ →₀ ℕ)
    (hA : A.IsHomogeneous d.degree) : coeff d (P * A) = constantCoeff P * coeff d A := by
  rw [coeff_mul, Finset.sum_eq_single ((0 : σ →₀ ℕ), d)]
  · rfl
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    have hb : coeff b A = 0 := by
      refine hA.coeff_eq_zero fun h1 => ?_
      have h2 : a.degree + b.degree = d.degree := by rw [← hab, map_add]
      have ha : a = 0 := (Finsupp.degree_eq_zero_iff a).1 (by omega)
      apply hne
      subst ha
      simp at hab
      simp [hab]
    simp [hb]
  · intro h
    simp at h

theorem constantCoeff_esymm (n k : ℕ) :
    constantCoeff (esymm (Fin n) ℝ k) = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [esymm_zero]
  · rw [if_neg hk.ne', esymm, map_sum]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨i, hi⟩ : t.Nonempty := Finset.card_pos.1 (ht.2 ▸ hk)
    rw [map_prod]
    exact Finset.prod_eq_zero hi (by simp)

theorem constantCoeff_chernRoots {ι : Type} (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) :
    constantCoeff (chernRoots m R) = eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R := by
  have h : (constantCoeff : MvPolynomial (Root m) ℝ →+* ℝ).comp (chernRoots m).toRingHom =
      eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [chernRoots]
    · intro x
      simp [chernRoots, constantCoeff_rename, constantCoeff_esymm]
  exact RingHom.congr_fun h R

theorem antisymm_isHomogeneous {ι : Type} [Fintype ι] (m : ι → ℕ) (F : MvPolynomial (Root m) ℝ) (n : ℕ)
    (hF : F.IsHomogeneous n) : (GoodMetric.antisymm F).IsHomogeneous n := by
  unfold GoodMetric.antisymm
  refine (mem_homogeneousSubmodule n _).1 (Submodule.sum_mem _ fun w _ => ?_)
  exact zsmul_mem ((mem_homogeneousSubmodule n _).2 (hF.rename_isHomogeneous)) _

theorem fibrePoint_isHomogeneous {ι : Type} [Fintype ι] (m : ι → ℕ) :
    (fibrePoint m).IsHomogeneous (∑ x : Root m, (m x.1 - 1 - (x.2 : ℕ))) := by
  unfold fibrePoint
  apply IsHomogeneous.prod
  intro x _
  simpa using ((isHomogeneous_X ℝ x).neg).pow (m x.1 - 1 - (x.2 : ℕ))

theorem degree_topExp (ι : Type) [Fintype ι] (N : ℕ) :
    (topExp ι N).degree = ∑ x : Root (fun _ : ι => N), (N - 1 - (x.2 : ℕ)) := by
  rw [Finsupp.degree_eq_sum]
  rfl

theorem rootDiscr_isHomogeneous (ι : Type) [Fintype ι] (N : ℕ) :
    (rootDiscr (fun _ : ι => N)).IsHomogeneous (topExp ι N).degree := by
  rw [← FibreAntisymm.antisymm_fibrePoint, degree_topExp]
  exact antisymm_isHomogeneous _ _ _ (fibrePoint_isHomogeneous _)

theorem degFl_rename_eq {ι : Type} [Fintype ι] {N : ℕ} (Q : MvPolynomial (Root (fun _ : ι => N)) ℝ) :
    degFl ι N (rename (fun x : Root (fun _ : ι => N) => (x.1, x.2)) Q) =
      (-1) ^ dimFl ι N * coeff (topExp ι N) (GoodMetric.antisymm Q) := by
  unfold degFl GoodMetric.antisymm
  congr 1
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e1 : rename (fun x : Root (fun _ : ι => N) => (x.1, x.2)) Q =
      rename (Equiv.sigmaEquivProd ι (Fin N)) Q := rfl
  have e2 : rename (fun x : Root (fun _ : ι => N) => (⟨x.1, w x.1 x.2⟩ : Root (fun _ : ι => N))) Q =
      rename (Equiv.sigmaCongrRight w) Q := rfl
  rw [e1, e2, coeff_smul, coeff_rename_equiv, coeff_rename_equiv]
  have e3 : Finsupp.equivMapDomain (Equiv.sigmaEquivProd ι (Fin N)).symm (permExp w) =
      Finsupp.equivMapDomain (Equiv.sigmaCongrRight w).symm (topExp ι N) := by
    ext x
    simp [Finsupp.equivMapDomain_apply, permExp, topExp]
  rw [e3]
  simp [zsmul_eq_mul]

theorem coeff_topExp_rootDiscr (ι : Type) [Fintype ι] (N : ℕ) :
    coeff (topExp ι N) (rootDiscr (fun _ : ι => N)) = (-1) ^ dimFl ι N := by
  have h := degFl_rename_eq (ι := ι) (N := N) (fibrePoint _)
  rw [FibreAntisymm.antisymm_fibrePoint] at h
  have hp : rename (fun x : Root (fun _ : ι => N) => (x.1, x.2)) (fibrePoint (fun _ : ι => N)) =
      ∏ x : ι × Fin N, (-X x) ^ (N - 1 - (x.2 : ℕ)) := by
    unfold fibrePoint
    rw [map_prod]
    simp only [map_pow, map_neg, rename_X]
    exact Fintype.prod_equiv (Equiv.sigmaEquivProd ι (Fin N)) _ _ fun x => rfl
  have hpt : degFl ι N (∏ x : ι × Fin N, (-X x) ^ (N - 1 - (x.2 : ℕ))) = 1 := degreePoint ι N
  rw [hp, hpt] at h
  have h2 : ((-1 : ℝ) ^ dimFl ι N) * (-1) ^ dimFl ι N = 1 := by rw [← mul_pow]; simp
  calc coeff (topExp ι N) (rootDiscr (fun _ : ι => N))
      = ((-1) ^ dimFl ι N * (-1) ^ dimFl ι N) * coeff (topExp ι N) (rootDiscr (fun _ : ι => N)) := by
        rw [h2, one_mul]
    _ = (-1) ^ dimFl ι N * ((-1) ^ dimFl ι N * coeff (topExp ι N) (rootDiscr (fun _ : ι => N))) := by ring
    _ = (-1) ^ dimFl ι N := by rw [← h, mul_one]

theorem eval_chernRoots_eq_degFl : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Q : MvPolynomial (GlobalTheory.GoodMetric.Root (fun _ : ι => N)) ℝ) (R : MvPolynomial (ι × ℕ) ℝ), GlobalTheory.GoodMetric.antisymm Q = GlobalTheory.GoodMetric.chernRoots (fun _ : ι => N) R * GlobalTheory.GoodMetric.rootDiscr (fun _ : ι => N) → MvPolynomial.eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R = degFl ι N (MvPolynomial.rename (fun x : GlobalTheory.GoodMetric.Root (fun _ : ι => N) => (x.1, x.2)) Q) := by
  intro ι _ N Q R h
  rw [degFl_rename_eq, h, coeff_mul_of_isHomogeneous _ _ _ (rootDiscr_isHomogeneous ι N),
    coeff_topExp_rootDiscr, constantCoeff_chernRoots]
  have h2 : ((-1 : ℝ) ^ dimFl ι N) * (-1) ^ dimFl ι N = 1 := by rw [← mul_pow]; simp
  calc eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R
      = ((-1) ^ dimFl ι N * (-1) ^ dimFl ι N) * eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R := by
        rw [h2, one_mul]
    _ = _ := by ring

end GlobalTheory.FlagAlternation
