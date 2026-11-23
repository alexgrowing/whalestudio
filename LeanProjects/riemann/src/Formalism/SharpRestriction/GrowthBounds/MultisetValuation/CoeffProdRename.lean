import Mathlib

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen

open Finset

def fac {σ : Type} (κ : σ →₀ ℕ) : ℕ := ∏ x ∈ κ.support, (κ x).factorial

def jp {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A) (f : MvPowerSeries σ K) : A :=
  ∑ κ ∈ P.support, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • MvPolynomial.coeff κ P

theorem jp_eq_sum {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A)
    (f : MvPowerSeries σ K) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jp P f = ∑ κ ∈ S, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • MvPolynomial.coeff κ P := by
  unfold jp
  refine Finset.sum_subset hS ?_
  intro κ _ hκ
  have h0 : MvPolynomial.coeff κ P = 0 := by simpa [MvPolynomial.mem_support_iff] using hκ
  rw [h0, smul_zero]

section Alg

variable {K Pl : Type} [CommRing K] {ι : Pl → Type}

def atP (v : Pl) (f : MvPowerSeries (ι v) K) : MvPowerSeries (Σ v, ι v) K :=
  MvPowerSeries.rename (Function.Embedding.sigmaMk v) f

theorem memLocalization_mul (v : Pl) (f g : MvPowerSeries (ι v) K) : atP v (f * g) = atP v f * atP v g := by
  unfold atP
  exact map_mul _ f g

variable [Fintype Pl]

abbrev eqv : ((Σ v, ι v) →₀ ℕ) ≃+ (∀ v, ι v →₀ ℕ) := Finsupp.sigmaFinsuppAddEquivPiFinsupp

variable [DecidableEq Pl]

theorem eqv_embDomain (v : Pl) (m : ι v →₀ ℕ) :
    eqv (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) = Pi.single v m := by
  funext w
  ext i
  rw [Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
  by_cases h : w = v
  · subst h
    rw [Pi.single_eq_same]
    exact Finsupp.embDomain_apply_self (Function.Embedding.sigmaMk w) m i
  · rw [Pi.single_eq_of_ne h, Finsupp.coe_zero, Pi.zero_apply, Finsupp.embDomain_notin_range]
    rintro ⟨j, hj⟩
    exact h (congrArg Sigma.fst hj).symm

theorem coeff_atP_single (v : Pl) (f : MvPowerSeries (ι v) K) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff (eqv.symm (Pi.single v m)) (atP v f) = MvPowerSeries.coeff m f := by
  have h : eqv.symm (Pi.single v m) = Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
    rw [AddEquiv.symm_apply_eq, eqv_embDomain]
  rw [h]
  exact MvPowerSeries.coeff_embDomain_rename _ _ _

theorem coeff_atP_eq_zero (v : Pl) (f : MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ)
    (h : ∀ m, n ≠ eqv.symm (Pi.single v m)) : MvPowerSeries.coeff n (atP v f) = 0 := by
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨u, hu⟩
  refine h u ?_
  rw [← hu, eq_comm, AddEquiv.symm_apply_eq, ← eqv_embDomain v u]
  exact congrArg eqv (Finsupp.embDomain_eq_mapDomain (Function.Embedding.sigmaMk v) u)

theorem coeff_prod_atP (g : ∀ v, MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPowerSeries.coeff n (∏ v, atP v (g v)) = ∏ v, MvPowerSeries.coeff (eqv n v) (g v) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  let l0 : Pl →₀ ((Σ v, ι v) →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm fun v => eqv.symm (Pi.single v (eqv n v))
  have hl0 : ∀ v, l0 v = eqv.symm (Pi.single v (eqv n v)) := fun v => rfl
  have hmem : l0 ∈ Finset.finsuppAntidiag Finset.univ n := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    calc ∑ v ∈ Finset.univ, l0 v = ∑ v, eqv.symm (Pi.single v (eqv n v)) :=
          Finset.sum_congr rfl fun v _ => hl0 v
      _ = n := by rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]
  rw [Finset.sum_eq_single_of_mem l0 hmem]
  · exact Finset.prod_congr rfl fun v _ => by rw [hl0]; exact coeff_atP_single v (g v) (eqv n v)
  · intro l hl hne
    rw [Finset.mem_finsuppAntidiag] at hl
    by_contra hprod
    apply hne
    have hall : ∀ v, ∃ m, l v = eqv.symm (Pi.single v m) := by
      intro v
      by_contra hv
      push_neg at hv
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ v) (coeff_atP_eq_zero v (g v) (l v) hv))
    choose m hm using hall
    have hn : n = eqv.symm m := by
      rw [← hl.1]
      calc ∑ v ∈ Finset.univ, l v = ∑ v, eqv.symm (Pi.single v (m v)) :=
            Finset.sum_congr rfl fun v _ => hm v
        _ = eqv.symm m := by rw [← map_sum, Finset.univ_sum_single]
    ext1 v
    rw [hm v, hl0, hn, AddEquiv.apply_symm_apply]

private theorem coe_rename_sigma_mk_eq_atP (v : Pl) (p : MvPolynomial (ι v) K) :
    ((MvPolynomial.rename (Sigma.mk v) p : MvPolynomial (Σ v, ι v) K) : MvPowerSeries (Σ v, ι v) K) =
      atP v (p : MvPowerSeries (ι v) K) := by
  ext d
  rw [MvPolynomial.coeff_coe]
  by_cases h : ∃ m, d = eqv.symm (Pi.single v m)
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_atP_single, MvPolynomial.coeff_coe]
    have h2 : eqv.symm (Pi.single v m) = Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
      rw [AddEquiv.symm_apply_eq, eqv_embDomain]
    rw [h2]
    exact MvPolynomial.coeff_rename_embDomain (Function.Embedding.sigmaMk v) p m
  · push_neg at h
    rw [coeff_atP_eq_zero v _ d h]
    apply MvPolynomial.coeff_rename_eq_zero
    intro u hu
    exfalso
    refine h u ?_
    rw [← hu, eq_comm, AddEquiv.symm_apply_eq, ← eqv_embDomain v u]
    exact congrArg eqv (Finsupp.embDomain_eq_mapDomain (Function.Embedding.sigmaMk v) u)

theorem coeff_prod_rename (P : ∀ v, MvPolynomial (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPolynomial.coeff n (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) =
      ∏ v, MvPolynomial.coeff (eqv n v) (P v) := by
  have h1 : ((∏ v, MvPolynomial.rename (Sigma.mk v) (P v) : MvPolynomial (Σ v, ι v) K) :
      MvPowerSeries (Σ v, ι v) K) = ∏ v, atP v (P v : MvPowerSeries (ι v) K) := by
    rw [← Finset.prod_congr rfl fun v _ => coe_rename_sigma_mk_eq_atP v (P v)]
    exact map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (R := K)) _ _
  rw [← MvPolynomial.coeff_coe, h1, coeff_prod_atP]
  simp only [MvPolynomial.coeff_coe]

theorem fac_eq [∀ v, Fintype (ι v)] (n : (Σ v, ι v) →₀ ℕ) : fac n = ∏ v, fac (eqv n v) := by
  classical
  have h1 : ∀ {τ : Type} [Fintype τ] (m : τ →₀ ℕ), fac m = ∏ x, (m x).factorial := by
    intro τ _ m
    unfold fac
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have h0 : m x = 0 := by simpa using hx
    rw [h0, Nat.factorial_zero]
  rw [h1, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [h1]
  exact Finset.prod_congr rfl fun i _ => by rw [Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]

end Alg

theorem jp_prod {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] [Fintype Pl] [DecidableEq Pl] {ι : Pl → Type}
    [∀ v, Fintype (ι v)] (P : ∀ v, MvPolynomial (ι v) A) (g : ∀ v, MvPowerSeries (ι v) K) :
    jp (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) (∏ v, atP v (g v)) = ∏ v, jp (P v) (g v) := by
  classical
  have hsub : (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)).support ⊆
      (Fintype.piFinset fun v => (P v).support).image eqv.symm := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, coeff_prod_rename] at hn
    rw [Finset.mem_image]
    refine ⟨eqv n, ?_, AddEquiv.symm_apply_apply _ _⟩
    rw [Fintype.mem_piFinset]
    intro v
    rw [MvPolynomial.mem_support_iff]
    exact fun h0 => hn (Finset.prod_eq_zero (Finset.mem_univ v) h0)
  rw [jp_eq_sum _ _ _ hsub, Finset.sum_image (fun x _ y _ h => eqv.symm.injective h)]
  unfold jp
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_prod_atP, coeff_prod_rename, fac_eq]
  simp only [AddEquiv.apply_symm_apply, Algebra.smul_def, Nat.cast_prod, map_mul, map_prod,
    Finset.prod_mul_distrib]

end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
