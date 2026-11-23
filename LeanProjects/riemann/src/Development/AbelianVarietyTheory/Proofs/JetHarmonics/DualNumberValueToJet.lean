import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq

noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.JetSer
namespace GlobalTheory.JetSer

theorem toJet_one_eq {O κ : Type} [CommRing O] [Fintype κ] (u : MvPowerSeries κ O) :
    toJet 1 u = Ideal.Quotient.mk _ (MvPolynomial.C (constantCoeff u) +
      ∑ q, MvPolynomial.C (coeff (Finsupp.single q 1) u) * MvPolynomial.X q) := by
  classical
  refine (toJet_eq_mk_iff 1 u _).2 fun a ha => ?_
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C, MvPolynomial.coeff_X]
  by_cases h0 : Finsupp.degree a = 0
  · rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    simp [Finsupp.single_eq_zero]
  · have h1 : a ∈ {d : κ →₀ ℕ | Finsupp.degree d = 1} := by
      show Finsupp.degree a = 1
      omega
    rw [← Finsupp.range_single_one] at h1
    obtain ⟨q, rfl⟩ := h1
    rw [if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_add, Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      rwa [Finsupp.single_left_inj one_ne_zero]
    · simp

theorem constantCoeff_dof {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d : ℕ}
    (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) :
    constantCoeff (Dof (G.mapF f) e u) =
      ∑ j, e j * coeff (Finsupp.single ((0 : Fin 1), j) 1) u := by
  have h : ∀ i j : Fin d, constantCoeff (ev (n := 1) ![pt O d 0, 0]
      (pderiv O ((1 : Fin 2), i) (G.mapF f j))) = if j = i then 1 else 0 := by
    intro i j
    rw [← coeff_zero_eq_constantCoeff_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_zero_right,
      Finsupp.embDomain_zero, coeff_pderiv, FGLaw.mapF, coeff_map, zero_add, SymbolOne.coeff_law]
    split_ifs <;> simp
  unfold Dof
  simp only [map_sum, map_mul, h, constantCoeff_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem dualNumber_value_toJet : ∀ (R O : Type) [CommRing R] [CommRing O] (f : R →+* O) (d : ℕ) (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) (S : Type) [CommRing S] [Algebra O S] (ψ : JetR O (Fin 1 × Fin d) 1 →ₐ[O] DualNumber S), (∀ q, ψ (zR 1 q) = TrivSqZeroExt.inr (algebraMap O S (e q.2))) → ψ (toJet 1 u) = TrivSqZeroExt.inl (algebraMap O S (MvPowerSeries.constantCoeff u)) + TrivSqZeroExt.inr (algebraMap O S (MvPowerSeries.constantCoeff (Dof (G.mapF f) e u))) := by
  intro R O _ _ f d G e u S _ _ ψ hψ
  have hC : ∀ c : O, ψ (Ideal.Quotient.mk _ (MvPolynomial.C c)) = TrivSqZeroExt.inl (algebraMap O S c) :=
    fun c => ψ.commutes c
  have hX : ∀ q, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      TrivSqZeroExt.inr (algebraMap O S (e q.2)) := hψ
  rw [toJet_one_eq, constantCoeff_dof]
  simp only [map_add, map_sum, map_mul, hC, hX, Fintype.sum_prod_type, Fin.sum_univ_one]
  congr 1
  ext
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, mul_comm]
    simp only [Algebra.smul_def]

end GlobalTheory.JetSer
