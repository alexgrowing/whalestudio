import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalIsometryIsometricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfIntersectionShiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricDifferenceLogStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsElementHeightDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundlesStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ArUniq

theorem isSelfInter_pow (hC : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ} (hX : IsArithVar p D) {L : HermLB p} {a : ℝ} (ha : L.IsSelfInter a) (m : ℕ) :
    (L.pow m).IsSelfInter ((m : ℝ) ^ (D + 1) * a) := by
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).1
  have h₁ := (((hC.arIso k X p D hX).2 Unit _ Φ hΦ).1 ()).unique hX ha
  obtain ⟨H, hH, e⟩ := hΦ.1 fun _ => (m : ℤ)
  refine ⟨H, (hC.arIso k X p D hX).1 _ _ H (GlobalTheory.T.comb_pow_isometric k X p L m) hH, e.trans ?_⟩
  rw [← h₁, ← smul_eq_mul, ← map_smul, ArInt.lin, Fintype.sum_unique, mul_pow, ← map_pow, MvPolynomial.smul_eq_C_mul]
  simp

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

def Reads (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (t : ℝ) :
    Prop :=
  A.Induced M L k cf ∧ ∃ a : ℝ, (haveI := M.ar.isIntegral; L.IsSelfInter a) ∧
    t = (a / (((k : ℕ) : ℝ) * (A.n : ℕ)) ^ (Y.dim + 1) + ((Y.dim : ℝ) + 1) * A.deg * ∑ᶠ v, cf v) /
      (Module.finrank ℚ F : ℝ)

variable {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 F) → ℝ} {t : ℝ}

theorem Reads.pull (hB : GlobalTheory.Published.ArBirational) (h : Reads A M L k cf t) (N : TrueGeo.Model Y) (π : N.X ⟶ M.X)
    (hπ : π ≫ M.p = N.p) (hj : N.j ≫ π = M.j) (hU : ∃ U : M.X.Opens, (U : Set M.X).Nonempty ∧ IsIso (π ∣_ U)) :
    Reads A N (L.pull π hπ) k cf t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  obtain ⟨U, hU, hU'⟩ := hU
  have := M.ar.isIntegral
  have := N.ar.isIntegral
  exact ⟨GlobalTheory.T.induced_metric_pullback F C Y A M N π hπ hj L k cf hI, a,
    hB _ M.X N.X M.p N.p Y.dim M.ar N.ar (GlobalTheory.T.generically_smooth_model F Y M) (GlobalTheory.T.generically_smooth_model F Y N) π hπ U hU hU' L a ha, ht⟩

theorem Reads.pow (hE : GlobalTheory.Published.ArCalc) (h : Reads A M L k cf t) (m : ℕ+) :
    Reads A M (L.pow m) (k * m) cf t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  have := M.ar.isIntegral
  refine ⟨GlobalTheory.T.induced_metric_pow F C Y A M L k m cf hI, _, isSelfInter_pow hE M.ar ha m, ?_⟩
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [ht, PNat.mul_coe, Nat.cast_mul]
  congr 2
  rw [mul_right_comm, mul_pow _ ((m : ℕ) : ℝ)]
  field_simp

theorem Reads.scale (hC : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree) (h : Reads A M L k cf t) {b : 𝓞 F} (hb : b ≠ 0) :
    ∃ L' : HermLB M.p, Reads A M L' k (fun v => cf v +
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / (((k : ℕ) : ℝ) * (A.n : ℕ))) t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  have hc : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖ := fun σ => by simp
  obtain ⟨hf, r, hr, -⟩ := id hI
  refine ⟨_, GlobalTheory.T.induced_metric_shift_element F C Y A M L k cf b hb hc hI, _,
    GlobalTheory.T.self_intersection_shift hC hD F Y M L _ r hr (fun σ => Real.log ‖σ b‖) hc a ha, ?_⟩
  obtain ⟨h₁, h₂⟩ := GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero F (algebraMap (𝓞 F) F b) (by simpa using hb)
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [finsum_add_distrib hf (h₁.subset fun v hv h0 => hv (by simp only [h0, zero_div]))]
  simp only [div_eq_mul_inv (Real.log _)]
  rw [← finsum_mul' _ _ h₁, eq_neg_of_add_eq_zero_right h₂, ht, Y.inter_const_nsmul, Adl.deg]
  simp only [RingHom.comp_apply]
  congr 1
  push_cast
  field_simp
  ring

theorem Reads.eq (hC : GlobalTheory.Published.ArCalc) (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) {L' : HermLB M.p} {t' : ℝ}
    (h : Reads A M L k cf t) (h' : Reads A M L' k cf t') : t = t' := by
  obtain ⟨hI, a, ⟨H, hH, rfl⟩, rfl⟩ := h
  obtain ⟨hI', a', ha', rfl⟩ := h'
  have := M.ar.isIntegral
  have e := HermLB.IsSelfInter.unique M.ar ⟨H, (hC.arIso _ M.X M.p Y.dim M.ar).1 L L' H
    (GlobalTheory.T.rational_isometry_isometric _ M.X M.p L L' (GlobalTheory.T.ratIsom_of_induced_hermitian_bundles F C Y A M hN L L' k cf hI hI')) hH, rfl⟩ ha'
  rw [e]

theorem Reads.eq' (hC : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree)
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) {L' : HermLB M.p} {t' : ℝ}
    {cf' : HeightOneSpectrum (𝓞 F) → ℝ} (h : Reads A M L k cf t) (h' : Reads A M L' k cf' t') : t = t' := by
  obtain ⟨m, b, b', hb, hb', e⟩ := GlobalTheory.T.exists_element_height_difference F (fun v => ((k : ℕ) : ℝ) * (A.n : ℕ) * (cf' v - cf v))
    ((h.1.1.union h'.1.1).subset fun v hv => by
      by_contra h0
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h0
      simp [h0.1, h0.2] at hv) fun v => by
    obtain ⟨e, α, hα, h₁⟩ := GlobalTheory.T.induced_metric_difference_log F C Y A M L L' k cf cf' h.1 h'.1 v
    rw [h₁]
    exact GlobalTheory.T.log_absolute_value_rational F v e α hα
  obtain ⟨L₁, h₁⟩ := (h.pow hC m).scale hC hD hb
  obtain ⟨L₂, h₂⟩ := (h'.pow hC m).scale hC hD hb'
  refine h₁.eq hC hN (L' := L₂) ?_
  convert h₂ using 2 with v
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [sub_eq_iff_eq_add.1 (e v).symm, PNat.mul_coe, Nat.cast_mul]
  field_simp
  ring

theorem isArTop_unique : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F)
    (Y : Var F) (A : Adl C Y) (t t' : ℝ), A.IsArTop t → A.IsArTop t' → t = t' := by
  rintro hC hD F _ _ C Y A t t' ⟨M, L, k, cf, a, hI, ha, ht⟩ ⟨M', L', k', cf', a', hI', ha', ht'⟩
  obtain ⟨N, π, π', hN, hπ, hπ', hj, hj', hU, hU'⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M'
  have h₁ := (Reads.pull hD.1 ⟨hI, a, ha, ht⟩ N π hπ hj hU).pow hC k'
  have h₂ := (Reads.pull hD.1 ⟨hI', a', ha', ht'⟩ N π' hπ' hj' hU').pow hC k
  rw [mul_comm k' k] at h₂
  exact h₁.eq' hC hD hN h₂

end GlobalTheory.TrueGeo.ArUniq
