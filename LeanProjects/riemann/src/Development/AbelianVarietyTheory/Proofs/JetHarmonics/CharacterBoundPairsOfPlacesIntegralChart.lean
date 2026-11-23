import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairData
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorEigenspaceStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvExpLinearPartIntegralCharMemIntegralGermStatement

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharPair

theorem sum_sigma_type {M : Type} [AddCommMonoid M] {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d)
    (f : (Σ b : ZMod d, Fin (m b)) → M) (hf : ∀ x, x.1 ≠ a → f x = 0) : ∑ x, f x = ∑ i : Fin (m a), f ⟨a, i⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    exact Finset.sum_eq_zero fun i _ => hf _ hb
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isSat_type {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) {n : ℕ}
    {w : Fin n → (Σ b : ZMod d, Fin (m b)) → C} (hw : IsSat V w) (h0 : ∀ q x, x.1 ≠ a → w q x = 0) :
    IsSat V fun q (i : Fin (m a)) => w q ⟨a, i⟩ := by
  obtain ⟨h1, w', h2, h3⟩ := hw
  refine ⟨fun q i => h1 q _, fun i q => w' ⟨a, i⟩ q, fun i q => h2 _ q, fun q q' => ?_⟩
  rw [← h3 q q', sum_sigma_type m a (fun x => w q x * w' x q') fun x hx => by rw [h0 q x hx, zero_mul]]

theorem coeff_single_one_uncurry_eq_partialDerivative {C : Type} [Field C] {dd : ℕ} (f : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.coeff (Finsupp.single i 1) (un1 f) = ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl f i := by
  show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem integralSeries_uncurry_one {C : Type} [Field C] {V : VF C} {dd : ℕ} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) :=
  fun _ => hf _

theorem isCharacter_uncurry_logarithm_law {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I) {f : PS C 1 dd}
    (hf : ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh Y.B.G.F f) :
    MvPowerSeries.subst (addP (Y.raw p) (gp C (Fin dd) (0 : Fin 2)) (gp C (Fin dd) 1)) (un1 f) =
      MvPowerSeries.subst (gp C (Fin dd) (0 : Fin 2)) (un1 f) * MvPowerSeries.subst (gp C (Fin dd) (1 : Fin 2)) (un1 f) := by
  rw [RowLawPair.formalAdd_eq_law Y p (RowLawPair.zc_gp 0) (RowLawPair.zc_gp 1),
    RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawSquare.zc_law Y (RowLawPair.zc_gp 0) (RowLawPair.zc_gp 1)),
    RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawPair.zc_gp 0), RowLawPair.subst_oneVarGerm_eq_substPointsPowerSeries (RowLawPair.zc_gp 1)]
  exact hf.2

theorem orbitSum_eq {d l : ℕ} (hl : 0 < l) (p : ZMod d → ℕ) (s : ZMod d) :
    (∑' i : ℕ, ((l : ℝ) ^ (-((i : ℝ) + 1))) * (p (s + ((i + 1 : ℕ) : ZMod d)) : ℝ)) = S4.frobSum l p s := by
  unfold S4.frobSum
  exact tsum_congr fun i => by rw [ValuationFitting.rpow_neg_succ hl]

theorem chSt_pair : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), lab.RankOK Dw → ∀ (o : Orb) (Hc : ∀ g, (Y.raw (pairOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb d _ lab ha hg hr o Hc g a hb w hw h0
  have hinj : Function.Injective (lab.tau o g) := fun s s' h =>
    (Prod.mk.inj (Prod.mk.inj (ha.inj (a₁ := (o, g, s)) (a₂ := (o, g, s')) h)).2).2
  obtain ⟨χ, hχ, hdet⟩ := GlobalTheory.T.exists_characters_bounded_minor_eigenspace hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl d (lab.tau o g) hinj
    (ha.frob o g) a lab.n (fun q i => w q ⟨a, i⟩) (isSat_type (fun b => Dw.mult (lab.tau o g b)) a hw h0)
  have hconj : ∀ s, ComplexEmbedding.conjugate (lab.tau o g s) = lab.tau o (1 - g) s := by
    intro s
    fin_cases g
    · exact (ha.conj o s).symm
    · show ComplexEmbedding.conjugate (lab.tau o 1 s) = lab.tau o 0 s
      rw [ha.conj]
      exact star_star _
  simp only [hconj] at hdet
  have hl1 : 1 < V.l := V.l_prime.one_lt
  rw [orbitSum_eq V.l_prime.pos (fun s => Dw.mult (lab.tau o (1 - g) s)) a] at hdet
  have hL : (1 : ℝ) < V.l := by exact_mod_cast hl1
  have h1 := S4.one_div_eq_gam_add_rho hl1
  have hdiv : ∀ x : ℝ, x / ((V.l : ℝ) - 1) = x * (S4.gam V.l + S4.rho V.l) := fun x => by
    rw [← h1]; ring
  have hrho : 0 ≤ S4.rho V.l := div_nonneg zero_le_one (by nlinarith)
  have hgam : 0 ≤ S4.gam V.l := div_nonneg (by linarith) (by nlinarith)
  have hj : (0 : ℝ) ≤ lab.j := Nat.cast_nonneg _
  have hj' : (0 : ℝ) ≤ lab.j' := Nat.cast_nonneg _
  obtain ⟨hc, hbig, hsm⟩ := hr o
  have hpb : ∀ b, lab.big o g b → Dw.mult (lab.tau o (1 - g) b) = 0 + lab.j' := fun b h => by
    rw [hsm (1 - g) b fun hh => (hc g b).1 hh h, zero_add]
  have hps : ∀ b, ¬ lab.big o g b → Dw.mult (lab.tau o (1 - g) b) = lab.n + lab.j := fun b h =>
    hbig (1 - g) b ((hc g b).2 h)
  have hmat : (Matrix.of fun ρ q : Fin lab.n => ∑ x : lab.II Dw o g,
      (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (un1 (χ ρ)) * lieBasisVector C3 ι lab o g x i) * w q x) =
      Matrix.of fun ρ q : Fin lab.n => ∑ x, (∑ i, ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ ρ) i *
        ι (chartUnitVectors C3 ⟨lab.tau o g a, x⟩ i)) * w q ⟨a, x⟩ := by
    ext ρ q
    simp only [Matrix.of_apply, coeff_single_one_uncurry_eq_partialDerivative]
    exact sum_sigma_type (fun b => Dw.mult (lab.tau o g b)) a _ fun x hx => by rw [h0 q x hx, mul_zero]
  rw [← hmat] at hdet
  refine ⟨fun ρ x => ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (un1 (χ ρ)) * lieBasisVector C3 ι lab o g x i,
    fun ρ x => VF.Ge.sum fun i _ => (integralSeries_uncurry_one (hχ ρ).1 _).mul_int (hg.u_int o g x i), fun S t ht ρ => ?_,
    fun hA => hdet.trans (WithTop.coe_le_coe.mpr ?_), fun hB => hdet.trans (WithTop.coe_le_coe.mpr ?_)⟩
  · exact GlobalTheory.T.mvExp_linearPart_integralChar_mem_integralGerm C V d (lab.II Dw o) (Fin (chD C3.ch)) (Y.raw (pairOfLab ha hg o))
      (RowLawPair.rLaw_raw Y _) Hc (un1 (χ ρ)) (integralSeries_uncurry_one (hχ ρ).1) ((constantCoeff_uncurry _).trans (hχ ρ).2.1)
      (isCharacter_uncurry_logarithm_law Y _ (hχ ρ).2) g S t ht
  · rw [S4.frobSum_alt hl1 0 lab.j' (lab.n + lab.j) (lab.big o g) (CharacteristicFromRanks.alt_step (lab.big o) hc hA g) _ hpb hps a hb]
    show _ ≤ (lab.n : ℝ) * S4.gam V.l + ((lab.j : ℝ) + lab.j') / ((V.l : ℝ) - 1)
    rw [hdiv]
    push_cast
    nlinarith [mul_nonneg hj hrho, mul_nonneg hj' hgam]
  · rw [S4.frobSum_const hl1 (0 + lab.j') _ (fun b => hpb b (hB b)) a]
    show _ ≤ ((lab.j : ℝ) + lab.j') / ((V.l : ℝ) - 1)
    rw [hdiv, hdiv]
    push_cast
    nlinarith [mul_nonneg hj hrho, mul_nonneg hj hgam]

end GlobalTheory.CharPair
