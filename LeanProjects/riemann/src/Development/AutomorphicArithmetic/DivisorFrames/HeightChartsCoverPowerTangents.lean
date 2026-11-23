import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.TangentCombinationTransitivity
import Development.AutomorphicArithmetic.DivisorFrames.CutLatticeNormBound
import Development.AutomorphicArithmetic.DivisorFrames.TangentBasisChangeTorsionCharacter
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem covMat_mulVec {K : Type} [CommRing K] {M N g r : ℕ} (T : Fin N → Fin M → K) (h : Fin M → Fin g → K)
    (A : Fin r → Fin g → K) (cf : Fin r → K) (k : Fin N) :
    (covMat T h A *ᵥ cf) k = ∑ m, T k m * ∑ j, h m j * (∑ i, cf i • A i) j := by
  simp only [covMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

private theorem delta_bounds {q d κ : ℝ} {n : ℕ} (hq : 1 < q) (hd : 0 < d) (hl : Real.log d = -(κ * Real.log q))
    (h0 : 0 ≤ κ) (hn : κ + 2 ≤ n) : d ≤ 1 ∧ q ^ 2 ≤ q ^ n * d := by
  have hq0 : 0 < q := by linarith
  have hlq : 0 < Real.log q := Real.log_pos hq
  constructor
  · rw [← Real.log_nonpos_iff hd.le, hl]
    have := mul_nonneg h0 hlq.le
    linarith
  · rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity) hd.ne', Real.log_pow,
      Real.log_pow, hl]
    have := mul_le_mul_of_nonneg_right hn hlq.le
    push_cast
    linarith

private theorem small {p : ℕ} [Fact p.Prime] {n : ℕ} {δ c : ℂ_[p]} (hδ : δ ≠ 0)
    (hn : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ n * ‖δ‖) (hc : ‖δ * p * c‖ ≤ (p : ℝ)⁻¹ ^ n) : ‖c‖ ≤ (p : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have := PadicComplex.norm_extends' (p := p) (p : ℚ_[p])
    simpa using this
  rw [norm_mul, norm_mul, hpn, inv_pow, ← one_div ((p : ℝ) ^ n), le_div_iff₀ (by positivity)] at hc
  have h1 : (p : ℝ) ^ 2 * ((p : ℝ)⁻¹ * ‖c‖) ≤ 1 := by
    calc _ ≤ ((p : ℝ) ^ n * ‖δ‖) * ((p : ℝ)⁻¹ * ‖c‖) := by gcongr
      _ = ‖δ‖ * (p : ℝ)⁻¹ * ‖c‖ * (p : ℝ) ^ n := by ring
      _ ≤ 1 := hc
  have h2 : (p : ℝ) ^ 2 * ((p : ℝ)⁻¹ * ‖c‖) = ‖c‖ * p := by field_simp
  rw [← one_div, le_div_iff₀ hp0]
  linarith

theorem UpperTheory.height_charts_cover_power_tangents :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X) (J : Type) (K : Charts Dw t V ρ' J) (W : Y.X.Opens) (p : ℕ) [Fact p.Prime] (n : ℕ), K.HTAt ρ W p n → ∀ (r : ℕ) (f : (∀ y : Y.X, Fin r → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))) (σ : 𝓞 E →+* F), EigFr t p ρ f σ → ∀ (M N : ℕ) (a : Fin M → Dw.La) (S : Fin N → Fin M → F) (κ : ℝ), CutAll Dw p σ a S κ → 0 ≤ κ → κ + 2 ≤ n → ∀ (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (P : J → Matrix (Fin M) (Fin r) V.G.functionField), (∀ j, ChartCo t V ρ' (K.aff j) (K.e j) (fun m => K.h j (a m)) f T (P j)) → CutAt t V W p ρ K.U f (fun j => constM V S * P j) T κ := by
  intro E _ _ _ H Dw X t F _ _ Y V ρ' ρ J K W p _ n hHT r f σ hEig M N a S κ hCut hκ0 hκn T P hCo v e y z yt hT j hj
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨x, ch, hx, hK⟩ := hHT v e y z yt hT
  obtain ⟨δ, hδ0, hδl, hC⟩ := hCut ((ioOf p e).comp (algebraMap F (AlgebraicClosure F)))
  obtain ⟨hδ1, hδn⟩ := delta_bounds hp1 (norm_pos_iff.2 hδ0) hδl hκ0 hκn
  obtain ⟨hind, hfr⟩ := hEig v e y
  rw [← hx] at hind hfr
  obtain ⟨ex, hc, b, hb, hd, hpt, het, hA⟩ := hK j hj
  obtain ⟨A, hA1, hA2⟩ := hA M r a f T (P j) (hCo j)
  obtain ⟨c1, c2⟩ := UpperTheory.tangent_combination_transitivity E H X t ℂ_[p] _ _ r _ _ A
    (fun i => GlobalTheory.LieMet.isTan_map _ rfl (hb.1 i)) hA1
  obtain ⟨s1, s2, s3⟩ := UpperTheory.cut_lattice_norm_bound E H Dw p n _ _ b _ hpt _ M N r a _ δ A hC hδ0 hδ1 hδn (c2 hind)
    (fun i => het _ _ (hA1 i) _ (hfr i).2)
  have eA := hA2 N S
  refine ⟨⟨δ, hδ0, hδl, ?_, fun cf => ?_⟩, fun j' hj' u hu k => ?_⟩
  · rw [eA]; exact s1
  · rw [eA, ← hx]
    refine Iff.trans ?_ (s2 cf)
    simp only [latCo, Set.mem_setOf_eq, c1]
  · obtain ⟨ex', hc', b', hb', hd', -, -, hA'⟩ := hK j' hj'
    obtain ⟨A', hA1', hA2'⟩ := hA' M r a f T (P j') (hCo j')
    obtain ⟨c1', -⟩ := UpperTheory.tangent_combination_transitivity E H X t ℂ_[p] _ _ r _ _ A'
      (fun i => GlobalTheory.LieMet.isTan_map _ rfl (hb'.1 i)) hA1'
    rw [eA] at hu
    rw [eA, hA2' N S, covMat_mulVec, covMat_mulVec, ← Finset.sum_sub_distrib]
    obtain ⟨w, -, hw⟩ := Guard.exists_comb (fun i => (hfr i).1) u
    have hs := (s3 u hu).1
    refine lt_of_le_of_lt (b := (p : ℝ)⁻¹) ?_ (inv_lt_one_of_one_lt₀ hp1)
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m _ => ?_
    rw [← mul_sub, norm_mul, norm_sub_rev]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hC.1 k m)).trans (small hδ0 hδn ?_)
    exact UpperTheory.tangent_basis_change_torsion_character E H X t p n x _ _ ex ex' hb hb' (ch (a m)) _ _ (hd _) (hd' _) _ _ w ((c1 u w).1 hw)
      ((c1' u w).1 hw) (δ * p) hs
