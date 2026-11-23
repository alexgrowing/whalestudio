import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionChars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullResult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormEqDrViaPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FactorAffineOpenOfClosedPointMem

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqHalf.ChartAgree

section Gen

open Formalism.MainNotions.DIV.Cons (intO)
open Formalism.L2.Pj GlobalTheory.LineNorm GlobalTheory.HalfGeo GlobalTheory.HalfGeo.PowFam MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {p : ℕ} [hp : Fact p.Prime]

theorem exists_tanBasis (x : Sp ↥(intO ℂ_[p]) ⟶ X) :
    ∃ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e := by
  haveI : ValuationRing ↥(intO ℂ_[p]) := Guard.intO_valRing _
  obtain ⟨V, g, e, hz, he⟩ := exists_affine_isTanBasis E H X t X (𝟙 _) (x (IsLocalRing.closedPoint _))
  obtain ⟨φ, hφ⟩ := GlobalTheory.LocM.FJ.factor_affineOpen_of_closedPoint_mem X _ x V.1 V.2 hz
  have h := WedgeMax.isTanBasis_map t φ he
  rw [Category.comp_id, hφ] at h
  exact ⟨g, _, h⟩

theorem dlogDvd_of_gens [IsLocallyNoetherian X] {x : Sp ↥(intO ℂ_[p]) ⟶ X} {n N g : ℕ} (hn : 2 ≤ n)
    {χ : Fin N → TorsChar t x (p ^ n)} (hχ : Gens χ) {e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)}
    (he : ∀ i, IsTanAtG t x (e i)) {b : Fin g → ↥(intO ℂ_[p])} {vO : Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left}
    (hb : IsCombAtG t x e b vO) (s : Fin N → ↥(intO ℂ_[p]))
    (hs : ∀ m, ∀ w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p])
        (DualNumber (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}))) ≫ vO →
        ((χ m).χ _ w : DualNumber (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ n})).snd =
          Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) (s m * (p : ↥(intO ℂ_[p])) ^ 2)) :
    DlogDvd t x p 2 vO := by
  have hv := Guard.comb_tan he hb
  have top : ∀ (c : TorsChar t x (p ^ n)) (D : Fin g → ↥(intO ℂ_[p])), DlogIs t p n c e D →
      (p : ↥(intO ℂ_[p])) ^ 2 ∣ ∑ i, D i * b i := by
    intro c D hD
    obtain ⟨w, hw⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) hv
    have hwt : w ^ (p ^ n) = 1 :=
      GlobalTheory.HTLevel.red_tors _ (by rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _) hv w hw
    have hqR : ((p ^ n : ℕ) : ↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n})), Ideal.Quotient.eq_zero_iff_mem,
        Nat.cast_pow]
      exact Ideal.mem_span_singleton_self _
    have hw' : w = GlobalTheory.DlogEx.red _ (GlobalTheory.LieMet.tanOf hv) :=
      Over.OverMorphism.ext (by rw [hw, GlobalTheory.DlogEx.red_left, GlobalTheory.LieMet.left_tanOf])
    have hf : ∀ m, ((χ m).χ _ w : DualNumber (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ n})).fst = 1 :=
      fun m => by rw [hw']; exact GlobalTheory.DlogEx.chi_fst _ hqR (χ m) _
    obtain ⟨k, hk⟩ := hχ c
    have h1 := hD b vO hb w hw
    rw [hk _ w hwt, Units.coe_prod] at h1
    simp only [Units.val_pow_eq_pow_val] at h1
    rw [(dual_prod _ _ fun m => (dual_pow _ (hf m) _).1).2] at h1
    have h2 : ∀ m, (((χ m).χ _ w : DualNumber (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ n})) ^ k m).snd =
        Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) ((k m : ↥(intO ℂ_[p])) * (s m * (p : ↥(intO ℂ_[p])) ^ 2)) :=
      fun m => by rw [(dual_pow _ (hf m) _).2, hs m w hw, map_mul (Ideal.Quotient.mk _) (k m : ↥(intO ℂ_[p])), map_natCast]
    simp only [h2] at h1
    rw [← map_sum, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
    have h3 := ((pow_dvd_pow _ hn).trans h1).add
      (Finset.dvd_sum fun m (_ : m ∈ Finset.univ) => ((dvd_mul_left _ (s m)).mul_left (k m : ↥(intO ℂ_[p]))))
    rwa [sub_add_cancel] at h3
  intro k c w hw
  obtain ⟨D, hD, r, hr⟩ : ∃ D, DlogIs t p k c e D ∧ (p : ↥(intO ℂ_[p])) ^ 2 ∣ ∑ i, D i * b i := by
    rcases le_total k n with hk | hk
    · obtain ⟨c', hc'⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t ℂ_[p] x (p ^ k) (p ^ n) (pow_ne_zero _ hp.out.ne_zero)
        (pow_dvd_pow _ hk) c
      obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p n c' g e he
      exact ⟨D, GlobalTheory.HTLevel.dlog_down hk c' c hc' he hD, top c' D hD⟩
    · obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p k c g e he
      exact ⟨D, hD, top (GlobalTheory.HTLevel.res (pow_dvd_pow p hk) c) D
        (GlobalTheory.HTLevel.dlog_down hk c _ (fun _ _ _ _ _ _ => rfl) he hD)⟩
  rw [hD b vO hb w hw, hr, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem exists_integral [IsLocallyNoetherian X] (hX : X.IsSeparated) {x : Sp ↥(intO ℂ_[p]) ⟶ X} {n N m : ℕ} (hn : 2 ≤ n)
    {χ : Fin N → TorsChar t x (p ^ n)} (hχ : Gens χ) {u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (u l)) {Mc : Matrix (Fin N) (Fin m) ℂ_[p]}
    (hM : DlogVals t x χ u Mc) (y : Fin m → ℂ_[p]) (hy : ∀ r, ‖∑ l, Mc r l * y l‖ ≤ 1) :
    ∃ vO, IsTanAtG t x vO ∧ IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u (fun l => (p : ℂ_[p]) ^ 2 * y l)
      (spMap (dualMap (intO ℂ_[p]).subtype) ≫ vO) := by
  obtain ⟨g, e, he⟩ := exists_tanBasis (t := t) x
  have heC := fun i => GlobalTheory.FactorDepth.isTanAtG_map t (intO ℂ_[p]).subtype (he.1 i)
  obtain ⟨w, hwt, hw⟩ := Guard.exists_comb hu y
  obtain ⟨a, ha, -⟩ := he.2 _ _ w hwt
  have lift : ∀ s : ℂ_[p], ∀ hs : ∀ i, ‖s * a i‖ ≤ 1, ∃ vO, IsCombAtG t x e (fun i => ⟨s * a i, hs i⟩) vO ∧
      spMap (dualMap (intO ℂ_[p]).subtype) ≫ vO = spMap (epsMul s) ≫ w := fun s hs => by
    obtain ⟨vO, -, hbv⟩ := Guard.exists_comb he.1 (fun i => (⟨s * a i, hs i⟩ : ↥(intO ℂ_[p])))
    exact ⟨vO, hbv, Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype hbv) (Guard.comb_smul heC ha _)⟩
  by_cases hbig : ∀ i, ‖(p : ℂ_[p]) ^ 2 * a i‖ ≤ 1
  · obtain ⟨vO, h1, h2⟩ := lift _ hbig
    refine ⟨vO, Guard.comb_tan he.1 h1, ?_⟩
    rw [h2]
    exact Guard.comb_smul hu hw _
  exfalso
  push_neg at hbig
  obtain ⟨i₀, hi₀⟩ := hbig
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖a i‖) ⟨i₀, Finset.mem_univ _⟩
  have hai : 1 < ‖(p : ℂ_[p]) ^ 2 * a i‖ := by
    refine lt_of_lt_of_le hi₀ ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hi i₀ (Finset.mem_univ _)) (norm_nonneg _)
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have ha0 : a i ≠ 0 := fun h0 => by rw [h0, mul_zero, norm_zero] at hai; linarith
  have hl1 : ‖((p : ℂ_[p]) ^ 2 * a i)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hai.le
  have hb' : ∀ k, ‖(a i)⁻¹ * a k‖ ≤ 1 := fun k => by
    rw [← div_eq_inv_mul, norm_div]
    exact div_le_one_of_le₀ (hi k (Finset.mem_univ _)) (norm_nonneg _)
  obtain ⟨vO, h1, h2⟩ := lift _ hb'
  have hv := Guard.comb_tan he.1 h1
  have h3 := hM vO (fun l => (a i)⁻¹ * y l) hv (by rw [h2]; exact Guard.comb_smul hu hw _)
  choose r hr hr' using h3
  let s : Fin N → ↥(intO ℂ_[p]) := fun j => ⟨((p : ℂ_[p]) ^ 2 * a i)⁻¹ * ∑ l, Mc j l * y l, by
    change ‖_‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ hl1 (norm_nonneg _) (hy j)⟩
  have hrs : ∀ j, r j = s j * (p : ↥(intO ℂ_[p])) ^ 2 := fun j => by
    apply (intO ℂ_[p]).subtype_injective
    simp only [map_mul, map_pow, map_natCast, Subring.subtype_apply, s, hr]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
  have hd : DlogDvd t x p 2 vO := dlogDvd_of_gens hn hχ he.1 h1 s fun j w' hw' => by rw [← hrs]; exact hr' j w' hw'
  have hlw := Guard.comb_smul heC ha ((p : ℂ_[p]) ^ 2 * a i)⁻¹
  have hmem : spMap (epsMul ((p : ℂ_[p]) ^ 2 * a i)⁻¹) ≫ w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) := by
    refine ⟨x, rfl, 2, vO, hv, ?_, hd⟩
    rw [h2]
    refine Guard.comb_unique heC (Guard.comb_smul heC ha _) ?_
    convert Guard.comb_smul heC hlw ((p : ℂ_[p]) ^ 2) using 2
    field_simp
  have hn' : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := PadicComplexHost.norm_p p
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  obtain ⟨x', hx', vO', hv', hs'⟩ := GlobalTheory.ShFam.Pad.HTBound.htBound E H X t p ℂ_[p] hn' x
    (fun x' hx' => WedgeMax.ext_intO hX x x' hx') _ hmem p (by
      rw [hn', ← Real.rpow_neg_one]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
      rw [div_le_one (by linarith)]
      linarith)
  obtain rfl := WedgeMax.ext_intO hX x x' hx'
  obtain ⟨b, -, hb⟩ := GlobalTheory.HTLevel.coords he hlw _ hv' hs'
  have h4 : ‖(b i : ℂ_[p])‖ ≤ 1 := (b i).2
  have e1 : (p : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a i) = (p : ℂ_[p])⁻¹ := by field_simp
  rw [hb, e1, norm_inv, hn', inv_inv] at h4
  linarith

theorem norm_sub_le [IsLocallyNoetherian X] (hX : X.IsSeparated) {x : Sp ↥(intO ℂ_[p]) ⟶ X} {n N m k : ℕ} (hn : k + 2 ≤ n)
    {χ : Fin N → TorsChar t x (p ^ n)} (hχ : Gens χ) {u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (u l)) {Mc Mc' : Matrix (Fin N) (Fin m) ℂ_[p]}
    (hM : DlogVals t x χ u Mc) (hM' : DlogVals t x χ u Mc') (y : Fin m → ℂ_[p]) (hy : ∀ r, ‖Mc.mulVec y r‖ ≤ 1)
    (j : Fin N) : ‖Mc'.mulVec y j - Mc.mulVec y j‖ ≤ ‖(p : ℂ_[p])‖ ^ k := by
  obtain ⟨vO, hv, hc⟩ := exists_integral hX (by omega) hχ hu hM y hy
  obtain ⟨r, hr, h1⟩ := hM vO _ hv hc j
  obtain ⟨r', hr', h1'⟩ := hM' vO _ hv hc j
  obtain ⟨w, hw⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) hv
  have h2 := (h1' w hw).symm.trans (h1 w hw)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
  obtain ⟨d, hd⟩ := (pow_dvd_pow _ hn).trans h2
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h3 : Mc'.mulVec y j - Mc.mulVec y j = (p : ℂ_[p]) ^ k * d := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hp0)
    have := congrArg (intO ℂ_[p]).subtype hd
    simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply, hr, hr'] at this
    have e1 : ∀ A : Matrix (Fin N) (Fin m) ℂ_[p],
        ∑ l, A j l * ((p : ℂ_[p]) ^ 2 * y l) = (p : ℂ_[p]) ^ 2 * A.mulVec y j := fun A => by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e1] at this
    linear_combination this
  rw [h3, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) d.2

end Gen

theorem w_le_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} [hp : Fact (resP v).Prime] (e : Ext v)
    (z z' : AlgebraicClosure F) : e.w z ≤ e.w z' ↔ ‖ioOf (resP v) e z‖ ≤ ‖ioOf (resP v) e z'‖ := by
  have hw := GlobalTheory.CovHt.Link.w_eq_norm_ioOf_rpow (resP v) v (residueCharacteristic_mem v) e
  have hw1 : e.w ((resP v : ℕ) : AlgebraicClosure F) < 1 := by
    have e1 : ((resP v : ℕ) : AlgebraicClosure F) =
        algebraMap F _ (algebraMap (𝓞 F) F ((resP v : ℕ) : 𝓞 F)) := by simp
    rw [e1, e.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 (residueCharacteristic_mem v)
  have hw0 : 0 < e.w ((resP v : ℕ) : AlgebraicClosure F) := e.w.pos (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hlp : 0 < Real.log (resP v) := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  rw [hw z, hw z']
  exact Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) (div_pos (neg_pos.2 (Real.log_neg hw0 hw1)) hlp)

theorem supN_sub_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} [hp : Fact (resP v).Prime]
    (e : Ext v) {N m k : ℕ} {A A' : Matrix (Fin N) (Fin m) (AlgebraicClosure F)}
    (h : ∀ y : Fin m → ℂ_[resP v], (∀ r, ‖(A.map (ioOf (resP v) e)).mulVec y r‖ ≤ 1) → ∀ j,
      ‖(A'.map (ioOf (resP v) e)).mulVec y j - (A.map (ioOf (resP v) e)).mulVec y j‖ ≤ ‖((resP v : ℕ) : ℂ_[resP v])‖ ^ k)
    (u : Fin m → AlgebraicClosure F) (hu : supN e.w (A.mulVec u) ≤ 1) :
    supN e.w (A'.mulVec u - A.mulVec u) ≤ e.w ((resP v : ℕ) : AlgebraicClosure F) ^ k := by
  refine supN_le _ (by positivity) fun j => ?_
  rw [← map_pow, w_le_iff, Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, map_pow, map_natCast, norm_pow]
  refine h _ (fun r => ?_) j
  rw [← RingHom.map_mulVec, ← norm_one (α := ℂ_[resP v]), ← map_one (ioOf (resP v) e), ← w_le_iff, map_one]
  exact (le_supN _ _ r).trans hu

theorem uAt_tan {D : D7} (O : Setup D) (c : O.s.Comp) {v : HeightOneSpectrum (𝓞 D.what₂.LL)} [Fact (resP v).Prime]
    (e : Ext v) (y : AlgPt (O.Φ.C c).Y) (l : Fin (D.R.f * O.N)) :
    Formalism.L2.Pj.IsTanAtG O.s.T.Z.t (ptAt O c e y) (uAt O c e y l) :=
  GlobalTheory.FactorDepth.isTanAtG_map _ (psiAt O c e y) ((frAt O c (below y.1)).tan _ _)

theorem charts_agree : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (hp : (resP v).Prime) (e : Ext v) (y : AlgPt (O.Φ.C c).Y) (Ch : Type)
    (inC : Ch → Prop) (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL)),
    resP v = p → PtData O c b n hp e y inC M → ∀ k : ℕ, k + 3 ≤ n → ∀ a a', inC a → inC a' → ∀ u : Fin (D.R.f * O.N) → AlgebraicClosure D.what₂.LL,
      supN e.w ((M a).mulVec u) ≤ 1 → supN e.w ((M a').mulVec u - (M a).mulVec u) ≤ e.w (p : AlgebraicClosure D.what₂.LL) ^ k := by
  intro _ _ _ _ _ D O _ T R _ p _ _ c b n _ v hp e y Ch inC M hv hP k hk a a' ha ha' u hu
  rw [← hv]
  haveI : Fact (resP v).Prime := ⟨hp⟩
  obtain ⟨xO, χ, hx, hχ, -, -, hM⟩ := hP
  haveI := GlobalTheory.Toroidal.isProper_toroidalModel_structureMap O.s.T.Z
  haveI : IsLocallyNoetherian O.s.T.Z.X := LocallyOfFiniteType.isLocallyNoetherian O.s.T.Z.s
  have hX : O.s.T.Z.X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from O.s.T.Z.s]; infer_instance⟩
  exact supN_sub_le e (fun z hz j => norm_sub_le hX (by omega) hχ (fun l => hx ▸ uAt_tan O c e y l)
    (hM a ha) (hM a' ha') z hz j) u hu

end GlobalTheory.EqHalf.ChartAgree
