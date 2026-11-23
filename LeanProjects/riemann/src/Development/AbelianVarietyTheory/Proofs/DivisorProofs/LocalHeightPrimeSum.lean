import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionChars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullResult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqHalf.Equi

open Formalism.MainNotions.DIV.Cons (intO)
open Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal MonObj Limits GlobalTheory.HalfGeo GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory

theorem dual_zpow {R : Type} [CommRing R] (u : (DualNumber R)ˣ) (hu : (u : DualNumber R).fst = 1) (k : ℤ) :
    ((u ^ k : (DualNumber R)ˣ) : DualNumber R).fst = 1 ∧
      ((u ^ k : (DualNumber R)ˣ) : DualNumber R).snd = (k : R) * (u : DualNumber R).snd := by
  have h1 : ((u⁻¹ : (DualNumber R)ˣ) : DualNumber R).fst = 1 := by
    have := congrArg TrivSqZeroExt.fst u.inv_mul
    rwa [TrivSqZeroExt.fst_mul, hu, _root_.mul_one, TrivSqZeroExt.fst_one] at this
  have h2 : ((u⁻¹ : (DualNumber R)ˣ) : DualNumber R).snd = -(u : DualNumber R).snd := by
    have := congrArg TrivSqZeroExt.snd u.inv_mul
    rw [TrivSqZeroExt.snd_mul, h1, hu, TrivSqZeroExt.snd_one] at this
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, _root_.one_mul, _root_.mul_one] at this
    linear_combination this
  cases k with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Int.cast_natCast]
    exact PowFam.dual_pow _ hu k
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    refine ⟨(PowFam.dual_pow _ h1 _).1, ?_⟩
    rw [(PowFam.dual_pow _ h1 _).2, h2, Int.cast_negSucc]
    ring

theorem snd_prod_zpow {R : Type} [CommRing R] {N : ℕ} (u : Fin N → (DualNumber R)ˣ)
    (hu : ∀ m, (u m : DualNumber R).fst = 1) (k : Fin N → ℤ) :
    ((∏ m, u m ^ k m : (DualNumber R)ˣ) : DualNumber R).snd = ∑ m, (k m : R) * (u m : DualNumber R).snd := by
  rw [Units.coe_prod, (PowFam.dual_prod _ _ fun m => (dual_zpow _ (hu m) _).1).2]
  exact Finset.sum_congr rfl fun m _ => (dual_zpow _ (hu m) _).2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem exists_basis_local {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X) :
    ∃ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), IsTanBasis t x e := by
  obtain ⟨⟨V, hV₀⟩, g, e, hz, he⟩ := exists_affine_isTanBasis E H X t X (𝟙 _) (x (IsLocalRing.closedPoint R))
  have hV : IsAffineOpen V := hV₀
  have hr : Set.range x ⊆ Set.range hV.fromSpec := by
    rw [IsAffineOpen.range_fromSpec (U := V) hV]
    rintro _ ⟨a, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint a).map x.continuous).mem_open V.2 hz
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, V) →+* R, spMap φ ≫ hV.fromSpec = x :=
    ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec x hr)).hom,
      (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  have h := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t φ he
  rw [Category.comp_id, hφ] at h
  exact ⟨g, _, h⟩

theorem gens_res {p : ℕ} [hp : Fact p.Prime] {x : Sp ↥(intO ℂ_[p]) ⟶ X} [IsLocallyNoetherian X] {k n N : ℕ} (hk : k ≤ n)
    {χ : Fin N → TorsChar t x (p ^ n)} (h : Gens χ) : Gens fun m => GlobalTheory.HTLevel.res (pow_dvd_pow p hk) (χ m) := by
  intro c₁
  obtain ⟨c', hc'⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t ℂ_[p] x (p ^ k) (p ^ n) (pow_ne_zero _ hp.out.ne_zero) (pow_dvd_pow _ hk) c₁
  obtain ⟨a, ha⟩ := h c'
  refine ⟨a, fun B _ _ _ w hw => ?_⟩
  obtain ⟨d, hd⟩ := pow_dvd_pow p hk
  rw [← hc' B w hw]
  exact ha B w (by rw [hd, pow_mul, hw, one_pow])

theorem exists_integral [IsLocallyNoetherian X] (hX : X.IsSeparated) {p : ℕ} [hp : Fact p.Prime]
    {x : Sp ↥(intO ℂ_[p]) ⟶ X} {n N g : ℕ} (hn : 2 ≤ n) {χ : Fin N → TorsChar t x (p ^ n)} (hg : Gens χ)
    {u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (u l))
    {Mc : Matrix (Fin N) (Fin g) ℂ_[p]} (hM : DlogVals t x χ u Mc) (cf : Fin g → ℂ_[p])
    (hcf : ∀ m, ‖∑ l, Mc m l * cf l‖ ≤ 1) :
    ∃ vO, IsTanAtG t x vO ∧ IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u (fun l => (p : ℂ_[p]) ^ 2 * cf l)
      (spMap (dualMap (intO ℂ_[p]).subtype) ≫ vO) := by
  have hnp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  haveI := GlobalTheory.TorsCharExt.intO_valuationRing ℂ_[p]
  obtain ⟨d, e, he⟩ := exists_basis_local (t := t) x
  choose h hh using fun m => (GlobalTheory.DlogEx.dlog_exists_unique E H X t _ x p n (χ m) d e he.1).1
  obtain ⟨N', c', nn, -, hall, -, hD⟩ := fullSt E H X t p x N _ (gens_res hn hg)
  have hH := hD d e h he.1 fun m => GlobalTheory.HTLevel.dlog_down hn (χ m) _ (fun _ _ _ _ _ _ => rfl) he.1 (hh m)
  have hlat := GlobalTheory.HTLevelSq.mem_latHT_iff_sq E H X t hX p x d e he N' c' _ hall hH
  have heC := fun i => GlobalTheory.FactorDepth.isTanAtG_map t (intO ℂ_[p]).subtype (he.1 i)
  obtain ⟨w, hw, hwu⟩ := Guard.exists_comb hu cf
  obtain ⟨a, ha, -⟩ := he.2 _ (intO ℂ_[p]).subtype w hw
  have lift : ∀ s : ℂ_[p], (∀ i, ‖s * a i‖ ≤ 1) → ∃ (b : Fin d → ↥(intO ℂ_[p])) (vO : _), (∀ i, (b i : ℂ_[p]) = s * a i) ∧
      IsTanAtG t x vO ∧ IsCombAtG t x e b vO ∧ IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u (fun l => s * cf l)
        (spMap (dualMap (intO ℂ_[p]).subtype) ≫ vO) := by
    intro s hs
    let b : Fin d → ↥(intO ℂ_[p]) := fun i => ⟨s * a i, hs i⟩
    obtain ⟨vO, hv, hbv⟩ := Guard.exists_comb he.1 b
    refine ⟨b, vO, fun _ => rfl, hv, hbv, ?_⟩
    rw [Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype hbv) (Guard.comb_smul heC ha s)]
    exact Guard.comb_smul hu hwu s
  by_cases hbig : ∀ i, ‖(p : ℂ_[p]) ^ 2 * a i‖ ≤ 1
  · obtain ⟨-, vO, -, hv, -, h2⟩ := lift _ hbig
    exact ⟨vO, hv, h2⟩
  exfalso
  push_neg at hbig
  obtain ⟨i₀, hi₀⟩ := hbig
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖a i‖) ⟨i₀, Finset.mem_univ _⟩
  have hai : 1 < ‖(p : ℂ_[p]) ^ 2 * a i‖ := by
    refine lt_of_lt_of_le hi₀ ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hi i₀ (Finset.mem_univ _)) (norm_nonneg _)
  have ha0 : a i ≠ 0 := fun h0 => by rw [h0, mul_zero, norm_zero] at hai; linarith
  have hl1 : ‖((p : ℂ_[p]) ^ 2 * a i)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hai.le
  obtain ⟨b, vO, hb, hv, hbv, h2⟩ := lift (a i)⁻¹ fun k => by
    rw [inv_mul_eq_div, norm_div]
    exact div_le_one_of_le₀ (hi k (Finset.mem_univ _)) (norm_nonneg _)
  obtain ⟨w', hw'⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) hv
  have key : ∀ m, ‖∑ k, (h m k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k)‖ ≤ 1 := fun m => by
    obtain ⟨r, hr, hr'⟩ := hM vO _ hv h2 m
    have h3 := (hh m b vO hbv w' hw').symm.trans (hr' w' hw')
    rw [Ideal.Quotient.eq] at h3
    obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 h3
    have h4 := congrArg (intO ℂ_[p]).subtype hδ
    simp only [map_mul, map_pow, map_natCast, map_sum, map_sub, Subring.subtype_apply, hb, hr] at h4
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h5 : ∑ k, (h m k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) =
        ((p : ℂ_[p]) ^ 2 * a i)⁻¹ * ∑ l, Mc m l * cf l + (δ : ℂ_[p]) * (p : ℂ_[p]) ^ j := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hp0)
      have e1 : (p : ℂ_[p]) ^ 2 * ∑ k, (h m k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) =
          ∑ k, (h m k : ℂ_[p]) * ((a i)⁻¹ * a k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by field_simp
      have e2 : (p : ℂ_[p]) ^ 2 * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * ∑ l, Mc m l * cf l) =
          ∑ l, Mc m l * ((a i)⁻¹ * cf l) := by
        rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by field_simp
      rw [mul_add, e1, e2]
      linear_combination -h4
    rw [h5]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_one₀ hl1 (norm_nonneg _) (hcf m)
    · rw [norm_mul, ← Nat.cast_pow]
      exact mul_le_one₀ δ.2 (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have hlw := hlat _ _ (Guard.comb_smul heC ha ((p : ℂ_[p]) ^ 2 * a i)⁻¹)
  have h6 := hlw.2 (hlw.1.2 fun j => by
    have e3 : ∑ k, ((∑ m, (nn j m : ↥(intO ℂ_[p])) * h m k : ↥(intO ℂ_[p])) : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) =
        ∑ m, (nn j m : ℂ_[p]) * ∑ k, (h m k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) := by
      have h1 : ∀ k, ((∑ m, (nn j m : ↥(intO ℂ_[p])) * h m k : ↥(intO ℂ_[p])) : ℂ_[p]) =
          ∑ m, (nn j m : ℂ_[p]) * (h m k : ℂ_[p]) := by
        intro k
        push_cast
        rfl
      simp only [h1, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    refine e3.symm ▸ IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _) (key m)) i
  have e1 : (p : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a i) = (p : ℂ_[p])⁻¹ := by field_simp
  rw [e1, norm_inv, hnp, inv_inv] at h6
  linarith

theorem comb_act {R : Type} [CommRing R] {x : Sp R ⟶ X} {g : ℕ} {u : Fin g → (Sp (DualNumber R) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t x (u l)) (α : 𝓞 E) {τ : Fin g → R}
    (hτ : ∀ l, u l ≫ (t.act.act α).left = spMap (epsMul (τ l)) ≫ u l) {cf : Fin g → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (hw : IsCombAtG t x u cf w) :
    IsCombAtG t x u (fun l => τ l * cf l) (w ≫ (t.act.act α).left) := by
  have := t.act.hom α
  have h1 := (isCombAtG_iff t x (fun j => ovT (hu j)) cf w).1 hw
  refine (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).2 ?_
  rw [← h1, ← Over.comp_left, combT_post]
  have h2 : ∀ j, ovT (hu j) ≫ t.act.act α = smT x (τ j) (ovT (hu j)) := fun j => Over.OverMorphism.ext (hτ j)
  simp only [h2, combT, smT_smT, _root_.mul_comm]

theorem eig_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {Y : Scheme.{0}} {w : Sp (DualNumber R) ⟶ Y}
    {A : Y ⟶ Y} {a : R} (h : w ≫ A = spMap (epsMul a) ≫ w) :
    (spMap (dualMap ψ) ≫ w) ≫ A = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) ≫ w := by
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc, Guard.sp_comp, Guard.sp_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  ext <;> simp [epsMul, dualMap, _root_.mul_comm]

theorem tan_act {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v)
    (α : 𝓞 E) : IsTanAtG t x (v ≫ (t.act.act α).left) := by
  have := t.act.hom α
  refine isTanAtG_of (ovT hv ≫ t.act.act α) ?_
  rw [smT_post, smT_zero_ovT]
  exact MonObj.one_comp _

theorem norm_equi [IsLocallyNoetherian X] (hX : X.IsSeparated) {p : ℕ} [hp : Fact p.Prime]
    {x : Sp ↥(intO ℂ_[p]) ⟶ X} {k N g : ℕ} {χ : Fin N → TorsChar t x (p ^ (k + 2))} (hg : Gens χ)
    {ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ} (hρ : Equivar t χ ρ)
    {u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (u l))
    {Mc : Matrix (Fin N) (Fin g) ℂ_[p]} (hM : DlogVals t x χ u Mc) (α : 𝓞 E) {τ : Fin g → ℂ_[p]}
    (hτ : ∀ l, u l ≫ (t.act.act α).left = spMap (epsMul (τ l)) ≫ u l) (cf : Fin g → ℂ_[p])
    (hcf : ∀ m, ‖∑ l, Mc m l * cf l‖ ≤ 1) (m : Fin N) :
    ∃ δ : ℂ_[p], ‖δ‖ ≤ 1 ∧ ∑ m', (ρ α m m' : ℂ_[p]) * ∑ l, Mc m' l * cf l - ∑ l, Mc m l * (τ l * cf l) =
      δ * (p : ℂ_[p]) ^ k := by
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  obtain ⟨vO, hv, hc⟩ := exists_integral hX (Nat.le_add_left 2 k) hg hu hM cf hcf
  have hc' := comb_act hu α hτ hc
  rw [Category.assoc] at hc'
  choose r hr hr' using hM vO _ hv hc
  obtain ⟨s, hs, hs'⟩ := hM _ _ (tan_act hv α) hc' m
  obtain ⟨w, hw⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ (k + 2)}) hv
  have hq : ((p ^ (k + 2) : ℕ) : ↥(intO ℂ_[p])) ∈ Ideal.span {(p : ↥(intO ℂ_[p])) ^ (k + 2)} := by
    rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _
  have hqR : ((p ^ (k + 2) : ℕ) : ↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ (k + 2)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ (k + 2)})), Ideal.Quotient.eq_zero_iff_mem]
    exact hq
  have hw' : w = GlobalTheory.DlogEx.red _ (GlobalTheory.LieMet.tanOf hv) :=
    Over.OverMorphism.ext (by rw [hw, GlobalTheory.DlogEx.red_left, GlobalTheory.LieMet.left_tanOf])
  have hf : ∀ m, ((χ m).χ _ w : DualNumber (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ (k + 2)})).fst = 1 :=
    fun m => by rw [hw']; exact GlobalTheory.DlogEx.chi_fst _ hqR (χ m) _
  have h1 := hs' (w ≫ t.act.act α) (by rw [Over.comp_left, hw, Category.assoc])
  rw [hρ α _ w (GlobalTheory.HTLevel.red_tors _ hq hv w hw) m] at h1
  replace h1 := (snd_prod_zpow _ hf _).symm.trans h1
  have h2 : Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ (k + 2)}) (∑ m', (ρ α m m' : ↥(intO ℂ_[p])) * r m') =
      Ideal.Quotient.mk _ s := by
    rw [← h1, map_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [hr' m' w hw, map_mul, map_intCast]
  rw [Ideal.Quotient.eq] at h2
  obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 h2
  have h4 := congrArg (intO ℂ_[p]).subtype hδ
  simp only [map_mul, map_pow, map_natCast, map_intCast, map_sum, map_sub, Subring.subtype_apply, hr, hs] at h4
  refine ⟨δ, δ.2, mul_left_cancel₀ (pow_ne_zero 2 hp0) ?_⟩
  have e1 : (p : ℂ_[p]) ^ 2 * ∑ m', (ρ α m m' : ℂ_[p]) * ∑ l, Mc m' l * cf l =
      ∑ m', (ρ α m m' : ℂ_[p]) * ∑ l, Mc m' l * ((p : ℂ_[p]) ^ 2 * cf l) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : (p : ℂ_[p]) ^ 2 * ∑ l, Mc m l * (τ l * cf l) = ∑ l, Mc m l * (τ l * ((p : ℂ_[p]) ^ 2 * cf l)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [mul_sub, e1, e2]
  linear_combination -h4

section Setup

variable {D : D7} (O : Setup D) (c : O.s.Comp) {v : HeightOneSpectrum (𝓞 D.what₂.LL)} [Fact (resP v).Prime] (e : Ext v)
  (y : AlgPt (O.Φ.C c).Y)

theorem uAt_tan (l : Fin (D.R.f * O.N)) : IsTanAtG O.s.T.Z.t (ptAt O c e y) (uAt O c e y l) :=
  GlobalTheory.LieMet.isTan_map _ rfl ((frAt O c (below y.1)).tan _ _)

theorem psiAt_const (a : O.κ.c.F) : psiAt O c e y (((O.Φ.C c).gr_spec (below y.1)).choose a) =
    ioOf (resP v) e (algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL) (O.κ.e.symm a)) := by
  have h := RingHom.congr_fun ((O.Φ.C c).gr_spec (below y.1)).choose_spec.choose_spec.choose_spec.1.2.1 a
  refine congrArg (ioOf (resP v) e) ?_
  rw [← GlobalTheory.TrueGeo.OfLattice.valAt_const y.1 y.2, ← Base.valAt_stalk]
  exact congrArg (valAt y.1) h.symm

theorem letterEmb_apply (l : Fin (D.R.f * O.N)) (α : 𝓞 D.host.E) :
    letterEmb O l (α : D.host.E) = O.κ.e.symm (embK O.κ.c (letterAt O l).1 α) := by
  have h : (letters O.S.Dw)[(l : ℕ)]? = some (letterAt O l) :=
    List.getElem?_eq_getElem (by rw [length_letters O]; exact l.2)
  unfold letterEmb
  rw [h]
  rfl

theorem uAt_act (l : Fin (D.R.f * O.N)) (α : 𝓞 D.host.E) :
    uAt O c e y l ≫ (O.s.T.Z.t.act.act α).left =
      spMap (epsMul (ioOf (resP v) e (algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL)
        (letterEmb O l (α : D.host.E))))) ≫ uAt O c e y l := by
  rw [letterEmb_apply, ← psiAt_const O c e y]
  exact eig_map _ ((frAt O c (below y.1)).eig _ _ α)

end Setup

end GlobalTheory.EqHalf.Equi

open GlobalTheory.EqHalf.Equi in

theorem GlobalTheory.EqHalf.equi_of_ptData : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (hp : (resP v).Prime) (e : Ext v) (y : AlgPt (O.Φ.C c).Y) (Ch : Type)
    (inC : Ch → Prop) (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL)),
    resP v = p → PtData O c b n hp e y inC M → ∀ k : ℕ, k + 3 ≤ n → ∀ a, inC a → ∀ (α : 𝓞 D.host.E) (u : Fin (D.R.f * O.N) → AlgebraicClosure D.what₂.LL),
      supN e.w ((M a).mulVec u) ≤ 1 →
      supN e.w (((chiAct O.S.Dw b α).map (Int.castRingHom (AlgebraicClosure D.what₂.LL))).mulVec ((M a).mulVec u) -
        (M a).mulVec fun l => algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL) (letterEmb O l (α : D.host.E)) * u l) ≤
        e.w (p : AlgebraicClosure D.what₂.LL) ^ k := by
  intro _ _ _ _ _ D O _ T R _ p _ _ c b n _ v hp e y Ch inC M hv hP k hk a ha α u hu
  subst hv
  haveI : Fact (resP v).Prime := ⟨hp⟩
  obtain ⟨xO, χ, hx, hg, -, hρ, hM⟩ := hP
  obtain ⟨j, rfl⟩ : ∃ j, n = (k + j) + 2 := ⟨n - 2 - k, by omega⟩
  haveI := GlobalTheory.Toroidal.isProper_toroidalModel_structureMap O.s.T.Z
  haveI : IsLocallyNoetherian O.s.T.Z.X := LocallyOfFiniteType.isLocallyNoetherian O.s.T.Z.s
  have hX : O.s.T.Z.X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from O.s.T.Z.s]; infer_instance⟩
  have hio : ∀ z, ‖ioOf (resP v) e z‖ ≤ 1 ↔ e.w z ≤ 1 := fun z => (ioOf_le_one_iff _ (residueCharacteristic_mem v) e z).trans (e.mem_O z)
  have hp0 : ((resP v : ℕ) : AlgebraicClosure D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hp1 : ((resP v : ℕ) : ℂ_[resP v]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  refine supN_le e.w (pow_nonneg (e.w.nonneg _) _) fun m => ?_
  obtain ⟨δ, hδ, h⟩ := norm_equi hX hg hρ (fun l => hx ▸ uAt_tan O c e y l) (hM a ha) α (fun l => uAt_act O c e y l α)
    (fun l => ioOf (resP v) e (u l)) (fun m => by
      have h1 := (hio _).2 ((le_supN e.w _ m).trans hu)
      simpa [Matrix.mulVec, dotProduct] using h1) m
  rw [← map_pow, ← div_le_one (e.w.pos (pow_ne_zero _ hp0)), ← map_div₀, ← hio, map_div₀, map_pow, map_natCast]
  have h2 : ioOf (resP v) e ((((chiAct O.S.Dw b α).map (Int.castRingHom (AlgebraicClosure D.what₂.LL))).mulVec ((M a).mulVec u) -
      (M a).mulVec fun l => algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL) (letterEmb O l (α : D.host.E)) * u l) m) =
      δ * (resP v : ℂ_[resP v]) ^ (k + j) := by
    rw [← h]
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, map_sub, map_sum, map_mul, Matrix.map_apply, eq_intCast,
      map_intCast]
  rw [h2, pow_add, mul_comm ((resP v : ℂ_[resP v]) ^ k), ← mul_assoc, mul_div_cancel_right₀ _ (pow_ne_zero _ hp1), norm_mul,
    ← Nat.cast_pow]
  exact mul_le_one₀ hδ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)

end
