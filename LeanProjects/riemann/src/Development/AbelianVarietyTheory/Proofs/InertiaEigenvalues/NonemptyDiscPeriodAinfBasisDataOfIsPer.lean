import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedPeriodsDiscAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumnsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodModuleIsClosedLAdicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeRationalInColumnsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscSpanFrobeniusStableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisDvdTauPowLPowAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDiscBasisCrystallineLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixMulEqEPowOfPeriodStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightEx

theorem exists_cols_det_ne_zero {R : Type} [CommRing R] [IsDomain R] {d : ℕ} {κ : Type} (col : κ → Fin d → R)
    (h : ∀ r : Fin d → R, (∀ k, r ⬝ᵥ col k = 0) → r = 0) :
    ∃ σ : Fin d → κ, (Matrix.of fun a b => col (σ b) a).det ≠ 0 := by
  classical
  let F := FractionRing R
  let v : κ → Fin d → F := fun k a => algebraMap R F (col k a)
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hspan : Submodule.span F (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
      (fun a : Fin d => f (Pi.single a 1))
    choose r hr using hb
    have hb0 : algebraMap R F b ≠ 0 := fun h0 => nonZeroDivisors.coe_ne_zero b (hinj (h0.trans (map_zero _).symm))
    have hr0 : r = 0 := h r fun k => hinj (by
      have h1 : f (v k) = 0 := hf (Submodule.subset_span ⟨k, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      rw [map_zero, dotProduct, map_sum]
      have h2 : ∀ a, algebraMap R F (r a * col k a) =
          algebraMap R F b * (v k a • f fun j => if a = j then 1 else 0) := fun a => by
        have e : (fun j => if a = j then (1 : F) else 0) = Pi.single a 1 := by
          ext j; simp [Pi.single_apply, eq_comm]
        rw [map_mul, hr, e, Algebra.smul_def, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl fun a _ => h2 a, ← Finset.mul_sum, h1, mul_zero])
    refine hf0 ((Pi.basisFun F (Fin d)).ext fun a => ?_)
    have h3 := hr a
    rw [hr0, Pi.zero_apply, map_zero, Algebra.smul_def] at h3
    rw [Pi.basisFun_apply]
    exact (mul_eq_zero.1 h3.symm).resolve_left hb0
  obtain ⟨κ', a, -, hs, hli⟩ := exists_linearIndependent' F v
  let B : Module.Basis κ' F (Fin d → F) := Module.Basis.mk hli (by rw [hs, hspan])
  let e : κ' ≃ Fin d := B.indexEquiv (Pi.basisFun F (Fin d))
  refine ⟨a ∘ e.symm, fun h0 => ?_⟩
  have hu : IsUnit ((Matrix.of fun x y => col (a (e.symm y)) x).map (algebraMap R F)) :=
    Matrix.linearIndependent_cols_iff_isUnit.1 (hli.comp e.symm e.symm.injective)
  have h4 := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h4
  exact h4.ne_zero ((congrArg (algebraMap R F) h0).trans (map_zero _))

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem injective_of_topBasis {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (TB : TopBasis s I ι) : Function.Injective s := fun a b h => by
  have e : ∀ a, TB.c TB.i₀ (s a * TB.b TB.i₀) = a := fun a => by rw [TB.c_mul, TB.c_self, mul_one]
  rw [← e a, h, e]

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem exists_cols (hinj : Function.Injective bk.iA) {d : ℕ} {ι : Type}
    (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (β : ι → Ainf l) (c : Ainf l) (hc : c ≠ 0)
    (h : ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * β i)) (bk.iA (c * if a = b then 1 else 0))) :
    ∃ σ : Fin d → ι × Fin d, (Matrix.of fun a b => v (σ b).1 a (σ b).2).det ≠ 0 := by
  refine exists_cols_det_ne_zero (fun (k : ι × Fin d) a => v k.1 a k.2) fun r hr => funext fun b => ?_
  have h1 := hasSum_sum (s := Finset.univ) fun a _ => (h a b).mul_left (bk.iA (r a))
  have h2 : (fun i => ∑ a, bk.iA (r a) * bk.iA (v i a b * β i)) = fun _ => 0 := funext fun i => by
    have h3 := hr (i, b)
    simp only [dotProduct] at h3
    simp only [← map_mul, ← map_sum, ← mul_assoc, ← Finset.sum_mul, h3, zero_mul, map_zero]
  rw [h2] at h1
  have h4 := h1.unique hasSum_zero
  simp only [← map_mul, ← map_sum] at h4
  have h5 := hinj (h4.trans (map_zero _).symm)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h5
  exact (mul_eq_zero.1 h5).resolve_right hc

theorem mem_lattice (hev : Function.Injective bk.ev) {d : ℕ} (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (m : ℕ)
    (P Y' : Matrix (Fin d) (Fin d) (WCb l)) (hY' : (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P)
    (hP : ∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) →
      ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w))
    (y : Fin d → Ainf l) (δ : bk.S) (c : Fin d → bk.S) (hδ : δ ≠ 0)
    (h : (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a)) :
    ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun a => inclW l (y a)) = Y' *ᵥ w := by
  have h0 : bk.evW δ ≠ 0 := fun h0 =>
    hδ (hev (inclW_injective (h0.trans (by rw [map_zero, map_zero]))))
  obtain ⟨n, u, u', -, hu', huu, he⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.2.1 _ (evW_mem bk δ) h0
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have h1 : Y1.map (inclW l) *ᵥ (u' • fun a => bk.evW (c a)) = (l : WCb l) ^ n • fun a => inclW l (y a) := by
    rw [Matrix.mulVec_smul]
    funext a
    have h2 := congrArg (inclW l) (congrFun h a)
    rw [RingHom.map_mulVec, map_mul] at h2
    change bk.evW δ * _ = (Y1.map (inclW l) *ᵥ fun a => bk.evW (c a)) a at h2
    rw [Pi.smul_apply, ← h2, he, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination ((l : WCb l) ^ n * inclW l (y a)) * huu
  obtain ⟨w, hw, hw2⟩ := hP (u' • fun a => bk.evW (c a)) (fun i => bk.OE.mul_mem hu' (evW_mem bk _)) n
    (fun i => by rw [h1]; exact ⟨_, rfl⟩)
  refine ⟨w, hw, ?_⟩
  have h3 := congrArg (Y1.map (inclW l)).mulVec hw2
  rw [Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, smul_comm] at h3
  exact smul_right_injective _ (pow_ne_zero m hl0) (smul_right_injective _ (pow_ne_zero n hl0) h3)

theorem nonempty_height : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ s : Seed bk d ρ τ, Nonempty (Height s) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨-, -, ⟨hρ0, hρ1, -⟩, -⟩ := GlobalTheory.BSP.flat_disc l K bk
  obtain ⟨ι, TB, k, v, Zf, -, hvZ, hsum⟩ := GlobalTheory.T.exists_bounded_periods_disc_ainf l K bk τ hτ d ρ hρ s
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB _ hρ0 hρ1).1
  have hev := injective_of_topBasis TB
  have hτ0 : τ ≠ 0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.2.1
  have hl0 : (l : Ainf l) ≠ 0 := WittVector.p_nonzero l (OCb l)
  obtain ⟨j₀, hj₀⟩ : ∃ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j :=
    GlobalTheory.BSP.exists_discMap_of_pow_dvd l _ _ bk.ev X (bk.ev X) _ _ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨σ, hσ⟩ := exists_cols bk hinj v TB.b _ (mul_ne_zero (pow_ne_zero k hl0) (pow_ne_zero _ hτ0)) hsum
  set Y1 : Matrix (Fin d) (Fin d) (Ainf l) := Matrix.of fun a b => v (σ b).1 a (σ b).2 with hY1
  let Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := Matrix.of fun a b => Zf (σ b).1 a (σ b).2
  have hZ1 : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (congrFun (hvZ j hj (σ b).1) a) (σ b).2
  clear_value Y1 Z1
  have hdet : (Y1.map (inclW l)).det ≠ 0 := fun h0 => hσ (inclW_injective (by
    rw [RingHom.map_det, map_zero]; exact h0))
  obtain ⟨δ, A1, hδ, hA1⟩ := GlobalTheory.T.crystallineLattice_frobenius_rational_columns l K bk τ hτ d ρ hρ s Y1 Z1 hσ hZ1
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → τ ^ s.N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) *
      Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ s.N • Y1 := fun g hg => by
    obtain ⟨G, hG⟩ := (GlobalTheory.BSP.galois_discMap l K bk).2 _ hρ0 (g : GQ l)
    obtain ⟨hfix, hW⟩ := GlobalTheory.T.crystallineDiscPeriods_galois_action_eq l K bk τ hτ d ρ hρ s g hg G hG
    have e1 : (Z1.map j₀).map G = Z1.map j₀ := Matrix.ext fun a b => hfix j₀ hj₀ _
    have e2 : s.W.map G * Z1.map j₀ = (Y1.map (Per.σA (g : GQ l))).map bk.iA := by
      rw [← e1, ← Matrix.map_mul, hZ1 j₀ hj₀]
      exact Matrix.ext fun a b => hG.ext _
    have e3 := congrArg (· * Z1.map j₀) hW
    simp only [Matrix.smul_mul, Matrix.mul_assoc] at e3
    rw [e2, hZ1 j₀ hj₀, hG.ext] at e3
    refine Matrix.ext fun a b => hinj ?_
    have e4 := congrFun (congrFun e3 a) b
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_sum,
      RingHom.comp_apply] at e4 ⊢
    exact e4
  obtain ⟨m, P, Y', hP, hPd, hY', hlat, hsat⟩ := GlobalTheory.T.exists_integralWittLattice_basis l K bk d _ hdet
  have hY'u := GlobalTheory.T.isUnit_saturated_basis_etale_lattice l K bk τ hτ d s.N ρ hρ Y1 δ A1 hdet hδ hA1 hgal m P Y' hP hPd hY' hlat hsat
  obtain ⟨Y, hYu, hY⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀,
      ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a))
    ⟨0, fun j _ => by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _⟩
    (fun y z ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun j hj => by
      simp only [Pi.add_apply, map_add]
      exact (Matrix.mulVec_add s.W (fun a => j (x a)) fun a => j (x' a)).trans (by rw [hx j hj, hx' j hj]; rfl)⟩)
    (fun c y ⟨x, hx⟩ => ⟨fun a => toDisc l X bk.ρ₀ c * x a, fun j hj => by
      simp only [map_mul, hj.ext]
      exact (Matrix.mulVec_smul s.W (bk.iA (bk.ev c)) fun a => j (x a)).trans (by rw [hx j hj]; rfl)⟩)
    (fun y ⟨x, hx⟩ => by
      obtain ⟨t, ht⟩ := (isUnit_l_disc l (X : bk.S) bk.ρ₀).exists_left_inv
      refine ⟨fun a => t * x a, fun j hj => ?_⟩
      have ht' := congrArg j ht
      rw [map_mul, map_natCast, map_one] at ht'
      simp only [map_mul]
      refine (Matrix.mulVec_smul s.W (j t) fun a => j (x a)).trans ?_
      rw [hx j hj]
      funext a
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, ← mul_assoc, ht', one_mul])
    (GlobalTheory.T.crystalline_disc_period_module_isClosed_lAdic l K bk τ hτ d ρ hρ s) Y1 Y' hdet hY'u
    (fun c => ⟨Z1 *ᵥ fun a => toDisc l X bk.ρ₀ (c a), fun j hj => by
      simp only [RingHom.map_mulVec]
      have e : (j ∘ fun a => toDisc l X bk.ρ₀ (c a)) = bk.iA ∘ fun a => bk.ev (c a) := funext fun a => hj.ext _
      rw [e, ← hZ1 j hj, ← Matrix.mulVec_mulVec]⟩)
    (fun y hy => by
      obtain ⟨δ, c, hδ, h⟩ := GlobalTheory.T.crystallineLattice_rational_in_columns l K bk τ hτ d ρ hρ s Y1 Z1 hdet hZ1 y hy
      exact mem_lattice bk hev Y1 m P Y' hY' hlat y δ c hδ h)
  obtain ⟨k', S', hS'⟩ := GlobalTheory.T.basis_dvd_tauPow_lPow_ainf l K bk τ hτ d ρ hρ s Y hYu hY
  have hcol : ∀ b : Fin d, ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (Y a b) := fun b =>
    (hY fun a => Y a b).2 ⟨Pi.single b 1, by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite]⟩
  have hφ := fun b => (hY _).1 (GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable l K bk τ hτ d ρ hρ s _ (hcol b))
  choose x hx using hcol
  choose c hc using hφ
  have hZ : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W * (Matrix.of fun a b => x b a).map j = Y.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (hx b j hj) a
  have hA : Y.map WittVector.frobenius = Y * (Matrix.of fun a b => c b a).map bk.ev :=
    Matrix.ext fun a b => congrFun (hc b) a
  obtain ⟨b, A', hA'⟩ := GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period l K bk τ hτ d Y S' _ k' _ hYu hS' hA
  exact ⟨⟨Y, hYu, _, GlobalTheory.T.isUnit_discBasis_crystallineLattice l K bk τ hτ d ρ hρ s Y _ k' S' hS' hZ, hZ, 0, b, _, A', hA', by
    rw [pow_zero, one_smul]; exact hA⟩⟩

end GlobalTheory.BSP.HeightEx
