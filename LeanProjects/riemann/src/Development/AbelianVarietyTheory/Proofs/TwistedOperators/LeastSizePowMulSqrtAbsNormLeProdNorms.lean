import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

noncomputable section

namespace GlobalTheory.LineBound

theorem relIndex_span_singleton {K : Type} [Field K] [NumberField K] (𝔪 𝔟 : Ideal (𝓞 K)) (a : 𝓞 K)
    (ha : a ≠ 0) (h : Ideal.span {a} = 𝔪 * 𝔟) :
    (Ideal.span {a}).toAddSubgroup.relIndex 𝔟.toAddSubgroup = Ideal.absNorm 𝔪 := by
  have hle : Ideal.span {a} ≤ 𝔟 := by rw [h, mul_comm]; exact Ideal.mul_le_left
  have h1 := AddSubgroup.relIndex_mul_index
    (show (Ideal.span {a}).toAddSubgroup ≤ 𝔟.toAddSubgroup from hle)
  have h2 : (Ideal.span {a}).toAddSubgroup.index = Ideal.absNorm 𝔪 * Ideal.absNorm 𝔟 := by
    rw [← map_mul, ← h, Ideal.absNorm_apply]; rfl
  have h3 : 𝔟.toAddSubgroup.index = Ideal.absNorm 𝔟 := by rw [Ideal.absNorm_apply]; rfl
  have hb : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h
    exact ha h
  have hb0 : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [h2, h3] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb0) h1

theorem ht_nonneg {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : 0 ≤ ht b X L := by
  unfold ht
  have hc : 0 ≤ Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    unfold Formalism.F.covol
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_rfl
  exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _)) hc

theorem size_nonneg {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : 0 ≤ size b X L :=
  Real.rpow_nonneg (ht_nonneg b X L) _

end GlobalTheory.LineBound

namespace GlobalTheory.LineBound

theorem least_pow_mul_sqrt_absNorm_le_prod : ∀ (I : AutInst) (x : I.GA) (𝔪 : Ideal (𝓞 I.E)), 𝔪 ≠ ⊥ →
    ∀ w ∈ 𝔪 • lamX I x, w ≠ 0 → least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪) ≤
      ∏ v, Real.sqrt (∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2) := by
  intro I x 𝔪 h𝔪 w hw hw0
  obtain ⟨hTC, hf, -, hbij, hX0⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  haveI := hTC
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hX0 v).1
  obtain ⟨a, ha𝔪, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  obtain ⟨𝔟, h𝔟⟩ := (Ideal.dvd_span_singleton).2 ha𝔪
  have haE : (a : I.E) ≠ 0 := by exact_mod_cast ha0
  set u : Fin I.n → I.E := (a : I.E)⁻¹ • w with hu
  set ℓ : 𝓞 I.E →ₗ[𝓞 I.E] (Fin I.n → I.E) := LinearMap.toSpanSingleton (𝓞 I.E) _ u with hℓ
  have hℓapp : ∀ c : 𝓞 I.E, ℓ c = (c : I.E) • u := fun c => by
    rw [hℓ, LinearMap.toSpanSingleton_apply]
    exact (algebraMap_smul I.E c u).symm
  have hℓa : ℓ a = w := by rw [hℓapp, hu, smul_smul, mul_inv_cancel₀ haE, one_smul]
  have hu0 : u ≠ 0 := by
    rw [hu]; exact smul_ne_zero (inv_ne_zero haE) hw0
  have hinj : Function.Injective ℓ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hℓapp] at hc
    have : (c : I.E) = 0 := (smul_eq_zero.1 hc).resolve_right hu0
    exact_mod_cast this
  set R : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.map ℓ 𝔟 with hR
  have hab : a ∈ 𝔟 := by
    have : Ideal.span {a} ≤ 𝔟 := by rw [h𝔟, mul_comm]; exact Ideal.mul_le_left
    exact this (Ideal.mem_span_singleton_self a)
  have hwR : w ∈ R := ⟨a, hab, hℓa⟩

  have hRle : R ≤ lamX I x := by
    have key : ∀ y ∈ 𝔪 • lamX I x, ∀ c ∈ 𝔟, ((c : I.E) * (a : I.E)⁻¹) • y ∈ lamX I x := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro m hm l hl c hc
        have hmc : m * c ∈ Ideal.span {a} := by rw [h𝔟]; exact Ideal.mul_mem_mul hm hc
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hmc
        have hdE : (d : I.E) = (c : I.E) * (a : I.E)⁻¹ * (m : I.E) := by
          have : (d : I.E) * (a : I.E) = (m : I.E) * (c : I.E) := by exact_mod_cast hd
          field_simp
          linear_combination this
        have : ((c : I.E) * (a : I.E)⁻¹) • (m • l) = d • l := by
          rw [← algebraMap_smul I.E m l, smul_smul, ← algebraMap_smul I.E d l]
          congr 1
          exact hdE.symm
        rw [this]
        exact (lamX I x).smul_mem d hl
      · intro y z hy hz c hc
        rw [smul_add]
        exact add_mem (hy c hc) (hz c hc)
    rintro y ⟨c, hc, rfl⟩
    rw [hℓapp, hu, smul_smul]
    exact key w hw c hc
  have hRfg : R.FG := (IsNoetherian.noetherian 𝔟).map ℓ
  have hR0 : R ≠ ⊥ := fun h => hw0 ((Submodule.mem_bot _).1 (h ▸ hwR))
  have hrange : Set.range (fun _ : Fin 1 => w) = {w} := Set.range_const
  have hli : LinearIndependent I.E (fun _ : Fin 1 => w) := LinearIndependent.of_subsingleton 0 hw0
  have hspanw : Submodule.span (𝓞 I.E) {w} = Submodule.map ℓ (Ideal.span {a}) := by
    rw [Ideal.span, Submodule.map_span, Set.image_singleton, hℓa]
  have hwle : Submodule.span (𝓞 I.E) (Set.range fun _ : Fin 1 => w) ≤ R := by
    rw [hrange, Submodule.span_le, Set.singleton_subset_iff]; exact hwR
  have hrk : rkK R = 1 := by
    unfold rkK
    have : Submodule.span I.E (R : Set (Fin I.n → I.E)) = Submodule.span I.E {w} := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro y ⟨c, -, rfl⟩
        rw [hℓapp, hu, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span hwR
    rw [this, finrank_span_singleton hw0]
  have hidx : (Submodule.span (𝓞 I.E) (Set.range fun _ : Fin 1 => w)).toAddSubgroup.relIndex
      R.toAddSubgroup = Ideal.absNorm 𝔪 := by
    rw [hrange, hspanw, hR, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact relIndex_span_singleton 𝔪 𝔟 a ha0 h𝔟
  obtain ⟨hG1, hG2⟩ := htGram I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) hX 1 (fun _ => w) hli
  have hht := hG2 R hRfg hwle (by rw [hrk])
  rw [hidx, hG1] at hht

  set g : InfinitePlace I.F → ℝ := fun v =>
    ∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2 with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => Finset.sum_nonneg fun i _ => by positivity
  have hdet : ∀ w' : InfinitePlace I.E,
      (gramPl (bas I) (frm I x) w' (fun _ : Fin 1 => w)).det.re = g (w'.comap (algebraMap I.F I.E)) := by
    intro w'
    rw [GlobalTheory.FlagMeas.SizeMove.norm_det_gram, Matrix.det_fin_one, Matrix.of_apply]
    have hU : uMat (x.1 (w'.comap (algebraMap I.F I.E)))⁻¹ = (uMat (x.1 (w'.comap (algebraMap I.F I.E))))⁻¹ := by
      simp [uMat]
    rw [hg]
    simp only [hU, GlobalTheory.FlagMeas.SizeMove.crd]
    set z := (uMat (x.1 (w'.comap (algebraMap I.F I.E))))⁻¹ *ᵥ
      ((I.P (w'.comap (algebraMap I.F I.E)))⁻¹ *ᵥ fun l => I.φ (w'.comap (algebraMap I.F I.E)) (w l))
    have : star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  have hprod : ∏ w' : InfinitePlace I.E, (gramPl (bas I) (frm I x) w' (fun _ : Fin 1 => w)).det.re =
      ∏ v, g v := by
    simp only [hdet]
    exact Fintype.prod_bijective _ hbij _ _ (fun _ => rfl)
  rw [hprod] at hht

  have hbdd : BddBelow {t | ∃ S : Submodule (𝓞 I.E) (Fin I.n → I.E), S ≤ lamX I x ∧ S ≠ ⊥ ∧
      size (bas I) (frm I x) S = t} := ⟨0, by rintro t ⟨S, -, -, rfl⟩; exact size_nonneg _ _ _⟩
  have hle : least I x ≤ size (bas I) (frm I x) R := csInf_le hbdd ⟨R, hRle, hR0, rfl⟩
  have h0 : 0 ≤ least I x := le_csInf ⟨_, ⟨R, hRle, hR0, rfl⟩⟩ (by rintro t ⟨S, -, -, rfl⟩; exact size_nonneg _ _ _)
  have hfpos : 0 < nPl I.E := Fintype.card_pos
  have hsz : size (bas I) (frm I x) R ^ (2 * I.f) = ht (bas I) (frm I x) R := by
    unfold size
    rw [hrk, ← Real.rpow_natCast, ← Real.rpow_mul (ht_nonneg _ _ _), ← hf]
    have : (1 : ℝ) / (2 * (nPl I.E : ℝ) * ((1 : ℕ) : ℝ)) * ((2 * nPl I.E : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hN0 : (0 : ℝ) ≤ Ideal.absNorm 𝔪 := Nat.cast_nonneg _
  have hsq : (least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪)) ^ 2 ≤
      (∏ v, Real.sqrt (g v)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN0, ← Finset.prod_pow]
    simp only [fun v => Real.sq_sqrt (hg0 v)]
    rw [← hht, ← pow_mul, mul_comm I.f 2, ← hsz]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hle _) hN0
  exact (pow_le_pow_iff_left₀ (by positivity) (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)
    two_ne_zero).1 hsq

end GlobalTheory.LineBound
