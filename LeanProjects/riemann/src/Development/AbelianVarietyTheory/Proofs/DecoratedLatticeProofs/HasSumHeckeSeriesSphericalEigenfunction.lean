import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesBorelSphericalIntegralCosetsStatement
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.HeckeShift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev IntCos (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :=
  {c : GL (Fin n) k ⧸ KO k (Fin n) // ∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k]}

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem int_mul {A B : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j : Fin n) :
    (A * B) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

theorem ord_det_of_mem_KO {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det κ) = 0 := by
  obtain ⟨g, rfl⟩ := hκ
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem out_smul (y : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    ∃ κ ∈ KO k (Fin n), ((y • c).out : GL (Fin n) k) = y * c.out * κ := by
  refine ⟨(y * c.out)⁻¹ * (y • c).out, ?_, by group⟩
  have h : (QuotientGroup.mk (y * c.out) : GL (Fin n) k ⧸ KO k (Fin n)) = y • c := by
    conv_rhs => rw [← QuotientGroup.out_eq' c]
    rfl
  exact QuotientGroup.eq.1 (h.trans (QuotientGroup.out_eq' _).symm)

theorem int_out_smul {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) (c : IntCos k n) (i j : Fin n) :
    ((y • c.1).out : GL (Fin n) k).1 i j ∈ 𝒪[k] := by
  obtain ⟨κ, hκ, e⟩ := out_smul y c.1
  rw [e, Units.val_mul, Units.val_mul]
  exact int_mul (int_mul ((SplitFlip.mem_KO_iff y).1 hy).1 c.2) ((SplitFlip.mem_KO_iff κ).1 hκ).1 i j

def smulEquiv {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) : IntCos k n ≃ IntCos k n where
  toFun c := ⟨y • c.1, int_out_smul hy c⟩
  invFun c := ⟨y⁻¹ • c.1, int_out_smul (inv_mem hy) c⟩
  left_inv c := Subtype.ext (inv_smul_smul y c.1)
  right_inv c := Subtype.ext (smul_inv_smul y c.1)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem diag_mul_upper {A B : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA i j h, zero_mul]
    · rw [hB j i h, mul_zero]
  · simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem diag_ne_zero {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (i : Fin n) : (b : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
  have h := Matrix.det_of_upperTriangular (M := (b : Matrix (Fin n) (Fin n) k)) (fun i j h => (mem_borel k).1 hb i j h)
  have hd : (b : Matrix (Fin n) (Fin n) k).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero b
  rw [h] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

end GlobalTheory.HeckeShift

namespace GlobalTheory.HeckeShift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def diagU {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (i : Fin n) : kˣ := Units.mk0 _ (diag_ne_zero hb i)

theorem exists_borel_mul (h : GL (Fin n) k) : ∃ b ∈ borel k (Fin n), ∃ x ∈ KO k (Fin n), h = b * x := by
  obtain ⟨b, hbT, x, hx, e⟩ := iwasawa_blockTriangular k (Fin n) (fun i => (i : ℕ)) h
  exact ⟨b, (mem_borel k).2 fun i j hij => hbT (show (j : ℕ) < i from hij), x, hx, e⟩

theorem sph_borel_mul {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (h : GL (Fin n) k) :
    φ (b * h) = (∏ i, γ i ^ ord k (diagU hb i)) * φ h := by
  obtain ⟨b', hb', x, hx, rfl⟩ := exists_borel_mul h
  have hbb : b * b' ∈ borel k (Fin n) := mul_mem hb hb'
  rw [← mul_assoc, hφ.1 _ x hx, hφ.1 _ x hx, hφ.2 b' hb' (diagU hb') fun i => rfl,
    hφ.2 (b * b') hbb (fun i => diagU hb i * diagU hb' i) fun i => ?_, ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [ord_mul, zpow_add₀ (hγ i)]
  · rw [Units.val_mul, Units.val_mul]
    exact diag_mul_upper ((mem_borel k).1 hb) ((mem_borel k).1 hb') i

end GlobalTheory.HeckeShift

namespace GlobalTheory.HeckeShift

theorem hasSum_hecke_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) → ∀ g : GL (Fin n) k, HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ (g * c.1.out)) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * φ g) := by
  intro k _ _ _ _ n γ φ hφ hγ X hX g
  obtain ⟨b, hb, x, hx, rfl⟩ := exists_borel_mul g
  have hI := (GlobalTheory.T.hasSum_heckeSeries_borelSpherical_integralCosets k n γ φ hφ X hX).mul_left (∏ i, γ i ^ ord k (diagU hb i))
  have key : ∀ c : IntCos k n,
      X ^ (ord k (Matrix.GeneralLinearGroup.det (smulEquiv (inv_mem hx) c).1.out)).toNat *
          φ (b * x * (smulEquiv (inv_mem hx) c).1.out) =
        (∏ i, γ i ^ ord k (diagU hb i)) * (X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) := by
    intro c
    obtain ⟨κ, hκ, e⟩ := out_smul x⁻¹ c.1
    have e' : (smulEquiv (inv_mem hx) c).1.out = x⁻¹ * c.1.out * κ := e
    have hd : ord k (Matrix.GeneralLinearGroup.det (x⁻¹ * c.1.out * κ)) =
        ord k (Matrix.GeneralLinearGroup.det c.1.out) := by
      rw [map_mul, map_mul, ord_mul, ord_mul, ord_det_of_mem_KO (inv_mem hx), ord_det_of_mem_KO hκ]
      ring
    rw [e', hd, show b * x * (x⁻¹ * c.1.out * κ) = b * c.1.out * κ by group, hφ.1 _ κ hκ,
      sph_borel_mul hφ hγ hb]
    ring
  have h1 : HasSum ((fun c : IntCos k n => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
      φ (b * x * c.1.out)) ∘ smulEquiv (inv_mem hx))
      ((∏ i, γ i ^ ord k (diagU hb i)) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) := by
    have hf : ((fun c : IntCos k n => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
        φ (b * x * c.1.out)) ∘ smulEquiv (inv_mem hx)) = fun c : IntCos k n => (∏ i, γ i ^ ord k (diagU hb i)) *
          (X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) := funext key
    rw [hf]
    exact hI
  have h2 := (Equiv.hasSum_iff (smulEquiv (inv_mem hx))).1 h1
  rw [hφ.1 b x hx, hφ.2 b hb (diagU hb) fun i => rfl, mul_comm]
  exact h2

end GlobalTheory.HeckeShift
