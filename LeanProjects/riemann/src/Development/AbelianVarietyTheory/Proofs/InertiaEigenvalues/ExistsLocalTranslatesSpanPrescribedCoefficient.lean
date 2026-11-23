import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef.Cons

open GlobalTheory.SplitScalar

variable {D : D7}

theorem isHalf_add {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u + v) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_neg {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := fun i j => by
  simp only [Matrix.neg_apply, mul_neg, hu i j]

theorem isHalf_sub {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u - v) := by
  rw [sub_eq_add_neg]; exact GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hu (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg hv)

theorem isHalf_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem isHalf_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := fun i j => by
  simp only [Matrix.zero_apply, mul_zero]

theorem isHalf_place_of_left {m n : ℕ} {a : AE D} (ha : a * cA D a = 0) {u : Mx D m n} (hu : IsHalf a u) :
    IsHalf (a + cA D a) u := fun i j => by
  have h : cA D a * u i j = 0 := by rw [← hu i j, ← mul_assoc, mul_comm (cA D a) a, ha, zero_mul]
  rw [add_mul, h, add_zero, hu i j]

theorem isHalf_place_of_right {m n : ℕ} {a : AE D} (ha : a * cA D a = 0) {u : Mx D m n}
    (hu : IsHalf (cA D a) u) : IsHalf (a + cA D a) u := fun i j => by
  have h : a * u i j = 0 := by rw [← hu i j, ← mul_assoc, ha, zero_mul]
  rw [add_mul, h, zero_add, hu i j]

theorem heisO_mem_locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ)
    {h : WO S T → ℂ} (hh : h ∈ locSpan ψ S T a f) {w : WO S T} (hw : IsHalf (a + cA D a) w) :
    heisO ψ S T w h ∈ locSpan ψ S T a f := by
  induction hh using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, hu, rfl⟩ := hp
    rw [heisO_heisO]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w + u, GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hw hu, rfl⟩)
  | zero =>
    rw [show heisO ψ S T w 0 = 0 from (heisL ψ S T w).map_zero]
    exact Submodule.zero_mem _
  | add p q _ _ hp hq =>
    rw [show heisO ψ S T w (p + q) = heisO ψ S T w p + heisO ψ S T w q from (heisL ψ S T w).map_add p q]
    exact Submodule.add_mem _ hp hq
  | smul c p _ hp =>
    rw [heisO_smul]
    exact Submodule.smul_mem _ _ hp

theorem self_mem_locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) :
    f ∈ locSpan ψ S T a f :=
  Submodule.subset_span ⟨0, GlobalTheory.DownLift.SplitCoef.Cons.isHalf_zero _, (heisO_zero ψ S T f).symm⟩

end GlobalTheory.DownLift.SplitCoef.Cons

open GlobalTheory.SplitScalar GlobalTheory.DownLift.SplitCoef.Cons in

theorem GlobalTheory.DownLift.SplitCoef.exists_locSpan_coef_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : WO S T → ℂ, IsSBHalf a (latH S T ΛS ΛT) Φ → ∀ x₁, IsHalf a x₁ → ∃ f' ∈ locSpan ψ S T a f, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f') = Φ x * ℓ (heisO ψ S T x₁ f) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha f hf Φ hΦ x₁ hx₁
  classical
  obtain ⟨⟨k₀, hk₀, hinv, hsupp⟩, -, -⟩ := GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform D ψ S T hψ ΛS ΛT hS hT a ha f hf
  obtain ⟨hΦs, kΦ, hkΦ, hΦinv, hΦsupp⟩ := hΦ
  obtain ⟨k₁, hk₁, hx₁Λ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS.1 hT.1 x₁ (half_fin ha hx₁)
  obtain ⟨k, hk, hfix, hΦk, hkx₁, hk0, hkΦ'⟩ : ∃ k : ℕ, 0 < k ∧
      (∀ u ∈ latH S T ΛS ΛT, IsHalf a u → heisO ψ S T (k • u) f = f) ∧
      (∀ u ∈ latH S T ΛS ΛT, IsHalf a u → ∀ t, Φ (t + k • u) = Φ t) ∧
      k • x₁ ∈ latH S T ΛS ΛT ∧
      (∀ y, k₀ • y ∈ latH S T ΛS ΛT → k • y ∈ latH S T ΛS ΛT) ∧
      (∀ y, kΦ • y ∈ latH S T ΛS ΛT → k • y ∈ latH S T ΛS ΛT) := by
    refine ⟨k₀ * kΦ * k₁, by positivity, fun u hu hua => ?_, fun u hu hua t => ?_, ?_, fun y hy => ?_,
      fun y hy => ?_⟩
    · rw [mul_assoc, mul_smul]
      exact hinv _ (AddSubgroup.nsmul_mem _ hu _) (Or.inl (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua _))
    · rw [show k₀ * kΦ * k₁ = kΦ * (k₀ * k₁) by ring, mul_smul]
      exact hΦinv _ (AddSubgroup.nsmul_mem _ hu _) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua _) t
    · rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ hx₁Λ _
    · rw [show k₀ * kΦ * k₁ = (kΦ * k₁) * k₀ by ring, mul_smul]
      exact AddSubgroup.nsmul_mem _ hy _
    · rw [show k₀ * kΦ * k₁ = (k₀ * k₁) * kΦ by ring, mul_smul]
      exact AddSubgroup.nsmul_mem _ hy _
  have hca : IsSplitIdem D (cA D a) := isSplitIdem_conj ha
  have hcaa : cA D a * a = 0 := by rw [mul_comm]; exact ha.2.1
  obtain ⟨Y, hYne, hY, -, hYsum⟩ :=
    GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ ΛS ΛT hS hT a ha.1 (infPart_splitIdem ha) k hk
  obtain ⟨X, -, hX, hXu, -⟩ :=
    GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ ΛS ΛT hS hT (cA D a) hca.1 (infPart_splitIdem hca) k hk
  simp only [GlobalTheory.DualPairCheck.cA_cA] at hX hXu
  obtain ⟨n, hn⟩ : ∃ n, n = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x₁ f) := ⟨_, rfl⟩

  have hA : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x n) =
      if (∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) then (Y.card : ℂ) * ℓ (heisO ψ S T x₁ f) else 0 := by
    intro ℓ hℓ x hx
    have hg : IsThetaFunO ψ S T (heisO ψ S T x₁ f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x₁
    have hxg : IsThetaFunO ψ S T (heisO ψ S T x (heisO ψ S T x₁ f)) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg x
    have h1 : ℓ (heisO ψ S T x n) =
        (∑ y ∈ Y, ψ (symplO S T x y)) * ℓ (heisO ψ S T x (heisO ψ S T x₁ f)) := by
      rw [hn, heisO_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [heisO_comm, ℓ.map_smul, smul_eq_mul, hℓ y (hY y hy).1 _ hxg]
    have h2 : heisO ψ S T x (heisO ψ S T x₁ f) = heisO ψ S T (x + x₁) f :=
      (heisO_add_of_orth ψ S T (symplO_eq_zero S T hcaa hx hx₁) f).symm
    rw [h1, h2]
    split_ifs with hP
    · obtain ⟨u, hu, hua, rfl⟩ := hP
      have hkx : k • (k • u) ∈ latH S T ΛS ΛT := AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hu _) _
      rw [Finset.sum_congr rfl fun y hy => (hYsum (k • u) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua k) hkx).1 ⟨u, hu, hua, rfl⟩ y hy,
        Finset.sum_const, nsmul_eq_mul, mul_one]
      have horth : symplO S T x₁ (k • u) = 0 := symplO_eq_zero S T hcaa hx₁ (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua k)
      rw [add_comm, heisO_add_of_orth ψ S T horth f, hfix u hu hua]
    · by_cases hkx : k • x ∈ latH S T ΛS ΛT
      · rw [(hYsum x hx hkx).2 hP, zero_mul]
      · have h3 : ℓ (heisO ψ S T (x + x₁) f) = 0 := by
          by_contra hne
          apply hkx
          have h4 := hk0 _ (hsupp ℓ hℓ (x + x₁) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hx hx₁) hne)
          have h5 : k • x = k • (x + x₁) - k • x₁ := by rw [nsmul_add, add_sub_cancel_right]
          rw [h5]
          exact AddSubgroup.sub_mem _ h4 hkx₁
        rw [h3, mul_zero]
  refine ⟨((Y.card : ℂ)⁻¹) • ∑ z ∈ X, Φ z • heisO ψ S T (-z) n, ?_, ?_⟩
  · have hg : heisO ψ S T x₁ f ∈ locSpan ψ S T a f :=
      heisO_mem_locSpan ψ S T a f (self_mem_locSpan ψ S T a f) (isHalf_place_of_left ha.2.1 hx₁)
    have hnm : n ∈ locSpan ψ S T a f := by
      rw [hn]
      exact Submodule.sum_mem _ fun y hy =>
        heisO_mem_locSpan ψ S T a f hg (isHalf_place_of_right ha.2.1 (hY y hy).1)
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _
      (heisO_mem_locSpan ψ S T a f hnm (isHalf_place_of_left ha.2.1 (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg (hX z hz).1))))
  · intro ℓ hℓ x hx
    have hc : (Y.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hYne.card_pos.ne'
    rw [heisO_smul, heisO_sum, ℓ.map_smul, map_sum, smul_eq_mul]
    have hterm : ∀ z ∈ X, ℓ (heisO ψ S T x (Φ z • heisO ψ S T (-z) n)) = Φ x *
        (if (∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x - z = k • u) then (Y.card : ℂ) * ℓ (heisO ψ S T x₁ f)
          else 0) := by
      intro z hz
      have hzh := (hX z hz).1
      rw [heisO_smul, ℓ.map_smul, smul_eq_mul,
        ← heisO_add_of_orth ψ S T (symplO_eq_zero S T hcaa hx (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg hzh)) n, ← sub_eq_add_neg,
        hA ℓ hℓ (x - z) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_sub hx hzh)]
      split_ifs with hP
      · obtain ⟨u, hu, hua, hxu⟩ := hP
        rw [(sub_eq_iff_eq_add').1 hxu, hΦk u hu hua]
      · rw [mul_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    by_cases hΦx : Φ x = 0
    · rw [hΦx, zero_mul, mul_zero, zero_mul]
    · obtain ⟨z₀, ⟨hz₀, hP₀⟩, huniq⟩ := hXu x hx (hkΦ' x (hΦsupp x hΦx))
      rw [Finset.sum_eq_single_of_mem z₀ hz₀ (fun z hz hne => if_neg fun hP => hne (huniq z ⟨hz, hP⟩)),
        if_pos hP₀]
      field_simp

end
