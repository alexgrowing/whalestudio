import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section
namespace GlobalTheory.DownLift.SplitRel
open GlobalTheory.SplitScalar
variable {D : D7}

theorem psi_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (z : AF D.host.F) : ψ z ≠ 0 := by
  intro h
  have h1 := AddChar.map_zero_eq_one ψ
  rw [← add_neg_cancel z, AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem idem_E {a E : AE D} (ha : IsSplitIdem D a) (hE : a + cA D a = E) : E * E = E := by
  obtain ⟨h1, h2, -⟩ := ha
  have h3 : cA D a * cA D a = cA D a := by rw [← map_mul, h1]
  have h4 : cA D a * a = 0 := by rw [mul_comm, h2]
  rw [← hE]; linear_combination h1 + h3 + h2 + h4

theorem one_sub_mul_self {a E : AE D} (ha : IsSplitIdem D a) (hE : a + cA D a = E) : (1 - E) * a = 0 := by
  obtain ⟨h1, h2, -⟩ := ha
  rw [← hE]; linear_combination (-1 : AE D) * h1 - h2

theorem one_sub_mul_conj {a E : AE D} (ha : IsSplitIdem D a) (hE : a + cA D a = E) : (1 - E) * cA D a = 0 := by
  obtain ⟨h1, h2, -⟩ := ha
  have h3 : cA D a * cA D a = cA D a := by rw [← map_mul, h1]
  rw [← hE]; linear_combination (-1 : AE D) * h3 - h2

theorem cA_E {a E : AE D} (hE : a + cA D a = E) : cA D E = E := by
  rw [← hE, map_add, GlobalTheory.DualPairCheck.cA_cA, add_comm]

theorem smul_half_zero {m n : ℕ} {a E : AE D} (h : (1 - E) * a = 0) {y : Mx D m n} (hy : IsHalf a y) :
    (1 - E) • y = 0 := by
  ext i j
  show (1 - E) * y i j = 0
  rw [← hy i j, ← mul_assoc, h, zero_mul]

theorem half_conj {m n : ℕ} {a : AE D} (ha : IsSplitIdem D a) (u : Mx D m n) : IsHalf (cA D a) (cA D a • u) := by
  intro i j
  show cA D a * (cA D a * u i j) = cA D a * u i j
  rw [← mul_assoc, ← map_mul, ha.1]

theorem half_add {m n : ℕ} {a : AE D} (ha : IsSplitIdem D a) {x : Mx D m n} (hx : IsHalf a x) (u : Mx D m n) :
    IsHalf a (x + a • u) := by
  intro i j
  show a * (x i j + a * u i j) = x i j + a * u i j
  rw [mul_add, hx i j, ← mul_assoc, ha.1]

theorem heisO_off_comm (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {E : AE D} (hcE : cA D E = E) (u y : WO S T)
    (hy : (1 - E) • y = 0) (f : WO S T → ℂ) :
    heisO ψ S T ((1 - E) • u) (heisO ψ S T y f) = heisO ψ S T y (heisO ψ S T ((1 - E) • u) f) := by
  rw [heisO_comm, symplO_smul, map_sub, map_one, hcE, hy, symplO_zero_right, AddChar.map_zero_eq_one, one_smul]

theorem invForm_comp {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {a E : AE D}
    (ha : IsSplitIdem D a) (hE : a + cA D a = E) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T a ℓ) (u : WO S T) :
    InvForm ψ S T a (ℓ ∘ₗ heisL ψ S T ((1 - E) • u)) := by
  intro w hw f hf
  simp only [LinearMap.comp_apply, heisL_apply]
  rw [heisO_off_comm ψ (cA_E hE) u w (smul_half_zero (one_sub_mul_conj ha hE) hw)]
  exact hℓ w hw _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _)

theorem shape_ratio {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {a : AE D} {Φ g : WO S T → ℂ}
    (hs : HasShape ψ S T a Φ g) {x₀ : WO S T} (hx₀ : IsHalf a x₀) (h0 : Φ x₀ ≠ 0) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ}
    (hℓ : InvForm ψ S T a ℓ) {y : WO S T} (hy : IsHalf a y) :
    ℓ (heisO ψ S T y g) = Φ y * (Φ x₀)⁻¹ * ℓ (heisO ψ S T x₀ g) := by
  obtain ⟨c, hc⟩ := hs ℓ hℓ
  rw [hc y hy, hc x₀ hx₀]
  have : (Φ x₀)⁻¹ * Φ x₀ = 1 := inv_mul_cancel₀ h0
  linear_combination (-(c * Φ y)) * this

theorem shape_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {a E : AE D}
    (ha : IsSplitIdem D a) (hE : a + cA D a = E) {Φ g : WO S T → ℂ} (hs : HasShape ψ S T a Φ g) {x₀ : WO S T}
    (hx₀ : IsHalf a x₀) (h0 : Φ x₀ ≠ 0) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T a ℓ) (u : WO S T)
    {y : WO S T} (hy : IsHalf a y) :
    ℓ (heisO ψ S T y (heisO ψ S T ((1 - E) • u) g)) =
      Φ y * (Φ x₀)⁻¹ * ℓ (heisO ψ S T x₀ (heisO ψ S T ((1 - E) • u) g)) := by
  have h1 := shape_ratio hs hx₀ h0 (invForm_comp hψ ha hE hℓ u) hy
  simp only [LinearMap.comp_apply, heisL_apply] at h1
  rw [← heisO_off_comm ψ (cA_E hE) u y (smul_half_zero (one_sub_mul_self ha hE) hy),
    ← heisO_off_comm ψ (cA_E hE) u x₀ (smul_half_zero (one_sub_mul_self ha hE) hx₀)]
  exact h1

theorem heisO_factor (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {a E : AE D} (hE : a + cA D a = E) (x u : WO S T) :
    ∃ p : ℂ, ∀ g, heisO ψ S T x (heisO ψ S T u g) =
      p • heisO ψ S T (cA D a • u) (heisO ψ S T (x + a • u) (heisO ψ S T ((1 - E) • u) g)) := by
  have hsum : cA D a • u + ((x + a • u) + (1 - E) • u) = x + u := by
    rw [← hE]; ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  obtain ⟨q, hq0, hq⟩ : ∃ q : ℂ, q ≠ 0 ∧ ∀ g, heisO ψ S T (cA D a • u)
      (heisO ψ S T (x + a • u) (heisO ψ S T ((1 - E) • u) g)) = q • heisO ψ S T (x + u) g := by
    refine ⟨ψ (symplOH S T (x + a • u) ((1 - E) • u)) * ψ (symplOH S T (cA D a • u) ((x + a • u) + (1 - E) • u)),
      mul_ne_zero (psi_ne_zero _ _) (psi_ne_zero _ _), fun g => ?_⟩
    rw [heisO_heisO ψ S T (x + a • u), heisO_smul, heisO_heisO, hsum, smul_smul]
  refine ⟨ψ (symplOH S T x u) * q⁻¹, fun g => ?_⟩
  rw [hq, smul_smul, inv_mul_cancel_right₀ hq0, heisO_heisO]

theorem form_sum (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (y : WO S T)
    (c : WO S T →₀ ℂ) (F : WO S T → ℂ → (WO S T → ℂ)) :
    ℓ (heisO ψ S T y (c.sum F)) = c.sum fun u z => ℓ (heisO ψ S T y (F u z)) := by
  rw [← heisL_apply, map_finsuppSum, map_finsuppSum]
  rfl

theorem sum_map_single (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (c : WO S T →₀ ℂ) (k : WO S T → ℂ)
    (τ : WO S T → WO S T) (g : WO S T → ℂ) :
    ((c.sum fun u z => Finsupp.single (τ u) (z * k u)).sum fun u z => z • heisO ψ S T u g) =
      c.sum fun u z => (z * k u) • heisO ψ S T (τ u) g := by
  rw [Finsupp.sum_sum_index (h := fun u z => z • heisO ψ S T u g) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  exact Finsupp.sum_congr fun u _ => Finsupp.sum_single_index (zero_smul ℂ _)

theorem mem_support_sum_single {X : Type} (c : X →₀ ℂ) (k : X → ℂ) (τ : X → X) {u : X}
    (hu : u ∈ (c.sum fun u z => Finsupp.single (τ u) (z * k u)).support) : ∃ u₀ ∈ c.support, u = τ u₀ := by
  classical
  obtain ⟨u₀, h₀, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hu)
  exact ⟨u₀, h₀, Finset.mem_singleton.1 (Finsupp.support_single_subset h)⟩

theorem rel_extend {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {a E : AE D}
    (ha : IsSplitIdem D a) (hE : a + cA D a = E) {Φ g₁ g₂ : WO S T → ℂ}
    (ht₁ : IsThetaFunO ψ S T g₁) (ht₂ : IsThetaFunO ψ S T g₂)
    (hs₁ : HasShape ψ S T a Φ g₁) (hs₂ : HasShape ψ S T a Φ g₂) (Q Q' : WO S T → Prop)
    (hQ : ∀ u, Q' u → Q ((1 - E) • u))
    (hrel : ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, Q u) → (c.sum fun u z => z • heisO ψ S T u g₁) = 0 →
      (c.sum fun u z => z • heisO ψ S T u g₂) = 0)
    (c : WO S T →₀ ℂ) (hc : ∀ u ∈ c.support, Q' u) (h1 : (c.sum fun u z => z • heisO ψ S T u g₁) = 0) :
    (c.sum fun u z => z • heisO ψ S T u g₂) = 0 := by
  have hsep := GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions D ψ S T hψ a ha
  have hz : ∀ x, heisO ψ S T x (0 : WO S T → ℂ) = 0 := fun x => (heisL ψ S T x).map_zero
  have hlc : ∀ (k : WO S T → ℂ) (τ : WO S T → WO S T) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (c.sum fun u z => (z * k u) • heisO ψ S T (τ u) g) := fun k τ g hg =>
    theta_sum c.support _ g hg fun u _ => theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg _)
  have hlc0 : ∀ g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (c.sum fun u z => z • heisO ψ S T u g) := fun g hg =>
    theta_sum c.support _ g hg fun u _ => theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg _)
  by_cases hΦ : ∀ x, IsHalf a x → Φ x = 0
  · have hg2 : g₂ = 0 := hsep g₂ ht₂ fun ℓ hℓ x hx => by
      obtain ⟨k, hk⟩ := hs₂ ℓ hℓ
      rw [hk x hx, hΦ x hx, mul_zero]
    subst hg2
    unfold Finsupp.sum
    refine Finset.sum_eq_zero fun u _ => ?_
    show c u • heisO ψ S T u 0 = 0
    rw [hz, smul_zero]
  push_neg at hΦ
  obtain ⟨x₀, hx₀, h0⟩ := hΦ
  choose p hp using fun x u => heisO_factor ψ S T hE x u
  have key : ∀ g, IsThetaFunO ψ S T g → HasShape ψ S T a Φ g → ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
      ℓ (heisO ψ S T x (c.sum fun u z => z • heisO ψ S T u g)) =
        ℓ (heisO ψ S T x₀ (c.sum fun u z => (z * (p x u * Φ (x + a • u) * (Φ x₀)⁻¹)) •
          heisO ψ S T ((1 - E) • u) g)) := by
    intro g hg hsg ℓ hℓ x hx
    rw [form_sum, form_sum]
    refine Finsupp.sum_congr fun u _ => ?_
    have ht : IsThetaFunO ψ S T (heisO ψ S T (x + a • u) (heisO ψ S T ((1 - E) • u) g)) :=
      GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg _) _
    rw [heisO_smul, heisO_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hp x u g, map_smul,
      smul_eq_mul, hℓ _ (half_conj ha u) _ ht, shape_off hψ ha hE hsg hx₀ h0 hℓ u (half_add ha hx u)]
    ring
  have shp : ∀ g, HasShape ψ S T a Φ g → ∀ ℓ, InvForm ψ S T a ℓ → ∀ (k : WO S T → ℂ) y, IsHalf a y →
      ℓ (heisO ψ S T y (c.sum fun u z => (z * k u) • heisO ψ S T ((1 - E) • u) g)) =
        Φ y * (Φ x₀)⁻¹ * ℓ (heisO ψ S T x₀ (c.sum fun u z => (z * k u) • heisO ψ S T ((1 - E) • u) g)) := by
    intro g hsg ℓ hℓ k y hy
    rw [form_sum, form_sum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun u _ => ?_
    rw [heisO_smul, heisO_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      shape_off hψ ha hE hsg hx₀ h0 hℓ u hy]
    ring
  have hA : ∀ x, IsHalf a x → (c.sum fun u z => (z * (p x u * Φ (x + a • u) * (Φ x₀)⁻¹)) •
      heisO ψ S T ((1 - E) • u) g₁) = 0 := by
    intro x hx
    refine hsep _ (hlc _ _ g₁ ht₁) fun ℓ hℓ y hy => ?_
    rw [shp g₁ hs₁ ℓ hℓ _ y hy, ← key g₁ ht₁ hs₁ ℓ hℓ x hx, h1, hz, map_zero, mul_zero]
  have hB : ∀ x, IsHalf a x → (c.sum fun u z => (z * (p x u * Φ (x + a • u) * (Φ x₀)⁻¹)) •
      heisO ψ S T ((1 - E) • u) g₂) = 0 := by
    intro x hx
    have h := hrel (c.sum fun u z => Finsupp.single ((1 - E) • u) (z * (p x u * Φ (x + a • u) * (Φ x₀)⁻¹)))
      (fun u hu => by
        obtain ⟨u₀, h₀, rfl⟩ := mem_support_sum_single c _ (fun u => (1 - E) • u) hu
        exact hQ u₀ (hc u₀ h₀))
      (by rw [sum_map_single]; exact hA x hx)
    rwa [sum_map_single] at h
  exact hsep _ (hlc0 g₂ ht₂) fun ℓ hℓ x hx => by rw [key g₂ ht₂ hs₂ ℓ hℓ x hx, hB x hx, hz, map_zero]

theorem offPl_step {S T' : HSp D} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} {a : AE D} (ha : IsSplitIdem D a) (hε : IsPlaceIdem D v ε)
    (hE : a + cA D a = algebraMap (AF D.host.F) (AE D) ε) (u : WO S T') (hu : OffPl (dropPl Sb v) u) :
    OffPl Sb ((1 - algebraMap (AF D.host.F) (AE D) ε) • u) := by
  obtain ⟨hinf, hpl⟩ := hu
  refine ⟨?_, fun w hw ε' hε' i j => ?_⟩
  · ext i j
    have h := congrFun (congrFun hinf i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at h ⊢
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, h, mul_zero]
  · rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hwv : w = v
    · rw [hwv] at hε'
      rw [GlobalTheory.PlaceDatum.placeIdem_eq hε' hε, ← mul_assoc, mul_sub, mul_one, idem_E ha hE, sub_self, zero_mul]
    · have h := hpl w (by classical unfold dropPl; convert Finset.mem_erase.2 ⟨hwv, hw⟩) ε' hε' i j
      rw [mul_left_comm, h, mul_zero]

theorem likeOff_dropPl : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), IsStdChar D R.ψ (-1) → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) (a : AE D), IsSplitIdem D a → IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) → ∀ Φ f : WO (Vc D i) (Wc D i) → ℂ, HasShape R.ψ (Vc D i) (Wc D i) a Φ (R.vP i t) → HasShape R.ψ (Vc D i) (Wc D i) a Φ f → LikeOff R i t Sb f → LikeOff R i t (dropPl Sb v) f := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hψ i t Sb v ε a ha hε hE hvP Φ f hsP hsf hL
  exact ⟨hL.1, fun c hc h1 => rel_extend hψ ha hE hvP hL.1 hsP hsf (OffPl Sb) (OffPl (dropPl Sb v))
    (fun u hu => offPl_step ha hε hE u hu) hL.2 c hc h1⟩

end GlobalTheory.DownLift.SplitRel
end
