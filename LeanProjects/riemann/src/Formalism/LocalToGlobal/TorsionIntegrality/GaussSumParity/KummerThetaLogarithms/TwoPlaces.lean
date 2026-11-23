import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TwoPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionRelationOfExpSpec
import Formalism.GaussJetBounds.StatementW

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas

open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong HasJetBound OrbitsMul opAlong jetPairPoly)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D Formalism.L2.Th1.D.BiextensionAlongSeries

theorem cc_xOfZ {K0 K : Type} [Field K0] [Field K] {ι : Type} {d N0 N1 : ℕ} [NeZero d] {l : ℕ}
    (hl : 2 ≤ l) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0) (x : PV ι N0 N1) :
    constantCoeff (xOfZ (d := d) l j σ om oms x) = 0 := by
  unfold xOfZ
  refine Pair.cc_ps ?_ (expSpec K l hl).1
  split_ifs <;>
    (rw [map_sum]; refine Finset.sum_eq_zero fun s _ => ?_; split_ifs <;> simp)

theorem comp_fam {K : Type} [Field K] {α β γ : Type} {A : α → MvPowerSeries β K}
    {C : β → MvPowerSeries γ K} (hA : HasSubst A) (hC : HasSubst C) (f : MvPowerSeries α K)
    (T : α → MvPowerSeries γ K) (hT : ∀ x, subst C (A x) = T x) :
    subst C (subst A f) = subst T f := by
  rw [subst_comp_subst_apply hA hC]
  congr 1
  funext x
  exact hT x

theorem twoPlaces (h : RelativeThetaFactorization) : TwoPlaces := by
  intro K0 K _ _ _ _ _ _ l d₁ d₂ N0 N1 _ _ σ j hK hj hd₁ he₁ hd₂ he₂ F hF be0 hF1 hF2 ι₁ ι₂ _ _ _ _
    om₁ oms₁ om₂ oms₂ hO₁ hT₁ hO₂ hT₂ ζ₁ ζ₂ hζ₁ hζ₂ U0 Φ hU0 hΦ0 hΦ
  have hl : 2 ≤ l := hK.1.two_le
  obtain ⟨U₁, hU₁, e₁⟩ := h K0 K l d₁ N0 N1 σ j hK hj hd₁ he₁ F hF be0 hF1 hF2 ι₁ om₁ oms₁ hO₁ hT₁
    ζ₁ hζ₁ (PV ι₂ N0 N1) U0 Φ (sumE (map j be0)) hU0 hΦ0 hΦ
  have hb0 : constantCoeff (map j be0) = 0 := by
    rw [constantCoeff_map]
    have := hF1.1 0 (Or.inl rfl)
    rw [coeff_zero_eq_constantCoeff_apply] at this
    rw [this, map_zero]
  have hS0 : constantCoeff (sumE (ι := ι₂) (N0 := N0) (N1 := N1) (map j be0)) = 0 := cc_sumE hb0
  have hz : serAlong (K := K) (Sum.inr : ZV d₁ N0 N1 → PV ι₂ N0 N1 ⊕ ZV d₁ N0 N1) 0 = 0 := by
    unfold serAlong
    exact TorusDerivation.subst_zero (hsX _)
  obtain ⟨U₂, hU₂, e₂⟩ := h K0 K l d₂ N0 N1 σ j hK hj hd₂ he₂ F hF be0 hF1 hF2 ι₂ om₂ oms₂ hO₂ hT₂
    ζ₂ hζ₂ (ZV d₁ N0 N1) (serAlong Sum.swap U₁) (serAlong Sum.inl (sumE (map j be0))) 0
    (integral_serAlong _ hU₁) (cc_serAlong _ hS0)
    (by rw [hz, add_zero]; exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules K _).1 _)
  refine ⟨serAlong Sum.swap U₂, integral_serAlong _ hU₂, ?_⟩
  intro g₁ g₂ hg₁0 hg₁ hg₂0 hg₂
  have E1 := e₁ g₁ hg₁0 hg₁
  have E2 := e₂ g₂ hg₂0 hg₂
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ = xOfZ (d := d₁) (N0 := N0) (N1 := N1) l j σ om₁ oms₁ := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, x₂ = xOfZ (d := d₂) (N0 := N0) (N1 := N1) l j σ om₂ oms₂ := ⟨_, rfl⟩
  have cx₁ : ∀ x, constantCoeff (x₁ x) = 0 := fun x => by rw [hx₁]; exact cc_xOfZ hl j σ om₁ oms₁ x
  have cx₂ : ∀ x, constantCoeff (x₂ x) = 0 := fun x => by rw [hx₂]; exact cc_xOfZ hl j σ om₂ oms₂ x
  obtain ⟨Ex₁, hEx₁⟩ : ∃ E, E = mvExp (-(bSum (idM : ZV d₁ N0 N1 → ZV d₁ N0 N1 → K)
      (map j (beMean l σ be0 om₁ oms₁ ζ₁)))) := ⟨_, rfl⟩
  obtain ⟨Ex₂, hEx₂⟩ : ∃ E, E = mvExp (-(bSum (idM : ZV d₂ N0 N1 → ZV d₂ N0 N1 → K)
      (map j (beMean l σ be0 om₂ oms₂ ζ₂)))) := ⟨_, rfl⟩
  obtain ⟨S₂, hS₂⟩ : ∃ S, S = sumE (ι := ι₂) (N0 := N0) (N1 := N1) (map j be0) := ⟨_, rfl⟩
  rw [← hx₁, ← hEx₁, ← hS₂] at E1
  rw [← hx₂, ← hEx₂, ← hS₂] at E2
  rw [← hx₁, ← hx₂, ← hEx₁, ← hEx₂]
  rw [← hS₂] at hS0

  obtain ⟨Cs, hCs⟩ : ∃ Cs : ZV d₁ N0 N1 ⊕ PV ι₂ N0 N1 → MvPowerSeries (ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) K,
      Cs = Sum.elim (fun y => X (Sum.inl y)) (fun x => serAlong Sum.inr (x₂ x)) := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ Ds : ZV d₂ N0 N1 ⊕ ZV d₁ N0 N1 → MvPowerSeries (ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) K,
      Ds = Sum.elim (fun y => X (Sum.inr y)) (fun y => serAlong Sum.inl (g₁ y)) := ⟨_, rfl⟩
  have hC : HasSubst Cs := hasSubst_of_constantCoeff_zero fun x => by
    rw [hCs]; rcases x with x | x
    · simp
    · exact cc_serAlong _ (cx₂ x)
  have hD : HasSubst Ds := hasSubst_of_constantCoeff_zero fun x => by
    rw [hDs]; rcases x with x | x
    · simp
    · exact cc_serAlong _ (hg₁0 x)
  have hCl : ∀ f : MvPowerSeries (ZV d₁ N0 N1) K, subst Cs (serAlong Sum.inl f) = serAlong Sum.inl f :=
    fun f => by rw [subst_serAlong _ hC, hCs]; rfl
  have hCr : ∀ f : MvPowerSeries (PV ι₂ N0 N1) K, subst Cs (serAlong Sum.inr f) =
      subst (fun x => serAlong Sum.inr (x₂ x)) f :=
    fun f => by rw [subst_serAlong _ hC, hCs]; rfl
  have hDl : ∀ f : MvPowerSeries (ZV d₂ N0 N1) K, subst Ds (serAlong Sum.inl f) = serAlong Sum.inr f :=
    fun f => by rw [subst_serAlong _ hD, hDs]; rfl
  have hDr : ∀ f : MvPowerSeries (ZV d₁ N0 N1) K, subst Ds (serAlong Sum.inr f) =
      subst (fun y => serAlong Sum.inl (g₁ y)) f :=
    fun f => by rw [subst_serAlong _ hD, hDs]; rfl
  have hsA : ∀ {α β γ : Type} [Finite α] [Finite β] (u : α → MvPowerSeries γ K)
      (v : β → MvPowerSeries γ K), (∀ x, constantCoeff (u x) = 0) → (∀ x, constantCoeff (v x) = 0) →
      HasSubst (Sum.elim u v) := fun u v hu hv =>
    hasSubst_of_constantCoeff_zero fun x => by rcases x with x | x <;> simp [hu, hv]

  obtain ⟨G, hG⟩ : ∃ G : ZV d₁ N0 N1 ⊕ PV ι₂ N0 N1 → MvPowerSeries (ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) K,
      G = Sum.elim (fun y => serAlong Sum.inl (g₁ y)) (fun x => serAlong Sum.inr (x₂ x)) := ⟨_, rfl⟩
  have F1' := congrArg (subst Cs) E1
  rw [subst_mul hC, subst_mul hC, hCl, hCr,
    comp_fam (hsA _ _ (fun x => cc_serAlong _ (cx₁ x)) (fun y => constantCoeff_X _)) hC _
      (Sum.elim (fun x => serAlong Sum.inl (x₁ x)) (fun x => serAlong Sum.inr (x₂ x)))
      (by
        intro x; rcases x with x | x
        · exact hCl _
        · simp only [Sum.elim_inr]; rw [subst_X hC, hCs]; rfl),
    comp_fam (hsA _ _ (fun x => cc_serAlong _ (hg₁0 x)) (fun y => constantCoeff_X _)) hC _ G
      (by
        intro x; rw [hG]; rcases x with x | x
        · exact hCl _
        · simp only [Sum.elim_inr]; rw [subst_X hC, hCs]; rfl)] at F1'
  have F2' := congrArg (subst Ds) E2
  have hone : serAlong (K := K) (Sum.inr : ZV d₁ N0 N1 → ZV d₂ N0 N1 ⊕ ZV d₁ N0 N1)
      (mvExp (-0)) = 1 := by
    rw [neg_zero, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero']
    unfold serAlong
    rw [← coe_substAlgHom (hsX _), map_one]
  rw [hone, mul_one, subst_mul hD, hDl,
    comp_fam (hsA _ _ (fun x => cc_serAlong _ (cx₂ x)) (fun y => constantCoeff_X _)) hD _
      (Sum.elim (fun x => serAlong Sum.inr (x₂ x)) (fun y => serAlong Sum.inl (g₁ y)))
      (by
        intro x; rcases x with x | x
        · exact hDl _
        · simp only [Sum.elim_inr]; rw [subst_X hD, hDs]; rfl),
    comp_fam (hsA _ _ (fun x => cc_serAlong _ (hg₂0 x)) (fun y => constantCoeff_X _)) hD _
      (Sum.elim (fun x => serAlong Sum.inr (g₂ x)) (fun y => serAlong Sum.inl (g₁ y)))
      (by
        intro x; rcases x with x | x
        · exact hDl _
        · simp only [Sum.elim_inr]; rw [subst_X hD, hDs]; rfl)] at F2'
  have hH : HasSubst (Sum.elim (fun x => serAlong (K := K) (Sum.inr : _ → ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) (x₂ x))
      (fun y => serAlong Sum.inl (g₁ y))) :=
    hsA _ _ (fun x => cc_serAlong _ (cx₂ x)) (fun y => cc_serAlong _ (hg₁0 y))
  have hT : HasSubst (Sum.elim (fun x => serAlong (K := K) (Sum.inl : _ → ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) (g₁ x))
      (fun y => serAlong Sum.inr (g₂ y))) :=
    hsA _ _ (fun x => cc_serAlong _ (hg₁0 x)) (fun y => cc_serAlong _ (hg₂0 y))
  rw [subst_mul hH, ← serAlong_neg, ← serAlong_mvExp _ (by rw [map_neg, hS0, neg_zero]),
    subst_serAlong _ hH, subst_serAlong _ hH] at F2'
  have k1 : (fun i : ZV d₁ N0 N1 ⊕ PV ι₂ N0 N1 =>
      Sum.elim (fun x => serAlong (K := K) (Sum.inr : _ → ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) (x₂ x))
      (fun y => serAlong Sum.inl (g₁ y)) (Sum.swap i)) = G := by
    rw [hG]; funext i; rcases i with i | i <;> rfl
  have k2 : (fun i : ZV d₂ N0 N1 ⊕ ZV d₁ N0 N1 =>
      Sum.elim (fun x => serAlong (K := K) (Sum.inl : _ → ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) (g₁ x))
      (fun y => serAlong Sum.inr (g₂ y)) (Sum.swap i)) =
      Sum.elim (fun x => serAlong Sum.inr (g₂ x)) (fun y => serAlong Sum.inl (g₁ y)) := by
    funext i; rcases i with i | i <;> rfl
  rw [k1] at F2'
  simp only [Sum.elim_inl] at F2'
  rw [F1', subst_serAlong _ hT, k2, ← mul_assoc, mul_right_comm _ (serAlong Sum.inl Ex₁), mul_comm (subst G U₁), F2']
  ring

theorem shape (hO : OrbitsMul) (K : Type) [NormedField K] [IsUltrametricDist K]
    (ι₁ ι₂ σ₁ σ₂ : Type) [Finite ι₁] [Finite ι₂]
    (g₁ : ι₁ → MvPowerSeries ι₁ K) (g₂ : ι₂ → MvPowerSeries ι₂ K)
    (h₁ : ∀ x, constantCoeff (g₁ x) = 0) (h₂ : ∀ x, constantCoeff (g₂ x) = 0)
    (E₁ : MvPowerSeries ι₁ K) (E₂ : MvPowerSeries ι₂ K)
    (P₁ : MvPolynomial ι₁ (MvPolynomial σ₁ K)) (P₂ : MvPolynomial ι₂ (MvPolynomial σ₂ K))
    (B₁ B₂ : ℝ) (b₁ : HasJetBound g₁ E₁ P₁ B₁) (b₂ : HasJetBound g₂ E₂ P₂ B₂)
    (U Th : MvPowerSeries (ι₁ ⊕ ι₂) K) (hU : Integral U)
    (hTh : Th = subst (Sum.elim (fun x => serAlong Sum.inl (g₁ x))
      (fun x => serAlong Sum.inr (g₂ x))) U * (serAlong Sum.inl E₁ * serAlong Sum.inr E₂))
    (n : σ₁ ⊕ σ₂ →₀ ℕ) :
    ‖MvPolynomial.coeff n (jetPairPoly (opAlong Sum.inl Sum.inl P₁ * opAlong Sum.inr Sum.inr P₂) Th)‖
      ≤ B₁ * B₂ := by
  rw [hTh]
  exact hO K ι₁ ι₂ σ₁ σ₂ g₁ g₂ h₁ h₂ E₁ E₂ P₁ P₂ B₁ B₂ b₁ b₂ U hU n

theorem two : TwoPlaces := twoPlaces biextension_relation_holds

end Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas

namespace Formalism.L2.Th1.D

end Formalism.L2.Th1.D
