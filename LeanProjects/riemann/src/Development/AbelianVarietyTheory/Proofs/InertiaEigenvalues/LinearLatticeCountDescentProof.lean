import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesOfSeparableCharPolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionIdempotentDecompositionOfSeparableCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlusElementEtaNormNegOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniformizerIdempotentFrameProdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoProdFiniteAlgebraWithInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumEqAlternatingSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartOrthogonalityClasseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardClProdFiniteAlgebraWithInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartProdInlStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumSubNormCharacterMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumProductSubFactorsStatement

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open Classical

theorem frame_exists (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (e π : ι → B.A) (S : Finset ι), IsFrame B e π S := by
  obtain ⟨ι, _, e, S, hP⟩ := GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly K B hs
  have : ∀ i, ∃ y : B.A, i ∈ S → B.Plus y ∧ y * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E y) = -1 := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨f, hf, hf0, hfld, hS, -⟩ := hP.2 i
      obtain ⟨he, hσ⟩ := hS hi
      obtain ⟨y, hy⟩ := GlobalTheory.T.exists_plus_element_eta_norm_neg_one K B f hf hf0 hfld hσ
      exact ⟨y, fun _ => by rw [he]; exact hy⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose π hπ using this
  exact ⟨ι, inferInstance, e, π, S, hP, fun i hi => hπ i hi⟩

theorem plus_mul {K : UQ} (B : InvAlg K) {x y : B.A} (hx : B.Plus x) (hy : B.Plus y) : B.Plus (x * y) :=
  ⟨hx.1.mul hy.1, by rw [map_mul, hx.2, hy.2]⟩

theorem plus_one {K : UQ} (B : InvAlg K) : B.Plus 1 := ⟨isUnit_one, map_one _⟩

theorem plus_prod {K : UQ} (B : InvAlg K) {ι : Type} (π : ι → B.A) (J : Finset ι) (h : ∀ j ∈ J, B.Plus (π j)) :
    B.Plus (∏ j ∈ J, π j) :=
  Finset.prod_induction _ B.Plus (fun _ _ => plus_mul B) (plus_one B) h

theorem isUnit_a {K : UQ} (B : InvAlg K) (a : K.O) (ha : K.Small a) : IsUnit (algebraMap K.O B.A a) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
  intro h
  exact ha.1 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))

theorem lim_HH {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O)
    (hB : B.LieReg) (ha : K.Small a) (hF : IsFrame B e π S) (ℓ : B.A → ℝ)
    (hℓ : ∀ x, B.Plus x → B.LinLim a x (ℓ x)) (I : Finset ι) (hI : I ⊆ S) (x : B.A) (hx : B.Plus x) :
    Tendsto (fun k : ℕ => ((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop
      (𝓝 (∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x))) := by
  have hπ : ∀ J ∈ S.powerset, B.Plus ((∏ j ∈ J, π j) * x) := fun J hJ =>
    plus_mul B (plus_prod B π J fun j hj => (hF.2 j (Finset.mem_powerset.1 hJ hj)).1) hx
  have hu : ∀ k : ℕ, IsUnit (x * algebraMap K.O B.A a ^ (2 * k)) := fun k => hx.1.mul ((isUnit_a B a ha).pow _)
  have heq : ∀ k : ℕ, ((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ) = ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card *
        ((B.GG ((∏ j ∈ J, π j) * x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) := by
    intro k
    rw [GlobalTheory.T.signedInvolutionStableLatticeSum_eq_alternating_sum K B ι e π S hB hF I hI _ (hu k)]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_assoc, mul_div_assoc]
  simp_rw [heq]
  exact tendsto_finset_sum _ fun J hJ => (hℓ _ (hπ J hJ)).const_mul _

theorem sum_formula {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O)
    (hB : B.LieReg) (ha : K.Small a) (hF : IsFrame B e π S) (ℓ : B.A → ℝ)
    (hℓ : ∀ x, B.Plus x → B.LinLim a x (ℓ x)) (I : Finset ι) (hI : I ⊆ S) :
    Tendsto (fun k : ℕ => ((HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop
      (𝓝 (∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j))) ∧
    ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card *
      ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j) := by
  set h : Finset ι → ℝ := fun I => ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j) with hh
  have lim1 : ∀ I ⊆ S, Tendsto (fun k : ℕ => ((HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 (h I)) := by
    intro I hI
    have := lim_HH B e π S a hB ha hF ℓ hℓ I hI 1 (plus_one B)
    simp only [one_mul, mul_one] at this
    exact this
  have key : ∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) =
      (chi B e I x : ℝ) * h I := by
    intro I hI x hx
    have t1 := lim_HH B e π S a hB ha hF ℓ hℓ I hI x hx
    have t2 := GlobalTheory.T.tendsto_signedLatticeSum_sub_normCharacter_mul K B ι e π S a hB ha hF I hI x hx
    have t3 := (lim1 I hI).const_mul (chi B e I x : ℝ)
    have t4 := t2.add t3
    rw [zero_add] at t4
    refine tendsto_nhds_unique t1 (t4.congr fun k => ?_)
    push_cast
    ring
  refine ⟨lim1 I hI, ?_⟩
  haveI : Finite B.Cl := GlobalTheory.T.finite_classes_of_separable_charPoly K B hB.2
  exact GlobalTheory.T.normCharacterOnIdempotentPart_orthogonality_classes K B ι e π S hF this ℓ h key I hI

theorem linearDescent : LinearDescent := by
  intro K B₁ B₂ hg₁ hg₂ hsep a ha ℓ ℓ₁ ℓ₂ hℓ hℓ₁ hℓ₂
  have hs₁ : B₁.P.Separable := hsep.of_mul_left
  have hs₂ : B₂.P.Separable := hsep.of_mul_right
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
      exact LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  obtain ⟨ι₁, _, e₁, π₁, S₁, hF₁⟩ := frame_exists K B₁ hs₁
  obtain ⟨ι₂, _, e₂, π₂, S₂, hF₂⟩ := frame_exists K B₂ hs₂
  have hF := GlobalTheory.T.isUniformizerIdempotentFrame_prod K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ hF₁ hF₂
  have hL₁ : B₁.LieReg := ⟨hg₁, hs₁⟩
  have hL₂ : B₂.LieReg := ⟨hg₂, hs₂⟩
  have hL : (B₁.prod B₂).LieReg := ⟨by
    show ((B₁.σ B₁.g, B₂.σ B₂.g) : B₁.A × B₂.A) = (B₁.g, B₂.g)
    rw [hg₁, hg₂], hP ▸ hsep⟩
  have hΛ : (S₁.disjSum S₂) \ S₁.map Function.Embedding.inl = S₂.map Function.Embedding.inr := by
    ext x; cases x <;> simp
  have hΛS : S₁.map Function.Embedding.inl ⊆ S₁.disjSum S₂ := by
    intro x; cases x <;> simp
  obtain ⟨l₁, c₁⟩ := sum_formula B₁ e₁ π₁ S₁ a hL₁ ha hF₁ ℓ₁ hℓ₁ S₁ subset_rfl
  obtain ⟨l₂, c₂⟩ := sum_formula B₂ e₂ π₂ S₂ a hL₂ ha hF₂ ℓ₂ hℓ₂ ∅ (Finset.empty_subset _)
  obtain ⟨l, c⟩ := sum_formula (B₁.prod B₂) _ _ _ a hL ha hF ℓ hℓ _ hΛS
  rw [Finset.sdiff_self] at l₁
  rw [Finset.sdiff_empty] at l₂
  rw [hΛ] at l
  change Tendsto (fun k : ℕ => ((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 : ℚ) : ℝ) / ((B₁.prod B₂).rho (algebraMap K.O (B₁.A × B₂.A) a ^ k) : ℝ)) atTop _ at l
  set h₁ := ∑ J ∈ S₁.powerset, (-1 : ℝ) ^ (J ∩ S₁).card * ℓ₁ (∏ j ∈ J, π₁ j)
  set h₂ := ∑ J ∈ S₂.powerset, (-1 : ℝ) ^ (J ∩ ∅).card * ℓ₂ (∏ j ∈ J, π₂ j)
  set h := ∑ J ∈ (S₁.disjSum S₂).powerset, (-1 : ℝ) ^ (J ∩ S₁.map Function.Embedding.inl).card *
    ℓ (∏ j ∈ J, Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) j)
  have hd := GlobalTheory.T.tendsto_signedLatticeSum_product_sub_factors K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a hL₁ hL₂ hsep ha hF₁ hF₂
  set v := val K.O (resultant B₁.P B₂.P)
  have hrho : ∀ k : ℕ, (B₁.prod B₂).rho (algebraMap K.O (B₁.A × B₂.A) a ^ k) =
      B₁.rho (algebraMap K.O B₁.A a ^ k) * B₂.rho (algebraMap K.O B₂.A a ^ k) := fun k =>
    GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution K B₁ B₂ _ _
  have hh : h = (-(K.q : ℝ)) ^ v * (h₁ * h₂) := by
    have t1 := (l₁.mul l₂).const_mul ((-(K.q : ℝ)) ^ v)
    have t2 := hd.add t1
    rw [zero_add] at t2
    refine tendsto_nhds_unique l (t2.congr fun k => ?_)
    rw [hrho k]
    push_cast
    ring
  have e₁' : ∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep =
      ∑ᶠ k : B₁.Cl, (chi B₁ e₁ S₁ k.rep : ℝ) * ℓ₁ k.rep := by
    refine finsum_congr fun k => ?_
    rw [((GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B₁ ι₁ e₁ π₁ S₁ hF₁).2.2.2 (InvAlg.Cl.rep k) ⟨Units.isUnit _, (Quot.out k).2⟩)]
  have e₂' : ∑ᶠ k : B₂.Cl, ℓ₂ k.rep = ∑ᶠ k : B₂.Cl, (chi B₂ e₂ ∅ k.rep : ℝ) * ℓ₂ k.rep := by
    refine finsum_congr fun k => ?_
    simp [chi, eS, UQ.eta, val]
  have e' : ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      ∑ᶠ k : (B₁.prod B₂).Cl, (chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A))
        (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) k.rep : ℝ) * ℓ k.rep := by
    refine finsum_congr fun k => ?_
    rw [GlobalTheory.T.normCharacterOnIdempotentPart_prod_inl K B₁ B₂ ι₁ ι₂ e₁ e₂ S₁ (InvAlg.Cl.rep k)]
    have hk : (B₁.prod B₂).Plus k.rep := ⟨Units.isUnit _, (Quot.out k).2⟩
    have hk1 : B₁.Plus (InvAlg.Cl.rep k).1 :=
      ⟨(Prod.isUnit_iff.1 hk.1).1, congrArg Prod.fst hk.2⟩
    rw [((GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B₁ ι₁ e₁ π₁ S₁ hF₁).2.2.2 (InvAlg.Cl.rep k).1 hk1)]
  rw [e₁', e₂', e', c, c₁, c₂, hh, GlobalTheory.T.card_cl_prod_finiteAlgebraWithInvolution, Finset.card_disjSum]
  push_cast
  ring

end GlobalTheory.UnitLemma.Desc
