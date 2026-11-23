import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfApplyOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotRealPowOfGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIrreducibleAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantSubmoduleInImageSpanStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

private theorem liftSmall_pairing_zero (hK : GlobalTheory.ThK.KP) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {x x' n m : ℕ} (hm : x + x' = m) (hn : n < x') {α β : kˣ →* ℂˣ}
    (hα : GlobalTheory.KSplit.IsSmU α) (hβ : GlobalTheory.KSplit.IsSmU β) (hne : ∀ t : ℝ, α * β⁻¹ ≠ GlobalTheory.SmGL.absPow k (t : ℂ))
    {H : Type} [Group H] (L : GL (Fin m) k →* H) (f : H → ℂ) (M : Submodule ℂ (H → ℂ))
    (hM : M = Submodule.span ℂ (Set.range fun g => fun y => f (y * L g)))
    (hf : f ∈ GlobalTheory.LocTypeGood.imgSpan (GlobalTheory.ThK.MidJac.detInd x x' α β)
      ((GlobalTheory.PRep.rightReg ℂ H ℂ).comp (L.comp (GlobalTheory.LocTypeGood.glReindex (finCongr hm)))))
    (P : M →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] ℂ)
    (hP : ∀ (h : GL (Fin m) k) (u : H → ℂ) (hu : u ∈ M) (hu' : (fun y => u (y * L h)) ∈ M)
      (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) k)),
      (∀ X, (Φ' : Matrix (Fin n) (Fin m) k → ℂ) X = ((α (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
        ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
        (Φ : Matrix (Fin n) (Fin m) k → ℂ) (X * ((h⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ)) →
      P ⟨fun y => u (y * L h), hu'⟩ Φ' = P ⟨u, hu⟩ Φ) : P = 0 := by
  subst hm
  have hre : L.comp (GlobalTheory.LocTypeGood.glReindex (finCongr (rfl : x + x' = x + x'))) = L :=
    MonoidHom.ext fun h => congrArg L (Units.ext (Matrix.ext fun i j => rfl))
  rw [hre] at hf
  set π := GlobalTheory.ThK.MidJac.detInd x x' α β with hπ
  set ρ : Representation ℂ (GL (Fin (x + x')) k) (H → ℂ) := (GlobalTheory.PRep.rightReg ℂ H ℂ).comp L with hρ
  have hρa : ∀ g (u : H → ℂ), ρ g u = fun y => u (y * L g) := fun _ _ => rfl
  have hst : ∀ g, ∀ u ∈ M, ρ g u ∈ M := by
    intro g u hu
    rw [hM] at hu ⊢
    refine (Submodule.span_le (p := (Submodule.span ℂ (Set.range fun g => fun y => f (y * L g))).comap (ρ g))).2 ?_ hu
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨g * a, ?_⟩
    funext y
    show f (y * L (g * a)) = f (y * L g * L a)
    rw [map_mul, mul_assoc]
  have hfM : f ∈ M := by
    rw [hM]
    exact Submodule.subset_span ⟨1, by funext y; simp⟩
  have hsp := GlobalTheory.T.invariant_submodule_in_image_span _ _ _ π ρ (GlobalTheory.T.determinant_induced_irreducible_admissible hK k x x' α β hα hβ).1 M hst f hfM hf
  let N : Submodule ℂ (H → ℂ) := (LinearMap.ker P).map M.subtype
  have hN : ∀ u (hu : u ∈ M), u ∈ N ↔ P ⟨u, hu⟩ = 0 := fun u hu =>
    ⟨fun ⟨w, h1, h2⟩ => by rw [← show w = ⟨u, hu⟩ from Subtype.ext h2]; exact h1, fun h => ⟨⟨u, hu⟩, h, rfl⟩⟩
  have hgen : ∀ T : _ →ₗ[ℂ] (H → ℂ), (∀ g, T ∘ₗ π g = ρ g ∘ₗ T) → (∀ u, T u ∈ M) → ∀ u, T u ∈ N := by
    intro T hTe hT u
    have h0 := GlobalTheory.DetEqv.no_pairing_of_lt k x x' n hn α β hα.1 hβ.1 hne (P ∘ₗ T.codRestrict M hT) (fun h w Φ Φ' hΦ => by
      have e : T (π h w) = fun y => T w (y * L h) := LinearMap.congr_fun (hTe h) w
      have e' : T.codRestrict M hT (π h w) = ⟨fun y => T w (y * L h), e ▸ hT _⟩ := Subtype.ext e
      show P (T.codRestrict M hT (π h w)) Φ' = P (T.codRestrict M hT w) Φ
      rw [e']
      exact hP h (T w) (hT w) _ Φ Φ' hΦ)
    exact (hN _ (hT u)).2 (LinearMap.congr_fun h0 u)
  have hall : ∀ g, ρ g f ∈ N := by
    intro g
    refine (Submodule.span_le (p := N.comap (ρ g))).2 ?_ hsp
    rintro _ ⟨T, hTe, hT, u, rfl⟩
    have e : ρ g (T u) = T (π g u) := (LinearMap.congr_fun (hTe g) u).symm
    show ρ g (T u) ∈ N
    rw [e]
    exact hgen T hTe hT _
  have hle : M ≤ N := by
    conv_lhs => rw [hM]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact hall g
  exact LinearMap.ext fun u => (hN u.1 u.2).1 (hle u.2)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem _root_.GlobalTheory.T.theta_tower_descent_period : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i, IsCT (W := sp i) (pl i) f 0 → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ (n k : ℕ) (JX : Matrix (Fin n) (Fin n) E), 1 ≤ k → n + 2 * k = a' → (∀ s t, σ (JX t s) = JX s t) → JX.det ≠ 0 →
        LiftZero B.ψ JX (sp i).J X.α (X.α / X.β) f := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso c h0 hj i hi f hf _ hdec n k JX hk hnk hX hXd
  by_contra hne
  have hT := hM.triple
  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hsk := NextStep.skew_sp hσ B hT.geo.hW.skew hH hiso i hi.le
  have hd := Nondeg.det_ne_zero_of_cartan B (sp i) (hiso i hi).2.2.2.2.2.2.1
  have hν : IsHecke F E (X.α / X.β) := ⟨hT.chars.heckeα.1.div' hT.chars.heckeβ.1, fun x => by
    rw [MonoidHom.div_apply, hT.chars.heckeα.2 x, hT.chars.heckeβ.2 x, div_one]⟩
  have hrank := hH.rank
  have hbig := hT.geo.eBig
  obtain ⟨hfc, hfl⟩ := Nondeg.lev_reg hK hM hH hiso c h0 hj i hi f hf
  have hα := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hT.chars.heckeα B.v₁ B.τ₁).1
  have hβ := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hT.chars.heckeβ B.v₁ B.τ₁).1
  have hermW : ∀ k l, σ ((sp i).J l k) = algebraMap F E (-1) * (sp i).J k l := fun k l => by
    rw [hsk k l, map_neg, map_one, neg_one_mul]
  have hJW : IsUnit ((sp i).J.map B.τ₁).det := by
    rw [show ((sp i).J.map B.τ₁).det = B.τ₁ (sp i).J.det from (AlgHom.map_det B.τ₁ (sp i).J).symm]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero B.τ₁).2 hd)
  have hm : a - 2 * (i + 1) + a' = d₁ - 2 * i := by omega
  have hloc := GlobalTheory.LocTypeGood.locType hK F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso c h0 hj i hi B.v₁
    hT.chars.good B.τ₁ hcm (-1) hermW hJW (finCongr hm) f hf 1
  simp only [mul_one] at hloc
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.ThK.LiftPair.exists_pairing hK hcm B.ψ hT.base.std JX (sp i).J hX hXd hsk hd X.α (X.α / X.β)
    hT.chars.heckeα hν f hfc hfl hdec hne B.v₁ B.τ₁
  exact hP0 (liftSmall_pairing_zero hK hm (by omega) hα hβ
    (GlobalTheory.LocTypeGood.notRealPow_of_good F E σ B a a' G X om om' hT B.v₁ hT.chars.good B.τ₁)
    (GlobalTheory.ThK.LiftPair.liftSk hcm B.τ₁ (sp i).J hsk hd) f _ rfl hloc P hP)
