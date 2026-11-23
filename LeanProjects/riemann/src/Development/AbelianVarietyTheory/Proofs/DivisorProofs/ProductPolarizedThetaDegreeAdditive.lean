import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHodgeCh2Omega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCh2DegOfIsCInfNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCovEqMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPolarizedAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexDegreeDirectSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDataProductProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProductOrthogonalSumStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.VB GlobalTheory.CxPts Matrix
open GlobalTheory.LieVB (omega omegaMap unitSec dUnit cotMap)
open GlobalTheory.Twist (resM)
open scoped ComplexOrder CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ProdHodge

theorem isIso_desc {S : Scheme.{0}} {A A₁ A₂ : Over S} [GrpObj A] [GrpObj A₁] [GrpObj A₂]
    [QuasiSeparated A.hom] (π₁ : A ⟶ A₁) (π₂ : A ⟶ A₂) [IsMonHom π₁] [IsMonHom π₂]
    (l : IsLimit (BinaryFan.mk π₁ π₂)) : IsIso (biprod.desc (omegaMap π₁) (omegaMap π₂)) := by
  have ex {T : Over S} (x : T ⟶ A₁) (y : T ⟶ A₂) : ∃ z : T ⟶ A, z ≫ π₁ = x ∧ z ≫ π₂ = y :=
    ⟨_, (BinaryFan.IsLimit.lift' l x y).2⟩
  obtain ⟨ι₁, a₁, b₁⟩ := ex (𝟙 A₁) 1
  obtain ⟨ι₂, a₂, b₂⟩ := ex 1 (𝟙 A₂)
  have ext {T : Over S} {x y : T ⟶ A} (h₁ : x ≫ π₁ = y ≫ π₁) (h₂ : x ≫ π₂ = y ≫ π₂) : x = y :=
    BinaryFan.IsLimit.hom_ext l h₁ h₂
  have o₁ : η[A₁] ≫ (1 : A₁ ⟶ A₂) = η[A₂] := by simp [Hom.one_def]
  have o₂ : η[A₂] ≫ (1 : A₂ ⟶ A₁) = η[A₁] := by simp [Hom.one_def]
  have p₁ := IsMonHom.one_hom π₁
  have p₂ := IsMonHom.one_hom π₂
  have u₁ : η[A₁] ≫ ι₁ = η[A] := ext (by rw [Category.assoc, a₁, p₁, Category.comp_id])
    (by rw [Category.assoc, b₁, p₂, o₁])
  have u₂ : η[A₂] ≫ ι₂ = η[A] := ext (by rw [Category.assoc, a₂, p₁, o₂])
    (by rw [Category.assoc, b₂, p₂, Category.comp_id])
  have e : (π₁ ≫ ι₁) * (π₂ ≫ ι₂) = 𝟙 A := ext
    (by rw [MonObj.mul_comp, Category.assoc, Category.assoc, a₁, a₂, MonObj.comp_one, _root_.mul_one,
      Category.comp_id, Category.id_comp])
    (by rw [MonObj.mul_comp, Category.assoc, Category.assoc, b₁, b₂, MonObj.comp_one, _root_.one_mul,
      Category.comp_id, Category.id_comp])
  have x₁ : η[A] ≫ π₁ ≫ ι₁ = η[A] := by rw [reassoc_of% p₁, u₁]
  have x₂ : η[A] ≫ π₂ ≫ ι₂ = η[A] := by rw [reassoc_of% p₂, u₂]
  let j₁ : omega A ⟶ omega A₁ := cotMap ι₁ u₁
  let j₂ : omega A ⟶ omega A₂ := cotMap ι₂ u₂
  have c₁₁ : omegaMap π₁ ≫ j₁ = 𝟙 _ :=
    (LieVB.cotMap_comp p₁ u₁ a₁ (Category.comp_id _)).trans (LieVB.cotMap_id rfl _)
  have c₁₂ : omegaMap π₁ ≫ j₂ = 0 :=
    (LieVB.cotMap_comp p₁ u₂ a₂ o₂).trans (LieVB.cotMap_eq_zero rfl _)
  have c₂₁ : omegaMap π₂ ≫ j₁ = 0 :=
    (LieVB.cotMap_comp p₂ u₁ b₁ o₁).trans (LieVB.cotMap_eq_zero rfl _)
  have c₂₂ : omegaMap π₂ ≫ j₂ = 𝟙 _ :=
    (LieVB.cotMap_comp p₂ u₂ b₂ (Category.comp_id _)).trans (LieVB.cotMap_id rfl _)
  have c : j₁ ≫ omegaMap π₁ +
      j₂ ≫ omegaMap π₂ = 𝟙 _ :=
    (congrArg₂ (· + ·) (LieVB.cotMap_comp u₁ p₁ rfl x₁) (LieVB.cotMap_comp u₂ p₂ rfl x₂)).trans
      ((LieVB.cotMap_mul x₁ x₂ (e ▸ Category.comp_id _)).symm.trans (LieVB.cotMap_id e _))
  clear_value j₁ j₂
  refine ⟨biprod.lift j₁ j₂, ?_, ?_⟩
  · refine biprod.hom_ext _ _ (biprod.hom_ext' _ _ ?_ ?_) (biprod.hom_ext' _ _ ?_ ?_) <;>
      simp [c₁₁, c₁₂, c₂₁, c₂₂]
  · rw [biprod.lift_desc, c]

theorem cov_appLE {S : Scheme.{0}} {P P' : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)
    (d' : P'.RiemannData y) (π : P.A ⟶ P'.A) (Q : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ))
    (hQ : ∀ z, (d'.u.ex (Q z)).left ≫ d'.φ = (d.u.ex z).left ≫ d.φ ≫ π.left)
    {W : P.A.left.Opens} {W' : P'.A.left.Opens} (k : W ≤ π.left ⁻¹ᵁ W')
    (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) (h' : ⊤ ≤ (y ≫ unitSec P'.A) ⁻¹ᵁ W') (f : Γ(P'.A.left, W')) :
    d.cov W (π.left.appLE W' W k f) = (LinearMap.toMatrix' Q)ᵀ *ᵥ d'.cov W' f := by
  have hfn : d.fn W (π.left.appLE W' W k f) =ᶠ[nhds 0] d'.fn W' f ∘ Q :=
    (CovFactor.eventually_le d h).mono fun z hz => by
      simp only [PPAS.RiemannData.fn, Function.comp_apply, hQ]
      rw [CovFactor.valR_appLE hz k f, Category.assoc]
  set M := LinearMap.toMatrix' Q with hM
  have hMv : ∀ z, M *ᵥ z = Q z := fun z => LinearMap.toMatrix'_mulVec Q z
  have hTd : ∀ v, fderiv ℂ (⇑Q) 0 v = Q v := fun v => by
    have := (LinearMap.toContinuousLinearMap Q).fderiv (x := 0)
    exact congrArg (fun L => L v) this
  funext a
  have hd := d'.differentiableAt_fn f h'
  have hd' : DifferentiableAt ℂ (d'.fn W' f) (Q 0) := by rw [map_zero]; exact hd
  have hTdiff : DifferentiableAt ℂ (⇑Q) 0 := (LinearMap.toContinuousLinearMap Q).differentiableAt
  simp only [PPAS.RiemannData.cov]
  rw [hfn.fderiv_eq, fderiv_comp 0 hd' hTdiff, ContinuousLinearMap.comp_apply, hTd, map_zero, ← hMv,
    mulVec_single_one]
  change _ = ∑ b, M.col a b * fderiv ℂ (d'.fn W' f) 0 (Pi.single b 1)
  generalize fderiv ℂ (d'.fn W' f) 0 = L
  conv_lhs => rw [pi_eq_sum_univ (M.col a)]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {P P₁ P₂ : PPAS S}

theorem form_add (π₁ : P.A ⟶ P₁.A) (π₂ : P.A ⟶ P₂.A) [IsMonHom π₁] [IsMonHom π₂] (hg : P.g = P₁.g + P₂.g)
    (hc : P.c = CechPic.pull (π₁ ⊗ₘ π₁).left P₁.c + CechPic.pull (π₂ ⊗ₘ π₂).left P₂.c)
    {h : VMetric p (omega P.A) P.g} {h₁ : VMetric p (omega P₁.A) P₁.g} {h₂ : VMetric p (omega P₂.A) P₂.g}
    (H : P.IsHodge h) (H₁ : P₁.IsHodge h₁) (H₂ : P₂.IsHodge h₂) (σ : k →+* ℂ) (V : S.Opens)
    (s₁ t₁ : Γ(omega P₁.A, V)) (s₂ t₂ : Γ(omega P₂.A, V)) (y : CxPts p σ) (hy : y ∈ ptsIn p σ V) :
    (h.met σ).form ((omegaMap π₁).app V s₁ + (omegaMap π₂).app V s₂)
        ((omegaMap π₁).app V t₁ + (omegaMap π₂).app V t₂) y =
      (h₁.met σ).form s₁ t₁ y + (h₂.met σ).form s₂ t₂ y := by
  obtain ⟨U₁, W₁, hx₁, le₁, c₁⟩ :=
    Conormal.exists_isChart (LieVB.sec_hom (MonObj.one (X := P₁.A))) (mem_ptsIn.1 hy)
  obtain ⟨U, W₂, hx, le₂, c₂⟩ := Conormal.exists_isChart (LieVB.sec_hom (MonObj.one (X := P₂.A))) hx₁
  have hU : y ∈ ptsIn p σ U := mem_ptsIn.2 hx
  have le := le₂.trans le₁
  have k₁ : U ≤ unitSec P₁.A ⁻¹ᵁ W₁ := le₂.trans c₁.le
  have k₂ : U ≤ unitSec P₂.A ⁻¹ᵁ W₂ := c₂.le
  have sur₁ (s : Γ(omega P₁.A, V)) : ∃ f, dUnit P₁.A k₁ f = resM _ le s := by
    obtain ⟨f, hf⟩ := c₁.d_surjective (LieVB.sec_hom (MonObj.one (X := P₁.A))) (resM (omega P₁.A) le₁ s)
    exact ⟨f, (LieVB.resM_dUnit P₁.A c₁.le le₂ f).symm.trans
      ((congrArg (resM (omega P₁.A) le₂) hf).trans (Twist.resM_resM _ _ _))⟩
  have sur₂ (s : Γ(omega P₂.A, V)) : ∃ f, dUnit P₂.A k₂ f = resM _ le s :=
    c₂.d_surjective (LieVB.sec_hom (MonObj.one (X := P₂.A))) (resM (omega P₂.A) le s)
  obtain ⟨f₁, e₁⟩ := sur₁ s₁
  obtain ⟨g₁, e₁'⟩ := sur₁ t₁
  obtain ⟨f₂, e₂⟩ := sur₂ s₂
  obtain ⟨g₂, e₂'⟩ := sur₂ t₂
  let W : P.A.left.Opens := π₁.left ⁻¹ᵁ W₁ ⊓ π₂.left ⁻¹ᵁ W₂
  have q₁ : unitSec P.A ≫ π₁.left = unitSec P₁.A := congrArg (·.left) (IsMonHom.one_hom π₁)
  have q₂ : unitSec P.A ≫ π₂.left = unitSec P₂.A := congrArg (·.left) (IsMonHom.one_hom π₂)
  have kW : U ≤ unitSec P.A ⁻¹ᵁ W := fun x hx' =>
    ⟨show x ∈ (unitSec P.A ≫ π₁.left) ⁻¹ᵁ W₁ from q₁ ▸ k₁ hx',
      show x ∈ (unitSec P.A ≫ π₂.left) ⁻¹ᵁ W₂ from q₂ ▸ k₂ hx'⟩
  have key {s : Γ(omega P₁.A, V)} {t : Γ(omega P₂.A, V)} {f : Γ(P₁.A.left, W₁)} {g : Γ(P₂.A.left, W₂)}
      (a : dUnit P₁.A k₁ f = resM _ le s) (b : dUnit P₂.A k₂ g = resM _ le t) :
      resM _ le ((omegaMap π₁).app V s + (omegaMap π₂).app V t) =
        dUnit P.A kW (π₁.left.appLE W₁ W inf_le_left f + π₂.left.appLE W₂ W inf_le_right g) := by
    rw [map_add, map_add, ← Twist.app_resM, ← Twist.app_resM, ← a, ← b,
      LieVB.omegaMap_dUnit π₁ k₁ kW inf_le_left, LieVB.omegaMap_dUnit π₂ k₂ kW inf_le_right]
  obtain ⟨d⟩ := (H σ y).1
  obtain ⟨d₁⟩ := (H₁ σ y).1
  obtain ⟨d₂⟩ := (H₂ σ y).1
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hH⟩ := GlobalTheory.T.riemann_data_product_projection S P P₁ P₂ π₁ π₂ inferInstance inferInstance hc y.1 d d₁ d₂
  have ty := DualRiemannEx.top_le_of_mem hU
  have m : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W := ty.trans (y.1.preimage_mono kW)
  have m₁ : ⊤ ≤ (y.1 ≫ unitSec P₁.A) ⁻¹ᵁ W₁ := ty.trans (y.1.preimage_mono k₁)
  have m₂ : ⊤ ≤ (y.1 ≫ unitSec P₂.A) ⁻¹ᵁ W₂ := ty.trans (y.1.preimage_mono k₂)
  rw [← Met.form_resM _ _ _ le hU, ← Met.form_resM _ s₁ _ le hU, ← Met.form_resM _ s₂ _ le hU,
    key e₁ e₂, key e₁' e₂', ← e₁, ← e₁', ← e₂, ← e₂', (H σ y).2 d U W kW _ _ hU,
    (H₁ σ y).2 d₁ U W₁ k₁ _ _ hU, (H₂ σ y).2 d₂ U W₂ k₂ _ _ hU, CovFactor.cov_add d m,
    CovFactor.cov_add d m, cov_appLE d d₁ π₁ Q₁ hQ₁ _ m m₁, cov_appLE d d₁ π₁ Q₁ hQ₁ _ m m₁,
    cov_appLE d d₂ π₂ Q₂ hQ₂ _ m m₂, cov_appLE d d₂ π₂ Q₂ hQ₂ _ m m₂]
  exact GlobalTheory.T.theta_product_orthogonal_sum _ _ _ hg d.H d₁.H d₂.H _ _ d.posDef d₁.posDef d₂.posDef
    (fun z w => by simp only [LinearMap.toMatrix'_mulVec]; exact hH z w) _ Real.pi_pos _ _ _ _

theorem isCh2Deg_of_isProd [IsIntegral S] (hP : P.IsProd P₁ P₂)
    {h : VMetric p (omega P.A) P.g} {h₁ : VMetric p (omega P₁.A) P₁.g} {h₂ : VMetric p (omega P₂.A) P₂.g}
    (H : P.IsHodge h) (H₁ : P₁.IsHodge h₁) (H₂ : P₂.IsHodge h₂) {c : ℝ}
    (hc : (h₁.orthSum h₂).IsCh2Deg c) : h.IsCh2Deg c := by
  obtain ⟨π₁, π₂, _, _, ⟨l⟩, hg, e⟩ := hP
  have I := form_add π₁ π₂ hg e H H₁ H₂
  have := isIso_desc π₁ π₂ l
  clear H
  revert h
  rw [hg]
  intro h I
  have J : (h₁.orthSum h₂).IsIsometry h (asIso (biprod.desc (omegaMap π₁) (omegaMap π₂))) := by
    intro σ V s t y hy
    have a (s : Γ(omega P₁.A ⊞ omega P₂.A, V)) :
        (asIso (biprod.desc (omegaMap π₁) (omegaMap π₂))).hom.app V s =
          (omegaMap π₁).app V ((biprod.fst : _ ⊞ omega P₂.A ⟶ _).app V s) +
            (omegaMap π₂).app V ((biprod.snd : omega P₁.A ⊞ _ ⟶ _).app V s) :=
      congr(($(biprod.desc_eq (f := omegaMap π₁) (g := omegaMap π₂))).app V s)
    rw [a, a, I σ V _ _ _ _ y hy]
    exact (VMetric.isOrthSum_orthSum h₁ h₂ σ V s t y hy).symm
  exact (IsometryPullback.isCh2Deg_iff_of_isIsometry (Iso.refl S) (Category.id_comp p)
    (IsometryPullback.isIsometry_trans (VMetric.isIsometry_pull_id_comp k S p _ _ _).1 J) c).2 hc

end GlobalTheory.ProdHodge

theorem GlobalTheory.PPAS.exists_prod_ch2Omega : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ P₁ P₂ : PPAS S, P₁.HasTheta → P₂.HasTheta → ∃ P : PPAS S, P.g = P₁.g + P₂.g ∧ P.HasTheta ∧ P.degOmega p = P₁.degOmega p + P₂.degOmega p ∧ ∀ a b : ℝ, P₁.IsCh2Omega p a → P₂.IsCh2Omega p b → P.IsCh2Omega p (a + b) := by
  intro hP hR k _ S p _ hS P₁ P₂ hT₁ hT₂
  obtain ⟨P, hPr⟩ := GlobalTheory.T.exists_product_polarized_abelian S P₁ P₂
  have hg : P.g = P₁.g + P₂.g := hPr.g_eq
  refine ⟨P, hg, GlobalTheory.T.hasTheta_of_isProd' S P P₁ P₂ hPr hT₁ hT₂, ?_, fun a b ha hb => ?_⟩
  · obtain ⟨π₁, π₂, _, _, ⟨l⟩, -, -⟩ := hPr
    have := ProdHodge.isIso_desc π₁ π₂ l
    unfold PPAS.degOmega
    rw [hg, ← cxDeg_congr (asIso (biprod.desc (omegaMap π₁) (omegaMap π₂))),
      GlobalTheory.T.complex_degree_direct_sum k S p hS.toIsArithVar _ _ _ _ P₁.isVB_omega P₂.isVB_omega]
  · obtain ⟨h, H⟩ := PPAS.exists_isDualRiemann k S p P _ Real.pi_pos
    obtain ⟨h₁, H₁, ha⟩ := ha
    obtain ⟨h₂, H₂, hb⟩ := hb
    exact ⟨h, H, ProdHodge.isCh2Deg_of_isProd hPr H H₁ H₂ (VMetric.isCh2Deg_orthSum hP.p4 k S p
      (fun Y q _ hq => GlobalTheory.RegCoverExists.nonempty_regCover hR k Y q hq) hS.toIsArithVar _ _ _ _ h₁ h₂ a b
      (P₁.isCInfNorm_of_isHodge H₁) (P₂.isCInfNorm_of_isHodge H₂) ha hb)⟩
