import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThEquiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.AtZeroCompProdX
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivGen
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace TE

section Rho

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem det_ufGL (γ : UF E n) : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det = ((LinearEquiv.det γ.1 : Eˣ) : E) := by
  show (LinearMap.toMatrix' ((γ.1 : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n)).det = _
  rw [LinearMap.det_toMatrix', LinearEquiv.coe_det]

variable {K : Type} [Field K] {ι : Type} [Fintype ι] (emb : ι → E →+* K)

def matT (γ : UF E n) (τ : ι) : Matrix (Fin n) (Fin n) K := ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ)

theorem det_matT (γ : UF E n) (τ : ι) : (matT emb γ τ).det = emb τ ((LinearEquiv.det γ.1 : Eˣ) : E) := by
  rw [← det_ufGL, RingHom.map_det]
  rfl

theorem matT_apply (γ : UF E n) (τ : ι) (i j : Fin n) : matT emb γ τ i j = emb τ (γ.1 (Pi.single j 1) i) := by
  unfold matT
  rw [Matrix.map_apply]
  congr 1

theorem rho_coe (lam : ι → DomWeight n) (γ : UF E n) (v : DIV.VV K lam) :
    ((((rhoVr emb lam).comp (ufGL E n)) γ v : DIV.VV K lam) : Pol K ι n) =
      (∏ τ, (emb τ ((LinearEquiv.det γ.1 : Eˣ) : E)) ^ (-(lam τ).detShift)) • Formalism.GradedWeylDivisibility.blockAct K (matT emb γ⁻¹) (v : Pol K ι n) := by
  show actP lam (invTrK (embGL emb (ufGL E n γ))) (v : Pol K ι n) = _
  unfold actP
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  congr 1
  · unfold detTwK
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← det_matT emb γ τ]
    unfold detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    show (((((Formalism.UG.bc (emb τ) (ufGL E n γ))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).transpose).det ^ _ = _
    rw [Matrix.det_transpose, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_zpow, zpow_neg]
    rfl

end Rho

end TE

section Main

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem pullV_eq (γ : UF X.E a) (γ' : UF X.E b) (z : VCx X.Tau a b) :
    A.pullV a b γ.1 γ'.1 z =
      TE.mulL (fun τ => (TE.matT X.emb γ'⁻¹ τ).map A.σ₀) (fun τ => (TE.matT X.emb γ τ).map A.σ₀) z := by
  funext τ i j
  rw [TE.mulL_apply]
  unfold Amb.pullV
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, TE.matT_apply, TE.matT_apply]
  rfl

theorem scal_a {ι K : Type} [Fintype ι] [Field K] (d : ι → K) (hd : ∀ τ, d τ ≠ 0) (e s : ι → ℤ) (n : ι → ℕ) (B : ℕ)
    (hw : ∀ τ, (n τ : ℤ) + (B : ℤ) - e τ = s τ) :
    (∏ τ, d τ ^ (-(e τ))) * (∏ τ, d τ) ^ (B : ℤ) * ∏ τ, d τ ^ n τ = ∏ τ, (d τ)⁻¹ ^ (-(s τ)) := by
  rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_natCast (d τ) (n τ), ← zpow_add₀ (hd τ), ← zpow_add₀ (hd τ), inv_zpow', neg_neg]
  congr 1
  have := hw τ
  omega

theorem scal_b {ι K : Type} [Fintype ι] [Field K] (d : ι → K) (hd : ∀ τ, d τ ≠ 0) (e s : ι → ℤ) (B : ℕ)
    (hw : ∀ τ, e τ - (B : ℤ) = -(s τ)) :
    (∏ τ, d τ ^ (-(e τ)))⁻¹ * (∏ τ, d τ) ^ (-(B : ℤ)) = ∏ τ, d τ ^ (-(s τ)) := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_neg, neg_neg, ← zpow_add₀ (hd τ)]
  congr 1
  have := hw τ
  omega

theorem thEquivP_of (e : X.Tau → ℤ) (hV : JetInVV X.K lam lam' n) (hrat : A.JetsRat a b Sall D) (hAn : A.IndOmega a b Sall D)
    (hInd : A.ThIndEq a b Sall D) (hChi : A.ChiLaw a b) (hMa : MuProdLaw a sel SB mU mI e) (hMb : MuProdLaw b sel SB mU mI e)
    (hW : WtLaw lam lam' n e) :
    ThEquivP (thDistC A Sall SB D sel mU mI lam lam' n) Sall D ((rhoVr X.emb lam).comp (ufGL X.E a)) ((rhoVr X.emb lam').comp (ufGL X.E b)) := by
  intro γ γ' N fr N' fr' c x hR
  have hR' : InRange Sall D c (gmap γ.1 N) (gmap γ'.1 N') (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) :=
    ⟨isSdLat_gmap hR.1 γ, isSdLat_gmap hR.2.1 γ', hR.2.2.1, hR.2.2.2.1, (divLat_gmap_iff Sall D γ.1 γ'.1 N N' x).2 hR.2.2.2.2⟩
  unfold thDistC
  rw [if_pos ⟨hR'.2.2.2.1, hR'.2.2.2.2⟩, if_pos ⟨hR.2.2.2.1, hR.2.2.2.2⟩]
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  obtain ⟨d, hd⟩ : ∃ d : X.Tau → X.K, d = fun τ => X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : X.Tau → X.K, d' = fun τ => X.emb τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) := ⟨_, rfl⟩
  have hdτ : ∀ τ, X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = d τ := fun τ => by rw [hd]
  have hdτ' : ∀ τ, X.emb τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) = d' τ := fun τ => by rw [hd']
  have hd0 : ∀ τ, d τ ≠ 0 := fun τ => by rw [← hdτ]; exact (map_ne_zero (X.emb τ)).2 (Units.ne_zero _)
  have hd0' : ∀ τ, d' τ ≠ 0 := fun τ => by rw [← hdτ']; exact (map_ne_zero (X.emb τ)).2 (Units.ne_zero _)
  have hinv : ∀ τ, X.emb τ ((LinearEquiv.det (γ⁻¹ : UF X.E a).1 : X.Eˣ) : X.E) = (d τ)⁻¹ := by
    intro τ
    rw [← hdτ, InvMemClass.coe_inv, map_inv, Units.val_inv_eq_inv_val, map_inv₀]
  have hpull := TE.jetMap_pull A.σ₀ A.cD (A.thInd Sall N N' c x) (hAn N N' c x hR) (TE.matT X.emb γ) (TE.matT X.emb γ'⁻¹)
    (TE.mulL (fun τ => (TE.matT X.emb γ'⁻¹ τ).map A.σ₀) (fun τ => (TE.matT X.emb γ τ).map A.σ₀))
    (fun k => TE.mulL_coordX _ _ k)
    (A.jetK Sall N N' c x) (A.jetK Sall (gmap γ.1 N) (gmap γ'.1 N') c (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap))
    (A.chiF a b N N')⁻¹ (A.chiF a b (gmap γ.1 N) (gmap γ'.1 N'))⁻¹ (jetK_spec A Sall D hrat N N' c x hR)
    (by
      intro m
      rw [jetK_spec A Sall D hrat _ _ c _ hR' m]
      congr 2
      funext z
      rw [hInd γ γ' N N' c x hR z, pullV_eq])
    ((∏ τ, d τ) ^ ((b / 2 : ℕ) : ℤ) * (∏ τ, d' τ) ^ (-((a / 2 : ℕ) : ℤ)))
    (by
      rw [hChi γ γ' N N' hR.1 hR.2.1, mul_inv, mul_inv, ← zpow_neg, neg_neg, ← zpow_neg, map_mul, map_zpow₀, map_zpow₀, map_prod, map_prod]
      simp only [hd, hd']
      rfl)
    n (P : Pol X.K X.Tau a)
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, Submodule.coe_smul,
    Submodule.coe_smul, jetOp_coe lam lam' n hV, TE.rho_coe, jetOp_coe lam lam' n hV, TE.rho_coe, inv_inv, hpull,
    hMa γ N fr hR.1, hMb γ' N' fr' hR.2.1]
  simp only [map_smul, smul_smul, TE.det_matT, hinv, hdτ, hdτ']
  congr 1
  have A1 := scal_a d hd0 e (fun τ => (lam τ).detShift) n (b / 2) hW.1
  have A2 := scal_b d' hd0' e (fun τ => (lam' τ).detShift) (a / 2) hW.2
  rw [← A1, ← A2, mul_inv]
  ring

end Main

end Formalism.L2.Ker
