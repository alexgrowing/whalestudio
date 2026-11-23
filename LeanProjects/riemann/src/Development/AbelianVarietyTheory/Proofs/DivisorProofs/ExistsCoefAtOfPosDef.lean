import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CoefModel

section BaseChange

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (lam : ι → DomWeight n)

theorem fockS_map_int {s : Type} (P : MvPolynomial s ℤ) (g : MvPolynomial s K) :
    fockS (map φ (map (Int.castRingHom K) P)) (map φ g) = φ (fockS (map (Int.castRingHom K) P) g) := by
  rw [fockS_eq_sum _ _ (map (Int.castRingHom K) P).support (support_map_subset _ _), fockS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem pairK_mapVV_int (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) (P : MvPolynomial (ι × Fin n × Fin n) ℤ)
    (hx : (x : Pol K ι n) = map (Int.castRingHom K) P) :
    pairK lam (fun τ => (G τ).map φ) (mapVV φ lam x) (mapVV φ lam y) = φ (pairK lam G x y) := by
  have h1 : (map φ).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).toRingHom =
      (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) fun τ => ((G τ).map φ)ᵀ).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp [blockAct_X]
  have h2 : map φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((G τ).map φ)ᵀ) (map φ y.1) :=
    congrArg (fun ψ : Pol K ι n →+* Pol ℂ ι n => ψ y.1) h1
  have h3 : φ (gramTw lam G) = gramTw lam fun τ => (G τ).map φ := by
    unfold gramTw
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  have h4 : φ (extNorm K lam) = extNorm ℂ lam := by
    unfold extNorm
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← map_extremal φ n (lam τ), ← map_extremal (Int.castRingHom K) n (lam τ), fockS_map_int]
  have h5 := fockS_map_int φ P (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1)
  rw [← hx] at h5
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, mapVV_coe, mapVV_coe, ← h2, fockL_apply, fockL_apply,
    h5, map_mul, map_div₀, h3, h4]

end BaseChange

def reindexFam {ι M : Type} [Monoid M] (e : ι → ι) : (ι → M) →* (ι → M) :=
  MonoidHom.pi fun τ => Pi.evalMonoidHom (fun _ => M) (e τ)

theorem reindexFam_apply {ι M : Type} [Monoid M] (e : ι → ι) (g : ι → M) (τ : ι) : reindexFam e g τ = g (e τ) := rfl

end GlobalTheory.CoefModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefModel

variable {D : D7}

theorem exists_coef_round_at (V : HSp D) (hV : ∀ τ, (V.gram.map (tauE D τ)).PosDef)
    (lam : D.what₂.Tau → DomWeight V.rank) (σ : D.what₂.LL →+* ℂ) (p : D.what₂.Tau ≃ D.what₂.Tau)
    (hp : ∀ τ, labE σ τ = tauE D (p τ)) :
    ∃ (c : CoefA V) (c₁ : VV D.what₂.LL lam →ₛₗ[σ] c.W), c.Is ∧
      (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
        ∀ v, c₁ (rhoVr (labLL D) lam γE v) = c.ρ (γ : GA D V) (c₁ v)) ∧
      (LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL lam a)) ∧
      Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL lam a)) = ⊤ ∧
      ∀ a y, inner ℂ (c₁ (bVV D.what₂.LL lam a)) (c₁ y) = σ (pairVr (labLL D) lam V.gram (bVV D.what₂.LL lam a) y) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨hc, hs⟩ := realGL_laws hθ V
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hG : ∀ τ, (((V.gram.map (tauE D (p τ)))⁻¹)ᵀ).PosDef := fun τ => (hV (p τ)).inv.transpose
  have hlab : ∀ τ x, σ (labLL D τ x) = tauE D (p τ) x := fun τ x => DFunLike.congr_fun (hp τ) x
  refine ⟨coefOf lam hG (invTrK.comp ((reindexFam p).comp (realGL θ V))),
    (toHilb lam hG).toLinearMap.comp (mapVV σ lam), coefOf_is lam hG _ (fun h hh => ?_) (fun h τ => ?_)
      (fun τ => ?_) (fun g hg => ?_), fun γ γE hγ v => ?_, ?_, ?_, fun a y => ?_⟩
  · have : realGL θ V h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom V h) = 1
      rw [show infHom V h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, this, map_one, map_one]
  · exact invTr_unitary (g := realGL θ V h (p τ)) (GlobalTheory.RecDictModel.archM_unitary V (hθ (p τ)) h)
  · refine ((hc (p τ)).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ (p τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (reindexFam p.symm (invTrK g)) fun ρ => by
      have := invTr_unitary (hg (p.symm ρ))
      rwa [p.apply_symm_apply, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (hV ρ).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e]
    refine funext fun τ => ?_
    show inside₂ ℂ _ (inside₂ ℂ _ (g (p.symm (p τ)))) = g τ
    rw [p.symm_apply_apply, invTr_invTr]
  · show toHilb lam hG (mapVV _ lam (rhoK lam (invTrK (embGL (labLL D) γE)) v)) =
      rhoH lam hG (invTrK (reindexFam p (realGL θ V γ))) (toHilb lam hG (mapVV _ lam v))
    have e : (fun τ => Formalism.UG.bc σ (invTrK (embGL (labLL D) γE) τ)) = invTrK (reindexFam p (realGL θ V γ)) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, reindexFam_apply, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    rw [rhoH_toHilb, mapVV_rhoK, e]
  · exact (linearIndependent_mapVV σ lam).map' (toHilb lam hG).toLinearMap (LinearEquiv.ker _)
  · exact span_mapVV σ lam
  · obtain ⟨P, hP⟩ := bVVfun_int D.what₂.LL lam a
    show inner ℂ (toHilb lam hG (mapVV σ lam (bVV D.what₂.LL lam a))) (toHilb lam hG (mapVV σ lam y)) =
      σ (pairK lam (gramKd (labLL D) V.gram) (bVV D.what₂.LL lam a) y)
    rw [inner_toHilb, ← pairK_mapVV_int σ lam _ _ y P ((bVV_coe _ lam a).trans hP)]
    have e : (fun τ => ((V.gram.map (tauE D (p τ)))⁻¹)ᵀ) = fun τ => (gramKd (labLL D) V.gram τ).map σ := by
      funext τ
      have e1 : V.gram.map (tauE D (p τ)) = (V.gram.map (labLL D τ)).map σ := by
        ext a b
        exact (hlab _ _).symm
      have hu : IsUnit (V.gram.map (labLL D τ)).det := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact ((_root_.map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)).isUnit
      rw [gramKd, Matrix.transpose_map, e1]
      congr 1
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg (fun G => pairK lam G (mapVV σ lam (bVV D.what₂.LL lam a)) (mapVV σ lam y)) e

theorem exists_coefAt_of_posDef (i : Fin D.R.m) (h : (Vc D i).IsPosDef) (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) :
    ∃ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ := by
  have hl := (GlobalTheory.GalLift.labels_overK σ).1 hσ
  have hV : ∀ τ, ((Vc D i).gram.map (tauE D τ)).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [h (tauE D τ)] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hg : gramV D i = (Vc D i).gram := by
    rw [gramV, GlobalTheory.StdFrame.neg_eq_false_of_posDef D i h, if_neg Bool.false_ne_true]
  have H := exists_coef_round_at (Vc D i) hV (lamV D i) σ (Equiv.ofBijective _ hl.1).symm fun τ =>
    (congrArg (labE σ) ((Equiv.ofBijective _ hl.1).apply_symm_apply τ).symm).trans (hl.2 _)
  obtain ⟨c, c₁, h1, h2, h3, h4, h5⟩ := H
  exact ⟨c, c₁, h1, h2, h3, h4, fun a b => hg ▸ h5 a _⟩

end GlobalTheory.CoefModel
