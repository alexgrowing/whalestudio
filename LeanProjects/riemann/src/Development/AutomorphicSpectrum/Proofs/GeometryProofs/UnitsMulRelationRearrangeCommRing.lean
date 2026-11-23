import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetLeftMem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusGeneratorCorrespondenceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermTorsionLiftCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermFrobeniusTorsionSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetUnitOnChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusTorsionGeneratorRelationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetQuotientFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetAugmentationOnePthPowerStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDifferenceGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGeneratorCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem units_mul_relation_rearrange_commRing {Q : Type} [CommRing Q] (D F V : Q) (h : D * D = 0) :
    (1 + D * F) * (1 + D * (V - F)) = 1 + D * V := by
  linear_combination (F * (V - F)) * h

set_option maxHeartbeats 4000000 in

theorem pfold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (gs : Germ.PS k 2 d), AxOne gs → pow1 g.B p = Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] gs → ∀ y : Tm x p ⟶ t.G, y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → y ^ p = 1 → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ (∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1) ∧ ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∀ m : ℕ, ∃ v : Jet k (Fin 1 × Fin d) m, ∀ h : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j₀), ((rQ t.G x p (g.x m)).appLE _ ⊤ h).hom (C.s fun _ => j₀).val = toΓ _ (1 + dQ _ p ^ p * algebraMap _ _ (v ^ p - psJet m (dSer gs fun i => w i ^ p))) := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ x d g w gs hax hpow y hy hy0 hyp
  obtain ⟨κ, hκ, hκ2, hκ3⟩ := GlobalTheory.T.line_bundle_generator_correspondence E H hstar X0 t p
  have hy1 : spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ y.left =
      spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ (1 : Tm x p ⟶ t.G).left := by
    have e₁ := congrArg (fun q => q.left) hy0
    have e₂ : homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ (1 : Tm x p ⟶ t.G) = 1 := by simp [Hom.one_def]
    exact e₁.trans (congrArg (fun q => q.left) e₂).symm
  obtain ⟨τ, hτ, hτ1⟩ := GlobalTheory.T.line_bundle_section_difference_generator t.G.left t.PP.L t.PP.isLB k p y.left (1 : Tm x p ⟶ t.G).left hy1
  obtain ⟨C, hC, hCv⟩ := GlobalTheory.T.frobenius_torsion_generator_relation E H X0 t k x p y hyp κ hκ τ hτ
  refine ⟨C, hC, GlobalTheory.T.frobenius_generator_correspondence E H X0 t k x p y hy0 κ hκ2 τ hτ1 C hCv, fun j₀ hj₀ m => ?_⟩
  obtain ⟨u, hu, hκ3'⟩ := hκ3 k x d g (p + m + 1)
  obtain ⟨e₀, he₀, hve⟩ := GlobalTheory.T.germ_jet_unit_on_chart E H X0 t k p x d g w m j₀ hj₀
  obtain ⟨τ₀, hτ₀, hvτ⟩ := GlobalTheory.T.jet_section_generator_value E H X0 t k x p y (Jet k (Fin 1 × Fin d) m) hy0 τ hτ1 j₀ hj₀
  have hp0 : ((p : ℕ) : Jet k (Fin 1 × Fin d) m) = 0 := by
    have : ((p : ℕ) : k) = 0 := CharP.cast_eq_zero k p
    rw [← map_natCast (algebraMap k (Jet k (Fin 1 × Fin d) m)), this, map_zero]
  obtain ⟨v, hv⟩ := GlobalTheory.T.jet_augmentation_one_pth_power (Jet k (Fin 1 × Fin d) m) p hp0 ((e₀ * τ₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ) : Jet (Jet k (Fin 1 × Fin d) m) Unit p) (by
    rw [Units.val_mul, map_mul, he₀, hτ₀, _root_.one_mul])
  refine ⟨v, fun h => ?_⟩
  have hju : jq w p m (u : Jet k (Fin 2 × Fin d) (p + m + 1)) = 1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer gs fun i => w i ^ p)) := by
    rw [hu, hpow]
    exact GlobalTheory.T.germ_jet_quotient_formula k p d m w gs hax
  let f : Jet k (Fin 2 × Fin d) (p + m + 1) →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p := (jq w p m : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] _)
  let ν : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ := Units.map (f : _ →* Jet (Jet k (Fin 1 × Fin d) m) Unit p) u
  let U : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ := ν⁻¹ * (e₀ * τ₀) ^ p
  have hU : (U : Jet (Jet k (Fin 1 × Fin d) m) Unit p) = 1 + dQ _ p ^ p * algebraMap _ _ (v ^ p - psJet m (dSer gs fun i => w i ^ p)) := by
    have h2p : dQ (Jet k (Fin 1 × Fin d) m) p ^ p * dQ (Jet k (Fin 1 × Fin d) m) p ^ p = 0 := by
      rw [← pow_add]
      exact pow_eq_zero_of_le (by have := (Fact.out : p.Prime).one_lt; omega) (dQ_pow _ p)
    have e := units_mul_relation_rearrange_commRing (dQ (Jet k (Fin 1 × Fin d) m) p ^ p) (algebraMap _ _ (psJet m (dSer gs fun i => w i ^ p))) (algebraMap _ _ (v ^ p)) h2p
    rw [← hju, ← hv, ← map_sub] at e
    show ((ν⁻¹ * (e₀ * τ₀) ^ p : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ) : Jet (Jet k (Fin 1 × Fin d) m) Unit p) = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ← e]
    exact Units.inv_mul_cancel_left ν _
  have hval : ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p))
      (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) →
      val C (rQ t.G x p (g.x m)) z J = gm (𝟙 _) z ⊤ (unitΓ U) := by
    intro z J hJ hJ₀
    have hk : val κ (rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J =
        gm (𝟙 _) z ⊤ (unitΓ ν) * (gm (𝟙 _) z ⊤ (unitΓ e₀) ^ p)⁻¹ := by
      have e₁ : val κ (rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J =
          val (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left) (homAt x (jq w p m)).left z J := by
        rw [GlobalTheory.T.germ_torsion_lift_compat E H X0 t k p x d g w m y hy]
        exact (val_pull hJ _ _ _).symm
      refine e₁.trans ((val_corr hJ hκ3' _).trans ((Pf.val_scale t _ _ _ _ _ z hJ).trans ?_))
      refine (congrArg (gm (spMap f) z ⊤ (unitΓ u) * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (GlobalTheory.T.germ_frobenius_torsion_section E H hstar X0 t k p x d g w m (hy ▸ hyp) z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹)
          ((Pf.val_genPow t _ _ _ p _ z J).trans (congrArg (· ^ p) (hve z J hJ hJ₀)))))))).trans ?_
      rw [_root_.one_mul]
      exact congrArg (· * _) (Pf.gm_spMap f u z)
    have ht : val τ (rQ t.G x p (g.x m) ≫ (fst (Tm x p) t.G).left) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
      rw [rQ_fst]
      exact hvτ z J hJ hJ₀
    rw [hCv _ _ z J hJ, hk, ht]
    let Φ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ →* ((Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)).presheaf.stalk z)ˣ :=
      (gm (𝟙 _) z ⊤).comp (Units.map (toΓ _).toMonoidHom)
    show (Φ ν * (Φ e₀ ^ p)⁻¹)⁻¹ * Φ τ₀ ^ p = Φ (ν⁻¹ * (e₀ * τ₀) ^ p)
    rw [map_mul Φ, map_inv Φ, map_pow Φ, map_mul Φ, mul_pow, mul_inv, inv_inv, _root_.mul_assoc]
  apply fn_ext
  intro z _
  have hz : rQ t.G x p (g.x m) z ∈ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j₀) := h trivial
  classical
  choose c hc using fun χ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left => exists_chart t.PP.isLB (χ z)
  let J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι := fun ψ => if ψ z ∈ t.PP.L.U j₀ then j₀ else c ψ
  have hJ₀ : ∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀ := fun ψ e => if_pos e
  have hJ : Good t.PP.L z J := fun ψ => by
    by_cases e : ψ z ∈ t.PP.L.U j₀
    · rw [hJ₀ ψ e]; exact e
    · show ψ z ∈ t.PP.L.U (if ψ z ∈ t.PP.L.U j₀ then j₀ else c ψ)
      rw [if_neg e]; exact hc ψ
  have e := val_of C (rQ t.G x p (g.x m)) z J (fun _ => j₀) (fun i => hJ₀ _ (Set.mem_iInter.1 hz i))
  refine (Pf.gs_appLE _ _ _ h z trivial _).trans ((gs_unit _ z _ hz _).trans ?_)
  refine (congrArg Units.val (e.symm.trans (hval z J hJ hJ₀))).trans ?_
  rw [← hU]
  exact (gs_unit (𝟙 _) z ⊤ trivial (unitΓ U)).symm

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
