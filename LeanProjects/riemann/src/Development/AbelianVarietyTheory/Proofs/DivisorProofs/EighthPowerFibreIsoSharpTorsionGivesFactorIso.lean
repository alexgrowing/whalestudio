import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoEqCoordinatewisePowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8WeightedBundleIsoPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.Poinc.Sep.conj_fibre_eighth_root : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  intro l hl hlo W hW j hj V V₁ _ _ _ _ _ hlu Q ρ hρ D e hSh K _ _ ev σ f hf hL ht hc a p hpf hps
  obtain ⟨pr, w, hmon, huniv, hwgen, hc4, -⟩ := hSh
  obtain ⟨f₁, hf₁, hcomp⟩ := GlobalTheory.T.eighth_power_fibre_iso_eq_coordinatewise_power l hl hlo W hW j hj V V₁ hlu Q ρ hρ D pr w hmon huniv hwgen K ev σ f hf hL ht
  have hw : f₁ ≫ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).hom = ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).hom := by
    simpa using hf₁.1.w
  let f' : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) := Over.homMk f₁ hw
  have hsq : IsSquare f₁ (f' ⊗ₘ f').left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst]; rfl
    · rw [← Over.comp_left, tensorHom_snd]; rfl
  refine ⟨f₁, (f' ⊗ₘ f').left, hf₁, hsq, ?_, ?_⟩
  · intro ψ₀ ψσ h0 hσ
    exact GlobalTheory.T.exists_e8_weighted_bundle_iso_pullback W hW V V₁ Q ρ D pr w hmon huniv hwgen K ev σ f hf hL f₁ hf₁ hcomp _ hsq ψ₀ ψσ h0 hσ
  · let mu0 : Fin 8 → Q.X := Pi.single 0 a
    have hsec : (spMap ev ≫ (D.c (e mu0)).left) ≫ D.P.A.hom = 𝟙 _ ≫ spMap ev := by
      rw [Category.assoc, Over.w]; simp
    let q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left := pullback.lift (spMap ev ≫ (D.c (e mu0)).left) (𝟙 _) hsec
    have hq1 : q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu0)).left := pullback.lift_fst _ _ _
    have hq2 : q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ := pullback.lift_snd _ _ _
    have hspc : spMap (ev.comp ρ) = spMap ev ≫ spMap ρ := by
      simp [spMap]
    have e1 : p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = q ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr 0).left ≫ pullback.fst Q.B.hom (spMap ρ) := by
      rw [hpf, reassoc_of% hq1, ← Over.comp_left_assoc, hc4, hspc, Category.assoc]
      simp [mu0]
    have e2 : p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = q ≫ pullback.snd D.P.A.hom (spMap ev) := by
      rw [hps, hq2]
    have h1 := hcomp 0 _ q p e1 e2
    have h2 := hc mu0 q hq1 hq2
    rw [← h1, reassoc_of% h2, e1]
