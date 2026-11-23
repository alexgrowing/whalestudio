import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiesOverFramedOfSquareLevelMoves
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevMoveCommLevelMapOfTrivialModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureChangeFramedGeometricPointUniqueStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevOrbit

def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Submodule R M) (f g : M →ₗ[R] M)
    (hK : ∀ a ∈ K, f a ∈ K) (hK' : ∀ a ∈ K, g a ∈ K) (hfg : ∀ a, f (g a) - a ∈ K) (hgf : ∀ a, g (f a) - a ∈ K) :
    (M ⧸ K) ≃ₗ[R] (M ⧸ K) :=
  LinearEquiv.ofLinear (K.mapQ K f (fun a ha => hK a ha)) (K.mapQ K g (fun a ha => hK' a ha))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hfg a))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hgf a))

theorem smul_top_comap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    ∀ a ∈ (I • ⊤ : Submodule R M), f a ∈ (I • ⊤ : Submodule R M) := by
  have h : (I • ⊤ : Submodule R M) ≤ (I • ⊤ : Submodule R M).comap f := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact fun a ha => h ha

theorem exists_gam_of_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (g : Sim Dw) :
    ∃ γ : Gam Dw l₂, ∀ a, γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f l₂.M a) := by
  obtain ⟨h, hh⟩ := g.inv l₂.M (GlobalTheory.LevelFibre.level_pos l₂)
  exact ⟨quotEquiv _ (g.f l₂.M) h (smul_top_comap _ _) (smul_top_comap _ _)
    (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).2) (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).1),
    fun a => rfl⟩

theorem fibre_torsor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → (FrOver d y₂' y ↔ ∃ γ, CongMod l.Mb (lift γ) LinearMap.id ∧ levR (lift γ, LinearMap.id) y₂ y₂') ∧ ∀ γ γ', levR (lift γ, LinearMap.id) y₂ y₂' → levR (lift γ', LinearMap.id) y₂ y₂' → γ = γ' := by
  intro E _ _ _ H Dw l Xo c d hpq hlev hA hbase lift hlift k _ _ _ _ hk y₂ y₂' y hy
  obtain ⟨hd, hM, -, -, -, hE, -, -, -⟩ := id hlev
  have hLaws : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hN := GlobalTheory.levelMaps_closed hLaws E H Dw hpq
  refine ⟨⟨fun h' => ?_, fun ⟨γ, hγ, hr⟩ => ?_⟩, fun γ γ' h₁ h₂ => GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique E H Dw d.l₂ d.Xo₂ d.c₂ hpq hA lift hlift k y₂ y₂' γ γ' h₁ h₂⟩
  · obtain ⟨g, ρ, ν, hg, -, hmv, hfr⟩ :=
      GlobalTheory.exists_levMove_of_frOver hLaws E H Dw l Xo c 0 d hN hd hM hE d.r d.m hE k hk y y₂ y₂' hy h'
    obtain ⟨γ, hγ⟩ := exists_gam_of_sim d.l₂ g
    have hl : ∀ a, lift γ a - g.f d.l₂.M a ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
      have e := congrArg (fun f => f a) (hlift γ)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, hγ] at e
      exact (Submodule.Quotient.eq _).1 e
    refine ⟨γ, fun a => ?_, (GlobalTheory.LevelActionOfLifts.levR_congr hl y₂ y₂').2 ⟨ρ.hom, ν, inferInstance,
      ⟨hmv.1, hmv.2.1, fun a => ?_⟩, hfr⟩⟩
    · have h1 : lift γ a - g.f d.l₂.M a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
        Submodule.smul_mono_left hd.2.1 (hl a)
      have h2 := GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg a
      have := Submodule.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at this
    · have e : ∀ x x', d.Xo₂.univ.etaA x = d.Xo₂.univ.etaA x' := fun x x' => by
        have h1 := d.Xo₂.univ.etaA_ker x
        have h2 := d.Xo₂.univ.etaA_ker x'
        rw [hA, one_smul] at h1 h2
        rw [h1, h2]
      rw [e (LinearMap.id a) (g.f d.l₂.A a)]
      exact hmv.2.2 a
  · obtain ⟨ρ₂, ν₂, hi, hmv, hfr⟩ := hr
    obtain ⟨e₁, e₂⟩ := GlobalTheory.T.levMove_comp_r_eq_of_trivial_mod E H Dw l Xo c 0 d hpq hlev hA hbase ρ₂ ν₂ (lift γ) LinearMap.id hi hmv hγ
    obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
    exact GlobalTheory.frOver_of_square_of_frMove E H Dw l Xo c 0 d (𝟙 _) ι ρ₂ ν₂ d.r d.m (by rw [e₁, Category.comp_id])
      (by rw [e₂, hι, Category.comp_id]) k y y y₂ y₂' hy (hone k y) hfr

end GlobalTheory.LevOrbit
