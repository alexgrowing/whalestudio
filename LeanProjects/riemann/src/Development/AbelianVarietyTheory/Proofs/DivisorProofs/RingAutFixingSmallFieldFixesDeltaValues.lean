import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterIsLadicOfFiniteOrderHecke

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.SeriesTie
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.JoinChr (IsPlIdem locE)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DeltaFixed

theorem aut_fixes_delta_values : ∀ {D : D7} (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (χ : HChar D.host.E),
    ChrEq (ρ.B i j b).de.chi χ → χ.ValuesIn 0 (embLL0 D) → ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (embLL0 D y) = embLL0 D y) →
    ∀ σ, τ (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  intro D ρ hρ i j b χ hχ hval τ hτ σ
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  set f : D.ntw.O0 i →+* ℂ := (ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)) with hf

  have hker : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := by
    cases b
    · have e : (ψ.ker : Set (G D.host.E D.nd.Om)) = ((D.ntw.delta i).ker : Set _) := by
        ext g
        simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
      rw [e]
      exact D.ntw.delta_open i
    · simpa [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt] using D.ntw.delta_open i

  have hram : ∀ v, v ∉ D.ntw.pD i → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ g ∈ Ine (F := D.host.E) A, ψ g = 1 := by
    intro v hv A hA g hg
    have h1 : D.ntw.delta i g = 1 := by
      by_contra h
      exact hv ((D.ntw.delta_ram i v A hA).1 ⟨g, hg, h⟩)
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h1]

  haveI : Finite (G D.host.E D.nd.Om ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hker
  have hn : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpow : ∀ g, ψ g ^ ψ.ker.index = 1 := fun g => by
    rw [← map_pow]
    exact (MonoidHom.mem_ker).1 (Subgroup.pow_index_mem _ g)

  have hchi : ChrEq (charOf ρ.rc f ψ) χ := by
    have := hχ
    rw [hρ.delta i j b] at this
    exact this

  let r' : G D.host.E D.nd.Om →* ℂˣ := (Units.map f.toMonoidHom).comp ψ
  let r : G D.host.E D.nd.Om →* ℂˣ := (Units.map ((τ : ℂ →+* ℂ).comp f).toMonoidHom).comp ψ
  have hr' : Continuous r' := GlobalTheory.DeltaGal.continuous_comp_of_isOpen_ker ψ hker (Units.map f.toMonoidHom)
  have hr : Continuous r := GlobalTheory.DeltaGal.continuous_comp_of_isOpen_ker ψ hker (Units.map ((τ : ℂ →+* ℂ).comp f).toMonoidHom)
  have hart : IsGlobalArtin ρ.rc.art := hρ.rc.artin
  obtain ⟨_, _, _, _, hidem, _⟩ := GlobalTheory.EtaProduct.exists_ev D
  have key : r = r' := by
    refine GlobalTheory.GalChar.eq_of_frob hart hr hr' ?_
    have h1 := GlobalTheory.GalChar.unr_ae χ
    have h2 : ∀ᶠ v in Filter.cofinite, v ∉ D.ntw.pD i :=
      Filter.eventually_cofinite.2 (by simpa using (D.ntw.pD i).finite_toSet)
    filter_upwards [h1, h2] with v hunr hv A hA s hs

    obtain ⟨x0, hx0, hx0a⟩ := (hart.frob v A hA (toAb D.host.E D.nd.Om s⁻¹)).2 ⟨s, hs, rfl⟩

    set k := unif v
    have hk : IsUnifAt v (atFin v k) := unif_spec v
    have hu : IsUnitAt v (x0 * (atFin v k)⁻¹) := by
      unfold IsUnitAt
      unfold IsUnifAt at hx0 hk
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx0, hk]
      exact mul_inv_cancel₀ (by simp)
    obtain ⟨t, ht, hta⟩ := GlobalTheory.GalChar.exists_ine hart hA hu
    have hψt : ψ t = 1 := hram v hv A hA t ht

    obtain ⟨e, he⟩ := hidem v
    let xe : (Formalism.L2.Theta.AE D)ˣ := (Formalism.L2.JoinChr.isUnit_locE he.1 k).unit
    have hxe : ρ.rc.sym xe = toAb D.host.E D.nd.Om (t⁻¹ * s⁻¹) := by
      have e1 : Units.map ρ.rc.κ.toMonoidHom xe = Neutral.B1.localIdele D.host.E v (atFin v k) := by
        apply Units.ext
        exact hρ.rc.loc v e he k
      have e2 : atFin v k = (x0 * (atFin v k)⁻¹)⁻¹ * x0 := by group
      change ρ.rc.art (Units.map ρ.rc.κ.toMonoidHom xe) = _
      rw [e1, e2, map_mul, map_mul, map_inv, map_inv, hta, hx0a, ← map_inv, ← map_mul]
    have hc := charOf_eq ρ.rc f hker hxe hn (hpow _)
    have hc2 := hchi.2 v e he k xe rfl
    have hloc : χ.locK v k = χ.val v := χ.val_eq hunr _ hk
    obtain ⟨y, hy⟩ := hval v hunr
    have hy' : embLL0 D y = ((χ.val v : ℂˣ) : ℂ) := by
      rw [hy, HChar.valTw]
      simp
    have hfs : f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = embLL0 D y⁻¹ := by
      have h3 : f ((ψ (t⁻¹ * s⁻¹) : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = embLL0 D y := by
        rw [← hc, hc2, hloc, hy']
      rw [map_mul, map_inv, map_inv, hψt, inv_one, one_mul, map_units_inv] at h3
      rw [map_inv₀, ← h3, inv_inv]
    apply Units.ext
    show τ (f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) = f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)
    rw [hfs]
    exact hτ _
  have := congrArg (fun φ : G D.host.E D.nd.Om →* ℂˣ => ((φ σ : ℂˣ) : ℂ)) key
  exact this

end GlobalTheory.DeltaFixed

end
