import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPlaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorLevelIndependentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperatorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSph

theorem satU_of_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v → NG.SatAt { a with S := S, irrS := hS } Dv α → ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ f ∈ S, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
  intro L _ _ _ n a S hS v w Dv α _ hsat U hU f hfS hfU h hh
  obtain ⟨f₀, hf₀S, hf₀0, U', hf₀U', hU', hH⟩ := hsat
  have hf₀S' : f₀ ∈ S := hf₀S
  have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
    fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
  have hUmax : ∀ κ : GAf L n, TrivOutside {v} κ → (κ ∈ Umax L n ↔ κ ∈ Umax L n) := fun _ _ => Iff.rfl
  let ρ : GAf L n →* Module.End ℂ (GAf L n → a.W) :=
    { toFun := fun g => NG.rt L n g
      map_one' := LinearMap.ext fun φ => funext fun x => by
        show φ (x * 1) = φ x
        rw [mul_one]
      map_mul' := fun g g' => LinearMap.ext fun φ => funext fun x => by
        show φ (x * (g * g')) = φ (x * g * g')
        rw [mul_assoc] }
  have hρ : ∀ g φ, ρ g φ = NG.rt L n g φ := fun _ _ => rfl
  have hf₀K : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f₀ = f₀ :=
    fun κ hκ ht => hf₀U' κ ((hU' κ ht).2 hκ)
  have hfK : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f :=
    fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)
  have hrtc : ∀ (φ : GAf L n → a.W) (x b : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ b →
      NG.rt L n x (NG.rt L n b φ) = NG.rt L n b (NG.rt L n x φ) := by
    intro φ x b hx hb
    funext y
    show φ (y * x * b) = φ (y * b * x)
    rw [mul_assoc, mul_assoc, (GlobalTheory.InertSph.commute_of_trivOutside v x b hx hb).eq]
  have hrtm : ∀ (φ : GAf L n → a.W) (x b : GAf L n),
      NG.rt L n x (NG.rt L n b φ) = NG.rt L n (x * b) φ := by
    intro φ x b
    funext y
    show φ (y * x * b) = φ (y * (x * b))
    rw [mul_assoc]

  have hloc := fun x (hx : TrivOutside {v} x) => GlobalTheory.T.inertDoubleCosetOperator_eq_inertHeckeOperator L n v w Dv (GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv) (GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv)
    (GlobalTheory.T.exists_trivOutside_inertDatum_local_eq L n v w Dv) (GlobalTheory.T.inertDatum_local_injective_on_trivOutside L n v w Dv) x hx
  choose! R ha hR hha hA using hloc
  have hχ : ∀ x, TrivOutside {v} x → ∑ γ ∈ R x, NG.rt L n γ f₀ =
      Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) (ha x) α • f₀ := by
    intro x hx
    rw [hA x hx a.W f₀ hf₀K, GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) U' hUmax hU' a.W (ha x) (hha x hx).1 f₀ hf₀K]
    exact hH _ (hha x hx)

  let W' : Submodule ℂ (GAf L n → a.W) :=
    Submodule.span ℂ (Set.range fun b : {b : GAf L n // TrivOutside {v}ᶜ b} => NG.rt L n (b : GAf L n) f₀)
  have hgen : ∀ b : GAf L n, TrivOutside {v}ᶜ b → NG.rt L n b f₀ ∈ W' :=
    fun b hb => Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  have hW : W' ≤ GlobalTheory.SphScalar.fixS ρ S (GlobalTheory.InertSph.Kv L n v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    refine ⟨hS.1.stable b f₀ hf₀S', fun k hk => ?_⟩
    rw [hρ, hrtc f₀ k b hk.2 hb, hf₀K k hk.1 hk.2]
  have hf₀W : f₀ ∈ W' := by
    have := hgen 1 (GlobalTheory.InertSph.trivOutside_one _)
    have e : NG.rt L n (1 : GAf L n) f₀ = f₀ := funext fun y => by
      show f₀ (y * 1) = f₀ y
      rw [mul_one]
    rwa [e] at this
  have hW0 : W' ≠ ⊥ := by
    intro h0
    apply hf₀0
    have := hf₀W
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hWb : ∀ b ∈ {b : GAf L n | TrivOutside {v}ᶜ b}, ∀ x ∈ W', ρ b x ∈ W' := by
    intro b hb x hx
    have hle : W' ≤ W'.comap (ρ b) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨b', hb'⟩, rfl⟩
      show ρ b (NG.rt L n b' f₀) ∈ W'
      rw [hρ, hrtm]
      exact hgen _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul hb hb')
    exact hle hx
  have hWR : ∀ x ∈ {x : GAf L n | TrivOutside {v} x}, ∀ y ∈ W', ∑ γ ∈ R x, ρ γ y ∈ W' := by
    intro x hx y hy
    have hγ : ∀ γ ∈ R x, TrivOutside {v} γ := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (hR x hx).1 γ hγ
      exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 hx) hk₂.2
    have hle : W' ≤ W'.comap (∑ γ ∈ R x, ρ γ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨b, hb⟩, rfl⟩
      show (∑ γ ∈ R x, ρ γ) (NG.rt L n b f₀) ∈ W'
      rw [LinearMap.sum_apply]
      have e : ∑ γ ∈ R x, ρ γ (NG.rt L n b f₀) = NG.rt L n b (∑ γ ∈ R x, NG.rt L n γ f₀) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun γ hγ' => hrtc f₀ γ b (hγ γ hγ') hb
      rw [e, hχ x hx, map_smul]
      exact W'.smul_mem _ (hgen b hb)
    have := hle hy
    rwa [Submodule.mem_comap, LinearMap.sum_apply] at this
  have hdec : ∀ g : GAf L n, ∃ x ∈ {x : GAf L n | TrivOutside {v} x}, ∃ b ∈ {b : GAf L n | TrivOutside {v}ᶜ b},
      g = x * b := by
    intro g
    obtain ⟨x, b, hx, hb, e⟩ := GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place L n v g
    exact ⟨x, hx, b, hb, e⟩
  have hirr : ∀ S' : Submodule ℂ (GAf L n → a.W), S' ≤ S → (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S :=
    fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, fun g x hx => hst g x hx⟩ hle
  have heq := GlobalTheory.SphScalar.fixS_simple ρ S (fun g x hx => hS.1.stable g x hx) hirr (GlobalTheory.InertSph.Kv L n v)
    {x : GAf L n | TrivOutside {v} x} {b : GAf L n | TrivOutside {v}ᶜ b} hdec R (fun x hx => hR x hx)
    W' hW hW0 hWR hWb
  have hfW : f ∈ W' := by
    rw [heq]
    exact ⟨hfS, fun k hk => hfK k hk.1 hk.2⟩

  obtain ⟨C, cf, xs, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h
    (GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv
      (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
      (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU h hh)
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α with hc
  let T : Module.End ℂ (GAf L n → a.W) := ∑ d ∈ C, cf d • NG.rt L n (xs d)
  have hT : ∀ φ, heckeFunI L n U Dv h φ = T φ := by
    intro φ
    rw [hC a.W φ, LinearMap.sum_apply]
    rfl
  let E : Module.End ℂ (GAf L n → a.W) := T - c • (1 : Module.End ℂ (GAf L n → a.W))
  have hE : ∀ φ, E φ = T φ - c • φ := fun φ => rfl
  have hker : W' ≤ LinearMap.ker E := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    show E (NG.rt L n b f₀) = 0
    rw [hE, ← hT,
      GlobalTheory.InertSph.heckeFunI_rt U Dv h f₀ b hb,
      GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK U U' hU hU' a.W h hh.1 f₀ hf₀K, hH h hh, map_smul, sub_self]
  have := hker hfW
  rw [LinearMap.mem_ker, hE, sub_eq_zero] at this
  rw [hT]
  exact this

end GlobalTheory.InertSph
