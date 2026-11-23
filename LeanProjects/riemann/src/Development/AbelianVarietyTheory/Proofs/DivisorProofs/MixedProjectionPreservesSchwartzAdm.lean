import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def finRepl (v : Pl F) (z : κ → Af F) (x : κ → Fv F v) : κ → Af F :=
  fun i => z i - GlobalTheory.AdelicU.singleFin v (evalV F v (z i)) + GlobalTheory.AdelicU.singleFin v (x i)

def finProj (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (g : (κ → Af F) → ℂ) :
    (κ → Af F) → ℂ :=
  fun z => φ₀ (fun i => evalV F v (z i)) * l fun x => g (finRepl v z x)

theorem evalV_finRepl (v : Pl F) (z : κ → Af F) (x : κ → Fv F v) (i : κ) :
    evalV F v (finRepl v z x i) = x i := by
  simp [finRepl, GlobalTheory.AdelicU.evalV_singleFin_self]

theorem finRepl_finRepl (v : Pl F) (z : κ → Af F) (x : κ → Fv F v) :
    finRepl v (finRepl v z x) (fun i => evalV F v (z i)) = z := by
  funext i
  have := evalV_finRepl v z x i
  simp only [finRepl] at this ⊢
  rw [this]; abel

theorem continuous_finRepl (v : Pl F) :
    Continuous fun p : (κ → Af F) × (κ → Fv F v) => finRepl v p.1 p.2 := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous fun p : (κ → Af F) × (κ → Fv F v) => p.1 i := (continuous_apply i).comp continuous_fst
  have h2 : Continuous fun p : (κ → Af F) × (κ → Fv F v) => p.2 i := (continuous_apply i).comp continuous_snd
  exact (h1.sub ((GlobalTheory.AdelicU.continuous_singleFin v).comp ((RestrictedProduct.continuous_eval v).comp h1))).add
    ((GlobalTheory.AdelicU.continuous_singleFin v).comp h2)

theorem finProj_mem_SB [Fintype κ] (v : Pl F) {φ₀ : (κ → Fv F v) → ℂ} (hφ₀ : φ₀ ∈ SB (κ → Fv F v))
    (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    finProj v φ₀ l g ∈ SB (κ → Af F) := by
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have he : Continuous fun z : κ → Af F => fun i => evalV F v (z i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  have hs : Continuous fun z : κ → Af F => fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z i)) :=
    continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp
      ((RestrictedProduct.continuous_eval v).comp (continuous_apply i))
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro z₀
    let δ : (κ → Af F) → (κ → Af F) := fun z =>
      (z₀ - fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z₀ i))) -
        (z - fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z i)))
    have hδ : Filter.Tendsto δ (nhds z₀) (nhds 0) := by
      have hc : Continuous δ := continuous_const.sub (continuous_id.sub hs)
      simpa [δ] using hc.tendsto z₀
    have hφe : ∀ᶠ z in nhds z₀, φ₀ (fun i => evalV F v (z i)) = φ₀ (fun i => evalV F v (z₀ i)) :=
      (hφ₀.1.comp_continuous he).eventually_eq z₀
    filter_upwards [hδ.eventually (GlobalTheory.SBConv.eventually_translate hg), hφe] with z hz h1
    simp only [finProj]
    rw [h1]
    congr 2
    funext x
    have e : finRepl v z x = finRepl v z₀ x - δ z := by
      funext i; simp only [finRepl, δ, Pi.sub_apply]; abel
    rw [e, hz]
  · refine HasCompactSupport.intro ((hg.2.isCompact.prod hφ₀.2.isCompact).image (continuous_finRepl v)) ?_
    intro z hz
    by_contra h
    apply hz
    simp only [finProj] at h
    have h1 : φ₀ (fun i => evalV F v (z i)) ≠ 0 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    obtain ⟨x, hx⟩ : ∃ x, g (finRepl v z x) ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      have : (fun x => g (finRepl v z x)) = 0 := funext hc
      rw [this, map_zero]
    refine ⟨(finRepl v z x, fun i => evalV F v (z i)), ⟨subset_tsupport _ hx, subset_tsupport _ h1⟩, ?_⟩
    exact finRepl_finRepl v z x

theorem proj_pureA [Fintype κ] (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    proj v φ₀ l (pureA F f g) = pureA F f (finProj v φ₀ l g) := by
  funext y
  have e : (fun x => pureA F f g (repl v y x)) =
      f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) • fun x => g (finRepl v (fun i => (y i).2) x) := by
    funext x
    have a1 : ∀ i, (repl v y x i).1 = (y i).1 := fun i => by
      show (y i).1 - (0 : Ainf F) + 0 = (y i).1
      rw [sub_zero, add_zero]
    have a2 : ∀ i, (repl v y x i).2 = finRepl v (fun i => (y i).2) x i := fun i => rfl
    show f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (repl v y x i).1) * g (fun i => (repl v y x i).2) = _
    simp only [a1, a2, Pi.smul_apply, smul_eq_mul]
  rw [proj_apply, e, map_smul]
  simp only [pureA, finProj, smul_eq_mul]
  change φ₀ (fun i => evalV F v (y i).2) * _ = _
  ring

theorem proj_schA_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ), φ₀ ∈ SB (κ → Fv F v) → ∀ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ Φ ∈ schA F κ, GlobalTheory.MixedForm.proj v φ₀ l Φ ∈ schA F κ) ∧
      ∀ L ∈ (adeleClass F).adm κ, L ∘ₗ GlobalTheory.MixedForm.proj v φ₀ l ∈ (adeleClass F).adm κ := by
  intro F _ _ κ _ v φ₀ hφ₀ l
  refine ⟨fun Φ hΦ => ?_, fun L hL => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      rw [proj_pureA]
      exact Submodule.subset_span ⟨f, _, finProj_mem_SB v hφ₀ l hg, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · intro g hg
    obtain ⟨T, hT⟩ := hL _ (finProj_mem_SB v hφ₀ l hg)
    exact ⟨T, fun f => by rw [LinearMap.comp_apply, proj_pureA, hT]⟩

end GlobalTheory.MixedForm

end
