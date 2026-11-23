import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HeisSchA

open GlobalTheory.Published.Metaplectic
open scoped Classical

theorem nonarch_of_isInducing {G S : Type} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    [AddGroup S] [TopologicalSpace S] [IsTopologicalAddGroup S] (f : S →+ G) (hf : Topology.IsInducing f) :
    NonarchimedeanAddGroup S where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean t ht
    exact ⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩

theorem nonarch_pi {ι : Type} {G : ι → Type} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩,
      fun x hx => hs fun i hi => hK i (hx i hi)⟩

variable {F : Type} [Field F] [NumberField F]

theorem nonarch_finiteAdeleRing : NonarchimedeanAddGroup (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v =>
    nonarch_of_isInducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal
  haveI := nonarch_pi (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F :=
    { toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb f
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))

def finChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem finChar_isLocallyConstant (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) :
    IsLocallyConstant (finChar ψ) := by
  haveI := nonarch_finiteAdeleRing (F := F)
  exact GlobalTheory.WeilM.isLocallyConstant_addChar _ (hψ.comp (continuous_const.prodMk continuous_id))

def p1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _

def p2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

def mk (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (a, b)

theorem finChar_apply (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (z : FiniteAdeleRing (𝓞 F) F) :
    finChar ψ z = ψ (mk 0 z) := rfl

theorem map_eq_mul (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (b : AdeleRing (𝓞 F) F) :
    ψ b = ψ (mk (p1 b) 0) * finChar ψ (p2 b) := by
  rw [finChar_apply, ← AddChar.map_add_eq_mul]
  congr 1
  exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem at_mk (b : InfiniteAdeleRing F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (mk b 0) := by
  intro u hu
  have hu1 : p1 u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  rw [smul_eq_mul]
  exact Prod.ext (show p1 u * b = 0 by rw [hu1, zero_mul]) (show p2 u * 0 = 0 from mul_zero _)

variable {κ : Type} [Fintype κ]

def trL (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem trL_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trL c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

def archS (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (c t : κ → mixedEmbedding.mixedSpace F) (k : ℝ) :
    SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun y => eChar ((-trL c) y + -k)) (SchwartzMap.compSubConstCLM ℂ (-t) f)

theorem archS_apply (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (c t : κ → mixedEmbedding.mixedSpace F)
    (k : ℝ) (y : κ → mixedEmbedding.mixedSpace F) :
    archS f c t k y = eChar ((-trL c) y + -k) * f (y + t) := by
  have htg : Function.HasTemperateGrowth (fun y => eChar ((-trL c) y + -k)) :=
    hasTemperateGrowth_eChar.comp ((-trL c).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))
  rw [archS, SchwartzMap.smulLeftCLM_apply_apply htg, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul]

def finS (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (d s : κ → FiniteAdeleRing (𝓞 F) F) (d₀ : FiniteAdeleRing (𝓞 F) F) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun z => finChar ψ (z ⬝ᵥ d + d₀) * g (z + s)

theorem finS_mem (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (d s : κ → FiniteAdeleRing (𝓞 F) F)
    (d₀ : FiniteAdeleRing (𝓞 F) F) : finS ψ g d s d₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have hlin : Continuous fun z : κ → FiniteAdeleRing (𝓞 F) F => z ⬝ᵥ d + d₀ :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  refine ⟨((finChar_isLocallyConstant ψ hψ).comp_continuous hlin).mul
    (hg.1.comp_continuous (continuous_add_right s)), ?_⟩
  exact (hg.2.comp_homeomorph (Homeomorph.addRight s)).mul_left

theorem schr_pureA_mem [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.pureA F f g) ∈ GlobalTheory.WeilM.schA F κ := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  refine Submodule.subset_span ⟨archS f c t k, finS ψ g d s (p2 h), finS_mem ψ hψ.1 hg d s (p2 h), funext fun x => ?_⟩
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add, RingHom.map_dotProduct]
        rfl
      rw [e1, map_add, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add, RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem schr_mem_schA [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilM.schr ψ w Φ ∈ GlobalTheory.WeilM.schA F κ := by
  let T : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := GlobalTheory.WeilM.schr ψ w
      map_add' := fun φ φ' => funext fun x => by simp only [GlobalTheory.WeilM.schr, Pi.add_apply]; ring
      map_smul' := fun a φ => funext fun x => by
        simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.schA F κ).comap T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    exact schr_pureA_mem ψ hψ w f hg
  exact fun Φ hΦ => hle hΦ

end GlobalTheory.HeisSchA

theorem GlobalTheory.HeisSchA.rho_mem_schA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X Y)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
      M.co.rho ψ γ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
  fun M ψ hψ γ Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA ψ hψ (M.co.e γ) Φ hΦ
