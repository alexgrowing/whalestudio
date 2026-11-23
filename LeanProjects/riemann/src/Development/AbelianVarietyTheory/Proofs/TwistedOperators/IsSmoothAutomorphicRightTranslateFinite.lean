import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

variable {D : D7} (θ : InfFam D) (V : HSp D)

theorem comm_fin_real {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GinfC V) : a * b = b * a := by
  have h1 : (GfC V).Normal := MonoidHom.normal_ker _
  have h2 : (GinfC V).Normal := MonoidHom.normal_ker _
  exact Subgroup.commute_of_normal_of_disjoint (GfC V) (GinfC V) h1 h2
    (Subgroup.disjoint_def.2 fun {x} hx hy => GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hx hy) a b ha hb

theorem atTau_mem (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

theorem oneP_mem (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : oneP θ V τ X t ∈ GinfC V :=
  atTau_mem θ V τ _

def rTrL (κ : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := LinearMap.funLeft ℂ ℂ fun g => g * κ

theorem rTrL_apply (κ : GA D V) (φ : GA D V → ℂ) : rTrL V κ φ = rTr V κ φ := rfl

variable {κ : GA D V}

theorem Rder_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V κ φ) = rTr V κ (Rder θ V τ X φ) := by
  funext g
  simp only [Rder, rTr]
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, comm_fin_real V hκ (oneP_mem θ V τ X t)]

theorem RderC_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ Z (rTr V κ φ) = rTr V κ (RderC θ V τ Z φ) := by
  unfold RderC
  rw [Rder_rTr θ V hκ, Rder_rTr θ V hκ]
  rfl

theorem foldr_comm {α : Type} (T : α → α) (l : List (α → α)) (hl : ∀ f ∈ l, ∀ x, f (T x) = T (f x)) (x : α) :
    l.foldr (fun f acc => f acc) (T x) = T (l.foldr (fun f acc => f acc) x) := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    simp only [List.foldr_cons]
    rw [ih fun g hg => hl g (List.mem_cons_of_mem _ hg), hl f List.mem_cons_self]

theorem gelf_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ k (rTr V κ φ) = rTr V κ (gelf θ V τ k φ) := by
  unfold gelf
  rw [← rTrL_apply V κ (∑ _, _), map_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [rTrL_apply]
  refine foldr_comm (rTr V κ) _ ?_ φ
  intro f hf x
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
  exact RderC_rTr θ V hκ τ _ x

theorem foldr_Rder_rTr (hκ : κ ∈ GfC V) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (rTr V κ φ) = rTr V κ (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih, Rder_rTr θ V hκ]

theorem isAutFun_rTr (hκ : κ ∈ GfC V) {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (rTr V κ φ) := by
  have := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const)⟩
  · simp only [rTr]
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, hinv⟩ := h.level
    refine ⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have hc : Continuous fun k : GA D V => κ⁻¹ * k * κ⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hU.preimage hc
    · have hk' : κ⁻¹ * k * κ⁻¹⁻¹ ∈ U := hk
      have hf : κ⁻¹ * k * κ⁻¹⁻¹ ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hκ) hkf) ((GfC V).inv_mem ((GfC V).inv_mem hκ))
      simp only [rTr]
      rw [← hinv _ hk' hf (g * κ)]
      congr 1
      group

theorem isAutFunSm_rTr : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ,
    IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  intro D θ V κ hκ φ h
  refine ⟨isAutFun_rTr V hκ h.toIsAutFun, fun k τs Xs hX g => ?_, ?_, ?_⟩
  · have e : (fun t : Fin k → ℝ => rTr V κ φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) =
        fun t : Fin k → ℝ => φ (g * κ * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
      funext t
      have hm : (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ GinfC V := by
        refine (GinfC V).list_prod_mem fun x hx => ?_
        obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
        exact oneP_mem θ V _ _ _
      simp only [rTr]
      rw [mul_assoc, mul_assoc, comm_fin_real V hκ hm]
    rw [e]
    exact h.smooth k τs Xs hX (g * κ)
  · obtain ⟨W, hW, hφ, hst⟩ := h.zfin
    refine ⟨W.map (rTrL V κ), inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨gelf θ V τ k f, hst τ k f hf, (gelf_rTr θ V hκ τ k f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * κ)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_Rder_rTr θ V hκ]
    simp only [rTr]
    rw [mul_assoc, ← comm_fin_real V hκ hg, ← mul_assoc]
    exact hC g hg

end GlobalTheory.FinTranslate

end
