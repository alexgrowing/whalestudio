import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctioStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Formalism.LocalToGlobal.Columns.CoefModAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.HarmLattice

theorem fg_span_comap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (O : Subring ℂ)
    (H : Submodule ℂ V) (f : V →ₗ[ℂ] W) (hinj : ∀ P ∈ H, f P = 0 → P = 0) (L : Submodule O W) (hfg : L.FG)
    (hsp : Submodule.span ℂ (L : Set W) = H.map f) :
    (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).FG ∧
      Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = H := by
  have him : f '' ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have : y ∈ H.map f := hsp ▸ Submodule.subset_span hy
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  constructor
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (f.restrictScalars O) ?_ ?_
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).map (f.restrictScalars O) = L :=
        SetLike.coe_injective him
      rw [this]
      exact hfg
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)) ⊓ LinearMap.ker (f.restrictScalars O) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hinj x hx.1.1 hx.2
      rw [this]
      exact Submodule.fg_bot
  · have hle : Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) ≤ H :=
      Submodule.span_le.2 fun x hx => hx.1
    refine le_antisymm hle fun x hx => ?_
    have : f x ∈ (Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V)).map f := by
      rw [Submodule.map_span, him, hsp]
      exact Submodule.mem_map_of_mem hx
    obtain ⟨y, hy, e⟩ := this
    have h0 : x - y = 0 := hinj _ (sub_mem hx (hle hy)) (by rw [map_sub, e, sub_self])
    rw [sub_eq_zero.1 h0]
    exact hy

variable {D : D7} {n : ℕ}

def cf (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)
  map_add' F G := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add, Pi.add_apply, mul_add]
  map_smul' c F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

theorem coefFn_eq {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : VV K lam) :
    coefFn σ lam (F : Pol K D.what₂.Tau n) = cf lam (GlobalTheory.CoefModel.mapVV σ lam F) := by
  funext x
  change _ = coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F.1) x
  simp only [coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

theorem coefLatFn_fg (hc : IsCoefRing σ emb O) (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsLattice D.host.E M) :
    (coefLatFn σ emb O lam M).FG := by
  obtain ⟨s, hs, e⟩ := Submodule.fg_def.1 (nabAtr_isLattice emb lam M hM).fg
  refine Submodule.fg_def.2 ⟨(fun F => cf lam (GlobalTheory.CoefModel.mapVV σ lam F)) '' s, hs.image _, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, e ▸ Submodule.subset_span hF, (coefFn_eq σ lam F).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    rw [coefFn_eq, SetLike.mem_coe]
    rw [← e] at hF
    induction hF using Submodule.span_induction with
    | mem F h => exact Submodule.subset_span ⟨F, h, rfl⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hc.int a⟩ : O) h1

theorem span_coefLatFn (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsLattice D.host.E M) :
    Submodule.span ℂ (coefLatFn σ emb O lam M : Set (GLR D n → ℂ)) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ lam, φ = coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)} := by
  rw [coefLatFn, Submodule.span_span_of_tower]
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨F, -, rfl⟩
    exact ⟨_, coefFn_eq σ lam F⟩
  · rintro _ ⟨F, rfl⟩
    have key : ∀ G : VV K lam, cf lam (GlobalTheory.CoefModel.mapVV σ lam G) ∈
        Submodule.span ℂ {φ | ∃ F ∈ nabAtr emb lam M, φ = coefFn σ lam (F : VV K lam)} := by
      intro G
      have hG : G ∈ Submodule.span K (nabAtr emb lam M : Set (VV K lam)) := by
        rw [(nabAtr_isLattice emb lam M hM).span_eq_top]; trivial
      induction hG using Submodule.span_induction with
      | mem F h => exact Submodule.subset_span ⟨F, h, (coefFn_eq σ lam F).symm⟩
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add _ _ _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
      | smul a F _ h1 =>
        rw [LinearMap.map_smulₛₗ, map_smul]
        exact Submodule.smul_mem _ _ h1
    have hF : F ∈ Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.mapVV σ lam (bVV K lam i)) := by
      rw [GlobalTheory.CoefModel.span_mapVV]; trivial
    change cf lam F ∈ _
    have := Submodule.mem_map_of_mem (f := cf lam) hF
    rw [Submodule.map_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact key _

theorem harmLat_fg_span : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  intro D m n w B K _ _ σ emb O M hw hm hc hM
  exact fg_span_comap O (harm m w B) (harmFn m w B) (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D m n w B hw hm) _ (coefLatFn_fg hc w.lam hM)
    ((span_coefLatFn w.lam hM).trans (GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D m n w B hw hm).symm)

end GlobalTheory.ExportSeries.HarmLattice

end
