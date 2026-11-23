import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial GlobalTheory.SeriesTie.Scale

variable {D : D7} {n : ℕ}

def polLat {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule O (VV ℂ lam) :=
  Submodule.span O {y | ∃ F ∈ nabAtr emb lam M, y = GlobalTheory.CoefModel.mapVV σ lam F}

theorem coefLatFn_eq {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K))
    (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn σ emb O lam M = (polLat σ emb O lam M).map ((coefLin lam).restrictScalars O) := by
  unfold coefLatFn polLat
  rw [Submodule.map_span]
  congr 1
  ext φ
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, coefFn_map σ lam _⟩
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, coefFn_map σ lam _⟩

theorem polLat_conj {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)}
    {O O' : Subring ℂ} {lam : D.what₂.Tau → DomWeight n} {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a : K, τ (σ a) = σ a) (hO : ∀ a ∈ O, τ a ∈ O') {y : VV ℂ lam} (hy : y ∈ polLat σ emb O lam M) :
    GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y ∈ polLat σ emb O' lam M := by
  induction hy using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hF, rfl⟩ := h
    refine Submodule.subset_span ⟨F, hF, Subtype.ext ?_⟩
    change MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map σ F.1) = MvPolynomial.map σ F.1
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp σ = σ from RingHom.ext hτ]
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul a y _ h1 =>
    have e : GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam (a • y) = (⟨τ a, hO a a.2⟩ : O') • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y := by
      rw [Subring.smul_def, Subring.smul_def, map_smulₛₗ]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ h1

theorem mapVV_symm_mapVV (lam : D.what₂.Tau → DomWeight n) (τ : ℂ ≃+* ℂ) (y : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) lam (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y) = y := by
  refine Subtype.ext ?_
  change MvPolynomial.map (τ.symm : ℂ →+* ℂ) (MvPolynomial.map (τ : ℂ →+* ℂ) y.1) = y.1
  rw [MvPolynomial.map_map]
  have : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
  rw [this, MvPolynomial.map_id]

section Base

variable {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)}

theorem pq_le (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ (Wc D i).rank := by
  obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
  rw [← hB.sig τ] at e
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

variable (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) {κ : ℂ}

theorem mem_coefLat_iff (hlam : B.w.lam = lamV D i) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) (x : VsV D i ℂ) :
    Φ x ∈ B.coefLat σ emb O h ↔ κ • x ∈ polLat σ emb O (lamV D i) (B.latAt h) := by
  show Φ x ∈ harmLat σ emb O _ B.w B.F.BS (B.latAt h) ↔ _
  rw [mem_harmLat, hlam, coefLatFn_eq, Submodule.mem_map]
  constructor
  · rintro ⟨-, y, hy, he⟩
    have e : coefLin (lamV D i) y = coefLin (lamV D i) (κ • x) := by
      rw [map_smul]
      exact he.trans (hκ x)
    exact coefLin_injective _ e ▸ hy
  · intro hx
    refine ⟨hval x, κ • x, hx, ?_⟩
    change coefLin (lamV D i) (κ • x) = _
    rw [map_smul, hκ]
    rfl

theorem existsUnique_eq (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) :
    ∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = Φ x := by
  intro P hP
  have h1 : harmFn (Wc D i).rank B.w B.F.BS P ∈ (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) :=
    Submodule.mem_map_of_mem hP
  rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt (pq_le hB), hlam] at h1
  have hs : Submodule.span ℂ {φ | ∃ F : VV ℂ (lamV D i), φ = coefFn (RingHom.id ℂ) (lamV D i) (F : Pol ℂ D.what₂.Tau (Vc D i).rank)}
      ≤ LinearMap.range (coefLin (lamV D i)) :=
    Submodule.span_le.2 (by rintro _ ⟨F, rfl⟩; exact ⟨F, rfl⟩)
  obtain ⟨y, hy⟩ := hs h1
  have hy' : coefLin (lamV D i) y = harmFn (Wc D i).rank B.w B.F.BS P := hy
  have hv : ∀ x, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefLin (lamV D i) x := hκ
  refine ⟨κ⁻¹ • y, ?_, fun x hx => ?_⟩
  · have e : harmFn (Wc D i).rank B.w B.F.BS (Φ (κ⁻¹ • y) - P) = 0 := by
      rw [map_sub, hv, map_smul, smul_smul, mul_inv_cancel₀ hκ0, one_smul, hy', sub_self]
    exact (sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (pq_le hB) _ (sub_mem (hval _) hP) e)).symm
  · refine coefLin_injective (lamV D i) ?_
    have e := hv x
    rw [← hx, ← hy'] at e
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hκ0, one_smul]

theorem conj_mem_iff (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (τ : ℂ ≃+* ℂ) (hτ : ∀ a : K, τ (σ a) = σ a) (h : Bridge.Gf (Vc D i)) {x x' : VsV D i ℂ} (hx : ConjVec i τ x x') :
    Φ x ∈ B.coefLat σ emb O h ↔ Φ ((τ κ / κ) • x') ∈ B.coefLat σ emb (O.map (τ : ℂ →+* ℂ)) h := by
  rw [mem_coefLat_iff Φ hlam hval hκ, mem_coefLat_iff Φ hlam hval hκ]
  have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
  have e : κ • ((τ κ / κ) • x') = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) (κ • x) := by
    rw [smul_smul, mul_div_cancel₀ _ hκ0, map_smulₛₗ, hx']
    rfl
  rw [e]
  constructor
  · exact polLat_conj τ hτ fun a ha => Subring.mem_map.2 ⟨a, ha, rfl⟩
  · intro h'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have := polLat_conj τ.symm hτ' (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 ha
      simpa using hb) h'
    rwa [mapVV_symm_mapVV] at this

theorem coefLat_eq_span (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) :
    B.coefLat σ emb O h = Submodule.span O
      {P | ∃ F ∈ nabAtr emb (lamV D i) (B.latAt h), P = Φ (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) F)} := by
  let Ψ : VsV D i ℂ →ₗ[O] PolF D (Wc D i).rank (Vc D i).rank := (Φ ∘ₗ (κ⁻¹ • LinearMap.id)).restrictScalars O
  have hΨ : ∀ y, Ψ y = Φ (κ⁻¹ • y) := fun _ => rfl
  have e : B.coefLat σ emb O h = (polLat σ emb O (lamV D i) (B.latAt h)).map Ψ := by
    ext P
    constructor
    · intro hP
      obtain ⟨x, rfl, -⟩ := existsUnique_eq Φ hB hlam hκ0 hval hκ P (Submodule.mem_inf.1 hP).1
      refine ⟨κ • x, (mem_coefLat_iff Φ hlam hval hκ σ emb O h x).1 hP, ?_⟩
      rw [hΨ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    · rintro ⟨y, hy, rfl⟩
      rw [hΨ, mem_coefLat_iff Φ hlam hval hκ, smul_smul, mul_inv_cancel₀ hκ0, one_smul]
      exact hy
  rw [e, polLat, Submodule.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, rfl⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, rfl⟩

end Base

end GlobalTheory.CoefLatConj
