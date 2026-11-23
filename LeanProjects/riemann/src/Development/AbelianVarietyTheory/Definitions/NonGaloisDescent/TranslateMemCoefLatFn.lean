import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix MvPolynomial
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct

namespace GlobalTheory.ExportSeries

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

abbrev GLR (D : D7) (n : ℕ) : Type := D.what₂.Tau → GL (Fin n) ℂ

structure Weight (D : D7) (n : ℕ) where
  p : D.what₂.Tau → ℕ
  q : D.what₂.Tau → ℕ
  ap : D.what₂.Tau → ℕ → ℕ
  am : D.what₂.Tau → ℕ → ℕ
  c : D.what₂.Tau → ℤ
  lam : D.what₂.Tau → DomWeight n

structure Weight.Good (w : Weight D n) : Prop where
  le : ∀ τ, w.p τ + w.q τ ≤ n
  lam_eq : ∀ τ (i : Fin n), (w.lam τ).w i =
    (if i.val < w.p τ then (w.ap τ i : ℤ) else if n - w.q τ ≤ i.val then -(w.am τ (n - 1 - i) : ℤ) else 0) + w.c τ

def fockSubst (p : D.what₂.Tau → ℕ) (u : GLR D n) : PolF D m n →ₐ[ℂ] PolF D m n :=
  aeval fun v => if v.2.1.val < p v.1 then ∑ b, C (((u v.1)⁻¹).val v.2.2 b) * X (v.1, v.2.1, b)
    else ∑ b, C ((u v.1).val b v.2.2) * X (v.1, v.2.1, b)

theorem fockSubst_one (p : D.what₂.Tau → ℕ) : fockSubst (m := m) p (1 : GLR D n) = AlgHom.id ℂ _ := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [fockSubst, aeval_X, AlgHom.id_apply]
  split_ifs
  · rw [Finset.sum_eq_single v.2.2 (fun b _ hb => by simp [Matrix.one_apply, Ne.symm hb]) (by simp)]; simp
  · rw [Finset.sum_eq_single v.2.2 (fun b _ hb => by simp [Matrix.one_apply, hb]) (by simp)]; simp

theorem fockSubst_mul (p : D.what₂.Tau → ℕ) (u u' : GLR D n) :
    fockSubst (m := m) p (u * u') = (fockSubst p u).comp (fockSubst p u') := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, fockSubst, fockSubst, fockSubst, aeval_X, aeval_X]
  split_ifs with h
  · simp only [map_sum, map_mul, aeval_C, aeval_X, if_pos h, Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul,
      Matrix.mul_apply, algebraMap_eq, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  · simp only [map_sum, map_mul, aeval_C, aeval_X, if_neg h, Pi.mul_apply, Units.val_mul,
      Matrix.mul_apply, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def detFam (e : D.what₂.Tau → ℤ) : GLR D n →* ℂˣ where
  toFun u := ∏ τ, GeneralLinearGroup.det (u τ) ^ e τ
  map_one' := by simp
  map_mul' u u' := by simp [mul_zpow, Finset.prod_mul_distrib]

def inBasis (B : GLR D n) : GLR D n →* GLR D n := (MulAut.conj B⁻¹).toMonoidHom

def fockGL (m : ℕ) (w : Weight D n) (B : GLR D n) : GLR D n →* Module.End ℂ (PolF D m n) where
  toFun u := (((detFam w.c u)⁻¹ : ℂˣ) : ℂ) • (fockSubst w.p (inBasis B u)).toLinearMap
  map_one' := by
    rw [map_one, map_one, fockSubst_one, inv_one, Units.val_one, one_smul]; rfl
  map_mul' u u' := by
    refine LinearMap.ext fun P => ?_
    simp only [map_mul, fockSubst_mul, Module.End.mul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, map_smul, smul_smul, mul_inv, Units.val_mul, mul_comm]

theorem fockGL_apply (w : Weight D n) (B u : GLR D n) (P : PolF D m n) :
    fockGL m w B u P = (((detFam w.c u)⁻¹ : ℂˣ) : ℂ) • fockSubst w.p (inBasis B u) P := rfl

def Weight.delta (m : ℕ) (w : Weight D n) : PolF D m n := Datum.delta w.p w.q w.ap w.am

def harm (m : ℕ) (w : Weight D n) (B : GLR D n) : Submodule ℂ (PolF D m n) :=
  Submodule.span ℂ (Set.range fun u => fockGL m w B u (w.delta m))

theorem delta_mem_harm (w : Weight D n) (B : GLR D n) : w.delta m ∈ harm m w B :=
  Submodule.subset_span ⟨1, by simp⟩

theorem fockGL_mem_harm (w : Weight D n) (B u : GLR D n) {P : PolF D m n} (h : P ∈ harm m w B) :
    fockGL m w B u P ∈ harm m w B := by
  induction h using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨u', rfl⟩ := h
    refine Submodule.subset_span ⟨u * u', ?_⟩
    beta_reduce
    rw [MonoidHom.map_mul, Module.End.mul_apply]
  | zero => rw [LinearMap.map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [LinearMap.map_add]; exact add_mem h1 h2
  | smul c _ _ h1 => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ c h1

def fockPt (p : D.what₂.Tau → ℕ) (y : GLR D n) (v : FVar D m n) : ℂ :=
  if v.2.1.val < p v.1 then (if h : v.2.1.val < n then (y v.1).val v.2.2 ⟨v.2.1.val, h⟩ else 0)
  else (if h : v.2.1.val - p v.1 < n then ((y v.1)⁻¹).val (Fin.rev ⟨v.2.1.val - p v.1, h⟩) v.2.2 else 0)

theorem aeval_fockPt_fockSubst (p : D.what₂.Tau → ℕ) (u y : GLR D n) (P : PolF D m n) :
    aeval (fockPt p y) (fockSubst p u P) = aeval (fockPt p (u⁻¹ * y)) P := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, fockSubst, aeval_X, aeval_X]
  by_cases h : v.2.1.val < p v.1
  · by_cases h' : v.2.1.val < n <;>
      simp [fockPt, h, h', Matrix.mul_apply]
  · by_cases h' : v.2.1.val - p v.1 < n <;>
      simp [fockPt, h, h', Matrix.mul_apply, mul_comm]

def harmFn (m : ℕ) (w : Weight D n) (B : GLR D n) : PolF D m n →ₗ[ℂ] (GLR D n → ℂ) :=
  LinearMap.pi fun x => ((detFam w.c (B⁻¹ * x) : ℂˣ) : ℂ) • (aeval (fockPt w.p (B⁻¹ * x))).toLinearMap

theorem harmFn_apply (w : Weight D n) (B x : GLR D n) (P : PolF D m n) :
    harmFn m w B P x = ((detFam w.c (B⁻¹ * x) : ℂˣ) : ℂ) * aeval (fockPt w.p (B⁻¹ * x)) P := rfl

theorem harmFn_fockGL (w : Weight D n) (B u x : GLR D n) (P : PolF D m n) :
    harmFn m w B (fockGL m w B u P) x = harmFn m w B P (u⁻¹ * x) := by
  rw [harmFn_apply, harmFn_apply, fockGL_apply, map_smul, aeval_fockPt_fockSubst, smul_eq_mul, ← mul_assoc, ← Units.val_mul]
  congr 2
  · simp only [map_mul, map_inv]
    rw [mul_assoc, mul_comm (detFam w.c x)]
  · have : (inBasis B u)⁻¹ * (B⁻¹ * x) = B⁻¹ * (u⁻¹ * x) := by
      simp [inBasis, mul_assoc]
    rw [this]

section Coef

variable {K : Type} [Field K] (σ : K →+* ℂ)

def coefFn (lam : D.what₂.Tau → DomWeight n) (F : Pol K D.what₂.Tau n) (x : GLR D n) : ℂ :=
  ((detFam (fun τ => (lam τ).detShift) x : ℂˣ) : ℂ) * eval₂Hom σ (fun v => (x v.1).val v.2.1 v.2.2) F

theorem coefFn_rhoVr {emb : D.what₂.Tau → (D.host.E →+* K)} (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (lam : D.what₂.Tau → DomWeight n) (γ : GL (Fin n) D.host.E) (F : VV K lam) (x : GLR D n) :
    coefFn σ lam (rhoVr emb lam γ F : VV K lam) x = coefFn σ lam F ((embGL (tauE D) γ)⁻¹ * x) := by
  have he : ∀ τ a, σ (emb τ a) = tauE D τ a := fun τ a => RingHom.congr_fun (hemb τ) a
  have e1 : ((rhoVr emb lam γ F : VV K lam) : Pol K D.what₂.Tau n) =
      detTwK lam (invTrK (embGL emb γ)) • trAct (invTrK (embGL emb γ)) (F : Pol K D.what₂.Tau n) := rfl
  have e2 : (eval₂Hom σ (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK (embGL emb γ)) : Pol K D.what₂.Tau n →+* Pol K D.what₂.Tau n) =
      eval₂Hom σ (fun v => (((embGL (tauE D) γ)⁻¹ * x) v.1).val v.2.1 v.2.2) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp [trAct, Formalism.GradedWeylDivisibility.blockAct]) fun v => ?_
    have : ∀ a b, σ (((embGL emb γ v.1)⁻¹).val a b) = ((embGL (tauE D) γ v.1)⁻¹).val a b := fun a b => he _ _
    simp only [RingHom.comp_apply, RingHom.coe_coe, trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, eval₂Hom_C,
      eval₂Hom_X', Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => congrArg (· * _) (this _ _)
  have e3 : σ (detTwK lam (invTrK (embGL emb γ))) =
      ((detFam (fun τ => (lam τ).detShift) (embGL (tauE D) γ)⁻¹ : ℂˣ) : ℂ) := by
    simp only [detTwK, detPow, detFam, map_prod, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      map_zpow₀, GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    change σ (((embGL emb γ τ)⁻¹).valᵀ).det = _
    rw [det_transpose, RingHom.map_det]
    congr 1
    ext a b
    exact he _ _
  rw [coefFn, coefFn, e1, smul_eq_C_mul, map_mul, eval₂Hom_C, e3, ← e2, map_mul, Units.val_mul]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  ring

variable [NumberField K] (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)

structure IsCoefRing : Prop where
  emb : ∀ τ, σ.comp (emb τ) = tauE D τ
  int : ∀ a : 𝓞 K, σ a ∈ O

def coefLatFn (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule O (GLR D n → ℂ) :=
  Submodule.span O {φ | ∃ F ∈ nabAtr emb lam M, φ = coefFn σ lam (F : VV K lam)}

def harmLat (m : ℕ) (w : Weight D n) (B : GLR D n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule O (PolF D m n) :=
  (harm m w B).restrictScalars O ⊓ (coefLatFn σ emb O w.lam M).comap ((harmFn m w B).restrictScalars O)

theorem mem_harmLat {w : Weight D n} {B : GLR D n} {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {P : PolF D m n} :
    P ∈ harmLat σ emb O m w B M ↔ P ∈ harm m w B ∧ harmFn m w B P ∈ coefLatFn σ emb O w.lam M := Iff.rfl

variable {σ emb O}

theorem nabAtr_of_mem_iff (lam : D.what₂.Tau → DomWeight n) (γ : GL (Fin n) D.host.E)
    {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : ∀ x, x ∈ M' ↔ (γ⁻¹).val *ᵥ x ∈ M) :
    nabAtr emb lam M' = (nabAtr emb lam M).map ((rhoVr emb lam γ).restrictScalars (𝓞 K)) := by
  have hM' : M' = M.map ((Matrix.mulVecLin γ.val).restrictScalars (𝓞 D.host.E)) := by
    ext x
    rw [hM, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨_, hx, by simp [Matrix.mulVec_mulVec]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [Matrix.mulVec_mulVec] using hy
  unfold nabAtr
  have : ∀ τ, tauLat emb τ M' = gLat (embGL emb γ τ) (tauLat emb τ M) := fun τ => by
    rw [hM']; exact tauLatG _ K _ n emb τ M γ
  simp_rw [this, Formalism.L2.Col.dualFr_gLat]
  exact Formalism.L2.Col.nabK_gLat lam _ (invTrK (embGL emb γ))

theorem translate_mem_coefLatFn (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ) (lam : D.what₂.Tau → DomWeight n)
    (γ : GL (Fin n) D.host.E) {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hM : ∀ x, x ∈ M' ↔ (γ⁻¹).val *ᵥ x ∈ M) {φ : GLR D n → ℂ} (h : φ ∈ coefLatFn σ emb O lam M) :
    (fun x => φ ((embGL (tauE D) γ)⁻¹ * x)) ∈ coefLatFn σ emb O lam M' := by
  induction h using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hF, rfl⟩ := h
    refine Submodule.subset_span ⟨rhoVr emb lam γ F, ?_, funext fun x => (coefFn_rhoVr σ hemb lam γ F x).symm⟩
    rw [nabAtr_of_mem_iff lam γ hM]
    exact Submodule.mem_map_of_mem hF
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ c h1

theorem fockGL_mem_harmLat (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ) (w : Weight D n) (B : GLR D n) (γ : GL (Fin n) D.host.E)
    {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : ∀ x, x ∈ M' ↔ (γ⁻¹).val *ᵥ x ∈ M)
    {P : PolF D m n} (h : P ∈ harmLat σ emb O m w B M) :
    fockGL m w B (embGL (tauE D) γ) P ∈ harmLat σ emb O m w B M' := by
  rw [mem_harmLat] at h ⊢
  refine ⟨fockGL_mem_harm w B _ h.1, ?_⟩
  rw [show harmFn m w B (fockGL m w B (embGL (tauE D) γ) P) = fun x => harmFn m w B P ((embGL (tauE D) γ)⁻¹ * x) from
    funext fun x => harmFn_fockGL w B _ x P]
  exact translate_mem_coefLatFn hemb w.lam γ hM h.2

end Coef

def Weight.first (D : D7) (n : ℕ) (p q : D.what₂.Tau → ℕ) (c : D.what₂.Tau → ℤ) : Weight D n where
  p := p
  q := q
  ap _ i := if i = 0 then 1 else 0
  am _ _ := 0
  c := c
  lam τ := ⟨fun i => (if i.val = 0 then 1 else 0) + c τ, fun i j hij => by
    have : i.val ≤ j.val := hij
    dsimp only
    split_ifs <;> omega⟩

theorem Weight.first_good {p q : D.what₂.Tau → ℕ} (c : D.what₂.Tau → ℤ) (hp : ∀ τ, 0 < p τ) (h : ∀ τ, p τ + q τ ≤ n) :
    (Weight.first D n p q c).Good where
  le := h
  lam_eq τ i := by
    have := hp τ
    simp only [Weight.first]
    split_ifs <;> first | omega | simp

example (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) (i a : Fin n) (hi : i.val < p τ) :
    aeval (fockPt (m := n) p y) (X (τ, i, a) : PolF D n n) = (y τ).val a i := by
  simp [fockPt, hi]

example (y : GLR D (n + 1)) (τ : D.what₂.Tau) (a : Fin (n + 1)) :
    aeval (fockPt (m := 1) (fun _ => 0) y) (X (τ, 0, a) : PolF D 1 (n + 1)) = ((y τ)⁻¹).val (Fin.last n) a := by
  simp [fockPt]

example (w : Weight D n) (B u : GLR D n) :
    fockGL m w B u 1 = ((∏ τ, GeneralLinearGroup.det (u τ) ^ (-w.c τ) : ℂˣ) : ℂ) • (1 : PolF D m n) := by
  rw [fockGL_apply, map_one]
  congr 2
  simp [detFam, Finset.prod_inv_distrib]

end GlobalTheory.ExportSeries

end
