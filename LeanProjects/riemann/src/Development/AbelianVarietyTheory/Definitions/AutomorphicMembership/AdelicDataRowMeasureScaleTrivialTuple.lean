import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OmegaUpDownForms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.NotHasInfExpThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev InfF (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

abbrev IdC (D : D7) : Type := (AE D)ˣ →* Circle

def IsHC (D : D7) (χ : IdC D) : Prop := IsHeckeChar D χ ∧ ∀ τ, ∃ a, HasInfExp D χ τ a

def AFs (θ : InfF D) (V : HSp D) : Submodule ℂ (GA D V → ℂ) := Submodule.span ℂ {φ | IsAutFunSm θ V φ}

def IsCuspForm (θ : InfF D) (V : HSp D) (φ : GA D V → ℂ) : Prop := IsAutFunSm θ V φ ∧ IsCuspFun V φ

def CuspS (θ : InfF D) (V : HSp D) : Submodule ℂ (GA D V → ℂ) := Submodule.span ℂ {φ | IsCuspForm θ V φ}

def TypS (θ : InfF D) (V : HSp D) (P : D.what₂.Tau → SPar) : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {φ | IsAutFunSm θ V φ ∧ ∀ τ, IsTypeAt θ V τ (P τ) φ}

def ThS (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (WA V W → ℂ) :=
  Submodule.span ℂ {f | IsThetaFun ψ V W f}

theorem mem_ThS {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {f : WA V W → ℂ} : f ∈ ThS ψ V W ↔ IsThetaFun ψ V W f := by
  obtain ⟨M, hM⟩ := GlobalTheory.FockCompare.exists_thetaSubmodule D ψ V W
  refine ⟨fun h => (hM f).1 ?_, fun h => Submodule.subset_span h⟩
  exact (Submodule.span_le.2 fun g hg => (hM g).2 hg : ThS ψ V W ≤ M) h

theorem CuspS_le (θ : InfF D) (V : HSp D) : CuspS θ V ≤ AFs θ V := Submodule.span_mono fun _ h => h.1

theorem const_mem_AFs (θ : InfF D) (V : HSp D) (c : ℂ) : (fun _ => c) ∈ AFs θ V :=
  Submodule.subset_span (isAutFunSm_const θ V c)

theorem CuspS_eq_of_aniso (θ : InfF D) {V : HSp D} (h : IsAniso V) : CuspS θ V = AFs θ V := by
  unfold CuspS AFs
  congr 1
  ext φ
  exact ⟨fun h => h.1, fun hφ => ⟨hφ, fun r C hC => absurd hC (h r C)⟩⟩

theorem isTypeAt_smul {θ : InfF D} {V : HSp D} {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (c : ℂ)
    (h : IsTypeAt θ V τ S φ) : IsTypeAt θ V τ S (c • φ) := by
  obtain ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, h5⟩ := h
  refine ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, fun x => ?_⟩
  obtain ⟨v, hv, ℓ, hℓ, ⟨L, C, k1, k2, k3, k4⟩, k5⟩ := h5 x
  refine ⟨v, hv, fun i => c • ℓ i, fun i => ?_, ⟨L, fun i => ‖c‖ * C i, k1, fun i w hw => ?_, ?_, k4⟩, fun g hg => ?_⟩
  · obtain ⟨L', C', m1, m2⟩ := hℓ i
    refine ⟨L', ‖c‖ * C', m1, fun w hw => ?_⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (m2 w hw) (norm_nonneg _)
  · rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (k2 i w hw) (norm_nonneg _)
  · intro S' hS'
    simpa only [mul_assoc] using (k3 S' hS').mul_left ‖c‖
  · exact (k5 g hg).const_smul c

def thCoef (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WA V W)) (𝓕 : Set (WA V W)) (f : WA V W → ℂ)
    (u : WA V W) : ℂ := ∫ w in 𝓕, Heisenberg₂ ψ V W u f w * star (f w) ∂μ

def IsPureAt (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (e : AE D) (f : WA V W → ℂ) : Prop :=
  AllSome (fun m : Measure (WA V W) × Set (WA V W) => m.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V W) m.2 m.1)
    fun m => (∀ u, IntegrableOn (fun w => Heisenberg₂ ψ V W u f w * star (f w)) m.2 m.1) ∧
      ∀ x y : WA V W, (∀ i j, e * x i j = x i j) → (∀ i j, e * y i j = 0) →
        thCoef ψ V W m.1 m.2 f (x + y) * thCoef ψ V W m.1 m.2 f 0 = thCoef ψ V W m.1 m.2 f x * thCoef ψ V W m.1 m.2 f y

def IsPureFun (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WA V W → ℂ) : Prop :=
  (∀ v, IsPureAt ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin D v) f) ∧ ∀ v, IsPureAt ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf D v) f

abbrev CptF (V : HSp D) : Type :=
  ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ

structure OrthDec (D : D7) where

  cpt : ∀ V : HSp D, CptF V
  cpt_gram : ∀ V : HSp D, V.SigOK → ∀ τ,
    (cpt V τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cpt V τ = gramAt D V τ

  bas : ∀ V : HSp D, Matrix (Fin V.rank) (Fin V.rank) D.host.E
  bas_unit : ∀ V : HSp D, V.SigOK → IsUnit (bas V).det
  bas_orth : ∀ V : HSp D, V.SigOK → ∀ i j, i ≠ j →
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (bas V) * V.gram * bas V) i j = 0
  cpt_bas : ∀ V : HSp D, V.SigOK → ∀ τ a i j,
    (cpt V τ * (bas V).map (tauE D τ)) a i ≠ 0 → (cpt V τ * (bas V).map (tauE D τ)) a j ≠ 0 → i = j

def OrthEx (D : D7) : Prop := ∀ V : HSp D, V.SigOK → ∃ (A : CptF V) (Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
  (∀ τ, (A τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A τ = gramAt D V τ) ∧ IsUnit Q.det ∧
  (∀ i j, i ≠ j → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Q * V.gram * Q) i j = 0) ∧
  ∀ τ a i j, (A τ * Q.map (tauE D τ)) a i ≠ 0 → (A τ * Q.map (tauE D τ)) a j ≠ 0 → i = j

theorem nonempty_orthDec (h : OrthEx D) : Nonempty (OrthDec D) := by
  classical
  choose A Q h1 h2 h3 h4 using h
  refine ⟨⟨fun V => if hV : V.SigOK then A V hV else 0, fun V hV => ?_, fun V => if hV : V.SigOK then Q V hV else 0,
    fun V hV => ?_, fun V hV => ?_, fun V hV => ?_⟩⟩ <;> simp only [dif_pos hV]
  exacts [h1 V hV, h2 V hV, h3 V hV, h4 V hV]

def KfinS (ψ : AddChar (AF D.host.F) ℂ) (θ : InfF D) (Dc : OrthDec D) (V W : HSp D) : Submodule ℂ (ThS ψ V W) :=
  Submodule.span ℂ {Φ | IsPolFock ψ θ V W (Dc.cpt V) (Dc.cpt W) Φ.1}

theorem OrthDec.exists_rel (Dc : OrthDec D) {V : HSp D} (hV : V.SigOK) :
    ∃ s : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InvFam V, ∀ τ, GlobalTheory.FockCompare.Rel V τ (Dc.cpt V τ) (s τ) := by
  classical
  obtain ⟨b, hb⟩ := (GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).1 _ (Dc.bas_unit V hV)
  have ho : ∀ i j, i ≠ j → V.hT (b i) (b j) = 0 := fun i j hij => by
    rw [← ((GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).2 b).2.1 i j, ← hb]
    exact Dc.bas_orth V hV i j hij
  refine ⟨fun τ => b.constr D.host.E fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i, fun τ =>
    GlobalTheory.FockCompare.rel_of_monomial hV τ b ho (fun i => b.constr_basis _ _ i) (Dc.cpt_gram V hV τ) ?_⟩
  rw [← hb]
  exact Dc.cpt_bas V hV τ

theorem mem_KfinS {ψ : AddChar (AF D.host.F) ℂ} {θ : InfF D} (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (Dc : OrthDec D)
    {V W : HSp D} (hV : V.SigOK) (hW : W.SigOK) (Φ : ThS ψ V W) :
    Φ ∈ KfinS ψ θ Dc V W ↔ IsPolFock ψ θ V W (Dc.cpt V) (Dc.cpt W) Φ.1 := by
  obtain ⟨s, hs⟩ := Dc.exists_rel hV
  obtain ⟨s', hs'⟩ := Dc.exists_rel hW
  have key := fun Φ : ThS ψ V W => GlobalTheory.FockCompare.isPolFock_iff hθ hψ hV hW hs hs' (mem_ThS.1 Φ.2)
  refine ⟨fun h => (key Φ).2 ?_, fun h => Submodule.subset_span h⟩
  exact (Submodule.span_le.2 fun g hg => (key g).1 hg :
    KfinS ψ θ Dc V W ≤ (GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.polFun ψ θ V W s s').comap (ThS ψ V W).subtype) h

def admitted (V W : HSp D) (χ χ' : IdC D) : Prop :=
  V.rank ≠ W.rank ∧ IsHC D χ ∧ IsHC D χ' ∧ ResEta D χ V.rank ∧ ResEta D χ' W.rank

structure IsWeilOn (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : IdC D)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) : Prop where
  Heisenberg₂ : ∀ g h w₀ (Φ Φ' : ThS ψ V W), Φ'.1 = Heisenberg₂ ψ V W w₀ Φ.1 →
    (om (g, h) Φ').1 = Formalism.L2.Theta.Heisenberg₂ ψ V W (actHom V W g h w₀) (om (g, h) Φ).1
  aut : ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ Φ : ThS ψ V W, (om (γ, γ') Φ).1 0 = Φ.1 0
  cont : ∀ (Φ : ThS ψ V W) w, Continuous fun p : GA D V × GA D W => (om p Φ).1 w
  unit : ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∀ p (Φ : ThS ψ V W), ∫ w in 𝓕, ‖(om p Φ).1 w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖Φ.1 w‖ ^ 2 ∂μ
  split : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : ThS ψ V W →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ' : ThS ψ V W,
        Φ'.1 = Formalism.L2.Theta.Heisenberg₂ ψ V W u Φ.1 → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (om (g, h) Φ) = (r : ℂ) * (splitFac V W χ χ' x y : ℂ) * ℓ Φ

structure WeilCore (D : D7) (ψ : AddChar (AF D.host.F) ℂ) where
  om : ∀ V W : HSp D, IdC D → IdC D → (GA D V × GA D W →* Module.End ℂ (ThS ψ V W))
  weil : ∀ (V W : HSp D) χ χ', admitted V W χ χ' → IsWeilOn ψ V W χ χ' (om V W χ χ')

structure WeilCore.Rules {ψ : AddChar (AF D.host.F) ℂ} (Wc : WeilCore D ψ) : Prop where

  twW : ∀ (V W : HSp D) χ χ' ν, admitted V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot V g x →
    Wc.om V W χ (χ' * ν) (g, h) =
      (((if V.rank < W.rank then (ν x)⁻¹ else ν x : Circle)) : ℂ) • Wc.om V W χ χ' (g, h)

  twV : ∀ (V W : HSp D) χ χ' ν, admitted V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot W h x →
    Wc.om V W (χ * ν) χ' (g, h) =
      (((if V.rank < W.rank then ν x else (ν x)⁻¹ : Circle)) : ℂ) • Wc.om V W χ χ' (g, h)

  om_swap : ∀ (V W : HSp D) χ χ', admitted V W χ χ' →
    ∀ g h (Φ : ThS ψ V W) (Φ' : ThS ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) →
      ∀ x : WA V W, (Wc.om W V χ' χ (h, g) Φ').1 x.transpose = (Wc.om V W χ χ' (g, h) Φ).1 x

  om_unr : ∀ (V W : HSp D) χ χ', admitted V W χ χ' → ∀ S, UnramOutside D χ S → UnramOutside D χ' S →
    ∀ k ∈ KsphC V S, ∀ k' ∈ KsphC W S, ∀ Φ : ThS ψ V W,
      (∀ u ∈ latVWS V W S, Heisenberg₂ ψ V W u Φ.1 = Φ.1) → Wc.om V W χ χ' (k, k') Φ = Φ

structure WeilFun (D : D7) (ψ : AddChar (AF D.host.F) ℂ) where
  om : ∀ V W : HSp D, IdC D → IdC D → (GA D V × GA D W →* Module.End ℂ (ThS ψ V W))
  om_heis : ∀ (V W : HSp D) χ χ', admitted V W χ χ' → ∀ g h w₀ (Φ Φ' : ThS ψ V W), Φ'.1 = Heisenberg₂ ψ V W w₀ Φ.1 →
    (om V W χ χ' (g, h) Φ').1 = Heisenberg₂ ψ V W (actHom V W g h w₀) (om V W χ χ' (g, h) Φ).1
  om_aut : ∀ (V W : HSp D) χ χ', admitted V W χ χ' → ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ Φ : ThS ψ V W,
    (om V W χ χ' (γ, γ') Φ).1 0 = Φ.1 0
  om_cont : ∀ (V W : HSp D) χ χ', admitted V W χ χ' → ∀ (Φ : ThS ψ V W) w,
    Continuous fun p : GA D V × GA D W => (om V W χ χ' p Φ).1 w
  om_unit : ∀ (V W : HSp D) χ χ', admitted V W χ χ' →
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∀ p (Φ : ThS ψ V W), ∫ w in 𝓕, ‖(om V W χ χ' p Φ).1 w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖Φ.1 w‖ ^ 2 ∂μ
  om_split : ∀ (V W : HSp D) χ χ', admitted V W χ χ' →
    ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : ThS ψ V W →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ' : ThS ψ V W, Φ'.1 = Heisenberg₂ ψ V W u Φ.1 → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (om V W χ χ' (g, h) Φ) = (r : ℂ) * (splitFac V W χ χ' x y : ℂ) * ℓ Φ
  twW : ∀ (V W : HSp D) χ χ' ν, admitted V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot V g x →
    om V W χ (χ' * ν) (g, h) =
      (((if V.rank < W.rank then (ν x)⁻¹ else ν x : Circle)) : ℂ) • om V W χ χ' (g, h)
  twV : ∀ (V W : HSp D) χ χ' ν, admitted V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot W h x →
    om V W (χ * ν) χ' (g, h) =
      (((if V.rank < W.rank then ν x else (ν x)⁻¹ : Circle)) : ℂ) • om V W χ χ' (g, h)
  om_swap : ∀ (V W : HSp D) χ χ', admitted V W χ χ' →
    ∀ g h (Φ : ThS ψ V W) (Φ' : ThS ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) →
      ∀ x : WA V W, (om W V χ' χ (h, g) Φ').1 x.transpose = (om V W χ χ' (g, h) Φ).1 x
  om_unr : ∀ (V W : HSp D) χ χ', admitted V W χ χ' → ∀ S, UnramOutside D χ S → UnramOutside D χ' S →
    ∀ k ∈ KsphC V S, ∀ k' ∈ KsphC W S, ∀ Φ : ThS ψ V W,
      (∀ u ∈ latVWS V W S, Heisenberg₂ ψ V W u Φ.1 = Φ.1) → om V W χ χ' (k, k') Φ = Φ

def WeilCore.toFun {ψ : AddChar (AF D.host.F) ℂ} (Wc : WeilCore D ψ) (h : Wc.Rules) : WeilFun D ψ where
  om := Wc.om
  om_heis V W χ χ' ha := (Wc.weil V W χ χ' ha).Heisenberg₂
  om_aut V W χ χ' ha := (Wc.weil V W χ χ' ha).aut
  om_cont V W χ χ' ha := (Wc.weil V W χ χ' ha).cont
  om_unit V W χ χ' ha := (Wc.weil V W χ χ' ha).unit
  om_split V W χ χ' ha := (Wc.weil V W χ χ' ha).split
  twW := h.twW
  twV := h.twV
  om_swap := h.om_swap
  om_unr := h.om_unr

namespace WeilFun

variable {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ)

def core : WeilCore D ψ :=
  ⟨Wf.om, fun V W χ χ' ha => ⟨Wf.om_heis V W χ χ' ha, Wf.om_aut V W χ χ' ha, Wf.om_cont V W χ χ' ha,
    Wf.om_unit V W χ χ' ha, Wf.om_split V W χ χ' ha⟩⟩

theorem rules : Wf.core.Rules := ⟨Wf.twW, Wf.twV, Wf.om_swap, Wf.om_unr⟩

def ker (V W : HSp D) (χ χ' : IdC D) (Φ : ThS ψ V W) (g : GA D V) (h : GA D W) : ℂ := (Wf.om V W χ χ' (g, h) Φ).1 0

theorem ker_left {V W : HSp D} {χ χ' : IdC D} (ha : admitted V W χ χ') (Φ : ThS ψ V W) {γ : GA D V} (hγ : γ ∈ GQ V)
    {δ : GA D W} (hδ : δ ∈ GQ W) (g h) : Wf.ker V W χ χ' Φ (γ * g) (δ * h) = Wf.ker V W χ χ' Φ g h := by
  have e : Wf.om V W χ χ' (γ * g, δ * h) = Wf.om V W χ χ' (γ, δ) * Wf.om V W χ χ' (g, h) := by rw [← map_mul]; rfl
  unfold ker
  rw [e, Module.End.mul_apply]
  exact Wf.om_aut V W χ χ' ha γ hγ δ hδ _

end WeilFun

theorem isHC_one (D : D7) : IsHC D 1 :=
  ⟨⟨continuous_const, fun _ => rfl⟩, fun _ => ⟨0, 0, by simp, GlobalTheory.Member.exists_isInfFam_family D, fun _ _ _ _ _ => by simp⟩⟩

theorem isAdmissibleIntegralBasisChange_one {V W : HSp D} (h : V.rank ≠ W.rank) (hV : Even V.rank) (hW : Even W.rank) : admitted V W 1 1 := by
  have h0 : ResEta D 1 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ _ => by simp⟩
  exact ⟨h, isHC_one D, isHC_one D, resEta_parity h0 (by rw [Nat.even_iff] at hV; omega),
    resEta_parity h0 (by rw [Nat.even_iff] at hW; omega)⟩

theorem isWeilOn_rank_zero (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hV : 0 < V.rank) (hW : W.rank = 0) (χ : IdC D) :
    IsWeilOn ψ V W χ 1 1 := by
  haveI : IsEmpty (Fin W.rank) := by rw [hW]; infer_instance
  have hs : ∀ x y : WA V W, x = y := fun x y => Matrix.ext fun _ j => isEmptyElim j
  refine ⟨fun g h w₀ Φ Φ' e => ?_, fun _ _ _ _ _ => rfl, fun Φ w => (continuous_const : Continuous fun _ : GA D V × GA D W => Φ.1 w), fun _ _ _ _ _ _ => rfl,
    fun e _ g h _ _ x y _ hy => ⟨1, one_pos, fun ℓ _ Φ => ?_⟩⟩
  · rw [hs (actHom V W g h w₀) w₀]; exact e
  · have hy1 : y = 1 := Units.ext (by rw [hy, Matrix.det_isEmpty]; simp)
    simp [splitFac, hy1]

structure Tow (D : D7) where
  Xs : ℕ → ℕ → HSp D
  Xs_rank : ∀ t j, j ≤ D.R.m → (Xs t j).rank = D.R.k + j * (t + 1)
  Xs_sig : ∀ t j, j ≤ D.R.m → (Xs t j).SigOK ∧ (Xs t j).IsPosDef
  Ys : ℕ → ℕ → HSp D
  Ys_rank : ∀ t j, j ≤ D.R.m → (Ys t j).rank = D.R.r + j * t
  Ys_sig : ∀ t j, j ≤ D.R.m → (Ys t j).SigOK ∧
    ∀ τ, (Ys t j).sig τ = (D.R.r + j * t - (D.R.m - j) / 2, (D.R.m - j) / 2)
  iXYs : ∀ t j, (Xs t j).V →ₗ[D.host.E] (Ys t j).V
  iXYs_isom : ∀ t j, j < D.R.m → HSpace.IsIsomEmb (Xs t j) (Ys t j) (iXYs t j)
  iYXm : ∀ t, (Ys t D.R.m).V →ₗ[D.host.E] (Xs t D.R.m).V
  iYXm_isom : ∀ t, HSpace.IsIsomEmb (Ys t D.R.m) (Xs t D.R.m) (iYXm t)
  YsLow : ℕ → ℕ → ℕ → HSp D
  YsLow_zero : ∀ t j, YsLow t j 0 = Ys t j
  YsLow_witt : ∀ t j i, (∃ C : Matrix (Fin (Ys t j).rank) (Fin i) D.host.E, IsIsoSub (Ys t j) C) →
    IsWittLower (Ys t j) (YsLow t j i) i ∧ (YsLow t j i).SigOK
  Xs_rec : ∀ j, j ≤ D.R.m → Xs D.R.t j = D.sp.X j
  Ys_rec : ∀ j, j ≤ D.R.m → Ys D.R.t j = D.sp.Y j
  iXYs_rec : ∀ j, j < D.R.m → HEq (iXYs D.R.t j) (D.sp.iXY j)
  iYXm_rec : HEq (iYXm D.R.t) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap)

theorem X_posDef (D : D7) : ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef := by
  intro j hj τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have hk := D.R.m_add_three_le_k
  rcases D.sp.X_def j hj τ with h | h
  · exact h
  exfalso
  have hsX := D.sp.X_sig j τ
  rw [h] at hsX
  rcases hj.lt_or_eq with hlt | rfl
  · have hw : (Matrix.of fun a b => (D.sp.Y j).hT (D.sp.iXY j ((D.sp.X j).frame a))
        (D.sp.iXY j ((D.sp.X j).frame b))) = (D.sp.X j).gram := by
      refine Matrix.ext fun a b => ?_
      exact D.sp.iXY_isom j hlt _ _
    rw [← hw] at hsX
    have hsY := D.sp.Y_sig j τ
    have hsum := sig_sum _ (D.sp.Y_sig j) τ
    rw [D.Y_sigval j hj τ] at hsY hsum
    have key := (sig_family (D.sp.Y j) τ hτ _ hsX hsY).2
    rw [D.sp.X_rank j hj] at key
    simp only [sigYD, Ranks.N] at key hsum
    omega
  · have hsY := D.sp.Y_sig D.R.m τ
    rw [D.Y_sigval _ hj τ] at hsY
    have hw : (Matrix.of fun a b => (D.sp.X D.R.m).hT (D.sp.iX' (D.sp.eYm.symm ((D.sp.Y D.R.m).frame a)))
        (D.sp.iX' (D.sp.eYm.symm ((D.sp.Y D.R.m).frame b)))) = (D.sp.Y D.R.m).gram := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.of_apply, D.sp.iX'_isom, ← D.sp.eYm_isom]
      simp [HSpace.gram]
    rw [← hw] at hsY
    have key := (sig_family (D.sp.X D.R.m) τ hτ _ hsY hsX).1
    simp only [sigYD, Ranks.rankY, Ranks.r] at key
    omega

def WittLowEx (D : D7) : Prop := ∀ (V : HSp D) (i : ℕ), (∃ C : Matrix (Fin V.rank) (Fin i) D.host.E, IsIsoSub V C) →
  ∃ V' : HSp D, IsWittLower V V' i ∧ V'.SigOK

theorem exists_towerSpaces (D : D7) (t : ℕ) :
    ∃ (X Y : ℕ → HSp D) (i : ∀ j, (X j).V →ₗ[D.host.E] (Y j).V) (i' : (Y D.R.m).V →ₗ[D.host.E] (X D.R.m).V),
      (∀ j, j ≤ D.R.m → (X j).rank = D.R.k + j * (t + 1)) ∧ (∀ j, j ≤ D.R.m → (X j).SigOK ∧ (X j).IsPosDef) ∧
      (∀ j, j ≤ D.R.m → (Y j).rank = D.R.r + j * t) ∧ (∀ j, (Y j).SigOK) ∧
      (∀ j, j ≤ D.R.m → ∀ τ, (Y j).sig τ = (D.R.r + j * t - (D.R.m - j) / 2, (D.R.m - j) / 2)) ∧
      (∀ j, j < D.R.m → HSpace.IsIsomEmb (X j) (Y j) (i j)) ∧ HSpace.IsIsomEmb (Y D.R.m) (X D.R.m) i' ∧
      (t = D.R.t → (∀ j, X j = D.sp.X j) ∧ (∀ j, Y j = D.sp.Y j) ∧ (∀ j, HEq (i j) (D.sp.iXY j)) ∧
        HEq i' (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap)) := by
  by_cases ht : t = D.R.t
  · subst ht
    refine ⟨D.sp.X, D.sp.Y, D.sp.iXY, D.sp.iX'.comp D.sp.eYm.symm.toLinearMap,
      fun j hj => D.sp.X_rank j hj, fun j hj => ⟨D.sp.X_sig j, X_posDef D j hj⟩,
      fun j hj => D.sp.Y_rank j hj, D.sp.Y_sig, D.Y_sigval, fun j hj => D.sp.iXY_isom j hj, ?_,
      fun _ => ⟨fun _ => rfl, fun _ => rfl, fun _ => HEq.rfl, HEq.rfl⟩⟩
    intro x y
    have h1 := D.sp.iX'_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    have h2 := D.sp.eYm_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm
  · have hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x) := Examples₂.star_isIntegral
    have hm := D.R.two_le_m
    have hk := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    refine ⟨fun j => Examples₂.posSpace hs (D.R.k + j * (t + 1)),
      fun j => DiagSp.signSpace hs (D.R.r + j * t) (DiagSp.cut _ (D.R.r + j * t - (D.R.m - j) / 2)),
      fun j => DiagSp.extTo _ _, DiagSp.extTo _ _, fun _ _ => rfl,
      fun j _ => ⟨Examples₂.posSpace_sigOK hs _, fun _ => rfl⟩, fun _ _ => rfl,
      fun j => DiagSp.signSpace_sigOK hs _ _, fun j hj τ => ?_,
      fun j hj x y => DiagSp.extTo_isom _ _ ?_ _ _ (fun a => ?_) x y,
      fun x y => DiagSp.extTo_isom _ _ ?_ _ _ (fun a => ?_) x y, fun h => absurd h ht⟩
    · rw [DiagSp.signSpace_cut_sig hs _ _ (Nat.sub_le _ _)]
      congr 1
      omega
    · rw [mul_add, mul_one]; omega
    · have := a.2
      have e : j * (t + 1) = j * t + j := by ring
      simp only [DiagSp.cut, Fin.val_castLE, decide_eq_false_iff_not]
      omega
    · rw [mul_add, mul_one]; omega
    · have := a.2
      symm
      simp only [DiagSp.cut, decide_eq_false_iff_not]
      omega

theorem nonempty_tow (h : WittLowEx D) : Nonempty (Tow D) := by
  choose X Y i i' hXr hXs hYr hYs hYv hi hi' hrec using exists_towerSpaces D
  have hL : ∀ t j n, ∃ V' : HSp D, (n = 0 → V' = Y t j) ∧
      ((∃ C : Matrix (Fin (Y t j).rank) (Fin n) D.host.E, IsIsoSub (Y t j) C) → IsWittLower (Y t j) V' n ∧ V'.SigOK) := by
    intro t j n
    by_cases hn : n = 0
    · subst hn
      exact ⟨Y t j, fun _ => rfl, fun _ => ⟨GlobalTheory.VolHeckeCheck.isWittLower_self D _, hYs t j⟩⟩
    · by_cases hC : ∃ C : Matrix (Fin (Y t j).rank) (Fin n) D.host.E, IsIsoSub (Y t j) C
      · obtain ⟨V', hV'⟩ := h _ n hC
        exact ⟨V', fun e => absurd e hn, fun _ => hV'⟩
      · exact ⟨Y t j, fun _ => rfl, fun e => absurd e hC⟩
  choose L h0 hL using hL
  exact ⟨{
    Xs := X, Xs_rank := hXr, Xs_sig := hXs, Ys := Y, Ys_rank := hYr
    Ys_sig := fun t j hj => ⟨hYs t j, hYv t j hj⟩
    iXYs := i, iXYs_isom := hi, iYXm := i', iYXm_isom := hi', YsLow := L
    YsLow_zero := fun t j => h0 t j 0 rfl
    YsLow_witt := hL
    Xs_rec := fun j _ => (hrec _ rfl).1 j
    Ys_rec := fun j _ => (hrec _ rfl).2.1 j
    iXYs_rec := fun j _ => (hrec _ rfl).2.2.1 j
    iYXm_rec := (hrec _ rfl).2.2.2 }⟩

structure RealMeas (D : D7) where
  petR : ℕ → ℕ → ℝ
  petR_pos : ∀ p q, 0 < petR p q
  petR_def : ∀ N, petR N 0 = 1 ∧ petR 0 N = 1
  petR_minf : ∀ p q, 0 < p → 0 < q → OmegaDensity (ENNReal.ofReal (petR p q) • D.cd.cd p q) (minfDensity (p + q))

theorem nonempty_realMeas (D : D7) : Nonempty (RealMeas D) := by
  have h : ∀ p q : ℕ, ∃ r : ℝ, 0 < r ∧ OmegaDensity (ENNReal.ofReal r • D.cd.cd p q) (minfDensity (p + q)) := by
    intro p q
    obtain ⟨c, h0, ht, hc, -⟩ := D.cd.trick p q
    have hm0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top (by simp))
    have hmt : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
    have hne0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hm0, ht⟩
    have hnet : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top hmt h0
    lift minfDensity (p + q) / c to NNReal using hnet with t htc
    have h := GlobalTheory.CompactDualUnique.omegaDensity_smul t hc
    rw [htc, ENNReal.div_mul_cancel h0 ht] at h
    refine ⟨t, by exact_mod_cast pos_iff_ne_zero.2 hne0, ?_⟩
    rw [ENNReal.ofReal_coe_nnreal]
    exact h
  choose r hr hd using h
  refine ⟨⟨fun p q => if p = 0 ∨ q = 0 then 1 else r p q, fun p q => ?_, fun N => by simp, fun p q hp hq => ?_⟩⟩
  · split_ifs
    · exact one_pos
    · exact hr p q
  · rw [if_neg (by omega)]; exact hd p q

def memberBes (D : D7) (u : D.what₂.Word) : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) :=
  GlobalTheory.BesselCompare.toBes (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.memberDatum D u)

theorem memberBes_spec (D : D7) (u : D.what₂.Word) :
    (memberBes D u).e = GlobalTheory.BesselCompare.eMat (D.sp.Y 0) D.sp.hypE ∧
    (memberBes D u).z = GlobalTheory.BesselCompare.co (D.sp.Y 0) (D.zmOf u) ∧ (∀ i, (memberBes D u).c i = D.host.xi0) ∧
    ((memberBes D u).y : GA D (D.sp.Y 0)) = 1 := ⟨rfl, rfl, fun _ => rfl, rfl⟩

theorem memberBes_norm (D : D7) (u : D.what₂.Word) :
    Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.Y 0).gram (memberBes D u).z (memberBes D u).z =
      -((D.mem u).A.T : D.host.E) := by
  rw [(memberBes_spec D u).2.1, GlobalTheory.BesselCompare.hform_co]
  unfold D7.zmOf
  rw [map_smul, LinearMap.map_smulₛₗ (D.sp.Y 0).hT, LinearMap.smul_apply, D.sp.zm_norm, D.sp_T, ← D.cOf_eq u,
    ← bridge_star_holds D.R D.host]
  have hc := D.cOf_ne u
  have hc' : star (D.cOf u) ≠ 0 := star_ne_zero.2 hc
  simp only [smul_eq_mul, starRingEnd_apply, star_inv₀]
  field_simp

def PlaceOver (D : D7) (ε : AE D) (𝔭 : Ideal (𝓞 D.host.K)) : Prop :=
  ∀ π ∈ 𝔭, π ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.BesselData.PlaceDivides D ε (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) π)

structure Pos1 (D : D7) where
  piT : D.what₂.Word → 𝓞 D.host.E
  piT_norm : ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.BesselData.IsNormGen D (piT u) (D.mem u).A.T
  gP : Fin 2 → Ideal (𝓞 D.host.K)
  gP_prime : ∀ i, (gP i).IsPrime
  gP_over : ∀ i, (D.host.g i : 𝓞 D.host.K) ∈ gP i
  dat : D.what₂.Word → GlobalTheory.IndefiniteRowSideFullHecke.BesselData.PosDatum (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0)
  dat_bes : ∀ u, (dat u).bes = GlobalTheory.IndefiniteRowSideFullHecke.BesselData.memberDatum D u
  dat_p : ∀ u a, (dat u).p a = 1
  dat_places : ∀ u ε, IsSplitIdem D ε →
    ((∃ a, (dat u).ε a = ε) ↔ (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.PlaceDivides D ε (piT u) ∨ ∃ i, PlaceOver D ε (gP i)))

structure RecFun (D : D7) (θ : InfF D) (ψ : AddChar (AF D.host.F) ℂ) where
  chr : D.what₂.Tup → ℕ → IdC D
  chr_hc : ∀ μ j, IsHC D (chr μ j)
  chr_inf : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (chr μ (j.1 + 1)) τ (-(D.hc τ).e j)
  chr_res : ∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (chr μ j) 0
  eta : IdC D
  eta_hc : IsHeckeChar D eta
  eta_inf : ∀ τ, HasInfExp D eta τ (1 / 2)
  eta_res : ResEta D eta 1
  eta_unr : UnramEverywhere D eta
  col : ∀ (u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), D.what₂.Mu u →ₗ[ℂ] CuspS θ (D.sp.X j)
  row : ∀ (μ : D.what₂.Tup) (j : ℕ), D.what₂.Mult μ j →ₗ[ℂ] CuspS θ (D.sp.Y j)
  Phi : ∀ (_μ : D.what₂.Tup) (j : ℕ), ThS ψ (D.sp.Y (j + 1)) (D.sp.Y j)
  Phi_ne : IsStdChar D ψ (-1) → ∀ μ j, j < D.R.m → Phi μ j ≠ 0
  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j
  adelicDataRowMeasureScale_trivialTuple : ∀ j, mY D.what₂.mu0 j = 1
  mY_zero : ∀ μ, mY μ 0 = 1
  petF : HSp D → ℝ
  petF_pos : ∀ V, 0 < petF V
  meas : RealMeas D
  dec : OrthDec D
  per1 : Pos1 D

namespace RecFun

variable {θ : InfF D} {ψ : AddChar (AF D.host.F) ℂ} (Rc : RecFun D θ ψ)

def posSym (_ : RecFun D θ ψ) (u : D.what₂.Word) : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) := memberBes D u

def pos1 (_ : RecFun D θ ψ) (u : D.what₂.Word) : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) := memberBes D u

theorem firstPosition_translate_one (u) : ((Rc.pos1 u).y : GA D (D.sp.Y 0)) = 1 := rfl

theorem posSym_y (u) : ((Rc.posSym u).y : GA D (D.sp.Y 0)) = 1 := rfl

def petC (V : HSp D) : ℝ := petCOf D Rc.petF Rc.meas.petR V

def carY (μ : D.what₂.Tup) (s i : ℕ) : IdC D := if Even i then Rc.chr μ s * Rc.eta⁻¹ else Rc.chr μ s

def RowIsom : Prop := ∀ μ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
  GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
    (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)

def IoTie (Wf : WeilFun D ψ) : Prop := ∀ μ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ,
  (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (Rc.mY μ (j + 1) * Rc.petC (D.sp.Y (j + 1)))
    (fun h => Wf.ker _ _ (Rc.carY μ (j + 1) (j + 1)) (Rc.carY μ (j + 1) j) (Rc.Phi μ j) h g * (Rc.row μ (j + 1) y).1 h)
    (L g)) ∧
  ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
    (fun g => star (L g) * (Rc.row μ j x).1 g) (inner ℂ (D.what₂.io μ j y) x)

def TopTie : Prop := ∀ u μ (φ : D.what₂.Mu u) (F : D.what₂.Amb μ) (s : GA D (D.sp.Y D.R.m) → GA D (D.sp.X D.R.m)),
  (∀ h, EmbRel (D.sp.X D.R.m) (D.sp.Y D.R.m) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap) (s h) h) →
  GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y D.R.m) (Rc.mY μ D.R.m * Rc.petC (D.sp.Y D.R.m))
    (fun h => (Rc.col u μ D.R.m φ).1 (s h) * (Rc.row μ D.R.m ((D.what₂.multTop μ).symm F)).1 h) (D.what₂.perCol u μ φ F)

structure OfRecord (Wf : WeilFun D ψ) : Prop where
  rowIsom : Rc.RowIsom
  io : Rc.IoTie Wf
  top : Rc.TopTie
  col_inj : ∀ u μ, Function.Injective (Rc.col u μ 0)
  phi_pure : ∀ μ j, j < D.R.m → IsPureFun ψ _ _ (Rc.Phi μ j).1
  phi_pol : ∀ μ j, j < D.R.m → IsPolFock ψ θ _ _ (Rc.dec.cpt _) (Rc.dec.cpt _) (Rc.Phi μ j).1

theorem RowIsom.injective (h : Rc.RowIsom) (μ) {j} (hj : j ≤ D.R.m) : Function.Injective (Rc.row μ j) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨⟨m, hm⟩, h2⟩ := h μ j hj x x
  have := (h2 m hm).2
  rw [hx] at this
  simpa using this

end RecFun

def EtaEx (D : D7) : Prop :=
  ∃ η : IdC D, IsHeckeChar D η ∧ (∀ τ, HasInfExp D η τ (1 / 2)) ∧ ResEta D η 1 ∧ UnramEverywhere D η

def VacEx (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ (Dc : OrthDec D) (V W : HSp D),
  V.rank ≠ W.rank → V.SigOK → W.SigOK →
    ∃ Φ : ThS ψ V W, Φ ≠ 0 ∧ IsPureFun ψ V W Φ.1 ∧ IsPolFock ψ θ V W (Dc.cpt V) (Dc.cpt W) Φ.1

def ChrEx (D : D7) : Prop :=
  ∀ j : Fin D.R.m, ∃ χ : IdC D, IsHeckeChar D χ ∧ (∀ τ, HasInfExp D χ τ (-(D.hc τ).e j)) ∧ ResEta D χ 0

theorem nonempty_recFun (θ : InfF D) (ψ : AddChar (AF D.host.F) ℂ) (hχ : ChrEx D) (hη : EtaEx D)
    (hΦ : IsStdChar D ψ (-1) → ∀ V W : HSp D, ∃ f, IsThetaFun ψ V W f ∧ f ≠ 0) (Dc : OrthDec D) (P : Pos1 D) :
    Nonempty (RecFun D θ ψ) := by
  obtain ⟨η, h1, h4, h3, h2⟩ := hη
  obtain ⟨M⟩ := nonempty_realMeas D
  choose χ k1 k2 k3 using hχ
  have hm := D.R.two_le_m
  have hP : ∀ V W : HSp D, ∃ Φ : ThS ψ V W, IsStdChar D ψ (-1) → Φ ≠ 0 := fun V W => by
    by_cases h : IsStdChar D ψ (-1)
    · obtain ⟨f, hf, h0⟩ := hΦ h V W
      exact ⟨⟨f, mem_ThS.2 hf⟩, fun _ e => h0 (congrArg Subtype.val e)⟩
    · exact ⟨0, fun e => absurd e h⟩
  choose Φ hΦ' using hP
  exact ⟨{
    chr := fun _ j => χ ⟨(j - 1) % D.R.m, Nat.mod_lt _ (by omega)⟩
    chr_hc := fun _ _ => ⟨k1 _, fun τ => ⟨_, k2 _ τ⟩⟩
    chr_inf := fun _ j τ => by
      have e : (⟨(j.1 + 1 - 1) % D.R.m, Nat.mod_lt _ (by omega)⟩ : Fin D.R.m) = j :=
        Fin.ext (by simp [Nat.mod_eq_of_lt j.2])
      rw [e]; exact k2 j τ
    chr_res := fun _ _ _ _ => k3 _
    eta := η, eta_hc := h1, eta_inf := h4, eta_res := h3, eta_unr := h2
    col := fun _ _ _ => 0, row := fun _ _ => 0
    Phi := fun _ _ => Φ _ _
    Phi_ne := fun h _ _ _ => hΦ' _ _ h
    mY := fun _ _ => 1, mY_pos := fun _ _ => one_pos, adelicDataRowMeasureScale_trivialTuple := fun _ => rfl, mY_zero := fun _ => rfl
    petF := fun _ => 1, petF_pos := fun _ => one_pos, meas := M, dec := Dc, per1 := P }⟩

def BesGlob {X : ThetaX D} (T : ThetaTied D X) (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}
    (d : BesDat A B ι) (p : X.Pos A B ι) : Prop :=
  ∀ σ μ 𝓕, IsVolPair D A μ 𝓕 → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
    ∀ (φ : X.AF A) (F : X.cusp B), IsAniso A ∨ φ ∈ X.cusp A →
      GlobalTheory.BesselCompare.ClauseFlag ψ d μ 𝓕 s (T.ev A φ) (T.ev B (F : X.AF B)) (T.petC A) (X.Bper A B ι p σ φ F)

structure Realises {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} (B : BesselTied D X T W)
    (Wf : WeilFun D W.ψ) (Tw : Tow D) (Rc : RecFun D θ W.ψ) : Prop where
  inf : IsInfFam θ

  forms : ∀ V, Set.range (T.ev V) = {φ | IsAutFunSm θ V φ}
  typ : ∀ V P F, F ∈ X.typ V P ↔ T.ev V F ∈ TypS θ V P

  sch : ∀ V V', Set.range (W.evS V V') = {f | IsThetaFun W.ψ V V' f}
  chr : ∀ μ j, T.eChr (X.chrOf μ j) = Rc.chr μ j
  eta : T.eChr X.etaT = Rc.eta
  col : ∀ u μ j φ, T.ev _ (X.colAF u μ j φ).1 = (Rc.col u μ j φ).1
  row : ∀ μ j F, T.ev _ (X.rowAF μ j F).1 = (Rc.row μ j F).1
  phi : ∀ μ j, W.evS _ _ (X.PhiY μ j) = (Rc.Phi μ j).1
  phiUp : PhiYupTied W
  mY : X.mY = Rc.mY
  petF : T.petF = Rc.petF
  petR : T.petR = Rc.meas.petR
  xs : X.Xs = Tw.Xs
  ys : X.Ys = Tw.Ys
  ysLow : X.YsLow = Tw.YsLow
  iXYs : ∀ t j, HEq (X.iXYs t j) (Tw.iXYs t j)
  iYXm : ∀ t, HEq (X.iYXm t) (Tw.iYXm t)
  om : ∀ V V' χ χ' p (Φ : X.Sch V V') (f : ThS W.ψ V V'), W.evS V V' Φ = f.1 →
    W.evS V V' (W.om V V' χ χ' p Φ) = (Wf.om V V' (T.eChr χ) (T.eChr χ') p f).1

  thOff : ∀ (V V' : HSp D) χ χ', ¬ (admitted V V' (T.eChr χ) (T.eChr χ') ∧ V.SigOK) → X.th V V' χ χ' = 0

  fact : ∀ V V' Φ, Φ ∈ X.fact V V' ↔ IsPureFun W.ψ V V' (W.evS V V' Φ)

  kfin : ∃ K : KfinTied W, K.cpt = Rc.dec.cpt ∧ K.bas = Rc.dec.bas

  posDat : ∀ u ho, B.dat _ _ _ ho (X.posSym u) = Rc.posSym u ∧ B.dat _ _ _ ho (X.pos1 u) = Rc.pos1 u

  pos1Val : ∀ u σ μ 𝓕, IsVolPair D (D.sp.X 0) μ 𝓕 → ∀ ν 𝓝, (Rc.per1.dat u).bes.IsUnitPair ν 𝓝 →
    ∀ s : GA D (D.sp.X 0) → GA D (D.sp.Y 0), (∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h) →
    ∀ (φ : X.AF (D.sp.X 0)) (F : X.cusp (D.sp.Y 0)), X.Bper _ _ _ (X.pos1 u) σ φ F = (T.petC (D.sp.X 0) : ℂ) *
      (Rc.per1.dat u).period W.ψ μ 𝓕 ν 𝓝 s (fun g => star (T.ev _ φ g)) (T.ev _ (F : X.AF (D.sp.Y 0)))

  besAll : ∀ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V) ho, A.SigOK → HSpace.IsIsomEmb A A' ι →
    ∀ d : BesDat A A' ι, (d.y : GA D A') = 1 → ∃ p, B.dat A A' ι ho p = d ∧ BesGlob T W.ψ d p

  besOnly : ∀ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V) ho, A.SigOK → HSpace.IsIsomEmb A A' ι →
    ∀ p, BesGlob T W.ψ (B.dat A A' ι ho p) p ∨ ∃ u,
      (⟨A, A', ι, p⟩ : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), X.Pos A A' ι) = ⟨_, _, _, X.pos1 u⟩

def IsQuot (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ

def FormSub (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), φ ∈ AFs θ V ↔ IsAutFunSm θ V φ

theorem mem_CuspS (h : FormSub D) {θ : InfF D} (hθ : IsInfFam θ) {V : HSp D} {φ : GA D V → ℂ} :
    φ ∈ CuspS θ V ↔ IsCuspForm θ V φ := by
  refine ⟨fun hφ => ?_, fun hφ => Submodule.subset_span hφ⟩
  have h1 := (h θ hθ V φ).1 (CuspS_le θ V hφ)
  refine ⟨h1, (GlobalTheory.AutFunCompare.isCuspFun_iff V φ h1.cont h1.left).2 ?_⟩
  exact (Submodule.span_le.2 fun g hg => (GlobalTheory.AutFunCompare.isCuspFun_iff V g hg.1.cont hg.1.left).1 hg.2 :
    CuspS θ V ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cuspidal D.sp.cm V) hφ

def PetInt (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ (V : HSp D) μ 𝓕, IsQuot V μ 𝓕 →
  ∀ φ φ', IsAutFunSm θ V φ → IsCuspForm θ V φ' → IntegrableOn (fun h => star (φ h) * φ' h) 𝓕 μ

def TopInt (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V),
  HSpace.IsIsomEmb B A ι → ∀ μ 𝓕, IsQuot B μ 𝓕 → ∀ s : GA D B → GA D A, (∀ h, EmbRel A B ι (s h) h) →
  ∀ φ φ', IsAutFunSm θ A φ → IsCuspForm θ B φ' → IntegrableOn (fun h => star (φ (s h)) * φ' h) 𝓕 μ

def BesInt (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) →
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ d : BesDat A B ι, ∀ μ 𝓕, IsQuot A μ 𝓕 →
  ∀ (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)), μN.IsHaarMeasure → IsFundamentalDomain (NFlagQ B d.e) 𝓕N μN →
  ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
  ∀ φ F, IsAutFunSm θ A φ → IsCuspForm θ B F → IsAniso A ∨ IsCuspFun A φ →
    (∀ h, IntegrableOn (fun n : NFlag B d.e => star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B))) 𝓕N μN) ∧
    IntegrableOn (fun h => ∫ n in 𝓕N, star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B)) ∂μN) 𝓕 μ

def PosLin (D : D7) : Prop := GlobalTheory.IndefiniteRowSideFullHecke.BesselData.ConvergesDef D ∧ GlobalTheory.IndefiniteRowSideFullHecke.BesselData.ExchangeFinite D ∧
  ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) →
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (P : GlobalTheory.IndefiniteRowSideFullHecke.BesselData.PosDatum A B ι), A.SigOK → A.IsDefinite →
    ∃ b : AFs θ A →ₗ⋆[ℂ] CuspS θ B →ₗ[ℂ] ℂ, ∀ μ 𝓕, IsVolPair D A μ 𝓕 → ∀ ν 𝓝, P.bes.IsUnitPair ν 𝓝 →
      ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) → ∀ φ F,
        P.period ψ μ 𝓕 ν 𝓝 s (fun g => star (φ.1 g)) F.1 = b φ F

def LiftAut (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ (Wf : WeilFun D ψ)
  (V W : HSp D) χ χ', admitted V W χ χ' → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ (Φ : ThS ψ V W) F, IsCuspForm θ V F →
    (∀ h, IntegrableOn (fun g => Wf.ker V W χ χ' Φ g h * F g) 𝓕 μ) ∧
    IsAutFunSm θ W fun h => ∫ g in 𝓕, Wf.ker V W χ χ' Φ g h * F g ∂μ

def TypAdd (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ V : HSp D, V.SigOK → ∀ τ S,
  GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S →
    IsTypeAt θ V τ S 0 ∧ ∀ φ φ', IsAutFunSm θ V φ → IsAutFunSm θ V φ' →
      IsTypeAt θ V τ S φ → IsTypeAt θ V τ S φ' → IsTypeAt θ V τ S (φ + φ')

theorem mem_TypS (h : FormSub D) (ht : TypAdd D) {θ : InfF D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.SigOK)
    {P : D.what₂.Tau → SPar} (hP : ∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (P τ)) {φ : GA D V → ℂ} :
    φ ∈ TypS θ V P ↔ IsAutFunSm θ V φ ∧ ∀ τ, IsTypeAt θ V τ (P τ) φ := by
  refine ⟨fun hφ => ?_, fun hφ => Submodule.subset_span hφ⟩
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨(h θ hθ V 0).1 (zero_mem _), fun τ => (ht θ hθ V hV τ _ (hP τ)).1⟩
  | add x y _ _ hx hy =>
    exact ⟨(h θ hθ V _).1 (add_mem ((h θ hθ V x).2 hx.1) ((h θ hθ V y).2 hy.1)),
      fun τ => (ht θ hθ V hV τ _ (hP τ)).2 x y hx.1 hy.1 (hx.2 τ) (hy.2 τ)⟩
  | smul c x _ hx =>
    exact ⟨(h θ hθ V _).1 (Submodule.smul_mem _ c ((h θ hθ V x).2 hx.1)), fun τ => isTypeAt_smul c (hx.2 τ)⟩

def WeilCoreEx (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → Nonempty (WeilCore D ψ)

def WeilRules (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → ∀ Wc : WeilCore D ψ, Wc.Rules

def WeilEx (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → Nonempty (WeilFun D ψ)

theorem weilEx_of (h : WeilCoreEx D) (hr : WeilRules D) : WeilEx D :=
  fun ψ hψ => (h ψ hψ).elim fun Wc => ⟨Wc.toFun (hr ψ hψ Wc)⟩

def RealisedEx (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) →
  ∀ (Wf : WeilFun D ψ) (Tw : Tow D) (Rc : RecFun D θ ψ),
    ∃ (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T) (B : BesselTied D X T W) (h : W.ψ = ψ),
      Realises (θ := θ) B (h ▸ Wf) Tw (h ▸ Rc)

namespace Realises

variable {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
  {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ} (h : Realises B Wf Tw Rc)

include h

theorem eq_of_isInfFam {θ' : InfF D} (h' : IsInfFam θ') : θ' = θ :=
  ((GlobalTheory.AutFunCompare.isInfFam_iff θ').1 h').trans ((GlobalTheory.AutFunCompare.isInfFam_iff θ).1 h.inf).symm

theorem afTiedSm : ThetaSmoothnessCondition T := ⟨⟨θ, h.inf⟩, fun _ h' V _ => by rw [h.eq_of_isInfFam h']; exact h.forms V⟩

theorem formSub : FormSub D := fun θ' h' V φ => by
  rw [h.eq_of_isInfFam h']
  refine ⟨fun hφ => ?_, fun hφ => Submodule.subset_span hφ⟩
  have : AFs θ V ≤ LinearMap.range (T.ev V) := Submodule.span_le.2 (by rw [LinearMap.coe_range, h.forms V])
  have h2 : φ ∈ Set.range (T.ev V) := this hφ
  rwa [h.forms V] at h2

theorem typTied (ht : TypAdd D) : TypTied T := ⟨⟨θ, h.inf⟩, fun _ h' V hV P hP => by
  intros
  rename_i F
  rw [h.eq_of_isInfFam h', h.typ, mem_TypS h.formSub ht h.inf hV hP]
  have : T.ev V F ∈ Set.range (T.ev V) := ⟨F, rfl⟩
  rw [h.forms V] at this
  exact ⟨fun k => k.2, fun k => ⟨this, k⟩⟩⟩

theorem weilUnrTied : WeilUnramifiedCondition W := fun V V' χ χ' hr h1 h2 S u1 u2 k hk k' hk' Φ hΦ => by
  have hc : ∀ χ, IsHC D (T.eChr χ) := fun χ => by
    have : T.eChr χ ∈ Set.range T.eChr := ⟨χ, rfl⟩
    rwa [T.eChr_range] at this
  have hf : W.evS V V' Φ ∈ Set.range (W.evS V V') := ⟨Φ, rfl⟩
  rw [h.sch] at hf
  refine W.evS_inj V V' ?_
  rw [h.om V V' χ χ' (k, k') Φ ⟨_, mem_ThS.2 hf⟩ rfl,
    Wf.om_unr V V' _ _ ⟨hr, hc χ, hc χ', h1, h2⟩ S u1 u2 k hk k' hk' _ hΦ]

theorem allTied (ht : TypAdd D) {A : ProvA} (hr : RealTied D) (hp : ProvisionCompatibility D A) : Nonempty (AllTied D X A) := by
  obtain ⟨K, -⟩ := h.kfin
  exact ⟨⟨T, h.afTiedSm, h.typTied ht, W, h.weilUnrTied, K, h.phiUp, B, hr, hp⟩⟩

theorem petC_eq (V : HSp D) : T.petC V = Rc.petC V := by
  unfold ThetaTied.petC RecFun.petC; rw [h.petF, h.petR]

theorem tieRowIsom (hi : Rc.RowIsom) : X.TieRowIsom := fun μ j hj x y => by
  obtain ⟨⟨m, hm⟩, h2⟩ := hi μ j hj x y
  have e := T.pet _ (D.sp.Y_sig j) m.1 m.2 hm (X.rowAF μ j x) (X.rowAF μ j y)
  unfold ThetaX.petY
  rw [e, (h2 m hm).2, h.row, h.row, h.mY, ← h.petC_eq]
  simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]

theorem tieBm (hi : Rc.TopTie) : X.TieBm := fun u μ φ F => by
  have hι : HSpace.IsIsomEmb (D.sp.Y D.R.m) (D.sp.X D.R.m) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap) := fun x y => by
    have h1 := D.sp.iX'_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    have h2 := D.sp.eYm_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm
  have hs := fun g => (GlobalTheory.AutFunCompare.embRel_iff _ _ _ hι _ g).2 rfl
  obtain ⟨⟨m, hm⟩, h2⟩ := hi u μ φ F _ hs
  rw [T.btop _ _ _ (D.sp.Y_sig _) hι m.1 m.2 hm _ hs, (h2 m hm).2]
  simp only [T.conj, star_star, h.col, h.row, h.mY, ← h.petC_eq, ThetaTied.petC, Complex.ofReal_mul, mul_assoc]

theorem carY_eq (μ s i) : T.eChr (X.carY μ s i) = Rc.carY μ s i := by
  unfold ThetaX.carY RecFun.carY
  split_ifs
  · rw [map_mul, map_inv, h.chr, h.eta]
  · exact h.chr _ _

theorem tieIo (hi : Rc.IoTie Wf) : X.TieIo := fun μ j hj y x => by
  obtain ⟨L, hL, hx⟩ := hi μ j hj y
  obtain ⟨⟨m, hm⟩, h2⟩ := hx x
  have e : T.ev _ (X.dnY μ j (X.rowAF μ (j + 1) y)) = L := by
    funext g
    obtain ⟨⟨n, hn⟩, h3⟩ := hL g
    have k := W.th _ _ _ _ (rank_Y_ne X j hj) (row_lift_ok T μ (j + 1) (by omega) hj (j + 1) hj)
      (row_lift_ok T μ (j + 1) (by omega) hj j hj.le) (D.sp.Y_sig _) n.1 n.2 hn (X.PhiY μ j) (X.rowAF μ (j + 1) y) g
    unfold ThetaX.dnY
    rw [LinearMap.smul_apply, map_smul, Pi.smul_apply, k, (h3 n hn).2]
    simp only [h.om _ _ _ _ _ _ _ (h.phi μ j), h.carY_eq, h.row, h.mY, ← h.petC_eq, WeilFun.ker, Complex.ofReal_mul,
      mul_assoc, smul_eq_mul]
  unfold ThetaX.petY
  rw [T.pet _ (D.sp.Y_sig j) m.1 m.2 hm, (h2 m hm).2, e, h.row, h.mY, ← h.petC_eq]
  simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]

end Realises

end GlobalTheory.Mem.Th

end
