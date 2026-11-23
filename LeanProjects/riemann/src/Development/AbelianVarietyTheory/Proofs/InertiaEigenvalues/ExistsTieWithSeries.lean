import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesInstall

variable {D : D7} {ρ : Setup D.ntw}

abbrev RdV (D : D7) (ρ : Setup D.ntw) : Type :=
  ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k]
    (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)

def rdVLin (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k]
      Via (D.ntw.Ok i k) (ρ.ek i b k) (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank) where
  toFun f := rdV i j b k Q ψ f
  map_add' f g := map_add _ f g
  map_smul' c f := by
    rw [← algebraMap_smul (FractionRing (D.ntw.Ok i k)) c f, map_smulₛₗ]
    rfl

open Classical in

def latI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i n b k Q ψ)
  | 0, b, k, Q, ψ => D.nexp.MtLat i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => if h : n < D.R.m ∧ TwOK i k Q ψ then
      (Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)).comap (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) else D.nexp.MtLat i (n + 1) b k Q ψ

def Onto (ρ : Setup D.ntw) (rdV : RdV D ρ) : Prop :=
  ∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧
    Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤

theorem latI_eq (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) :
    latI rdV i ((j : ℕ) + 1) b k Q ψ = (Via.lat (ρ.mt i j b k Q ψ)).comap (rdVLin rdV i j b k Q ψ) :=
  dif_pos ⟨j.2, h⟩

theorem mem_latI (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) (f) :
    f ∈ latI rdV i ((j : ℕ) + 1) b k Q ψ ↔ rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ := by
  rw [latI_eq rdV j h]; exact Iff.rfl

theorem latI_fg (rdV : RdV D ρ) (hV : Onto ρ rdV) (hL : ρ.LatFG) (i) :
    ∀ n b k Q ψ, (latI rdV i n b k Q ψ).FG
  | 0, b, k, Q, ψ => D.nexp.MtLat_fg i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · obtain ⟨hinj, hon, -⟩ := hV i ⟨n, h.1⟩ b k Q ψ h.2
      refine Submodule.fg_of_fg_map_injective (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) hinj ?_
      rw [Submodule.map_comap_eq_self (f := rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) (q := Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ))
        fun x (hx : x ∈ Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)) => by obtain ⟨y, hy⟩ := hon (Via.out _ _ x) hx; exact ⟨y, hy⟩]
      exact Via.lat_fg (hL i ⟨n, h.1⟩ b k Q ψ h.2)
    · exact D.nexp.MtLat_fg i (n + 1) b k Q ψ

theorem latI_span (rdV : RdV D ρ) (hV : Onto ρ rdV) (i) :
    ∀ n b k Q ψ, Submodule.span (FractionRing (D.ntw.Ok i k)) (latI rdV i n b k Q ψ : Set (D.nexp.MtV i n b k Q ψ)) = ⊤
  | 0, b, k, Q, ψ => D.nexp.MtLat_span i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · exact (hV i ⟨n, h.1⟩ b k Q ψ h.2).2.2
    · exact D.nexp.MtLat_span i (n + 1) b k Q ψ

variable (hρ : ρ.Good) (rd : Rds D.nexp ρ) (hF : ∀ i j b, Faithful (rd i j b))

include hF in
theorem exists_thPI (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    ∃ φ : D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b,
      ∀ f, ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) ∈ Set.range (rdK (rd i j b) hρ k) →
        rdK (rd i j b) hρ k (φ f) = ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) :=
  exists_lift ((ρ.sum i j b k Q ψ).comp (rdV i j b k Q ψ)) (rdK (rd i j b) hρ k) ((hF i j b).injective_rdK hρ k)
    (divisible_baseChange D.nexp i _ b k)

def thPI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ,
    D.nexp.MtV i n b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i n b
  | 0, _, _, _, _ => 0
  | n + 1, b, k, Q, ψ => if h : n < D.R.m then (exists_thPI hρ rd hF rdV i ⟨n, h⟩ b k Q ψ).choose else 0

theorem exists_tie_withSeries : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) → ρ.LevelOf D.nexp → ρ.LatFG → ∀ rdV : ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank), (∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧ Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤) → ∃ Dat th lev thPsi h1 thU thP MtLat h2 h3, (∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, IsEmpty (Dat i j b)) ∧ ∃ t : Comparison₂ hρ (Y := { D.nexp with Dat := Dat, th := th, lev := lev, thPsi := thPsi, thPsi_one := h1, thU := thU, thP := thP, MtLat := MtLat, MtLat_fg := h2, MtLat_span := h3 }) rd, ∀ i j b, (t i j b).rdV = rdV i j b := by
  intro D ρ hρ rd hF hU hL rdV hV
  refine ⟨Model.Dat rd, Model.th rd, Model.lev rd, Model.thPsi hρ rd, Model.thPsi_one hρ rd hF, Model.thU rd,
    thPI hρ rd hF rdV, latI rdV, latI_fg rdV hV hL, latI_span rdV hV, ?_, ?_⟩
  · intro i n hn b
    cases n with
    | zero => exact ⟨fun d => d.elim⟩
    | succ n =>
      refine ⟨fun d => hn (Finset.mem_Icc.2 ⟨Nat.succ_pos n, d.1⟩)⟩
  · refine ⟨fun i j b =>
      { supp := fun d => d.2.s
        cls := fun d => d.2.h
        coef := fun d => d.2.P
        rdV := rdV i j b
        U_eq := hU.U_eq i j b
        psiU_eq := hU.psiU_eq i j b
        dat := fun d => d.2.isDatum
        dat_onto := fun s h P h1 h2 => ⟨⟨j.2, s, h, P, h1, h2⟩, rfl, rfl, rfl⟩
        lev_iff := fun _ _ => Set.Finite.mem_toFinset _
        th_eq := fun d => d.2.rat.choose_spec
        thPsi_iff := fun _ _ _ _ _ _ => Iff.rfl
        thU_eq := fun Q M d hQ x hx => by
          have h : InRange D.ntw i Q ∧ ∀ a, ρ.xi i j b D.nexp Q M d.2.h d.2.P a ∈ Set.range (rd i j b) :=
            ⟨hQ, fun a => ⟨x a, hx a⟩⟩
          refine (dif_pos h).trans (congrArg (grpSum D.nexp (ρ.ch i) Q M) (funext fun a => (hF i j b).injective ?_))
          exact (h.2 a).choose_spec.trans (hx a).symm
        thU_off := fun _ _ _ h => dif_neg h
        rdV_inj := fun k Q ψ h => (hV i j b k Q ψ h).1
        mtLat_iff := fun k Q ψ h F => by
          refine ⟨fun hF' => ?_, fun ⟨f, hf, e'⟩ => ?_⟩
          · obtain ⟨f, rfl⟩ := (hV i j b k Q ψ h).2.1 F hF'
            exact ⟨f, (mem_latI rdV j h f).2 hF', rfl⟩
          · exact e' ▸ (mem_latI rdV j h f).1 hf
        thP_eq := fun k Q ψ _ f hf => by
          have e : thPI hρ rd hF rdV i ((j : ℕ) + 1) b k Q ψ = (exists_thPI hρ rd hF rdV i j b k Q ψ).choose := dif_pos j.2
          exact (congrArg (fun φ => rdK (rd i j b) hρ k (φ f)) e).trans
            ((exists_thPI hρ rd hF rdV i j b k Q ψ).choose_spec f hf) }, fun _ _ _ => rfl⟩

end GlobalTheory.SeriesInstall
end
