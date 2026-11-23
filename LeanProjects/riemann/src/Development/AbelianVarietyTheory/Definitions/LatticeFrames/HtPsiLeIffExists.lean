import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions

def rkPsiC {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (A : ColumnsAtT R C)
    (P : PeriodMap R C) : ℕ := Module.finrank ℂ (LinearMap.range (PsiC C A P))

variable (D : D7) (u : D.what₂.Word)

abbrev Pt : HLat D.what₂.LL := (D.fm u).ptLat

def IsPsi (Ψ : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V) : Prop :=
  ∀ x : (D.div.Nu u).V, (D.fm u).ptEmb (Ψ x) = PsiC (D.mem u).C (D.mem u).A (D.mem u).P (D.eMu u (D.jN u x))

def PsiRat : Prop := ∃ Ψ, IsPsi D u Ψ

open Classical in

def Psi : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V := if h : PsiRat D u then h.choose else 0

theorem isPsi_Psi (h : PsiRat D u) : IsPsi D u (Psi D u) := by
  unfold Psi; rw [dif_pos h]; exact h.choose_spec

theorem IsPsi.unique {Ψ Ψ'} (h : IsPsi D u Ψ) (h' : IsPsi D u Ψ') : Ψ = Ψ' :=
  LinearMap.ext fun x => (D.fm u).ptEmb_inj ((h x).trans (h' x).symm)

theorem IsPsi.eq_Psi {Ψ} (h : IsPsi D u Ψ) : Ψ = Psi D u :=
  IsPsi.unique D u h (isPsi_Psi D u ⟨Ψ, h⟩)

def RKPsi : Prop := Module.finrank D.what₂.LL (D.div.Nu u).V < 2 * Module.finrank D.what₂.LL (LinearMap.range (Psi D u))

def htPsi : ℝ := Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X (Pt D u).b (Pt D u).X (Psi D u)

def HtPsiLe (h : ℝ) : Prop := PsiRat D u ∧ (Psi D u ≠ 0 → htPsi D u ≤ h)

def PsiInt (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Prop :=
  PsiRat D u ∧ ∀ x ∈ N, Psi D u x ∈ (Pt D u).L

theorem psiInt_iff_exists (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    PsiInt D u N ↔ ∃ Ψ, IsPsi D u Ψ ∧ ∀ x ∈ N, Ψ x ∈ (Pt D u).L := by
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨_, isPsi_Psi D u h, h'⟩
  · rintro ⟨Ψ, h, h'⟩
    refine ⟨⟨Ψ, h⟩, ?_⟩
    rw [← IsPsi.eq_Psi D u h]
    exact h'

theorem psiInt_iff (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    PsiInt D u N ↔ PsiRat D u ∧ ∀ x ∈ N, ∃ y ∈ (Pt D u).L,
      (D.fm u).ptEmb y = PsiC (D.mem u).C (D.mem u).A (D.mem u).P (D.eMu u (D.jN u x)) := by
  refine and_congr_right fun h => forall₂_congr fun x _ => ⟨fun hx => ⟨_, hx, isPsi_Psi D u h x⟩, ?_⟩
  rintro ⟨y, hy, e⟩
  rwa [← (D.fm u).ptEmb_inj (e.trans (isPsi_Psi D u h x).symm)]

theorem PsiInt.mono {N N' : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V} (h : PsiInt D u N) (hle : N' ≤ N) :
    PsiInt D u N' := ⟨h.1, fun x hx => h.2 x (hle hx)⟩

theorem htPsiLe_iff_exists (h : ℝ) : HtPsiLe D u h ↔ ∃ Ψ, IsPsi D u Ψ ∧
    (Ψ ≠ 0 → Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X (Pt D u).b (Pt D u).X Ψ ≤ h) := by
  constructor
  · rintro ⟨hr, h'⟩
    exact ⟨_, isPsi_Psi D u hr, h'⟩
  · rintro ⟨Ψ, hΨ, h'⟩
    refine ⟨⟨Ψ, hΨ⟩, ?_⟩
    unfold htPsi
    rw [← IsPsi.eq_Psi D u hΨ]
    exact h'

theorem RKPsi.psi_ne_zero (h : RKPsi D u) : Psi D u ≠ 0 := by
  intro h0
  unfold RKPsi at h
  rw [h0, LinearMap.range_zero, finrank_bot] at h
  omega

theorem RKPsi.psiRat (h : RKPsi D u) : PsiRat D u := by
  by_contra h'
  exact RKPsi.psi_ne_zero D u h (dif_neg h')

theorem RKPsi.htPsi_le (h : RKPsi D u) {t : ℝ} (ht : HtPsiLe D u t) : htPsi D u ≤ t :=
  ht.2 (RKPsi.psi_ne_zero D u h)

example : PsiInt D u ⊥ ↔ PsiRat D u := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun x hx => ?_⟩⟩
  rw [(Submodule.mem_bot _).1 hx, map_zero]
  exact Submodule.zero_mem _

example (x : (D.div.Nu u).V)
    (hx : PsiC (D.mem u).C (D.mem u).A (D.mem u).P (D.eMu u (D.jN u x)) ∉ Set.range (D.fm u).ptEmb)
    (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (t : ℝ) : ¬ PsiInt D u N ∧ ¬ HtPsiLe D u t :=
  ⟨fun h => hx ⟨_, isPsi_Psi D u h.1 x⟩, fun h => hx ⟨_, isPsi_Psi D u h.1 x⟩⟩

variable (Am : AmbForm D (RowSide.sharp D))

def IsPer (e : (Pt D u).V ≃ₗ[D.what₂.LL] (MtDual D Am).V) : Prop :=
  ∀ (x : (Pt D u).V) (z : (Mt D Am).V),
    D.what₂.embLL ((show Module.Dual D.what₂.LL (Mt D Am).V from e x) z) =
      (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm (Am.jAmb D.what₂.mu0 z))

theorem IsPer.unique {e e'} (h : IsPer D u Am e) (h' : IsPer D u Am e') : e = e' :=
  LinearEquiv.ext fun x => LinearMap.ext fun z => D.what₂.embLL.injective ((h x z).trans (h' x z).symm)

theorem IsPer.isPhi_comp {e} (he : IsPer D u Am e) {Ψ} (h : IsPsi D u Ψ) : IsPhi D Am u (e.toLinearMap ∘ₗ Ψ) := fun x z => by
  refine (he (Ψ x) z).trans ?_
  rw [h x]
  exact (PhiC_apply _ _ _ _ _).trans (D.perCol_base_eq_PtilCol u _ _).symm

def AmbMetric : Prop :=
  ∃ e, IsPer D u Am e ∧ ∀ (v : InfinitePlace D.what₂.LL) (x : (Pt D u).V),
    Formalism.HermitianLatticesTheory.normAt (MtDual D Am).b (MtDual D Am).X v (e x) = Formalism.HermitianLatticesTheory.normAt (Pt D u).b (Pt D u).X v x

def AmbLattice : Prop :=
  ∃ e, IsPer D u Am e ∧ (∀ x, e x ∈ (MtDual D Am).L → x ∈ (Pt D u).L) ∧
    ∀ x ∈ (Pt D u).L, ((D.mem u).C.DGam : D.what₂.LL) • e x ∈ (MtDual D Am).L

example (hL : AmbLattice D u Am) (h : PsiRat D u) {N} (hN : PhiInt D Am u N) : PsiInt D u N := by
  obtain ⟨e, he, h1, -⟩ := hL
  refine ⟨h, fun x hx => h1 _ ?_⟩
  have := hN.2 x hx
  rw [← IsPhi.eq_Phi D Am u (IsPer.isPhi_comp D u Am he (isPsi_Psi D u h))] at this
  exact this

end GlobalTheory.Core.Rk

end
