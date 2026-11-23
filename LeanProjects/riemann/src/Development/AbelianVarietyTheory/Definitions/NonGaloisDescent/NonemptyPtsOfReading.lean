import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

theorem frBor_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {A : Type} [CommRing A] [Algebra c.F A] (w : FrPt Xo c A) : FrBor 1 w w :=
  ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c _ w w w).1 1).2 ⟨fun _ => 1, fun _ _ _ h => Matrix.one_apply_ne h.ne,
    fun _ _ => Matrix.one_apply_eq _, (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ w w w).1⟩

def IsUnitDiag {p : ℕ} [Fact p.Prime] {F ι : Type} [Field F] {φ : F →+* ℂ_[p]} (t : ι → (PAt φ)ˣ) : Prop :=
  ∀ a, ‖toCp φ (t a)‖ = 1

theorem isUnitDiag_one {p : ℕ} [Fact p.Prime] {F ι : Type} [Field F] {φ : F →+* ℂ_[p]} : IsUnitDiag (1 : ι → (PAt φ)ˣ) :=
  fun _ => by simp

abbrev toK {i : D.ntw.Tw} (j : Fin D.R.m) (b : Bool) :
    D.nexp.Fm i ((j : ℕ) + 1) b ≃ₗ[FractionRing (D.ntw.O i)] NX.Fm S i ((j : ℕ) + 1) b :=
  YS.eF i _ b (Nat.le_add_left _ _) j.2

variable (T : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp)

structure SideTie (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) where

  pt : T.Pt i ((j : ℕ) + 1) → Option (Pts YS (T.iC i) b ((j : ℕ) + 1))

  cover : ∀ z : Pts YS (T.iC i) b ((j : ℕ) + 1), ∃ y z' t, pt y = some z' ∧ IsUnitDiag t ∧ FrBor t z'.1 z.1

  ev_eq : ∀ f y, T.ev i _ b f y = (pt y).elim 0 fun z => valAt YS fw j z.1 (toK YS j b f)

  fmUr : ∀ f, f ∈ T.FmUr i _ b ↔ toK YS j b f ∈ ratForms S _ b (kurAt YS (T.iC i) b)

  hk : ∀ k P, HkIdx i k P → ∃ s : T0.Q.c.F, ‖embC YS (T.iC i) b s‖ = 1 ∧ ∀ y z, pt y = some z →
    ∃ e : T.hkIdx i ((j : ℕ) + 1) k P ≃ HkKer P.asIdeal (charAt P) k z.1, ∀ c, ∃ z' t w,
      pt (T.hkMove i _ k P c y) = some z' ∧ IsHkQuot P.asIdeal (charAt P) k z.1 (e c) w ∧ IsUnitDiag t ∧ FrBor t z'.1 w ∧
        T.hkU i _ b k P c y = embC YS (T.iC i) b s * wtChar (wtA (κ j)) (κ j).n t

  hk_none : ∀ k P, HkIdx i k P → ∀ y, pt y = none → ∀ c, ‖T.hkU i _ b k P c y‖ = 1

structure ThetaTie where

  side : ∀ i j b, SideTie YS fw T i j b

  isUnramified₂ : ∀ i, T.MaximalUnramifiedExtension i = kurAt YS (T.iC i) true ⊓ kurAt YS (T.iC i) false

namespace SideTie

variable {YS fw T} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (Z : SideTie YS fw T i j b)

theorem ev_some {y z} (h : Z.pt y = some z) (f) : T.ev i _ b f y = valAt YS fw j z.1 (toK YS j b f) := by
  rw [Z.ev_eq, h]; rfl

theorem ev_none {y} (h : Z.pt y = none) (f) : T.ev i _ b f y = 0 := by rw [Z.ev_eq, h]; rfl

theorem ev_eq_evI {y z} (h : Z.pt y = some z) :
    ∃ (Tc : CDVR) (io : T0.Q.c.F →+* Tc.Fr) (k : Tc.Fr →+* ℂ_[D.ntw.l i]) (_ : IsReading (embC YS (T.iC i) b) Tc io k)
      (y₀ : IntFr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c Tc io) (u : ℂ_[D.ntw.l i]), y₀.IsAlg ∧ ‖u‖ = 1 ∧
      ∀ (a : NX.KB S i b) (x : NX.FmK S ((j : ℕ) + 1)),
        T.ev i _ b ((toK YS j b).symm (a ⊗ₜ[S.Ks] x : NX.KB S i b ⊗[S.Ks] _)) y =
          T.iC i a * (u * k (evI y₀ (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)))) := by
  obtain ⟨Tc, io, k, hk, y₀, u, hy, hu, hv⟩ := z.exists_valC (wtA (κ j)) (κ j).n
  refine ⟨Tc, io, k, hk, y₀, u, hy, hu, fun a x => ?_⟩
  rw [Z.ev_some h, ← hv _ (cuspOf_mem_sec YS fw j x), ← valAt_tmul]
  exact congrArg _ ((toK YS j b).apply_symm_apply _)

include Z in

theorem exists_ev_eq (z : Pts YS (T.iC i) b ((j : ℕ) + 1)) :
    ∃ (y : T.Pt i ((j : ℕ) + 1)) (u : ℂ_[D.ntw.l i]), ‖u‖ = 1 ∧ ∀ f, valAt YS fw j z.1 (toK YS j b f) = u * T.ev i _ b f y := by
  obtain ⟨y, z', t, hy, ht, hb⟩ := Z.cover z
  exact ⟨y, _, norm_wchar ht _, fun f => by rw [Z.ev_some hy]; exact valAt_frBor YS fw j hb _⟩

include Z in

theorem exists_ev_eq_evI {Tc : CDVR} {io : T0.Q.c.F →+* Tc.Fr} {k : Tc.Fr →+* ℂ_[D.ntw.l i]}
    (hk : IsReading (embC YS (T.iC i) b) Tc io k) (y₀ : IntFr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c Tc io) (hy : y₀.IsAlg) :
    ∃ (y : T.Pt i ((j : ℕ) + 1)) (u : ℂ_[D.ntw.l i]), ‖u‖ = 1 ∧ ∀ (a : NX.KB S i b) (x : NX.FmK S ((j : ℕ) + 1)),
      T.iC i a * k (evI y₀ (cuspOf YS fw j x : T0.R ((j : ℕ) + 1))) =
        u * T.ev i _ b ((toK YS j b).symm (a ⊗ₜ[S.Ks] x : NX.KB S i b ⊗[S.Ks] _)) y := by
  obtain ⟨z, hz⟩ := PtC.exists_of_reading hk y₀ hy
  obtain ⟨y, u, hu, h⟩ := Z.exists_ev_eq z
  refine ⟨y, u, hu, fun a x => ?_⟩
  rw [← h, ← hz _ _ _ (cuspOf_mem_sec YS fw j x), ← valAt_tmul]
  exact congrArg _ ((toK YS j b).apply_symm_apply _).symm

include Z in

theorem norm_le_iff {B : ℝ} (hB : 0 ≤ B) (f : D.nexp.Fm i ((j : ℕ) + 1) b) : (∀ y, ‖T.ev i _ b f y‖ ≤ B) ↔
    ∀ z : Pts YS (T.iC i) b ((j : ℕ) + 1), ‖valAt YS fw j z.1 (toK YS j b f)‖ ≤ B := by
  refine ⟨fun h z => ?_, fun h y => ?_⟩
  · obtain ⟨y, u, hu, e⟩ := Z.exists_ev_eq z
    rw [e, norm_mul, hu, one_mul]
    exact h y
  · rcases hy : Z.pt y with _ | z
    · rw [Z.ev_none hy, norm_zero]; exact hB
    · rw [Z.ev_some hy]; exact h z

include Z in

theorem ball_iff {B : ℝ} (hB : 0 ≤ B) (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (f ∈ T.FmUr i _ b ∧ ∀ y, ‖T.ev i _ b f y‖ ≤ B) ↔ toK YS j b f ∈ urBall YS fw (T.iC i) b j B :=
  and_congr (Z.fmUr f) (Z.norm_le_iff hB f)

theorem norm_hkU {k P} (h : HkIdx i k P) {y z} (hy : Z.pt y = some z) (c) : ‖T.hkU i _ b k P c y‖ = 1 := by
  obtain ⟨u, hu, H⟩ := Z.hk k P h
  obtain ⟨e, he⟩ := H y z hy
  obtain ⟨z', t, w, -, -, ht, -, e'⟩ := he c
  rw [e', norm_mul, hu, one_mul]
  exact norm_wchar ht _

include Z in

theorem norm_hkU_all {k P} (h : HkIdx i k P) (c) (y) : ‖T.hkU i ((j : ℕ) + 1) b k P c y‖ = 1 := by
  rcases hy : Z.pt y with _ | z
  · exact Z.hk_none k P h y hy c
  · exact Z.norm_hkU h hy c

theorem hecke {k P} (h : HkIdx i k P) : ∃ s : T0.Q.c.F, ‖embC YS (T.iC i) b s‖ = 1 ∧ ∀ y z, Z.pt y = some z →
    ∃ quot : HkKer P.asIdeal (charAt P) k z.1 → FrC YS (T.iC i) b ((j : ℕ) + 1),
      (∀ C, IsHkQuot P.asIdeal (charAt P) k z.1 C (quot C)) ∧ ∀ f,
        valAt YS fw j z.1 (toK YS j b (D.nexp.hkF i _ b k P f)) =
          embC YS (T.iC i) b s * ∑ᶠ C, valAt YS fw j (quot C) (toK YS j b f) := by
  obtain ⟨u, hu, H⟩ := Z.hk k P h
  refine ⟨u, hu, fun y z hy => ?_⟩
  obtain ⟨e, he⟩ := H y z hy
  choose z' t w h1 h2 _ h4 h5 using he
  refine ⟨fun C => w (e.symm C), fun C => by simpa using h2 (e.symm C), fun f => ?_⟩
  rw [← Z.ev_some hy, T.hk_ev i _ b k P h.1 h.2.1 h.2.2.1 h.2.2.2, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  beta_reduce
  rw [h5, Z.ev_some (h1 c), e.symm_apply_apply, valAt_frBor YS fw j (h4 c), mul_assoc]

include Z in

theorem exists_hkF_eq {k P} (h : HkIdx i k P) : ∃ s : T0.Q.c.F, ‖embC YS (T.iC i) b s‖ = 1 ∧
    ∀ (f : D.nexp.Fm i ((j : ℕ) + 1) b) (g : NX.Fm S i ((j : ℕ) + 1) b),
      (∀ (z : Pts YS (T.iC i) b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z.1 → FrC YS (T.iC i) b ((j : ℕ) + 1)),
        (∀ C, IsHkQuot P.asIdeal (charAt P) k z.1 C (quot C)) →
          valAt YS fw j z.1 g = ∑ᶠ C, valAt YS fw j (quot C) (toK YS j b f)) →
      toK YS j b (D.nexp.hkF i _ b k P f) = sideK YS i b s • g := by
  obtain ⟨s, hs, H⟩ := Z.hecke h
  refine ⟨s, hs, fun f g hfg => ?_⟩
  obtain ⟨g, rfl⟩ := (toK YS j b).surjective g
  rw [← map_smul]
  refine congrArg _ (T.ev_inj i _ b (funext fun y => ?_))
  rcases hy : Z.pt y with _ | z
  · rw [Z.ev_none hy, Z.ev_none hy]
  · obtain ⟨quot, hq, hv⟩ := H y z hy
    rw [Z.ev_some hy, Z.ev_some hy, hv, map_smul, valAt_smul, hfg z quot hq]
    rfl

include Z in

theorem hkF_mem_fmUr {k P} (h : HkIdx i k P) (f : D.nexp.Fm i ((j : ℕ) + 1) b) {g : NX.Fm S i ((j : ℕ) + 1) b}
    (hg : g ∈ ratForms S _ b (kurAt YS (T.iC i) b))
    (hfg : ∀ (z : Pts YS (T.iC i) b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z.1 → FrC YS (T.iC i) b ((j : ℕ) + 1)),
      (∀ C, IsHkQuot P.asIdeal (charAt P) k z.1 C (quot C)) →
        valAt YS fw j z.1 g = ∑ᶠ C, valAt YS fw j (quot C) (toK YS j b f)) :
    D.nexp.hkF i _ b k P f ∈ T.FmUr i _ b := by
  obtain ⟨s, -, H⟩ := Z.exists_hkF_eq h
  rw [Z.fmUr, H f g hfg]
  exact smul_mem_ratForms (sideK_mem_kurAt YS _ b s) hg

include Z in

theorem detects : Detects YS fw (T.iC i) b j := fun x hx => by
  obtain ⟨f, rfl⟩ := (toK YS j b).surjective x
  have : f = 0 := T.ev_inj i _ b (funext fun y => by
    rw [map_zero, Pi.zero_apply, ← norm_le_zero_iff]
    exact (Z.norm_le_iff le_rfl f).2 (fun z => by rw [hx z, norm_zero]) y)
  rw [this, map_zero]

end SideTie

variable {YS} in

theorem mem_span_toK {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {s : Set (D.nexp.Fm i ((j : ℕ) + 1) b)}
    {s' : Set (NX.Fm S i ((j : ℕ) + 1) b)} (h : ∀ f, f ∈ s ↔ toK YS j b f ∈ s') (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    f ∈ Submodule.span (D.ntw.O i) s ↔ toK YS j b f ∈ Submodule.span (D.ntw.O i) s' := by
  have e : s' = (toK YS j b).restrictScalars (D.ntw.O i) '' s := by
    ext x
    obtain ⟨g, rfl⟩ := (toK YS j b).surjective x
    exact ⟨fun hx => ⟨g, (h g).2 hx, rfl⟩, fun ⟨g', hg, e⟩ => (h g).1 ((toK YS j b).injective e ▸ hg)⟩
  rw [e, Submodule.span_image_linearEquiv]
  exact ⟨fun hf => ⟨f, hf, rfl⟩, fun ⟨g, hg, e⟩ => (toK YS j b).injective e ▸ hg⟩

def SupPin (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) : Prop :=
  ∀ f : D.nexp.Fm i ((j : ℕ) + 1) b, f ∈ D.nexp.Bsup i _ b ↔ toK YS j b f ∈ NX.Bsup S i ((j : ℕ) + 1) b

variable {YS fw T} in

theorem SideTie.mem_bsup_iff {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (Z : SideTie YS fw T i j b)
    (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    f ∈ D.nexp.Bsup i _ b ↔ toK YS j b f ∈ Submodule.span (D.ntw.O i) (urBall YS fw (T.iC i) b j 1) := by
  rw [T.Bsup_def]
  exact mem_span_toK (Z.ball_iff zero_le_one) f

variable {YS fw T} in

theorem SideTie.supPin_iff {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (Z : SideTie YS fw T i j b) :
    SupPin YS i j b ↔ SupDescent YS fw (T.iC i) b j := by
  refine ⟨fun h => ?_, fun h f => ?_⟩
  · ext x
    obtain ⟨f, rfl⟩ := (toK YS j b).surjective x
    exact (h f).symm.trans (Z.mem_bsup_iff f)
  · rw [Z.mem_bsup_iff, h]

variable {YS fw T} in

theorem SideTie.supDescent {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (Z : SideTie YS fw T i j b) (h : SupPin YS i j b) :
    SupDescent YS fw (T.iC i) b j := Z.supPin_iff.1 h

variable {YS fw T} in

theorem ThetaTie.kur_eq (Z : ThetaTie YS fw T)
    (h : ∀ x : S.Ks, ∃ y : S.Ks, algebraMap S.Ks D.what₂.LL y = star (algebraMap S.Ks D.what₂.LL x)) (i : D.ntw.Tw) (b : Bool) :
    T.MaximalUnramifiedExtension i = kurAt YS (T.iC i) b := by
  rw [Z.isUnramified₂, ← kurAt_eq YS _ h, inf_idem]
  cases b
  · exact kurAt_eq YS _ h
  · rfl

variable {YS fw T} in

theorem ThetaTie.root_mem_kur (Z : ThetaTie YS fw T) (i : D.ntw.Tw) {ζ : FractionRing (D.ntw.O i)} {n : ℕ} (hn : ¬ D.ntw.l i ∣ n)
    (h : ζ ^ n = 1) : ζ ∈ T.MaximalUnramifiedExtension i := by
  have h' : T.iC i ζ ^ n = 1 := by rw [← map_pow, h, map_one]
  rw [Z.isUnramified₂]
  exact ⟨root_mem_kurC _ hn h', root_mem_kurC _ hn h'⟩

section Record

def extLift {m : ℕ} {α : ℕ → Type} (f : ∀ n : Fin m, α ((n : ℕ) + 1)) (d : ∀ j, α j) : ∀ j, α j
  | 0 => d 0
  | n + 1 => if h : n < m then f ⟨n, h⟩ else d _

theorem extLift_succ {m : ℕ} {α : ℕ → Type} (f : ∀ n : Fin m, α ((n : ℕ) + 1)) (d : ∀ j, α j) (n : Fin m) :
    extLift f d ((n : ℕ) + 1) = f n := dif_pos n.2

theorem extLift_off {m : ℕ} {α : ℕ → Type} (f : ∀ n : Fin m, α ((n : ℕ) + 1)) (d : ∀ j, α j) {j : ℕ}
    (h : j ∉ Finset.Icc 1 m) : extLift f d j = d j := by
  cases j with
  | zero => rfl
  | succ n => exact dif_neg fun h' => h (Finset.mem_Icc.2 ⟨Nat.le_add_left _ _, h'⟩)

theorem lift_cases {m : ℕ} {p : ℕ → Prop} (h1 : ∀ n : Fin m, p ((n : ℕ) + 1)) (h2 : ∀ j, j ∉ Finset.Icc 1 m → p j) (j : ℕ) :
    p j := by
  by_cases h : j ∈ Finset.Icc 1 m
  · obtain ⟨a, b⟩ := Finset.mem_Icc.1 h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' a
    exact h1 ⟨n, b⟩
  · exact h2 j h

def atSide {P : Bool → Type} (b : Bool) (y : Σ b', P b') : Option (P b) := if h : y.1 = b then some (h ▸ y.2) else none

theorem atSide_same {P : Bool → Type} (b : Bool) (z : P b) : atSide b (⟨b, z⟩ : Σ b', P b') = some z := dif_pos rfl

theorem atSide_other {P : Bool → Type} {b : Bool} {y : Σ b', P b'} (h : y.1 ≠ b) : atSide b y = none := dif_neg h

theorem eq_of_atSide {P : Bool → Type} {b : Bool} {y : Σ b', P b'} {z : P b} (h : atSide b y = some z) : y = ⟨b, z⟩ := by
  obtain ⟨b', z'⟩ := y
  by_cases e : b' = b
  · subst e
    rw [atSide_same, Option.some.injEq] at h
    rw [h]
  · rw [atSide_other e] at h
    cases h

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i])

abbrev AllPts (j : ℕ) : Type := Σ b, Pts YS iC b j

def allEv (j : Fin D.R.m) (b : Bool) : D.nexp.Fm i ((j : ℕ) + 1) b →+ (AllPts YS iC ((j : ℕ) + 1) → ℂ_[D.ntw.l i]) where
  toFun f y := (atSide b y).elim 0 fun z => valAt YS fw j z.1 (toK YS j b f)
  map_zero' := funext fun y => by cases atSide b y <;> simp
  map_add' f g := funext fun y => by
    rw [Pi.add_apply]
    cases atSide b y <;> simp

open Classical in

def kerNum (j k : ℕ) (P : PlE D.host) : ℕ := if h : ∃ n, KerCard YS iC j k P n then h.choose else 0

open Classical in

def allMove (j k : ℕ) (P : PlE D.host) (c : Fin (kerNum YS iC j k P)) (y : AllPts YS iC j) : AllPts YS iC j :=
  if h : Nonempty (Fin (kerNum YS iC j k P) ≃ HkKer P.asIdeal (charAt P) k y.2.1) ∧
      ∀ C, ∃ z' : Pts YS iC y.1 j, IsHkQuot P.asIdeal (charAt P) k y.2.1 C z'.1 then ⟨y.1, (h.2 (h.1.some c)).choose⟩ else y

theorem allMove_fst (j k : ℕ) (P : PlE D.host) (c) (y : AllPts YS iC j) : (allMove YS iC j k P c y).1 = y.1 := by
  unfold allMove
  split_ifs <;> rfl

open Classical in

def hkUnit (j : Fin D.R.m) (b : Bool) (k : ℕ) (P : PlE D.host) : ℂ_[D.ntw.l i] :=
  if h : ∃ s : T0.Q.c.F, ‖embC YS iC b s‖ = 1 ∧ HeckeIs YS fw iC b j k P (embC YS iC b s) then embC YS iC b h.choose else 1

structure GeoLaws : Prop where
  detects : ∀ b j, Detects YS fw iC b j
  sup : ∀ b j, SupDescent YS fw iC b j
  pin : ∀ b j, SupPin YS i j b
  hecke : ∀ b j, HeckeGeo YS fw iC b j
  stable : ∀ b j, HeckeStable YS iC b j
  count : ∀ j, HeckeCount YS iC j
  off : ∀ j, j ∉ Finset.Icc 1 D.R.m → ∀ b, Subsingleton (D.nexp.Fm i j b)

variable {YS fw iC}

theorem GeoLaws.move (h : GeoLaws YS fw iC) {j : Fin D.R.m} {k P} (hk : HkIdx i k P) (b : Bool) (z : Pts YS iC b ((j : ℕ) + 1)) :
    ∃ (e : Fin (kerNum YS iC ((j : ℕ) + 1) k P) ≃ HkKer P.asIdeal (charAt P) k z.1)
      (q : HkKer P.asIdeal (charAt P) k z.1 → Pts YS iC b ((j : ℕ) + 1)),
      (∀ C, IsHkQuot P.asIdeal (charAt P) k z.1 C (q C).1) ∧ ∀ c, allMove YS iC _ k P c ⟨b, z⟩ = ⟨b, q (e c)⟩ := by
  have h1 : Nonempty (Fin (kerNum YS iC ((j : ℕ) + 1) k P) ≃ HkKer P.asIdeal (charAt P) k z.1) := by
    rw [kerNum, dif_pos (h.count j k P hk)]
    exact (h.count j k P hk).choose_spec b z
  have h2 := h.stable b j k P hk z
  exact ⟨h1.some, fun C => (h2 C).choose, fun C => (h2 C).choose_spec, fun c => dif_pos ⟨h1, h2⟩⟩

theorem GeoLaws.hkUnit_spec (h : GeoLaws YS fw iC) {j : Fin D.R.m} {k P} (hk : HkIdx i k P) (b : Bool) :
    ‖hkUnit YS fw iC j b k P‖ = 1 ∧ HeckeIs YS fw iC b j k P (hkUnit YS fw iC j b k P) := by
  rw [hkUnit, dif_pos (h.hecke b j k P hk)]
  exact (h.hecke b j k P hk).choose_spec

theorem exists_hkUnit_eq (j : Fin D.R.m) (b : Bool) (k : ℕ) (P : PlE D.host) :
    ∃ s : T0.Q.c.F, hkUnit YS fw iC j b k P = embC YS iC b s := by
  unfold hkUnit
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨1, (map_one _).symm⟩

theorem allEv_same {j : Fin D.R.m} {b : Bool} (f : D.nexp.Fm i ((j : ℕ) + 1) b) (z : Pts YS iC b ((j : ℕ) + 1)) :
    allEv YS fw iC j b f ⟨b, z⟩ = valAt YS fw j z.1 (toK YS j b f) :=
  (congrArg (fun o : Option (Pts YS iC b ((j : ℕ) + 1)) => o.elim 0 fun z => valAt YS fw j z.1 (toK YS j b f))
    (atSide_same (P := fun b => Pts YS iC b ((j : ℕ) + 1)) b z)).trans rfl

theorem allEv_other {j : Fin D.R.m} {b : Bool} (f : D.nexp.Fm i ((j : ℕ) + 1) b) {y : AllPts YS iC ((j : ℕ) + 1)} (h : y.1 ≠ b) :
    allEv YS fw iC j b f y = 0 :=
  congrArg (fun o : Option (Pts YS iC b ((j : ℕ) + 1)) => o.elim 0 fun z => valAt YS fw j z.1 (toK YS j b f)) (atSide_other h)

theorem allEv_ball {j : Fin D.R.m} {b : Bool} {B : ℝ} (hB : 0 ≤ B) (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (∀ y, ‖allEv YS fw iC j b f y‖ ≤ B) ↔ ∀ z : Pts YS iC b ((j : ℕ) + 1), ‖valAt YS fw j z.1 (toK YS j b f)‖ ≤ B := by
  refine ⟨fun h z => allEv_same (fw := fw) f z ▸ h ⟨b, z⟩, fun h ⟨b', z⟩ => ?_⟩
  by_cases hb : b' = b
  · subst hb
    rw [allEv_same]
    exact h z
  · rw [allEv_other f hb, norm_zero]
    exact hB

variable (YS fw) in

def evN (j : ℕ) : ∀ b, D.nexp.Fm i j b →+ (AllPts YS iC j → ℂ_[D.ntw.l i]) :=
  extLift (α := fun j => ∀ b, D.nexp.Fm i j b →+ (AllPts YS iC j → ℂ_[D.ntw.l i])) (allEv YS fw iC) (fun _ _ => 0) j

theorem evN_succ (j : Fin D.R.m) : evN YS fw (iC := iC) ((j : ℕ) + 1) = allEv YS fw iC j := extLift_succ _ _ j

variable (YS iC) in

def fmUrN (j : ℕ) : ∀ b, AddSubgroup (D.nexp.Fm i j b) :=
  extLift (α := fun j => ∀ b, AddSubgroup (D.nexp.Fm i j b))
    (fun j b => (ratForms S _ b (kurAt YS iC b)).comap (toK YS j b).toAddEquiv.toAddMonoidHom) (fun _ _ => ⊤) j

theorem mem_fmUrN (j : Fin D.R.m) (b : Bool) (f) :
    f ∈ fmUrN YS iC ((j : ℕ) + 1) b ↔ toK YS j b f ∈ ratForms S _ b (kurAt YS iC b) := by
  rw [fmUrN, extLift_succ]; rfl

variable (YS fw iC) in

def hkUnitN (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) : ℂ_[D.ntw.l i] :=
  extLift (α := fun _ => ℂ_[D.ntw.l i]) (fun j => hkUnit YS fw iC j b k P) (fun _ => 1) j

theorem hkUnitN_succ (j : Fin D.R.m) (b : Bool) (k : ℕ) (P : PlE D.host) :
    hkUnitN YS fw iC ((j : ℕ) + 1) b k P = hkUnit YS fw iC j b k P := extLift_succ (α := fun _ => ℂ_[D.ntw.l i]) _ _ j

namespace GeoLaws

variable (h : GeoLaws YS fw iC)
include h

theorem ev_smul (j : ℕ) (b : Bool) (a : FractionRing (D.ntw.O i)) (f : D.nexp.Fm i j b) (y : AllPts YS iC j) :
    evN YS fw j b (a • f) y = iC a * evN YS fw j b f y := by
  induction j using lift_cases (m := D.R.m) with
  | h1 j =>
    rw [evN_succ]
    obtain ⟨b', z⟩ := y
    by_cases hb : b' = b
    · subst hb
      rw [allEv_same, allEv_same, map_smul, valAt_smul]
    · rw [allEv_other _ hb, allEv_other _ hb, mul_zero]
  | h2 j hj =>
    have := h.off j hj b
    rw [Subsingleton.elim (a • f) 0, Subsingleton.elim f 0, map_zero, Pi.zero_apply, mul_zero]

theorem ev_inj (j : ℕ) (b : Bool) : Function.Injective (evN YS fw (iC := iC) j b) := by
  induction j using lift_cases (m := D.R.m) with
  | h1 j =>
    rw [evN_succ]
    refine (injective_iff_map_eq_zero _).2 fun f hf => (toK YS j b).injective ?_
    rw [map_zero]
    refine h.detects b j _ fun z => ?_
    rw [← allEv_same, hf, Pi.zero_apply]
  | h2 j hj =>
    have := h.off j hj b
    exact fun _ _ _ => Subsingleton.elim _ _

theorem hk_ev (j : ℕ) (b : Bool) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P) (f : D.nexp.Fm i j b) (y : AllPts YS iC j) :
    evN YS fw j b (D.nexp.hkF i j b k P f) y = ∑ c, hkUnitN YS fw iC j b k P * evN YS fw j b f (allMove YS iC j k P c y) := by
  induction j using lift_cases (m := D.R.m) with
  | h1 j =>
    rw [evN_succ, hkUnitN_succ, ← Finset.mul_sum]
    by_cases hb : y.1 = b
    · obtain ⟨b', z⟩ := y
      obtain rfl : b' = b := hb
      obtain ⟨e, q, hq, hm⟩ := h.move hk b' z
      rw [allEv_same, (h.hkUnit_spec hk b').2 z (fun C => (q C).1) hq f, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
      refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
      rw [hm, allEv_same]
    · rw [allEv_other _ hb, Finset.sum_eq_zero fun c _ => allEv_other _ ((allMove_fst YS iC _ k P c y).trans_ne hb), mul_zero]
  | h2 j hj =>
    have := h.off j hj b
    rw [Subsingleton.elim (D.nexp.hkF i j b k P f) 0, Subsingleton.elim f 0, map_zero]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem fmUr_smul (j : ℕ) (b : Bool) (a : FractionRing (D.ntw.O i)) (f : D.nexp.Fm i j b)
    (ha : a ∈ kurAt YS iC true ⊓ kurAt YS iC false) (hf : f ∈ fmUrN YS iC j b) : a • f ∈ fmUrN YS iC j b := by
  induction j using lift_cases (m := D.R.m) with
  | h1 j =>
    rw [mem_fmUrN] at hf ⊢
    rw [map_smul]
    exact smul_mem_ratForms (by cases b; exacts [ha.2, ha.1]) hf
  | h2 j hj =>
    have := h.off j hj b
    rw [Subsingleton.elim (a • f) f]
    exact hf

theorem fmUr_span (j : ℕ) (b : Bool) :
    Submodule.span (FractionRing (D.ntw.O i)) (fmUrN YS iC j b : Set (D.nexp.Fm i j b)) = ⊤ := by
  induction j using lift_cases (m := D.R.m) with
  | h1 j =>
    refine Submodule.map_injective_of_injective (f := (toK YS j b).toLinearMap) (toK YS j b).injective ?_
    rw [Submodule.map_top, LinearEquiv.range, Submodule.map_span, ← span_ratForms (S := S) (b := b) _ (kurAt YS iC b)]
    refine congrArg _ (Set.ext fun x => ?_)
    obtain ⟨g, rfl⟩ := (toK YS j b).surjective x
    exact ⟨fun ⟨g', hg, e⟩ => (show toK YS j b g' = toK YS j b g from e) ▸ (mem_fmUrN j b g').1 hg,
      fun hx => ⟨g, (mem_fmUrN j b g).2 hx, rfl⟩⟩
  | h2 j hj =>
    have := h.off j hj b
    exact Subsingleton.elim _ _

theorem bsup_def (j : ℕ) (b : Bool) : D.nexp.Bsup i j b =
    Submodule.span (D.ntw.O i) {f | f ∈ fmUrN YS iC j b ∧ ∀ y, ‖evN YS fw (iC := iC) j b f y‖ ≤ 1} := by
  induction j using lift_cases (m := D.R.m) with
  | h1 j =>
    ext f
    rw [h.pin b j f, h.sup b j, evN_succ]
    exact (mem_span_toK (fun f => and_congr (mem_fmUrN j b f) (allEv_ball zero_le_one f)) f).symm
  | h2 j hj =>
    have := h.off j hj b
    exact Subsingleton.elim _ _

end GeoLaws

variable {T}

def geoNTh (h : ∀ i, GeoLaws YS fw (T.iC i)) : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp :=
  { T with
    Pt := fun i j => AllPts YS (T.iC i) j
    ev := fun _ j => evN YS fw j
    ev_smul := fun i => (h i).ev_smul
    ev_inj := fun i => (h i).ev_inj
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => (add_zero _).symm
    thV_smul := fun _ _ _ _ _ _ => (mul_zero _).symm
    thV_addP := fun _ _ _ _ _ _ => (add_zero _).symm
    thV_smulP := fun _ _ _ _ _ _ => (mul_zero _).symm
    recDet := fun _ _ _ => 1
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun i j k P => Fin (kerNum YS (T.iC i) j k P)
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun i j k P => allMove YS (T.iC i) j k P
    hkU := fun i j b k P _ _ => hkUnitN YS fw (T.iC i) j b k P
    hk_ev := fun i j b _ _ h1 h2 h3 h4 => (h i).hk_ev j b ⟨h1, h2, h3, h4⟩
    MaximalUnramifiedExtension := fun i => kurAt YS (T.iC i) true ⊓ kurAt YS (T.iC i) false
    FmUr := fun i => fmUrN YS (T.iC i)
    FmUr_smul := fun i => (h i).fmUr_smul
    FmUr_span := fun i => (h i).fmUr_span
    Bsup_def := fun i => (h i).bsup_def }

theorem GeoLaws.hk_tie (h : GeoLaws YS fw iC) (j : Fin D.R.m) (b : Bool) {k P} (hk : HkIdx i k P) :
    ∃ s : T0.Q.c.F, ‖embC YS iC b s‖ = 1 ∧ ∀ (y : AllPts YS iC ((j : ℕ) + 1)) (z : Pts YS iC b ((j : ℕ) + 1)), atSide b y = some z →
      ∃ e : Fin (kerNum YS iC ((j : ℕ) + 1) k P) ≃ HkKer P.asIdeal (charAt P) k z.1, ∀ c,
        ∃ (z' : Pts YS iC b ((j : ℕ) + 1)) (t : Ix (T0.Q.Dw ((j : ℕ) + 1)) → (PAt (embC YS iC b))ˣ) (w : FrC YS iC b ((j : ℕ) + 1)),
          atSide b (allMove YS iC _ k P c y) = some z' ∧ IsHkQuot P.asIdeal (charAt P) k z.1 (e c) w ∧ IsUnitDiag t ∧
            FrBor t z'.1 w ∧ hkUnitN YS fw iC ((j : ℕ) + 1) b k P = embC YS iC b s * wtChar (wtA (κ j)) (κ j).n t := by
  obtain ⟨s, hs⟩ := exists_hkUnit_eq (YS := YS) (fw := fw) (iC := iC) j b k P
  refine ⟨s, hs ▸ (h.hkUnit_spec (j := j) hk b).1, fun y z hy => ?_⟩
  obtain rfl := eq_of_atSide hy
  obtain ⟨e, q, hq, hm⟩ := h.move hk b z
  refine ⟨e, fun c => ⟨q (e c), 1, (q (e c)).1, by rw [hm, atSide_same], hq _, isUnitDiag_one, frBor_one _, ?_⟩⟩
  rw [hkUnitN_succ, hs]
  simp only [wtChar, wchar, Pi.one_apply, Units.val_one, one_pow, Finset.prod_const_one, map_one, mul_one]

theorem evN_eq (j : Fin D.R.m) (b : Bool) (f : D.nexp.Fm i ((j : ℕ) + 1) b) (y : AllPts YS iC ((j : ℕ) + 1)) :
    evN YS fw ((j : ℕ) + 1) b f y = (atSide b y).elim 0 fun z => valAt YS fw j z.1 (toK YS j b f) := by
  rw [evN_succ]
  rfl

def geoTie (h : ∀ i, GeoLaws YS fw (T.iC i)) : ThetaTie YS fw (geoNTh h) where
  side i j b :=
    { pt := atSide (P := fun b => Pts YS (T.iC i) b ((j : ℕ) + 1)) b
      cover := fun z => ⟨⟨b, z⟩, z, 1, atSide_same (P := fun b => Pts YS (T.iC i) b ((j : ℕ) + 1)) b z, isUnitDiag_one, frBor_one _⟩
      ev_eq := evN_eq j b
      fmUr := mem_fmUrN j b
      hk := fun _ _ hk => (h i).hk_tie j b hk
      hk_none := fun k P hk _ _ _ => (congrArg norm (hkUnitN_succ j b k P)).trans ((h i).hkUnit_spec hk b).1 }
  isUnramified₂ _ := rfl

theorem nonempty_pts_of_reading {b : Bool} {j : ℕ} {Tc : CDVR} {io : T0.Q.c.F →+* Tc.Fr} {k : Tc.Fr →+* ℂ_[D.ntw.l i]}
    (hk : IsReading (embC YS iC b) Tc io k) (y₀ : IntFr (T0.Q.Xo j) T0.Q.c Tc io) (hy : y₀.IsAlg) : Nonempty (Pts YS iC b j) :=
  ⟨(PtC.exists_of_reading hk y₀ hy).choose⟩

end Record

example {i : D.ntw.Tw} (b : Bool) : ((D.ntw.l i : ℕ) : 𝓞 T0.Q.c.F) ∈ (placeC YS (T.iC i) b).asIdeal := natCast_mem_placeAt _

example (i : D.ntw.Tw) (b : Bool) (a : S.Ks) : sideK YS i b (eKs YS a) = NX.readLL0 S i b (S.kKs a) := sideK_eKs YS i b a

example {i : D.ntw.Tw} (b : Bool) (s : T0.Q.c.F) : embC YS (T.iC i) b s ∈ kurC (embC YS (T.iC i) b) := mem_kurC _ s

example (n : ℕ) : atSide (P := fun _ => ℕ) true ⟨false, n⟩ = none := atSide_other (by simp)

end GlobalTheory.GeoTie

end
