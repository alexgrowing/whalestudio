import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF Vc Wc)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {R : Type} [CommRing R] [IsDomain R]

def Via (R : Type) [CommRing R] (_e : FractionRing R →+* ℂ) (A : Type) : Type := A

variable {e : FractionRing R →+* ℂ} {A : Type} [AddCommGroup A] [Module ℂ A]

instance : AddCommGroup (Via R e A) := inferInstanceAs (AddCommGroup A)
instance : Module (FractionRing R) (Via R e A) := Module.compHom A e
instance : Module R (Via R e A) := Module.compHom A (e.comp (algebraMap R (FractionRing R)))
instance : IsScalarTower R (FractionRing R) (Via R e A) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def Via.out (e : FractionRing R →+* ℂ) (A : Type) [AddCommGroup A] [Module ℂ A] : Via R e A →ₛₗ[e] A where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Via.lat (L : Submodule (e.comp (algebraMap R (FractionRing R))).range A) : Submodule R (Via R e A) where
  carrier := {x | Via.out e A x ∈ L}
  add_mem' := L.add_mem
  zero_mem' := L.zero_mem
  smul_mem' c _ h := L.smul_mem ⟨_, c, rfl⟩ h

theorem Via.lat_fg {L : Submodule (e.comp (algebraMap R (FractionRing R))).range A} (h : L.FG) : (Via.lat L).FG := by
  obtain ⟨S, rfl⟩ := h
  refine ⟨S, le_antisymm (Submodule.span_le.2 fun x hx => Submodule.subset_span (M := A) hx) fun x hx => ?_⟩
  have key : ∀ y : A, y ∈ Submodule.span (e.comp (algebraMap R (FractionRing R))).range (S : Set A) →
      (y : Via R e A) ∈ Submodule.span R (M := Via R e A) (S : Set A) := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem _ h => exact Submodule.subset_span h
    | zero => exact zero_mem _
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | smul c _ _ h1 =>
      obtain ⟨_, c, rfl⟩ := c
      exact Submodule.smul_mem _ c h1
  exact key x hx

variable {V : Type} [AddCommGroup V] [Module (FractionRing R) V] [Module R V] [IsScalarTower R (FractionRing R) V]

def inSpan (L : Submodule R V) : Submodule R (Submodule.span (FractionRing R) (L : Set V)) :=
  L.comap ((Submodule.span (FractionRing R) (L : Set V)).subtype.restrictScalars R)

theorem inSpan_fg {L : Submodule R V} (h : L.FG) : (inSpan L).FG := by
  refine Submodule.fg_of_fg_map_injective ((Submodule.span (FractionRing R) (L : Set V)).subtype.restrictScalars R)
    Subtype.val_injective ?_
  rwa [inSpan, Submodule.map_comap_eq_self fun x hx => ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩]

theorem span_inSpan (L : Submodule R V) : Submodule.span (FractionRing R)
    (inSpan L : Set (Submodule.span (FractionRing R) (L : Set V))) = ⊤ := Submodule.span_span_coe_preimage

theorem finiteDimensional_span {L : Submodule R V} (h : L.FG) :
    FiniteDimensional (FractionRing R) (Submodule.span (FractionRing R) (L : Set V)) := by
  obtain ⟨S, rfl⟩ := h
  rw [Submodule.span_span_of_tower]
  exact FiniteDimensional.span_of_finite _ S.finite_toSet

theorem exists_lift {M : Type} [AddCommGroup M] [Module R M] (g : V →ₛₗ[e] A)
    (r : M →ₛₗ[e.comp (algebraMap R (FractionRing R))] A) (hr : Function.Injective r)
    (hdiv : ∀ a : R, a ≠ 0 → ∀ m : M, ∃ m', a • m' = m) :
    ∃ φ : V →ₗ[R] M, ∀ v, g v ∈ Set.range r → r (φ v) = g v := by
  let U : Submodule (FractionRing R) V :=
    { carrier := {v | g v ∈ Set.range r}
      zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
      add_mem' := by
        rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, by rw [map_add, map_add, hx, hy]⟩
      smul_mem' := by
        rintro c v ⟨x, hx⟩
        obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) c
        have hd' := nonZeroDivisors.ne_zero hd
        obtain ⟨y, rfl⟩ := hdiv d hd' x
        refine ⟨a • y, ?_⟩
        rw [map_smulₛₗ, map_smulₛₗ, ← hx, map_smulₛₗ, smul_smul, RingHom.comp_apply, RingHom.comp_apply, ← map_mul,
          div_mul_cancel₀ _ (by simpa using hd')] }
  obtain ⟨p, hp⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  choose s hs using fun u : U => u.2
  let ψ : U →ₗ[R] M :=
    { toFun := s
      map_add' := fun u u' => hr (by rw [map_add, hs, hs, hs, Submodule.coe_add, map_add])
      map_smul' := fun c u => hr (by
        rw [RingHom.id_apply, map_smulₛₗ, hs, hs, Submodule.coe_smul_of_tower, ← algebraMap_smul (FractionRing R) c,
          map_smulₛₗ]; rfl) }
  refine ⟨ψ ∘ₗ p.restrictScalars R, fun v hv => ?_⟩
  have : p v = ⟨v, hv⟩ := LinearMap.congr_fun hp ⟨v, hv⟩
  change r (s (p v)) = _
  rw [this, hs]

end Lin

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem divisible_baseChange (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (n : ℕ) (b : Bool) (k : ℕ) (a : X.Ok i k)
    (ha : a ≠ 0) (m : X.Ok i k ⊗[X.O i] Y.Fm i n b) : ∃ m', a • m' = m := by
  haveI := X.Ok_fin i k
  obtain ⟨d, hd, c, hc⟩ := (Algebra.IsIntegral.isIntegral (R := X.O i) a).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha)
  have key : ∀ m : X.Ok i k ⊗[X.O i] Y.Fm i n b, ∃ m', d • m' = m := fun m => by
    induction m using TensorProduct.induction_on with
    | zero => exact ⟨0, smul_zero _⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, smul_add _ _ _⟩
    | tmul z f =>
      refine ⟨z ⊗ₜ ((algebraMap (X.O i) (FractionRing (X.O i)) d)⁻¹ • f), ?_⟩
      rw [← TensorProduct.tmul_smul, ← algebraMap_smul (FractionRing (X.O i)) d, smul_inv_smul₀ (by simpa using hd)]
  obtain ⟨m', rfl⟩ := key m
  exact ⟨c • m', by rw [smul_smul, ← hc, algebraMap_smul]⟩

theorem finite_dvd_normProd (s : Finset (Pl D.host.E)) :
    {v : Pl D.host.E | ((normProd s : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((normProd s : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact Finset.prod_ne_zero_iff.2 fun v _ h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

variable {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (rd : Rds Y ρ)

def Setup.LatFG (ρ : Setup X) : Prop := ∀ i j b k Q ψ, TwOK i k Q ψ → (ρ.mt i j b k Q ψ).FG

structure Setup.LevelOf (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop where
  U_eq : ∀ i j b g, ρ.eG i j b g ∈ (ρ.B i j b).G.P.H ↔ g ∈ Y.U
  psiU_eq : ∀ i j b (u : Y.U) hu,
    (((ρ.B i j b).G.P.chi ⟨ρ.eG i j b u, hu⟩ : ℂˣ) : ℂ) = ρ.e i b (Y.psiU i b u : (FractionRing (X.O i))ˣ)

namespace Model

structure RatDatum (i : X.Tw) (j : Fin D.R.m) (b : Bool) where
  s : Finset (Pl D.host.E)
  h : GA D (Vc D j)
  P : PolF D (Wc D j).rank (Vc D j).rank
  isDatum : ρ.IsDatum i j b s h P
  rat : ρ.theta i j b h P ∈ Set.range (rd i j b)

def Dat (i : X.Tw) : ℕ → Bool → Type
  | 0, _ => PEmpty
  | n + 1, b => (h : n < D.R.m) ×' RatDatum rd i ⟨n, h⟩ b

def th (i : X.Tw) : ∀ n b, Dat rd i n b → Y.Fm i n b
  | 0, _ => fun d => d.elim
  | _ + 1, _ => fun d => d.2.rat.choose

def lev (i : X.Tw) : ∀ n b, Dat rd i n b → Finset (Pl D.host.E)
  | 0, _ => fun d => d.elim
  | _ + 1, _ => fun d => (finite_dvd_normProd d.2.s).toFinset

def thPsi (i : X.Tw) : ∀ n b k (_ : Finset (Pl D.host.E)) (_ : G D.host.E N.Om →* (X.Ok i k)ˣ),
    Dat rd i n b → Set (X.Ok i k ⊗[X.O i] Y.Fm i n b)
  | 0, _, _, _, _ => fun d => d.elim
  | n + 1, b, k, Q, ψ => fun d => rdK (rd i ⟨n, d.1⟩ b) hρ k ⁻¹' ρ.gens i ⟨n, d.1⟩ b k Q ψ d.2.h d.2.P

open Classical in
def thU (i : X.Tw) : ∀ n b (Q : Finset (Pl D.host.E)) (M : ℕ), Dat rd i n b →
    Y.Fm i n b ⊗[X.O i] AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)
  | 0, _, _, _ => fun d => d.elim
  | n + 1, b, Q, M => fun d =>
    if h : InRange X i Q ∧ ∀ a, ρ.xi i ⟨n, d.1⟩ b Y Q M d.2.h d.2.P a ∈ Set.range (rd i ⟨n, d.1⟩ b) then
      grpSum Y (ρ.ch i) Q M fun a => (h.2 a).choose
    else 0

abbrev Amb (ρ : Setup X) (i : X.Tw) (n : ℕ) (b : Bool) (k : ℕ) : Type :=
  Via (X.Ok i k) (ρ.ek i b k) (Bridge.Gf (D.sp.V n) → PolF D (D.sp.W n).rank (D.sp.V n).rank)

open Classical in

def lat (ρ : Setup X) (i : X.Tw) : ∀ n b k (_ : Finset (Pl D.host.E)) (_ : G D.host.E N.Om →* (X.Ok i k)ˣ),
    Submodule (X.Ok i k) (Amb ρ i n b k)
  | 0, _, _, _, _ => ⊥
  | n + 1, b, k, Q, ψ => if h : n < D.R.m ∧ TwOK i k Q ψ then Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ) else ⊥

theorem lat_fg (hL : ρ.LatFG) (i : X.Tw) : ∀ n b k Q ψ, (lat ρ i n b k Q ψ).FG
  | 0, _, _, _, _ => Submodule.fg_bot
  | n + 1, b, k, Q, ψ => by
    rw [lat]
    split_ifs with h
    · exact Via.lat_fg (hL i ⟨n, h.1⟩ b k Q ψ h.2)
    · exact Submodule.fg_bot

abbrev MtV (ρ : Setup X) (i : X.Tw) (n : ℕ) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Type :=
  Submodule.span (FractionRing (X.Ok i k)) (lat ρ i n b k Q ψ : Set (Amb ρ i n b k))

def rdV (ρ : Setup X) (i : X.Tw) (n : ℕ) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) :
    MtV ρ i n b k Q ψ →ₛₗ[ρ.ek i b k] (Bridge.Gf (D.sp.V n) → PolF D (D.sp.W n).rank (D.sp.V n).rank) :=
  (Via.out _ _).comp (Submodule.subtype _)

variable (hF : ∀ i j b, Faithful (rd i j b))

include hF in
theorem exists_thP (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) :
    ∃ φ : MtV ρ i ((j : ℕ) + 1) b k Q ψ →ₗ[X.Ok i k] X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b,
      ∀ f, ρ.sum i j b k Q ψ (rdV ρ i _ b k Q ψ f) ∈ Set.range (rdK (rd i j b) hρ k) →
        rdK (rd i j b) hρ k (φ f) = ρ.sum i j b k Q ψ (rdV ρ i _ b k Q ψ f) :=
  exists_lift ((ρ.sum i j b k Q ψ).comp (rdV ρ i _ b k Q ψ)) (rdK (rd i j b) hρ k) ((hF i j b).injective_rdK hρ k)
    (divisible_baseChange Y i _ b k)

def thP (i : X.Tw) : ∀ n b k Q ψ, MtV ρ i n b k Q ψ →ₗ[X.Ok i k] X.Ok i k ⊗[X.O i] Y.Fm i n b
  | 0, _, _, _, _ => 0
  | n + 1, b, k, Q, ψ => if h : n < D.R.m then (exists_thP hρ rd hF i ⟨n, h⟩ b k Q ψ).choose else 0

include hF in
theorem thPsi_one (i : X.Tw) : ∀ n b k (d : Dat rd i n b),
    thPsi hρ rd i n b k ∅ 1 d = {(1 : X.Ok i k) ⊗ₜ[X.O i] th rd i n b d}
  | 0, _, _, d => d.elim
  | n + 1, b, k, d => by
    ext x
    rw [thPsi, Set.mem_preimage, Setup.gens_one, Set.mem_singleton_iff, Set.mem_singleton_iff,
      ← ((hF i ⟨n, d.1⟩ b).injective_rdK hρ k).eq_iff, rdK_tmul, map_one, one_smul, ← d.2.rat.choose_spec]
    rfl

end Model

variable (hF : ∀ i j b, Faithful (rd i j b)) (hL : ρ.LatFG)

def withSeries : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    Dat := Model.Dat rd
    th := Model.th rd
    lev := Model.lev rd
    thPsi := Model.thPsi hρ rd
    thPsi_one := Model.thPsi_one hρ rd hF
    thU := Model.thU rd
    MtV := Model.MtV ρ
    acgMt := fun _ _ _ _ _ _ => inferInstance
    modMtK := fun _ _ _ _ _ _ => inferInstance
    modMtO := fun _ _ _ _ _ _ => inferInstance
    towMt := fun _ _ _ _ _ _ => inferInstance
    fdMt := fun i n b k Q ψ => finiteDimensional_span (Model.lat_fg hL i n b k Q ψ)
    MtLat := fun i n b k Q ψ => inSpan (Model.lat ρ i n b k Q ψ)
    MtLat_fg := fun i n b k Q ψ => inSpan_fg (Model.lat_fg hL i n b k Q ψ)
    MtLat_span := fun _ _ _ _ _ _ => span_inSpan _
    thP := Model.thP hρ rd hF }

def tieWithSeries (hU : ρ.LevelOf Y) : Comparison₂ hρ (Y := withSeries hρ rd hF hL) rd := fun i j b =>
  { supp := fun d => d.2.s
    cls := fun d => d.2.h
    coef := fun d => d.2.P
    rdV := Model.rdV ρ i _ b
    U_eq := hU.U_eq i j b
    psiU_eq := hU.psiU_eq i j b
    dat := fun d => d.2.isDatum
    dat_onto := fun s h P h1 h2 => ⟨⟨j.2, s, h, P, h1, h2⟩, rfl, rfl, rfl⟩
    lev_iff := fun _ _ => Set.Finite.mem_toFinset _
    th_eq := fun d => d.2.rat.choose_spec
    thPsi_iff := fun _ _ _ _ _ _ => Iff.rfl
    thU_eq := fun Q M d hQ x hx => by
      have h : InRange X i Q ∧ ∀ a, ρ.xi i j b Y Q M d.2.h d.2.P a ∈ Set.range (rd i j b) := ⟨hQ, fun a => ⟨x a, hx a⟩⟩
      refine (dif_pos h).trans (congrArg (grpSum Y (ρ.ch i) Q M) (funext fun a => (hF i j b).injective ?_))
      exact (h.2 a).choose_spec.trans (hx a).symm
    thU_off := fun _ _ _ h => dif_neg h
    rdV_inj := fun _ _ _ _ => Subtype.val_injective
    mtLat_iff := fun k Q ψ h F => by
      have e : Model.lat ρ i ((j : ℕ) + 1) b k Q ψ = Via.lat (ρ.mt i j b k Q ψ) := dif_pos ⟨j.2, h⟩
      refine ⟨fun hF => ?_, fun ⟨f, hf, e'⟩ => ?_⟩
      · have h1 : F ∈ Model.lat ρ i ((j : ℕ) + 1) b k Q ψ := e ▸ hF
        exact ⟨⟨F, Submodule.subset_span h1⟩, h1, rfl⟩
      · have h1 : f.1 ∈ Model.lat ρ i ((j : ℕ) + 1) b k Q ψ := hf
        exact e' ▸ e.le h1
    thP_eq := fun k Q ψ _ f hf => by
      have e : Model.thP hρ rd hF i ((j : ℕ) + 1) b k Q ψ = (Model.exists_thP hρ rd hF i j b k Q ψ).choose := dif_pos j.2
      exact (congrArg (fun φ => rdK (rd i j b) hρ k (φ f)) e).trans ((Model.exists_thP hρ rd hF i j b k Q ψ).choose_spec f hf) }

end GlobalTheory.SeriesTie

end
