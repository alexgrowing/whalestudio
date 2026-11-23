import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF Vc Wc)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.MainNotions.NAdm (TWSet AdmQ)
open GlobalTheory.UnivChar (IsUnivChar withUnivChar)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_end_reads {K M A ι : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module ℂ A] {e : K →+* ℂ}
    (r : M →ₛₗ[e] A) (hr : Function.Injective r) (S : ι → A →ₗ[ℂ] A) :
    ∃ T : Module.End K M, ∀ f, (∃ g, ∀ a, r g = S a (r f)) → ∀ a, r (T f) = S a (r f) := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨a₀⟩⟩
  · exact ⟨0, fun _ _ a => isEmptyElim a⟩
  let U : Submodule K M :=
    { carrier := {f | ∃ g, ∀ a, r g = S a (r f)}
      zero_mem' := ⟨0, fun a => by rw [map_zero, map_zero]⟩
      add_mem' := by
        rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, fun a => by rw [map_add, map_add, map_add, hx a, hy a]⟩
      smul_mem' := by
        rintro c v ⟨x, hx⟩
        exact ⟨c • x, fun a => by rw [map_smulₛₗ, map_smulₛₗ, map_smul, hx a]⟩ }
  obtain ⟨p, hp⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  choose s hs using fun u : U => u.2
  let ψ : U →ₗ[K] M :=
    { toFun := s
      map_add' := fun u u' => hr (by rw [map_add, hs _ a₀, hs _ a₀, hs _ a₀, Submodule.coe_add, map_add, map_add])
      map_smul' := fun c u => hr (by
        rw [RingHom.id_apply, map_smulₛₗ, hs _ a₀, hs _ a₀, Submodule.coe_smul, map_smulₛₗ, map_smul]) }
  refine ⟨ψ ∘ₗ p, fun v hv a => ?_⟩
  have : p v = ⟨v, hv⟩ := LinearMap.congr_fun hp ⟨v, hv⟩
  change r (s (p v)) = _
  rw [this, hs _ a]

namespace Setup

variable (ρ : Setup X) (i : X.Tw) (j : Fin D.R.m) (b : Bool)

structure IsHeckeDatum (k : ℕ) (P : Pl D.host.E) (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) : Prop where
  elt : Links.IsHeckeAt (Wc D j) P k α
  reps : Bridge.IsDC (ρ.levK i j b) α R
  det : IsDetAt (idemAt P) (Wc D j) α z

def hecke (k : ℕ) (P : Pl D.host.E) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) :
    (GA D (Wc D j) → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
  ((((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹) •
    ∑ γ ∈ R, LinearMap.funLeft ℂ ℂ fun x => x * γ

theorem hecke_apply (k : ℕ) (P : Pl D.host.E) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) (F : GA D (Wc D j) → ℂ)
    (x : GA D (Wc D j)) : ρ.hecke i j b k P R z F x = (((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ *
      (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹ * ∑ γ ∈ R, F (x * γ) := by
  simp only [hecke, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.funLeft_apply]

end Setup

section Hecke

variable {ρ : Setup X} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b)

def HeckeAt (k : ℕ) (P : Pl D.host.E) (f g : Y.Fm i ((j : ℕ) + 1) b) : Prop :=
  ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → rd g = ρ.hecke i j b k P R z (rd f)

def HeckeTie : Prop :=
  ∀ k P, HkIdx i k P → ∀ f, (∃ g, HeckeAt rd k P f g) → HeckeAt rd k P f (Y.hkF i _ b k P f)

def RatHecke : Prop := ∀ k P, HkIdx i k P → ∀ f, ∃ g, HeckeAt rd k P f g

variable {rd}

theorem heckeRead_iff : HeckeRead rd ↔ ∀ k P, HkIdx i k P → ∀ f, HeckeAt rd k P f (Y.hkF i _ b k P f) :=
  ⟨fun h k P hk f α R z d => funext fun x => (h k P hk α R z d.1 d.2 d.3 f x).trans (ρ.hecke_apply ..).symm,
    fun h k P hk α R z h1 h2 h3 f x => (congrFun (h k P hk f α R z ⟨h1, h2, h3⟩) x).trans (ρ.hecke_apply ..)⟩

theorem heckeRead_iff_tie : HeckeRead rd ↔ HeckeTie rd ∧ RatHecke rd := by
  rw [heckeRead_iff]
  exact ⟨fun h => ⟨fun k P hk f _ => h k P hk f, fun k P hk f => ⟨_, h k P hk f⟩⟩,
    fun h k P hk f => h.1 k P hk f (h.2 k P hk f)⟩

theorem HeckeTie.heckeRead (h : HeckeTie rd) (hR : RatHecke rd) : HeckeRead rd := heckeRead_iff_tie.2 ⟨h, hR⟩

theorem HeckeTie.eq (h : HeckeTie rd) (hinj : Function.Injective rd) {k P} (hk : HkIdx i k P) {α R z}
    (d : ρ.IsHeckeDatum i j b k P α R z) {f g : Y.Fm i ((j : ℕ) + 1) b} (hg : HeckeAt rd k P f g) : Y.hkF i _ b k P f = g :=
  hinj ((h k P hk f ⟨g, hg⟩ α R z d).trans (hg α R z d).symm)

theorem ratHecke_of_range
    (h1 : ∀ k P, HkIdx i k P → ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → ∀ f, ρ.hecke i j b k P R z (rd f) ∈ Set.range rd)
    (h2 : ∀ k P, HkIdx i k P → ∀ α R z α' R' z', ρ.IsHeckeDatum i j b k P α R z → ρ.IsHeckeDatum i j b k P α' R' z' →
      ∀ f, ρ.hecke i j b k P R z (rd f) = ρ.hecke i j b k P R' z' (rd f)) : RatHecke rd := fun k P hk f => by
  by_cases h : ∃ α R z, ρ.IsHeckeDatum i j b k P α R z
  · obtain ⟨α, R, z, d⟩ := h
    obtain ⟨g, hg⟩ := h1 k P hk α R z d f
    exact ⟨g, fun α' R' z' d' => hg.trans (h2 k P hk α R z α' R' z' d d' f)⟩
  · exact ⟨0, fun α R z d => absurd ⟨α, R, z, d⟩ h⟩

theorem exists_hecke (hinj : Function.Injective rd) (k : ℕ) (P : Pl D.host.E) :
    ∃ T : Module.End (FractionRing (X.O i)) (Y.Fm i ((j : ℕ) + 1) b), ∀ f, (∃ g, HeckeAt rd k P f g) → HeckeAt rd k P f (T f) := by
  obtain ⟨T, hT⟩ := exists_end_reads rd hinj
    fun a : {a : GA D (Wc D j) × Finset (GA D (Wc D j)) × (AE D)ˣ // ρ.IsHeckeDatum i j b k P a.1 a.2.1 a.2.2} =>
      ρ.hecke i j b k P a.1.2.1 a.1.2.2
  exact ⟨T, fun f ⟨g, hg⟩ α R z d => hT f ⟨g, fun a => hg _ _ _ a.2⟩ ⟨(α, R, z), d⟩⟩

theorem CellTie.injective_rdK {hρ : ρ.Good} (T : CellTie hρ Y rd) (k : ℕ) : Function.Injective (rdK rd hρ k) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨d⟩ := T.nonempty_dat
  have h := (T.thPsi_iff k ∅ 1 (twOK_one i k) d ((1 : X.Ok i k) ⊗ₜ[X.O i] Y.th i _ b d + x)).2 (by
    rw [map_add, hx, add_zero, rdK_tmul, map_one, one_smul, T.th_eq, Setup.gens_one]
    rfl)
  rw [Y.thPsi_one] at h
  exact add_eq_left.1 h

end Hecke

section Univ

theorem admQ_admissibleConjugatePairPlaces (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) : AdmQ X i (admissibleConjugatePairPlaces X i Q M) M := by
  classical
  refine ⟨fun P hP => ?_, fun P hP => ?_⟩
  · obtain ⟨-, P', -, -, h⟩ := mem_admissibleConjugatePairPlaces_iff.1 hP
    exact h.1 P (by simp)
  · obtain ⟨-, P', -, hc, h⟩ := mem_admissibleConjugatePairPlaces_iff.1 hP
    exact ⟨⟨P', conj_mem_admissibleConjugatePairPlaces hP hc, hc⟩, (h.2 P (by simp)).2⟩

theorem InRange.twSet {i : X.Tw} {Q : Finset (Pl D.host.E)} (h : InRange X i Q) : TWSet X i Q :=
  fun v hv => ⟨h.1 v hv, fun hl => Finset.disjoint_left.1 h.2.2 hv (X.twistExcludedPlaces_contains_residueChar i hl)⟩

theorem twSet_of_twOK {i : X.Tw} {k : ℕ} {Q : Finset (Pl D.host.E)} {ψ} (h : TwOK (X := X) i k Q ψ) : TWSet X i Q :=
  fun v hv => ⟨h.1 v hv, fun hl => Finset.disjoint_left.1 h.2.1 hv (X.twistExcludedPlaces_contains_residueChar i hl)⟩

variable {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hY : IsUnivChar Y) {i : X.Tw} {Q : Finset (Pl D.host.E)} {M : ℕ}
include hY

theorem delU_off (hQ : TWSet X i Q) (σ : G D.host.E N.Om) (v : ↥Q) (hv : v.1 ∉ admissibleConjugatePairPlaces X i Q M) :
    Multiplicative.toAdd (Y.delU i Q M σ) v = 0 := by
  classical
  rw [hY, GalChar.delU_apply, GalChar.delCoord]
  split_ifs with h
  · rw [GalChar.delOf, dif_neg]
    · rfl
    rintro ⟨d, h1, h2, h3, h4, h5⟩
    obtain ⟨P', hc⟩ := GlobalTheory.TwistDet.exists_isConjPl v.1
    have hP' : P' ∈ Q := h (Or.inr hc)
    have key : ∀ P, GalChar.pair D.host P = GalChar.pair D.host v.1 →
        ∃ χ : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)), IsOpen (χ.ker : Set (G D.host.E N.Om)) ∧ AntiHom X.cc χ ∧
        (∀ w ∈ placesOver D.host.E (X.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
          ∀ σ ∈ Dec (F := D.host.E) A, χ σ = 1) ∧
        (∀ w : PlE D.host, w ≠ P → ¬ IsConjPl D.host P w → ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
          ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1) ∧
        ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
          Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (χ σ) := fun P e =>
      ⟨d, h1, h2, h3, fun w a c => h4 w (e ▸ fun t => t.elim a c), fun A hA x => by
        obtain ⟨σ, hσ, hx⟩ := h5 P (e ▸ Or.inl rfl) A hA (Multiplicative.ofAdd x)
        exact ⟨⟨σ, hσ⟩, congrArg Multiplicative.toAdd hx⟩⟩
    refine hv (mem_admissibleConjugatePairPlaces_iff.2 ⟨v.2, P', hP', hc, fun w hw => ?_, fun w hw => ?_⟩)
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hQ _ v.2
      · exact Finset.mem_singleton.1 hw ▸ hQ _ hP'
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact ⟨⟨P', by simp, hc⟩, key _ rfl⟩
      · obtain rfl := Finset.mem_singleton.1 hw
        exact ⟨⟨v.1, by simp, GalChar.isConjPl_symm hc⟩, key _ (GalChar.pair_eq hc)⟩
  · rfl

theorem delU_on (σ : G D.host.E N.Om) (v : ↥Q) (hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M) :
    Multiplicative.toAdd (Y.delU i Q M σ) v =
      Multiplicative.toAdd (GalChar.delOf D.host X.cc (X.l i) M (GalChar.pair D.host v.1) σ) := by
  rw [hY, GalChar.delU_apply, GalChar.delCoord, if_pos]
  rintro w (rfl | hw)
  · exact v.2
  · exact admissibleConjugatePairPlaces_subset i Q M (conj_mem_admissibleConjugatePairPlaces hv hw)

theorem delU_eq_coord (hQ : TWSet X i Q) (σ : G D.host.E N.Om) (v : ↥Q) :
    Multiplicative.toAdd (Y.delU i Q M σ) v = Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M v.1 σ) := by
  by_cases hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M
  · rw [delU_on hY σ v hv, coord_apply _ _ _ _ hv, hY, GalChar.delU_apply,
      GalChar.delCoord_of_closed _ _ _ (fun _ h _ hc => conj_mem_admissibleConjugatePairPlaces h hc) M hv]
  · rw [delU_off hY hQ σ v hv, coord, dif_neg hv]
    rfl

theorem delU_eq_spread (hQ : TWSet X i Q) {ch : Set (Pl D.host.E)} (hch : IsChoice ch) (σ : G D.host.E N.Om) :
    Multiplicative.toAdd (Y.delU i Q M σ) =
      spread Y i Q M ch fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) :=
  funext fun v => (delU_eq_coord hY hQ σ v).trans (spread_coord Y i Q M hch σ v).symm

theorem delU_eq_one (hQ : TWSet X i Q) (h0 : admissibleConjugatePairPlaces X i Q M = ∅) : Y.delU i Q M = 1 :=
  MonoidHom.ext fun σ => Multiplicative.toAdd.injective (funext fun v => delU_off hY hQ σ v (by simp [h0]))

end Univ

section Full

variable {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (rd : Rds Y ρ)

structure FullTie : Type where

  tie : Comparison₂ hρ rd

  hecke : ∀ i j b, HeckeTie (rd i j b)

  univ : IsUnivChar Y

variable (hF : ∀ i j b, Faithful (rd i j b))

open Classical in

def Model.hkF (i : X.Tw) : ∀ n b, ℕ → Pl D.host.E → Module.End (FractionRing (X.O i)) (Y.Fm i n b)
  | 0, b => Y.hkF i 0 b
  | n + 1, b => fun k P =>
    if h : n < D.R.m ∧ HkIdx i k P then (exists_hecke (hF i ⟨n, h.1⟩ b).injective k P).choose else Y.hkF i (n + 1) b k P

def withHecke : NExp D.R D.host D.what₂ D.LL0 N X := { Y with hkF := Model.hkF rd hF }

theorem heckeTie_withHecke (i j b) : HeckeTie (Y := withHecke rd hF) (rd i j b) := fun k P hk f hf => by
  have e : Model.hkF rd hF i ((j : ℕ) + 1) b k P = (exists_hecke (hF i j b).injective k P).choose := dif_pos ⟨j.2, hk⟩
  have h := (exists_hecke (hF i j b).injective k P).choose_spec f hf
  rw [← e] at h
  exact h

theorem withHecke_hkF_zero (i n b P) : (withHecke rd hF).hkF i n b 0 P = Y.hkF i n b 0 P := by
  cases n with
  | zero => rfl
  | succ n => exact dif_neg fun h => absurd h.2.1 (by omega)

variable (hL : ρ.LatFG)

def withAll : NExp D.R D.host D.what₂ D.LL0 N X :=
  withSeries hρ (Y := withHecke (Y := withUnivChar Y) rd hF) rd hF hL

def fullTieWithAll (hU : ρ.LevelOf Y) : FullTie hρ (Y := withAll hρ rd hF hL) rd where
  tie := tieWithSeries hρ (Y := withHecke (Y := withUnivChar Y) rd hF) rd hF hL ⟨hU.1, hU.2⟩
  hecke := heckeTie_withHecke (Y := withUnivChar Y) rd hF
  univ := fun _ _ _ => rfl

end Full

example (ρ : Setup X) (i j b) (P : Pl D.host.E) (F : GA D (Wc D j) → ℂ) : ρ.hecke i j b 0 P {1} 1 F = F := by
  funext x
  simp [Setup.hecke_apply]

end GlobalTheory.SeriesTie

end
