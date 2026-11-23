import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.Columns.RowFormsSym
import Formalism.LocalToGlobal.Columns.GoodXgE
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

theorem isAbsIrrChar_comp {K G H : Type} [Field K] [Group G] [Group H] (e : G ≃* H) {χ : H → K} (h : IsAbsIrrChar χ) :
    IsAbsIrrChar fun g => χ (e g) := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  refine ⟨n, ρ.comp e.toMonoidHom, ?_, fun t => hχ (e t)⟩
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun q => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective
      (congrArg (Subrepresentation.toSubmodule (ρ := ρ.comp e.toMonoidHom)) q :))
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule, fun g v hv => by
      obtain ⟨x, rfl⟩ := e.surjective g
      exact S.apply_mem_toSubmodule x hv⟩
    rcases hρ.eq_bot_or_eq_top S' with q | q
    · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) q :))
    · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) q :))

theorem isAbsIrrChar_comp_iff {K G H : Type} [Field K] [Group G] [Group H] (e : G ≃* H) {χ : H → K} :
    (IsAbsIrrChar fun g => χ (e g)) ↔ IsAbsIrrChar χ :=
  ⟨fun h => by simpa using isAbsIrrChar_comp e.symm h, isAbsIrrChar_comp e⟩

section Base

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

abbrev Gc (B : Base) (px : PreX B.toPre) : Type := Formalism.L2.Col.G0 B.fields.E (B.primes px).vGs B.R.r

abbrev PlS (B : Base) (px : PreX B.toPre) : Type := letI := B.fields.starE; Formalism.L2.Col.LevOff (E := B.fields.E) ∅ (B.primes px).vGs ∅

abbrev PlI (B : Base) (px : PreX B.toPre) : Type := letI := B.fields.starE; Formalism.L2.Col.LevOffI (E := B.fields.E) ∅ (B.primes px).vGs ∅

open Classical in

def tuOf (U : Set I.ι) : Finset (Tup B.fields.F B.fields.E B.fields.K I.S) :=
  (Finset.univ.filter fun a => a ∈ U).image I.tup

abbrev TupU (U : Set I.ι) : Type := TupF (X := B.fields) (tuOf I U)

open Classical in

def ixOf (U : Set I.ι) (t : TupU I U) : I.ι := if h : ∃ a, I.tup a = t.1 then h.choose else I.mu0

open Classical in

def xiValOf (τ : Tup B.fields.F B.fields.E B.fields.K I.S) (P : HeightOneSpectrum (𝓞 B.fields.E)) : B.LLˣ :=
  if h : ∃ z : B.LLˣ, ∃ a, I.tup a = τ ∧ B.embLL (z : B.LL) = (((I.xi a).val P : ℂˣ) : ℂ) then h.choose else 1

abbrev TrI (B : Base) (px : PreX B.toPre) : Type :=
  Fin B.R.m → (PlI B px × List ℕ → B.LL) → PlI B px × List ℕ → B.LL

def famC (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px) :
    FamIn3 B.LL (Gc B px) (PlS B px) (PlI B px) (List ℕ) (TupU I U) B.R.m :=
  colIn3 (X := B.fields) (Pr := B.primes px) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr

open Classical in

def psiC : ∀ PP : Pl B.host.E, AddChar (kP PP) B.LL :=
  fun PP => if h : PP ∈ (B.primes px).vGs then I.Ch.psi0 ⟨PP, h⟩ else 1

def lev0 : Subgroup (Gc B px) := (P0 (B.primes px).vGs B.R.r (psiC I)).H

def chr0 : lev0 I →* B.LLˣ := (P0 (B.primes px).vGs B.R.r (psiC I)).chi

def lev1 : Subgroup (Gc B px) := (Formalism.L2.Col.rPsymF (R := B.R) I.Ch).grp

def chr1 : lev1 I →* B.LLˣ := (Formalism.L2.Col.rPsymF (R := B.R) I.Ch).chr

theorem famC_A (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL)) (tr tr' : TrI B px) :
    (famC I hX U Xg tr).A = (famC I hX U Xg tr').A := rfl

def usedOf (T : Top.TwDat B) (Wt : Set B.places.Pl) : Set I.ι := {a | ∃ w ∈ Wt, I.xi a = T.xiTw I.C w}

def SelHalf : Prop :=
  ∀ a b : I.ι, ∀ P ∈ I.Q a, ∀ P' ∈ I.Q b, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 B.host.E) ∈ P.asIdeal ∧ (p : 𝓞 B.host.E) ∈ P'.asIdeal) →
    P.asIdeal.comap (algebraMap (𝓞 B.host.K) (𝓞 B.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 B.host.K) (𝓞 B.host.E))

def ValsIn : Prop :=
  (∀ a P, (I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
    ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (kP P))

theorem mem_tuOf {U : Set I.ι} {τ : Tup B.fields.F B.fields.E B.fields.K I.S} : τ ∈ tuOf I U ↔ ∃ a ∈ U, I.tup a = τ := by
  unfold tuOf
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem tup_mem_tuOf {U : Set I.ι} {a : I.ι} : I.tup a ∈ tuOf I U ↔ a ∈ U :=
  (mem_tuOf I).trans ⟨fun ⟨_, hb, e⟩ => I.tup_inj e ▸ hb, fun h => ⟨a, h, rfl⟩⟩

theorem ixOf_eq {U : Set I.ι} {t : TupU I U} {a : I.ι} (h : I.tup a = t.1) : ixOf I U t = a := by
  have h' : ∃ a, I.tup a = t.1 := ⟨a, h⟩
  unfold ixOf
  rw [dif_pos h']
  exact I.tup_inj (h'.choose_spec.trans h.symm)

theorem tup_ixOf {U : Set I.ι} (t : TupU I U) : I.tup (ixOf I U t) = t.1 := by
  have h : ∃ a, I.tup a = t.1 := by
    rcases t.2 with h | h
    · exact ⟨I.mu0, I.trueColumn_tuple_trivial_eq_one.trans h.symm⟩
    · obtain ⟨a, -, e⟩ := (mem_tuOf I).1 h
      exact ⟨a, e⟩
  obtain ⟨a, ha⟩ := h
  rw [ixOf_eq I ha, ha]

theorem ixOf_mu0F (U : Set I.ι) : ixOf I U (mu0F (X := B.fields) (tuOf I U)) = I.mu0 := ixOf_eq I I.trueColumn_tuple_trivial_eq_one

theorem ixOf_injective (U : Set I.ι) : Function.Injective (ixOf I U) := fun t t' h =>
  Subtype.ext ((tup_ixOf I t).symm.trans ((congrArg I.tup h).trans (tup_ixOf I t')))

theorem mem_range_ixOf {U : Set I.ι} {a : I.ι} : a ∈ Set.range (ixOf I U) ↔ a = I.mu0 ∨ a ∈ U := by
  constructor
  · rintro ⟨t, rfl⟩
    rcases t.2 with h | h
    · exact Or.inl (ixOf_eq I (I.trueColumn_tuple_trivial_eq_one.trans h.symm))
    · exact Or.inr ((tup_mem_tuOf I).1 (by rw [tup_ixOf]; exact h))
  · rintro (rfl | h)
    · exact ⟨_, ixOf_mu0F I U⟩
    · exact ⟨⟨I.tup a, Or.inr ((tup_mem_tuOf I).2 h)⟩, ixOf_eq I rfl⟩

theorem usedOf_mono (T : Top.TwDat B) {Wt Wt' : Set B.places.Pl} (h : Wt ⊆ Wt') : usedOf I T Wt ⊆ usedOf I T Wt' :=
  fun _ ⟨w, hw, e⟩ => ⟨w, h hw, e⟩

section Fields

variable (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px)

theorem family_infinitePlace : (famC I hX U Xg tr).A.v0 = InfinitePlace.mk B.embLL := rfl

theorem famC_μ0 : (famC I hX U Xg tr).A.μ0 = mu0F (X := B.fields) (tuOf I U) := rfl

theorem famC_X : (famC I hX U Xg tr).A.X = Xg := rfl

theorem famC_r : (famC I hX U Xg tr).A.r = B.R.r := rfl

theorem famC_A_t : (famC I hX U Xg tr).A.t = B.R.t := rfl

theorem famC_trI : (famC I hX U Xg tr).trI = tr := rfl

theorem famC_muVal (j : Fin B.R.m) (t : TupU I U) (P : PlS B px) :
    (famC I hX U Xg tr).A.muVal j t P = I.Ch.muVal j P.1 * xiValOf I t.1 P.1 := rfl

end Fields

theorem embLL_xiValOf (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (h : ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) :
    B.embLL (xiValOf I (I.tup a) P : B.LL) = (((I.xi a).val P : ℂˣ) : ℂ) := by
  obtain ⟨z, hz⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact Units.ne_zero _ (hz.symm.trans (map_zero _))
  have h' : ∃ z : B.LLˣ, ∃ b, I.tup b = I.tup a ∧ B.embLL (z : B.LL) = (((I.xi b).val P : ℂˣ) : ℂ) :=
    ⟨Units.mk0 z hz0, a, rfl, hz⟩
  unfold xiValOf
  rw [dif_pos h']
  obtain ⟨b, hb, e⟩ := h'.choose_spec
  rw [e, I.tup_inj hb]

theorem psiC_of_mem {PP : Pl B.host.E} (h : PP ∈ (B.primes px).vGs) : psiC I PP = I.Ch.psi0 ⟨PP, h⟩ := by
  unfold psiC
  rw [dif_pos h]

theorem psiC_of_notMem {PP : Pl B.host.E} (h : PP ∉ (B.primes px).vGs) : psiC I PP = 1 := by
  unfold psiC
  rw [dif_neg h]

theorem ValsIn.embLL_xiValOf {I : ColIn B px} (h : ValsIn I) (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hP : (I.xi a).UnrAt P) : B.embLL (xiValOf I (I.tup a) P : B.LL) = (((I.xi a).val P : ℂˣ) : ℂ) :=
  GlobalTheory.Mem.R3.embLL_xiValOf I a P (h.1 a P hP)

example : tuOf I ∅ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun τ h => ?_
  obtain ⟨a, ha, -⟩ := (mem_tuOf I).1 h
  exact ha

example : (1 : Tup B.fields.F B.fields.E B.fields.K I.S) ∈ tuOf I {I.mu0} := (mem_tuOf I).2 ⟨_, rfl, I.trueColumn_tuple_trivial_eq_one⟩

example (h : I.Ok) (P : HeightOneSpectrum (𝓞 B.fields.E)) : B.embLL (xiValOf I (I.tup I.mu0) P : B.LL) = 1 := by
  have e : (((I.xi I.mu0).val P : ℂˣ) : ℂ) = 1 := by
    rw [h.trueColumnChoices_heckeChar_reference_eq_one]
    rfl
  rw [embLL_xiValOf I I.mu0 P ⟨1, by rw [e, map_one]⟩, e]

example (T : Top.TwDat B) : usedOf I T ∅ = ∅ := Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ => h

end Base

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)

abbrev famR (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) :
    FamIn3 X.toD7.what₂.LL (Gc X.B px) (PlS X.B px) (PlI X.B px) (List ℕ) (TupU I U) X.toD7.R.m :=
  famC I hX U Xg tr

structure LevOf (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) : Prop where

  is : L.Is (mu0F (X := X.B.fields) (tuOf I U))

  C : L.C = Top.Fr.at X I.C

  xiH : ∀ t, L.xiH t = I.xi (ixOf I U t)

  Pg : L.Pg = (X.B.primes px).vGs

  Q : ∀ t, L.Q t = I.Q (ixOf I U t)

  beta : (∀ i, L.βV i = 1) ∧ L.βX = 1

def IsPlacewiseIdentity {Pg : Finset (Pl X.toD7.host.E)} (eG : Gc X.B px ≃* G0 Pg X.toD7.R.r) : Prop :=
  ∀ (g : Gc X.B px) (P : Pl X.toD7.host.E) (h : P ∈ (X.B.primes px).vGs) (h' : P ∈ Pg), eG g ⟨P, h'⟩ = g ⟨P, h⟩

def GoodSet (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)) : Prop :=
  letI : Fintype (G0g X.toD7.nd) := Fintype.ofEquiv _ eR.toEquiv
  (∀ χ : Gc X.B px → X.B.LL, χ ∈ Xg ↔ (fun g => χ (eR.symm g)) ∈ Formalism.L2.Col.XgE X.B.embLL X.toD7.ntypes.e0) ∧
    ∀ g, X.B.embLL ((idemOf Xg).coeff g) = X.toD7.ntypes.e0.coeff (eR g)

theorem goodSet_iff (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)) :
    GoodSet X (px := px) eR Xg ↔
      (∀ χ : Gc X.B px → X.B.LL, χ ∈ Xg ↔ IsAbsIrrChar χ ∧
        ∑ g : Gc X.B px, X.toD7.ntypes.e0.coeff (eR g) * X.B.embLL (χ g) = X.B.embLL (χ 1)) ∧
      ∀ g, X.B.embLL ((idemOf Xg).coeff g) = X.toD7.ntypes.e0.coeff (eR g) := by
  let _ : Fintype (G0g X.toD7.nd) := Fintype.ofEquiv _ eR.toEquiv
  refine and_congr_left' (forall_congr' fun χ => iff_congr Iff.rfl ?_)
  rw [Formalism.L2.Col.mem_XgE, ← Equiv.sum_comp eR.toEquiv, isAbsIrrChar_comp_iff eR.symm]
  simp

theorem GoodSet.unique {eR : Gc X.B px ≃* G0g X.toD7.nd} {Xg Xg' : Finset (Gc X.B px → X.B.LL)}
    (h : GoodSet X (px := px) eR Xg) (h' : GoodSet X (px := px) eR Xg') : Xg = Xg' :=
  Finset.ext fun χ => (h.1 χ).trans (h'.1 χ).symm

theorem GoodSet.irr {eR : Gc X.B px ≃* G0g X.toD7.nd} {Xg : Finset (Gc X.B px → X.B.LL)}
    (h : GoodSet X (px := px) eR Xg) : ∀ χ ∈ Xg, IsAbsIrrChar χ :=
  fun χ hχ => ((((goodSet_iff X eR Xg).1 h).1 χ).1 hχ).1

theorem isIdG_refl : IsPlacewiseIdentity X (px := px) (Pg := (X.B.primes px).vGs) (MulEquiv.refl _) := fun _ _ _ _ => rfl

structure GrpAt : Prop where

  pl : ∃ plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ (X.B.primes px).vGs,
    ∀ kv, ((plg kv).1 : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2 ∧ I.C.P.Div kv.1 (plg kv).1

  idem : IsIdempotentElem X.toD7.ntypes.e0

  cen : X.toD7.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g X.toD7.nd))

end Record

end GlobalTheory.Mem.R3

end
