import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces

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

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

variable (X) in

def sideEmb (i : X.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (X.O i) :=
  (IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i)) (L := FractionRing (X.O i))
    (X.O_inj i)).comp (if b then X.emb0 i else X.emb0b i)

def labLL0 (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ↥D.LL0 :=
  (Links.labLL D τ).codRestrict D.LL0 fun _ => D.hostField_le_fixedField _

theorem embLL0_labLL0 (τ : D.what₂.Tau) : (embLL0 D).comp (labLL0 D τ) = tauE D τ :=
  FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ

structure Setup (X : NTw D.R D.host D.what₂ D.LL0 N) : Type 1 where

  rc : Recip D N.Om

  ch : X.Tw → Set (Pl D.host.E)

  bad : X.Tw → ℕ

  e : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)

  ek : ∀ i, Bool → ∀ k, FractionRing (X.Ok i k) →+* ℂ

  B : X.Tw → ∀ j : Fin D.R.m, Bool → Base (Vc D j) (Wc D j)

  om : X.Tw → ∀ j : Fin D.R.m, Bool → ((AE D)ˣ →* Circle) → PairRep (Vc D j) (Wc D j)

  Cl : X.Tw → Fin D.R.m → Bool → Twist D Circle → Type
  [finCl : ∀ i j b t, Fintype (Cl i j b t)]
  rep : ∀ i j b t, Cl i j b t → GA D (Vc D j)

  β : ∀ (j : Fin D.R.m) (P : Pl D.host.E), DetBases (kP P) (Wc D j).rank (Vc D j).rank

  eG : ∀ i j b, G0g N ≃* G0 (B i j b).G.Pg (Wc D j).rank

attribute [instance] Setup.finCl

namespace Setup

variable (ρ : Setup X) (i : X.Tw) (j : Fin D.R.m) (b : Bool)

def eO : X.O i →+* ℂ := (ρ.e i b).comp (algebraMap _ _)

def eOk (k : ℕ) : X.Ok i k →+* ℂ := (ρ.ek i b k).comp (algebraMap _ _)

def tw (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Twist D Circle :=
  twistOf ρ.rc (ρ.eOk i b k) (ρ.ch i) Q ψ

abbrev lat (O : Subring ℂ) (h : GA D (Vc D j)) : Submodule O (PolF D (Wc D j).rank (Vc D j).rank) :=
  (ρ.B i j b).coefLat (embLL0 D) (labLL0 D) O (finPt _ h)

structure IsDatum (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) : Prop where
  split : SplitSet s
  off : ∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal
  fin : h ∈ GfC (Vc D j)
  supp : SuppAt (idem s) (Vc D j) h
  mem : P ∈ ρ.lat i j b (ρ.eO i b).range h

abbrev theta (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  (ρ.B i j b).theta (ρ.om i j b 1) h P

abbrev gens (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : Set (GA D (Wc D j) → ℂ) :=
  (ρ.B i j b).genSet (ρ.om i j b 1) (ρ.tw i b k Q ψ) h P

abbrev mt (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) :
    Submodule (ρ.eOk i b k).range (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank) :=
  (ρ.B i j b).mtLat (embLL0 D) (labLL0 D) (ρ.eOk i b k).range (ρ.tw i b k Q ψ)

abbrev sum (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) :
    (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank) →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
  (ρ.B i j b).classSum (ρ.om i j b (ρ.tw i b k Q ψ).chi) (ρ.tw i b k Q ψ) (ρ.rep i j b (ρ.tw i b k Q ψ))

abbrev xi (Y : NExp D.R D.host D.what₂ D.LL0 N X) (Q : Finset (Pl D.host.E)) (M : ℕ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) : GA D (Wc D j) → ℂ :=
  (ρ.B i j b).xiCoef (ρ.om i j b 1) (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))
    (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) h P a

abbrev levK : Subgroup (GA D (Wc D j)) := Lev.levG (Wc D j) (ρ.B i j b).F.βT (Lev.flag1L (ρ.B i j b).G.levT)

structure Good : Prop where
  rc : ρ.rc.Good
  ch : ∀ i, IsChoice (ρ.ch i)
  bad_ne : ∀ i, ρ.bad i ≠ 0

  goodSetup_bad_mem_badPlaces : ∀ i, ∀ P ∈ X.S0 i, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal

  goodSetup_badPlaces_conj : ∀ i, ∀ P ∈ X.S0 i, ∀ P', IsConjPl D.host P P' → P' ∈ X.S0 i
  goodSetup_placesOverTwo_subset : ∀ i, placesOver D.host.E 2 ⊆ ↑(X.S0 i)
  goodSetup_count_eq_zero_off_badPlaces : ∀ i P, P ∉ X.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0

  e_LL0 : ∀ i b x, ρ.e i b (sideEmb X i b x) = embLL0 D x
  ek_e : ∀ i b k (x : X.O i), ρ.eOk i b k (algebraMap (X.O i) (X.Ok i k) x) = ρ.eO i b x
  base : ∀ i j b, (ρ.B i j b).Good

  latS : ∀ i j b, Lev.IsBaseFrame (Vc D j) (ρ.B i j b).F.βS (ρ.B i j b).F.ΛS 1
  latT : ∀ i j b, Lev.IsBaseFrame (Wc D j) (ρ.B i j b).F.βT (ρ.B i j b).F.ΛT 1

  Pg : ∀ i j b, ∀ P ∈ (ρ.B i j b).G.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k)

  delta : ∀ i j b, (ρ.B i j b).de = twistOf ρ.rc ((ρ.eO i b).comp (algebraMap (X.O0 i) (X.O i))) (ρ.ch i) (X.pD i)
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i))
  weil : ∀ i j b (t : Twist D Circle), t.Good → (ρ.B i j b).IsWeil t.chi (ρ.om i j b t.chi)
  classes : ∀ i j b (t : Twist D Circle), t.Good → (ρ.B i j b).admitted t.Q →
    IsClassSystem (Vc D j) ((ρ.B i j b).levJ t) (ρ.rep i j b t)

theorem Good.weil_base {ρ : Setup X} (h : ρ.Good) (i : X.Tw) (j : Fin D.R.m) (b : Bool) :
    (ρ.B i j b).IsWeil 1 (ρ.om i j b 1) := h.weil i j b (Twist.triv Circle ∅) (Twist.triv_good splitSet_empty)

theorem eO_injective : Function.Injective (ρ.eO i b) := (ρ.e i b).injective.comp (IsFractionRing.injective _ _)

theorem eOk_injective (k : ℕ) : Function.Injective (ρ.eOk i b k) := (ρ.ek i b k).injective.comp (IsFractionRing.injective _ _)

theorem Good.isCoefRing {ρ : Setup X} (h : ρ.Good) (i : X.Tw) (b : Bool) :
    IsCoefRing (embLL0 D) (labLL0 D) (ρ.eO i b).range := by
  refine ⟨embLL0_labLL0, fun a => ?_⟩
  have h1 : IsIntegral (X.O i) (sideEmb X i b a) :=
    a.isIntegral_coe.map_of_comp_eq (Int.castRingHom _) (sideEmb X i b) (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  exact ⟨y, by rw [← h.e_LL0 i b, ← hy]; rfl⟩

theorem Good.range_le {ρ : Setup X} (h : ρ.Good) (i : X.Tw) (b : Bool) (k : ℕ) : (ρ.eO i b).range ≤ (ρ.eOk i b k).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨_, h.ek_e i b k x⟩

theorem Good.isCoefRing_k {ρ : Setup X} (h : ρ.Good) (i : X.Tw) (b : Bool) (k : ℕ) :
    IsCoefRing (embLL0 D) (labLL0 D) (ρ.eOk i b k).range :=
  ⟨embLL0_labLL0, fun a => h.range_le i b k ((h.isCoefRing i b).int a)⟩

theorem gens_one (k : ℕ) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) :
    ρ.gens i j b k ∅ 1 h P = {ρ.theta i j b h P} := by
  have key : ∀ t : Twist D Circle, t.Q = ∅ → t.chi = 1 → ∀ ω, (ρ.B i j b).genSet ω t h P = {(ρ.B i j b).theta ω h P} := by
    rintro ⟨_, _, r⟩ rfl rfl ω
    have e : (ρ.B i j b).vecFlat ⟨∅, 1, r⟩ = (ρ.B i j b).vecFlat (Twist.triv Circle ∅) :=
      ((ρ.B i j b).vecAt_empty _).trans (ρ.B i j b).vecFlat_triv.symm
    rw [← Base.genSet_triv]
    unfold Base.genSet Base.gen
    rw [e]
    rfl
  exact key _ (half_empty _) (charOf_one _ _) _

theorem xi_of_empty (Y : NExp D.R D.host D.what₂ D.LL0 N X) {Q : Finset (Pl D.host.E)} {M : ℕ}
    (hQ : half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M) = ∅) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) (a) :
    ρ.xi i j b Y Q M h P a = ρ.theta i j b h P := by
  have key : ∀ (Q' : Finset (Pl D.host.E)) (u : UnivTwist D (ZMod (X.l i ^ M))) Φ (a : ↥Q' → ZMod (X.l i ^ M)), Q' = ∅ →
      (ρ.B i j b).xiCoef (ρ.om i j b 1) u Q' Φ h P a = ρ.theta i j b h P := by
    rintro _ u Φ a rfl
    exact Base.xiCoef_empty _ _ _ _ _ _ _
  exact key _ _ _ _ hQ

end Setup

theorem twOK_one (i : X.Tw) (k : ℕ) : TwOK i k ∅ (1 : G D.host.E N.Om →* (X.Ok i k)ˣ) :=
  ⟨by simp, by simp, by simp, fun _ _ _ => inv_one.symm, fun _ => one_mem _, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl⟩

section Read

variable (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool)

abbrev Rd : Type := Y.Fm i ((j : ℕ) + 1) b →ₛₗ[ρ.e i b] (GA D (Wc D j) → ℂ)

variable {ρ Y i j b} (rd : Rd ρ Y i j b)

theorem rd_smul (a : X.O i) (f : Y.Fm i ((j : ℕ) + 1) b) : rd (a • f) = ρ.eO i b a • rd f := by
  rw [← algebraMap_smul (FractionRing (X.O i)) a f, map_smulₛₗ]
  rfl

def rdK (hρ : ρ.Good) (k : ℕ) : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b →ₛₗ[ρ.eOk i b k] (GA D (Wc D j) → ℂ) :=
  let φ : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b →+ (GA D (Wc D j) → ℂ) := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.eOk i b k a)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun c a f => by
      change ρ.eOk i b k (c • a) • rd f = ρ.eOk i b k a • rd (c • f)
      rw [rd_smul, Algebra.smul_def c a, map_mul, hρ.ek_e, smul_smul, mul_comm]
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun c x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        change ρ.eOk i b k (c • a) • rd f = ρ.eOk i b k c • ρ.eOk i b k a • rd f
        rw [smul_eq_mul, map_mul, mul_smul] }

theorem rdK_tmul (hρ : ρ.Good) (k : ℕ) (a : X.Ok i k) (f : Y.Fm i ((j : ℕ) + 1) b) :
    rdK rd hρ k (a ⊗ₜ f) = ρ.eOk i b k a • rd f := rfl

def Faithful : Prop :=
  ∀ (n : ℕ) (v : Fin n → Y.Fm i ((j : ℕ) + 1) b), LinearIndependent (FractionRing (X.O i)) v → LinearIndependent ℂ fun c => rd (v c)

variable {rd}

theorem Faithful.injective (h : Faithful rd) : Function.Injective rd := by
  refine (injective_iff_map_eq_zero rd).2 fun f hf => ?_
  by_contra h0
  exact (h 1 (fun _ => f) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hf

theorem Faithful.injective_rdK (h : Faithful rd) (hρ : ρ.Good) (k : ℕ) : Function.Injective (rdK rd hρ k) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  let v := Module.finBasis (FractionRing (X.O i)) (Y.Fm i ((j : ℕ) + 1) b)
  have key : ∀ x : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b, ∃ d : X.O i, d ≠ 0 ∧ ∃ c : _ → X.Ok i k,
      d • x = ∑ a, c a ⊗ₜ v a := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | add x y hx hy =>
      obtain ⟨d, hd, c, e⟩ := hx
      obtain ⟨d', hd', c', e'⟩ := hy
      refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
      rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
      simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
    | tmul a f =>
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (X.O i)) fun c => v.repr f c
      choose y hy using hd
      refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing (X.O i)) (y c), hy, smul_assoc]
  obtain ⟨d, hd, c, e⟩ := key x
  have h1 : ∑ a, ρ.eOk i b k (c a) • rd (v a) = 0 := by
    have := congrArg (rdK rd hρ k) e
    rw [← algebraMap_smul (X.Ok i k) d x, map_smulₛₗ, hx, smul_zero, map_sum] at this
    exact this.symm
  have h2 : ∀ a, c a = 0 := fun a => ρ.eOk_injective i b k
    ((Fintype.linearIndependent_iff.1 (h _ v v.linearIndependent) _ h1 a).trans (map_zero _).symm)
  have h3 : d • x = 0 := by simp [e, h2]
  have h4 : ∀ x : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b,
      LinearMap.lTensor (X.Ok i k) (((algebraMap (X.O i) (FractionRing (X.O i)) d)⁻¹ • LinearMap.id :
        Module.End (FractionRing (X.O i)) (Y.Fm i ((j : ℕ) + 1) b)).restrictScalars (X.O i)) (d • x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
    | tmul a f =>
      rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul]
      congr 1
      change (algebraMap (X.O i) (FractionRing (X.O i)) d)⁻¹ • d • f = f
      rw [← algebraMap_smul (FractionRing (X.O i)) d f, inv_smul_smul₀ (by simpa using hd)]
  rw [← h4 x, h3, map_zero]

end Read

section Comparison₂

variable (X) in

def InRange (i : X.Tw) (Q : Finset (Pl D.host.E)) : Prop :=
  (∀ P ∈ Q, IsSplitPl D.host P) ∧ ClsQ (D := D) Q ∧ Disjoint Q (X.S0 i)

def normProd (s : Finset (Pl D.host.E)) : ℕ := ∏ v ∈ s, Ideal.absNorm v.asIdeal

open Classical in

def grpSum (Y : NExp D.R D.host D.what₂ D.LL0 N X) {i : X.Tw} {j : ℕ} {b : Bool} (ch : Set (Pl D.host.E))
    (Q : Finset (Pl D.host.E)) (M : ℕ) (x : (↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) → Y.Fm i j b) :
    Y.Fm i j b ⊗[X.O i] AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M) :=
  ∑ a, x a ⊗ₜ[X.O i] AddMonoidAlgebra.single (spread Y i Q M ch a) (1 : X.O i)

variable {ρ : Setup X} (hρ : ρ.Good) (Y : NExp D.R D.host D.what₂ D.LL0 N X) {i : X.Tw} {j : Fin D.R.m} {b : Bool}
  (rd : Rd ρ Y i j b)

structure CellTie where

  supp : Y.Dat i ((j : ℕ) + 1) b → Finset (Pl D.host.E)
  cls : Y.Dat i ((j : ℕ) + 1) b → GA D (Vc D j)
  coef : Y.Dat i ((j : ℕ) + 1) b → PolF D (Wc D j).rank (Vc D j).rank

  rdV : ∀ k Q ψ, Y.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)

  U_eq : ∀ g, ρ.eG i j b g ∈ (ρ.B i j b).G.P.H ↔ g ∈ Y.U

  psiU_eq : ∀ (u : Y.U) hu, (((ρ.B i j b).G.P.chi ⟨ρ.eG i j b u, hu⟩ : ℂˣ) : ℂ) = ρ.e i b (Y.psiU i b u : (FractionRing (X.O i))ˣ)

  dat : ∀ d, ρ.IsDatum i j b (supp d) (cls d) (coef d)

  dat_onto : ∀ s h P, ρ.IsDatum i j b s h P → ρ.theta i j b h P ∈ Set.range rd → ∃ d, supp d = s ∧ cls d = h ∧ coef d = P

  lev_iff : ∀ d v, v ∈ Y.lev i _ b d ↔ ((normProd (supp d) : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal

  th_eq : ∀ d, rd (Y.th i _ b d) = ρ.theta i j b (cls d) (coef d)

  thPsi_iff : ∀ k Q ψ, TwOK i k Q ψ → ∀ d x,
    x ∈ Y.thPsi i _ b k Q ψ d ↔ rdK rd hρ k x ∈ ρ.gens i j b k Q ψ (cls d) (coef d)

  thU_eq : ∀ Q M d, InRange X i Q → ∀ x, (∀ a, rd (x a) = ρ.xi i j b Y Q M (cls d) (coef d) a) →
    Y.thU i _ b Q M d = grpSum Y (ρ.ch i) Q M x

  thU_off : ∀ Q M d, ¬ (InRange X i Q ∧ ∀ a, ρ.xi i j b Y Q M (cls d) (coef d) a ∈ Set.range rd) → Y.thU i _ b Q M d = 0

  rdV_inj : ∀ k Q ψ, TwOK i k Q ψ → Function.Injective (rdV k Q ψ)

  mtLat_iff : ∀ k Q ψ, TwOK i k Q ψ → ∀ F, F ∈ ρ.mt i j b k Q ψ ↔ ∃ f ∈ Y.MtLat i _ b k Q ψ, rdV k Q ψ f = F

  thP_eq : ∀ k Q ψ, TwOK i k Q ψ → ∀ f, ρ.sum i j b k Q ψ (rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) →
    rdK rd hρ k (Y.thP i _ b k Q ψ f) = ρ.sum i j b k Q ψ (rdV k Q ψ f)

variable {Y}

def RatBase : Prop := ∀ s h P, ρ.IsDatum i j b s h P → ρ.theta i j b h P ∈ Set.range rd

def RatTwist : Prop := ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ s h P, ρ.IsDatum i j b s h P →
  ρ.gens i j b k Q ψ h P ⊆ Set.range (rdK rd hρ k)

def RatUniv : Prop := ∀ Q M, InRange X i Q → ∀ s h P, ρ.IsDatum i j b s h P →
  (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ρ.xi i j b Y Q M h P a ∈ Set.range rd

def Rat : Prop := RatBase rd ∧ RatTwist hρ rd ∧ RatUniv rd

def ActRead : Prop := ∀ (g : G0g N) (κ : GA D (Wc D j)),
  Lev.IsLevelLift (Wc D j) (ρ.B i j b).F.βT (ρ.B i j b).G.levT (ρ.eG i j b g) κ →
    ∀ f x, rd (Y.actG i _ b g f) x = rd f (x * κ)

def HeckeRead : Prop := ∀ k P, HkIdx i k P → ∀ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ),
  Links.IsHeckeAt (Wc D j) P k α → Bridge.IsDC (ρ.levK i j b) α R → IsDetAt (idemAt P) (Wc D j) α z →
    ∀ f x, rd (Y.hkF i _ b k P f) x = (((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ *
      (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹ * ∑ γ ∈ R, rd f (x * γ)

namespace CellTie

variable {hρ rd} (T : CellTie hρ Y rd)
include T

theorem thU_of_empty {Q : Finset (Pl D.host.E)} {M : ℕ} (hQ : InRange X i Q) (h0 : half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M) = ∅)
    (d : Y.Dat i ((j : ℕ) + 1) b) : Y.thU i _ b Q M d = Y.th i _ b d ⊗ₜ[X.O i] 1 := by
  haveI : IsEmpty ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) := ⟨fun P => Finset.eq_empty_iff_forall_notMem.1 h0 P.1 P.2⟩
  rw [T.thU_eq Q M d hQ (fun _ => Y.th i _ b d) fun a => by rw [T.th_eq, ρ.xi_of_empty i j b Y h0], grpSum,
    Finset.sum_eq_single 0 (fun a _ h => absurd (funext fun P => isEmptyElim P) h) (fun h => absurd (@Finset.mem_univ _ (_) _) h), map_zero]
  rfl

theorem thU_empty (M : ℕ) (d : Y.Dat i ((j : ℕ) + 1) b) : Y.thU i _ b ∅ M d = Y.th i _ b d ⊗ₜ[X.O i] 1 :=
  T.thU_of_empty ⟨by simp, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩ (by simp) d

theorem thU_of_rat (hR : RatUniv rd) {Q : Finset (Pl D.host.E)} (M : ℕ) (hQ : InRange X i Q) {d : Y.Dat i ((j : ℕ) + 1) b}
    (hd : Disjoint Q (Y.lev i _ b d)) : ∃ x, (∀ a, rd (x a) = ρ.xi i j b Y Q M (T.cls d) (T.coef d) a) ∧
      Y.thU i _ b Q M d = grpSum Y (ρ.ch i) Q M x := by
  choose x hx using hR Q M hQ _ _ _ (T.dat d) fun v hv h => Finset.disjoint_left.1 hd hv ((T.lev_iff d v).2 h)
  exact ⟨x, hx, T.thU_eq Q M d hQ x hx⟩

theorem rdV_mem {k Q ψ} (h : TwOK i k Q ψ) {f : Y.MtV i ((j : ℕ) + 1) b k Q ψ} :
    f ∈ Y.MtLat i _ b k Q ψ ↔ T.rdV k Q ψ f ∈ ρ.mt i j b k Q ψ := by
  rw [T.mtLat_iff k Q ψ h]
  exact ⟨fun hf => ⟨f, hf, rfl⟩, fun ⟨_, hf, e⟩ => T.rdV_inj k Q ψ h e ▸ hf⟩

theorem nonempty_dat : Nonempty (Y.Dat i ((j : ℕ) + 1) b) := by
  obtain ⟨d, -⟩ := T.dat_onto ∅ 1 0 ⟨splitSet_empty, by simp, one_mem _, fun a c => by
    rw [show Formalism.L2.Theta.mt (Vc D j) 1 - 1 = 0 from sub_self _, Matrix.zero_apply, mul_zero], zero_mem _⟩
    ⟨0, rd.map_zero.trans (LinearMap.map_zero _).symm⟩
  exact ⟨d⟩

end CellTie

variable (Y) in

abbrev Rds (ρ : Setup X) : Type := ∀ i j b, Rd ρ Y i j b

abbrev Comparison₂ (rd : Rds Y ρ) : Type := ∀ i j b, CellTie hρ Y (rd i j b)

end Comparison₂

end GlobalTheory.SeriesTie

end
