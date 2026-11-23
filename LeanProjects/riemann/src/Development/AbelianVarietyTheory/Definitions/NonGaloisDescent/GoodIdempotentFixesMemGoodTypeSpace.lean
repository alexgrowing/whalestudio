import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingsConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallIdealNeBot

noncomputable section

namespace GlobalTheory.EigTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.MainNotions.IntegralHeckeForms (HkIdx V0 Fm0 eG Eigsp)
open Formalism.MainNotions.BlochKatoReduction.Gen (goodE Tmat eps0 chiS)
open Formalism.L2.Host (HChar CharFrame embLL0)
open GlobalTheory.Triple (Reading embSide muBase heckeVal IsParam IsResidual FbAt jIdx)
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open scoped TensorProduct

variable {D : D7}

section Sys

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def IsEigVec (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) (x : Y.Fm i j b) : Prop :=
  x ∈ V0 Y i j b ∧ x ≠ 0 ∧ ∀ k P, HkIdx i k P → Y.hkF i j b k P x = ev k P • x

def IsEigSys (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) : Prop :=
  ∃ x, IsEigVec Y i j b ev x

def sigEv {i : X.Tw} (s : X.Sig i) (k : ℕ) (P : PlE D.host) : FractionRing (X.O i) :=
  algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P)

abbrev HkSet (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) : Type := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}

def sysOf {i : X.Tw} (s : X.Sig i) : ℕ × Bool × (HkSet X i → FractionRing (X.O i)) :=
  (X.jS i s, X.side i s, fun p => sigEv s p.1.1 p.1.2)

def eigSet (i : X.Tw) : Set (ℕ × Bool × (HkSet X i → FractionRing (X.O i))) :=
  {t | t.1 ∈ Finset.Icc 1 D.R.m ∧ ∃ ev, IsEigSys Y i t.1 t.2.1 ev ∧ t.2.2 = fun p => ev p.1.1 p.1.2}

structure SigTiedAt (i : X.Tw) : Prop where
  inj : ∀ s s' : X.Sig i, X.jS i s = X.jS i s' → X.side i s = X.side i s' →
    (∀ k P, HkIdx i k P → X.hEig i s k P = X.hEig i s' k P) → s = s'
  vec : ∀ s : X.Sig i, IsEigSys Y i (X.jS i s) (X.side i s) (sigEv s)
  all : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b ev, IsEigSys Y i j b ev →
    ∃ s : X.Sig i, X.jS i s = j ∧ X.side i s = b ∧ ∀ k P, HkIdx i k P → sigEv s k P = ev k P
  zero : ∀ (s : X.Sig i) P, X.hEig i s 0 P = 1
  mem : ∀ (s : X.Sig i) k P, HkIdx i k P → ∃ x : X.O0 i, algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P
  ss : ∀ s : X.Sig i, IsSSRep (mapRep (algebraMap (X.O0 i) (FractionRing (X.O0 i))) (X.rhoS i s))
  frob : ∀ s : X.Sig i, HkFrob i s

def SigTiedOf : Prop := ∀ i, X.NonzeroIndexPlace i → SigTiedAt Y i

variable {Y} {i : X.Tw} {j : ℕ} {b : Bool}

theorem isEigSys_iff {ev : ℕ → PlE D.host → FractionRing (X.O i)} :
    IsEigSys Y i j b ev ↔ Eigsp Y i j b ev ⊓ V0 Y i j b ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine exists_congr fun x => ?_
  simp only [IsEigVec, Eigsp, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  tauto

theorem IsEigSys.congr {ev ev' : ℕ → PlE D.host → FractionRing (X.O i)} (h : IsEigSys Y i j b ev)
    (e : ∀ k P, HkIdx i k P → ev k P = ev' k P) : IsEigSys Y i j b ev' :=
  let ⟨x, h1, h2, h3⟩ := h
  ⟨x, h1, h2, fun k P hk => e k P hk ▸ h3 k P hk⟩

theorem good_idempotent_fixes_mem_good_type_space {x : Y.Fm i j b} (hx : x ∈ V0 Y i j b) : eG Y i j b x = x := by
  obtain ⟨y, -, rfl⟩ := hx
  rw [← Module.End.mul_apply, eG, ← map_mul, Y.eAlg_idem]

theorem bijOn_iff : Set.BijOn (sysOf (X := X) (i := i)) Set.univ (eigSet Y i) ↔
    (∀ s s' : X.Sig i, X.jS i s = X.jS i s' → X.side i s = X.side i s' →
      (∀ k P, HkIdx i k P → X.hEig i s k P = X.hEig i s' k P) → s = s') ∧
    (∀ s : X.Sig i, IsEigSys Y i (X.jS i s) (X.side i s) (sigEv s)) ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b ev, IsEigSys Y i j b ev →
      ∃ s : X.Sig i, X.jS i s = j ∧ X.side i s = b ∧ ∀ k P, HkIdx i k P → sigEv s k P = ev k P := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun s s' e1 e2 e3 => h2 trivial trivial ?_, fun s => ?_, fun j hj b ev h => ?_⟩
    · exact Prod.ext e1 (Prod.ext e2 (funext fun p => congrArg (algebraMap _ _) (e3 _ _ p.2)))
    · obtain ⟨-, ev, h, e⟩ := h1 (Set.mem_univ s)
      exact IsEigSys.congr h fun k P hk => (congrFun e ⟨(k, P), hk⟩).symm
    · obtain ⟨s, -, e⟩ := h3 (show (j, b, fun p : HkSet X i => ev p.1.1 p.1.2) ∈ eigSet Y i from ⟨hj, ev, h, rfl⟩)
      exact ⟨s, congrArg Prod.fst e, congrArg (fun t => t.2.1) e,
        fun k P hk => congrFun (congrArg (fun t => t.2.2) e) ⟨(k, P), hk⟩⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun s _ => ⟨Finset.mem_Icc.2 (X.jS_range i s), _, h2 s, rfl⟩, fun s _ s' _ e => ?_, ?_⟩
    · exact h1 s s' (congrArg Prod.fst e) (congrArg (fun t => t.2.1) e) fun k P hk =>
        IsFractionRing.injective (X.O i) (FractionRing (X.O i)) (congrFun (congrArg (fun t => t.2.2) e) ⟨(k, P), hk⟩)
    · rintro ⟨j, b, f⟩ ⟨hj, ev, h, e⟩
      obtain ⟨s, e1, e2, e3⟩ := h3 j hj b ev h
      exact ⟨s, trivial, Prod.ext e1 (Prod.ext e2 ((funext fun p => e3 _ _ p.2).trans e.symm))⟩

theorem SigTiedAt.bijOn (h : SigTiedAt Y i) : Set.BijOn (sysOf (X := X) (i := i)) Set.univ (eigSet Y i) :=
  bijOn_iff.2 ⟨h.inj, h.vec, h.all⟩

theorem SigTiedAt.goodE (h : SigTiedAt Y i) (s : X.Sig i) : goodE Y i s :=
  let ⟨x, h1, h2, h3⟩ := h.vec s
  ⟨x, h2, good_idempotent_fixes_mem_good_type_space h1, fun k P a b c d => h3 k P ⟨a, b, c, d⟩⟩

theorem SigTiedAt.mem' (h : SigTiedAt Y i) (s : X.Sig i) {k : ℕ} {P : PlE D.host} (hk : k ≤ D.R.r)
    (hP : IsSplitPl D.host P) (hS : P ∉ X.S0 i) : ∃ x : X.O0 i, algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P := by
  rcases Nat.eq_zero_or_pos k with rfl | h0
  · exact ⟨1, by rw [map_one, h.zero]⟩
  · exact h.mem s k P ⟨h0, hk, hP, hS⟩

theorem SigTiedAt.hEig_one (h : SigTiedAt Y i) (s : X.Sig i) {P : PlE D.host} (hP : IsSplitPl D.host P)
    (hS : P ∉ X.S0 i) {σ : G D.host.E N.Om} (hσ : IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ⁻¹) :
    X.hEig i s 1 P = algebraMap (X.O0 i) (X.O i)
      ((((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s σ).trace := by
  have h1 : 1 ≤ D.R.r := (GlobalTheory.GalChar.odd_r D.R).pos
  have := h.frob s P hS hP σ hσ 1 h1
  rw [Matrix.coeff_charpolyRev_eq_neg_trace, map_neg] at this
  simpa using this

end Sys

def SignatureCompatibility (D : D7) : Prop := SigTiedOf D.nexp

section Read

variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)

def fracMap (i : X.Tw) : FractionRing (X.O0 i) →+* FractionRing (X.O i) :=
  IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i)) (L := FractionRing (X.O i)) (X.O_inj i)

def embO (i : X.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (X.O i) := (fracMap X i).comp (embSide X i b)

theorem fracMap_algebraMap (i : X.Tw) (x : X.O0 i) :
    fracMap X i (algebraMap (X.O0 i) (FractionRing (X.O0 i)) x) =
      algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) x) :=
  by simp [fracMap, IsFractionRing.map]

structure CoefRead (i : X.Tw) (b : Bool) where

  F : Type
  [fld : Field F]

  e : ↥D.LL0 →+* F

  u : F →+* FractionRing (X.O i)

  toC : F →+* ℂ
  u_e : ∀ x, u (e x) = embO X i b x
  toC_e : ∀ x, toC (e x) = embLL0 D x

attribute [instance] CoefRead.fld

def CoefRead.base (i : X.Tw) (b : Bool) : CoefRead X i b :=
  { F := ↥D.LL0, e := RingHom.id _, u := embO X i b, toC := embLL0 D, u_e := fun _ => rfl, toC_e := fun _ => rfl }

variable {X} {i : X.Tw} {b : Bool}

def CoefRead.ofReading (ρ : Reading X i b) : CoefRead X i b :=
  { F := FractionRing (X.O0 i), e := embSide X i b, u := fracMap X i, toC := ρ.ι.toRingHom.comp ρ.κ
    u_e := fun _ => rfl, toC_e := ρ.read }

def CoefRead.ofFull (iC : FractionRing (X.O i) →+* ℂ) (h : ∀ x, iC (embO X i b x) = embLL0 D x) : CoefRead X i b :=
  { F := FractionRing (X.O i), e := embO X i b, u := RingHom.id _, toC := iC, u_e := fun _ => rfl, toC_e := h }

end Read

section Par

def IsRowPar (Rw : RowSide D) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  IsParam σ π ∧ ∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w

def liftIdx {j : ℕ} (hj : j ∈ Finset.Icc 1 D.R.m) : Fin D.R.m := ⟨j - 1, by have := Finset.mem_Icc.1 hj; omega⟩

variable (C : CharFrame D) (Rw : RowSide D) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X)

def EigParAt (i : X.Tw) : Prop :=
  ∀ (b : Bool) (τ : CoefRead X i b) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (ev : ℕ → PlE D.host → τ.F),
    IsEigSys Y i j b (fun k P => τ.u (ev k P)) →
    ∃ σ π, D.nd.goodRow σ ∧ D.what₂.isot j σ ≠ ⊥ ∧ IsRowPar Rw σ π ∧
      ∀ k P, HkIdx i k P → τ.toC (ev k P) = heckeVal (muBase C (X.l i) (liftIdx hj)) π k P

def EigParOf : Prop := ∀ i, X.NonzeroIndexPlace i → EigParAt C Rw Y i

variable {C Rw Y} {i : X.Tw} {b : Bool}

theorem liftIdx_jS (s : X.Sig i) : liftIdx (Finset.mem_Icc.2 (X.jS_range i s)) = jIdx s := rfl

theorem EigParAt.full (h : EigParAt C Rw Y i) (iC : FractionRing (X.O i) →+* ℂ)
    (hC : ∀ x, iC (embO X i b x) = embLL0 D x) {j : ℕ} (hj : j ∈ Finset.Icc 1 D.R.m)
    {ev : ℕ → PlE D.host → FractionRing (X.O i)} (hev : IsEigSys Y i j b ev) :
    ∃ σ π, D.nd.goodRow σ ∧ D.what₂.isot j σ ≠ ⊥ ∧ IsRowPar Rw σ π ∧
      ∀ k P, HkIdx i k P → iC (ev k P) = heckeVal (muBase C (X.l i) (liftIdx hj)) π k P :=
  h b (CoefRead.ofFull iC hC) j hj ev hev

theorem EigParAt.evidence (h : EigParAt C Rw Y i) (ρ : Reading X i b) {j : ℕ} (hj : j ∈ Finset.Icc 1 D.R.m)
    {ev : ℕ → PlE D.host → X.O0 i}
    (hev : IsEigSys Y i j b fun k P => algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) (ev k P))) :
    ∃ σ π, D.nd.goodRow σ ∧ D.what₂.isot j σ ≠ ⊥ ∧ IsRowPar Rw σ π ∧
      ∀ k P, HkIdx i k P → ρ.toC (ev k P) = heckeVal (muBase C (X.l i) (liftIdx hj)) π k P :=
  h b (CoefRead.ofReading ρ) j hj (fun k P => algebraMap (X.O0 i) (FractionRing (X.O0 i)) (ev k P))
    (hev.congr fun k P _ => (fracMap_algebraMap X i (ev k P)).symm)

theorem EigParAt.exists_row (h : EigParAt C Rw Y i) (hS : SigTiedAt Y i) (s : X.Sig i) (ρ : Reading X i (X.side i s)) :
    ∃ σ π, D.nd.goodRow σ ∧ D.what₂.isot (X.jS i s) σ ≠ ⊥ ∧ IsRowPar Rw σ π ∧
      ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
        algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P := by
  have H : ∀ k P, ∃ x : X.O0 i, HkIdx i k P → algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P := fun k P => by
    by_cases hk : HkIdx i k P
    · exact (hS.mem s k P hk).imp fun _ e _ => e
    · exact ⟨0, fun a => (hk a).elim⟩
  choose ev hev using H
  obtain ⟨σ, π, h1, h2, h3, h4⟩ := h.evidence ρ (Finset.mem_Icc.2 (X.jS_range i s)) (ev := ev)
    ((hS.vec s).congr fun k P hk => by rw [hev k P hk, sigEv])
  refine ⟨σ, π, h1, h2, h3, fun k P a c d => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | h0
  · exact ⟨1, by rw [map_one, hS.zero], by rw [map_one, GlobalTheory.Triple.heckeVal_zero]⟩
  · exact ⟨ev k P, hev k P ⟨h0, a, c, d⟩, h4 k P ⟨h0, a, c, d⟩⟩

end Par

def EigPar (D : D7) (C : CharFrame D) (Rw : RowSide D) : Prop := EigParOf C Rw D.nexp

section Res

variable (Rw : RowSide D)

def IsoInduces {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1

def TeichAt {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  ∀ k, l ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 → ∀ z : Zbar l,
    (z : Qbar l) = ι.symm (D.ntypes.teichC k x) → red z = D.ntypes.iota k v w x

def ResAt {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  IsoInduces ι w ∧ TeichAt ι w red ∧
    ∀ σ π (r : GalE D →* GL (Fin D.R.r) (Qbar l)), D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      IsGaloisRepOf D π l ι r → IsResidual ι r σ w red

end Res

def ResTied (D : D7) (Rw : RowSide D) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ (l : ℕ) [Fact l.Prime], D.what₂.places.resChar w = l →
    ∃ (ι : Qbar l ≃+* ℂ) (red : Zbar l →+* FbAt D w), ResAt Rw ι w red

section Bridge

theorem norm_int_le {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (a : L →+* Qbar l) (x : 𝓞 L) :
    ‖a x‖ ≤ 1 := by
  let v : Valuation (Qbar l) NNReal := NormedField.valuation
  have h : IsIntegral v.integer (a x) := (map_isIntegral_int a x.isIntegral_coe).tower_top
  have := (Valuation.integer.integers v).mem_of_integral h
  rw [Valuation.mem_integer_iff] at this
  exact_mod_cast this

theorem ball_of_int {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (a b : L →+* Qbar l)
    (h : ∀ x : 𝓞 L, ‖a x‖ < 1 ↔ ‖b x‖ < 1) (x : L) : ‖a x‖ ≤ 1 ↔ ‖b x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff
  | exact _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff
  | (apply _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff ..)

theorem val_pos_iff (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ≠ 0) :
    0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
  have h := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, AddValuation.map_one, D.val_eq w x hx, D.val_eq w _ (inv_ne_zero hx)] at h
  rw [D.val_eq w x hx, D.val_eq w _ (inv_ne_zero hx)]
  norm_cast at h ⊢
  omega

theorem IsoInduces.lt_iff {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {w : D.what₂.places.Pl} (h : IsoInduces ι w)
    (x : D.what₂.LL) : 0 < D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖ι.symm (D.what₂.embLL x)‖ := by simpa using hx
    rw [val_pos_iff w hx, h, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ h0, not_le]

theorem resChar_eq {w : D.what₂.places.Pl} {l : ℕ} (hl : l.Prime) (h : 0 < D.what₂.places.val w (l : D.what₂.LL)) :
    D.what₂.places.resChar w = l := by
  by_contra hne
  have hp := D.what₂.places.resChar_prime w
  have h1 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := fun n => by
    have hn : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ]; exact (D.what₂.places.val w).map_le_add ih (by simp)
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
    · simpa using hn n
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hn n
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hne)
  have e' : (a : D.what₂.LL) * (D.what₂.places.resChar w : ℕ) + (b : D.what₂.LL) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) e
  have := (D.what₂.places.val w).map_lt_add (g := 0) (x := (a : D.what₂.LL) * (D.what₂.places.resChar w : ℕ))
    (y := (b : D.what₂.LL) * l) (by rw [AddValuation.map_mul]; exact h1.trans_le (le_add_of_nonneg_left (hint a)))
    (by rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b)))
  rw [e', AddValuation.map_one] at this
  exact lt_irrefl _ this

variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}

theorem norm_lt_iff (ρ : Reading X i b) (z : FractionRing (X.O0 i)) :
    (∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = z) ↔ ‖ρ.κ z‖ < 1 := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.padicAlgCl_embedding_bounded_continuous (X.l i) (X.twistBaseCoefficientRing_isAdic i) (GlobalTheory.GalChar.toQ ρ.κ) ρ.κ_alg
  refine ⟨fun ⟨y, hy, e⟩ => e ▸ h2 y hy, fun h => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, zero_mem _, map_zero _⟩
  have h0 : 0 < ‖ρ.κ z‖ := by simpa using hz
  rcases ValuationRing.isInteger_or_isInteger (X.O0 i) z with ⟨y, e⟩ | ⟨y, e⟩
  · refine ⟨y, ?_, e⟩
    by_contra hy
    obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hy
    have e1 : ‖GlobalTheory.GalChar.toQ ρ.κ u‖ * ‖GlobalTheory.GalChar.toQ ρ.κ (u⁻¹ : (X.O0 i)ˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have e2 : ‖GlobalTheory.GalChar.toQ ρ.κ u‖ < 1 := by rw [← e] at h; exact h
    exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) e2 (h1 _)).ne e1
  · have := h1 y
    change ‖ρ.κ (algebraMap _ _ y)‖ ≤ 1 at this
    rw [e, map_inv₀, norm_inv, inv_le_one₀ h0] at this
    exact absurd h (not_lt.2 this)

theorem exists_reading_of_induces {b' : Bool} (ρ : Reading X i b') {ι : Qbar (X.l i) ≃+* ℂ} {w : D.what₂.places.Pl}
    (h : IsoInduces ι w) (hw : ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.κ (embSide X i b x)‖ ≤ 1) :
    ∃ ρ' : Reading X i b, ρ'.ι = ι := by
  obtain ⟨g, hg⟩ := GlobalTheory.EmbUnitBallConj.exists_conj (X.l i) ↥D.LL0 (ρ.κ.comp (embSide X i b))
    (ι.symm.toRingHom.comp (embLL0 D)) fun x => (hw x).symm.trans (h x)
  refine ⟨⟨(g : Qbar (X.l i) →+* Qbar (X.l i)).comp ρ.κ, ι, fun z => ?_, fun x => ?_⟩, rfl⟩
  · rw [RingHom.comp_apply, ρ.κ_alg]
    exact g.commutes _
  · exact (congrArg ι (hg x)).trans (ι.apply_symm_apply _)

theorem ResTied.exists_reading {Rw : RowSide D} (h : ResTied D Rw) (hs : ∀ x : ↥D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hi : X.NonzeroIndexPlace i) (b : Bool) :
    ∃ (ρ : Reading X i b) (w : D.what₂.places.Pl) (red : Zbar (X.l i) →+* FbAt D w), ρ.Induces w ∧ ResAt Rw ρ.ι w red := by
  obtain ⟨w, hw, H⟩ := hi
  obtain ⟨ρ⟩ := Reading.nonempty (X := X) i true
  have hl : 0 < D.what₂.places.val w ((X.l i : ℕ) : D.what₂.LL) := by
    have := (H ((X.l i : ℕ) : 𝓞 ↥D.LL0)).1 ((norm_lt_iff ρ _).2 (by
      rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, map_natCast,
        ← map_natCast (algebraMap ℚ_[X.l i] (Qbar (X.l i))), norm_algebraMap']
      exact Padic.norm_p_lt_one))
    simpa using this
  obtain ⟨ι, red, hι⟩ := h w hw (X.l i) (resChar_eq (X.lPrime i).out hl)
  have key : ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.κ (X.emb0 i x)‖ ≤ 1 := fun x =>
    (hι.1 x).trans (ball_of_int (ι.symm.toRingHom.comp (embLL0 D)) (ρ.κ.comp (X.emb0 i))
      (fun y => ((hι.1.lt_iff _).symm.trans (H y).symm).trans (norm_lt_iff ρ _)) x)
  cases b
  · obtain ⟨ι', red', hι'⟩ := h (D.what₂.places.conj w) (by rwa [D.what₂.muAt_conj]) (X.l i)
      (resChar_eq (X.lPrime i).out (by rwa [D.conj_val, star_natCast]))
    obtain ⟨ρ', rfl⟩ := exists_reading_of_induces (b := false) ρ hι'.1 fun x => by
      rw [D.conj_val]
      exact (key ⟨_, hs x⟩).trans (by rw [← X.restX_coefficientEmbedding_conj i x ⟨_, hs x⟩ rfl]; rfl)
    exact ⟨ρ', _, red', hι'.1, hι'⟩
  · obtain ⟨ρ', rfl⟩ := exists_reading_of_induces (b := true) ρ hι.1 key
    exact ⟨ρ', _, red, hι.1, hι⟩

end Bridge

namespace Model

open Formalism.MainNotions.BlochKatoReduction (scalGL)

variable (D)

def val (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host) : D.ntw.O0 i :=
  (D.R.r.choose k : D.ntw.O0 i) * Ring.inverse ((normV P : ℕ) : D.ntw.O0 i) ^ (D.R.t * k + k * (k - 1) / 2)

@[reducible] def tw : @NTw D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd :=
  { D.ntw with
    Sig := fun _ => Fin D.R.m × Bool
    finSig := fun _ => inferInstance
    jS := fun _ s => s.1.1 + 1
    jS_range := fun _ s => ⟨Nat.le_add_left _ _, s.1.2⟩
    side := fun _ s => s.2
    rhoS := fun i s => (scalGL D.R.r).comp (D.ntw.chi1 i (s.1.1 + 1) s.2)
    rhoS_cont := fun i s => (continuous_pi fun _ => D.ntw.twistCharacterFamily_continuous i (s.1.1 + 1) s.2).matrix_diagonal
    hEig := fun i _ k P => algebraMap (D.ntw.O0 i) (D.ntw.O i) (val D i k P)
    B := fun i _ _ => D.ntw.O i
    acgB := fun _ _ _ => inferInstance
    modB := fun _ _ _ => inferInstance
    freeB := fun _ _ _ => inferInstance
    finB := fun _ _ _ => inferInstance
    Theta := fun _ _ _ => ⊤
    ThetaPsi := fun _ _ _ _ _ _ => ⊤
    ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_top _).symm
    hk := fun i _ _ k P => algebraMap (D.ntw.O0 i) (D.ntw.O i) (val D i k P) • 1
    hk_zero := fun i _ _ P => by simp [val] }

open Classical in

@[reducible] def ex : @NExp D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D) :=
  { D.nexp with
    Fm := fun i _ _ => FractionRing (D.ntw.O i)
    acgFm := fun _ _ _ => inferInstance
    modFmK := fun _ _ _ => inferInstance
    modFmO := fun _ _ _ => inferInstance
    towFm := fun _ _ _ => inferInstance
    fdFm := fun _ _ _ => inferInstance
    actG := fun _ _ _ => 1
    U := ⊥
    psiU := fun _ _ => 1
    eAlg := fun _ _ => 1
    eLL0 := fun g => if 1 = g then 1 else 0
    eAlg_def := fun i b g => by
      by_cases h : 1 = g
      · subst h
        simp [MonoidAlgebra.one_def]
      · simp [MonoidAlgebra.one_def, h]
    eAlg_idem := fun _ _ => mul_one _
    eAlg_central := fun _ _ x => by rw [one_mul, mul_one]
    Bsup := fun i _ _ => LinearMap.range (Algebra.linearMap (D.ntw.O i) (FractionRing (D.ntw.O i)))
    Dat := fun _ _ _ => Empty
    th := fun _ _ _ a => a.elim
    lev := fun _ _ _ a => a.elim
    thPsi := fun _ _ _ _ _ _ a => a.elim
    thPsi_one := fun _ _ _ _ a => a.elim
    thU := fun _ _ _ _ _ a => a.elim
    twPsi := fun i _ _ k _ => TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i k) (FractionRing (D.ntw.O i)) 1
    twPsi_one := fun _ _ _ _ _ => rfl
    twDel := fun _ _ _ _ _ => 0
    thP := fun _ _ _ _ _ _ => 0
    hkF := fun i _ _ k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      (algebraMap (D.ntw.O0 i) (D.ntw.O i) (val D i k P)) • LinearMap.id
    embB := fun i _ _ => Algebra.linearMap (D.ntw.O i) (FractionRing (D.ntw.O i))
    embB_inj := fun i _ _ => IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
    eH := fun _ _ _ => 1
    eH_idem := fun _ _ _ => mul_one _ }

theorem mem_invariant_forms (i : D.ntw.Tw) (j : ℕ) (b : Bool) (x : (ex D).Fm i j b) : x ∈ V0 (ex D) i j b := by
  refine ⟨x, ?_, ?_⟩
  · simp only [Fm0, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro u
    exact sub_eq_zero.2 (one_smul (FractionRing (D.ntw.O i)) x).symm
  · have : eG (ex D) i j b = 1 := map_one _
    rw [this]
    rfl

theorem coeff_charpolyRev_scalar {A : Type} [CommRing A] (n k : ℕ) (c : A) :
    (c • (1 : Matrix (Fin n) (Fin n) A)).charpolyRev.coeff k = (-1) ^ k * (n.choose k : A) * c ^ k := by
  have e : (1 : Matrix (Fin n) (Fin n) A[X]) - (X : A[X]) • (c • (1 : Matrix (Fin n) (Fin n) A)).map C =
      Matrix.diagonal fun _ => 1 + C (-c) * X := by
    ext a b : 2
    by_cases h : a = b
    · subst h
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_one,
        Matrix.diagonal_apply_eq, map_neg]
      ring_nf
    · simp [h]
  have e2 : ((1 + C (-c) * X) ^ n : A[X]) = ((1 + X) ^ n : A[X]).comp (C (-c) * X) := by simp
  rw [Matrix.charpolyRev, e, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, e2,
    comp_C_mul_X_coeff, coeff_one_add_X_pow, neg_pow c]
  ring

theorem tmat_eq (i : D.ntw.Tw) (s : (tw D).Sig i) (g : GalE D) : Tmat (X := tw D) i s g = 1 := by
  change (((chiS (X := tw D) i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) •
    Matrix.scalar (Fin D.R.r) ((chiS (X := tw D) i s g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = 1
  rw [Matrix.scalar_apply, ← Matrix.diagonal_smul, ← Matrix.diagonal_one]
  congr 1
  funext a
  simp

theorem hkFrob (i : D.ntw.Tw) (s : (tw D).Sig i) : HkFrob (X := tw D) i s := by
  intro P hS _ σ hσ k _
  have h1 := (GlobalTheory.TripleGal.eps0_unram_frob D i P (fun h => hS (D.ntw.twistExcludedPlaces_contains_residueChar i h)) _ (D.nd.plOm.2 P)).2 σ⁻¹ hσ
  have h2 : Ring.inverse ((normV P : ℕ) : D.ntw.O0 i) = ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
    rw [← h1, Ring.inverse_unit, map_inv, inv_inv]
  have h3 : ((normV P : ℕ) : D.ntw.O0 i) * ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = 1 := by
    rw [← h1, map_inv, Units.inv_mul]
  rw [tmat_eq, coeff_charpolyRev_scalar]
  change (-1 : D.ntw.O i) ^ k * ((normV P : ℕ) : D.ntw.O i) ^ (k * (k - 1) / 2) *
    algebraMap (D.ntw.O0 i) (D.ntw.O i) (val D i k P) = algebraMap (D.ntw.O0 i) (D.ntw.O i)
      ((-1) ^ k * (D.R.r.choose k : D.ntw.O0 i) * (((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) ^ k)
  have h4 : (-1) ^ k * (D.R.r.choose k : D.ntw.O0 i) * (((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) ^ k =
      (-1) ^ k * ((normV P : ℕ) : D.ntw.O0 i) ^ (k * (k - 1) / 2) * val D i k P := by
    rw [val, h2, pow_add, pow_mul]
    linear_combination (-((-1) ^ k * (D.R.r.choose k : D.ntw.O0 i) *
      (((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) ^ k)) *
      ((mul_pow _ _ (k * (k - 1) / 2)).symm.trans ((congrArg (· ^ (k * (k - 1) / 2)) h3).trans (one_pow _)))
  rw [h4]
  simp

theorem sigTiedAt (i : D.ntw.Tw) : SigTiedAt (X := tw D) (ex D) i where
  inj s s' e1 e2 _ := Prod.ext (Fin.ext (Nat.succ_injective e1)) e2
  vec s := ⟨(1 : FractionRing (D.ntw.O i)), mem_invariant_forms D i _ _ _, one_ne_zero, fun _ _ _ => rfl⟩
  all j hj b ev := fun ⟨x, _, h0, h⟩ =>
    ⟨(liftIdx hj, b), Nat.sub_add_cancel (Finset.mem_Icc.1 hj).1, rfl, fun k P hk => smul_left_injective _ h0 (h k P hk)⟩
  zero s P := by change algebraMap _ _ (val D i 0 P) = 1; simp [val]
  mem s k P _ := ⟨val D i k P, rfl⟩
  ss s W _ := by
    obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
    refine ⟨W', fun g v hv => ?_, hW'⟩
    have : ((mapRep (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) ((tw D).rhoS i s) g : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (D.ntw.O0 i))) =
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) (chiS (X := tw D) i s g : (D.ntw.O0 i)ˣ) • 1 := by
      change (Matrix.diagonal fun _ => ((chiS (X := tw D) i s g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)).map _ = _
      rw [Matrix.diagonal_map (map_zero _), Matrix.smul_one_eq_diagonal]
    rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W'.smul_mem _ hv
  frob := hkFrob D i

theorem exists_sigTied : ∃ (X : NTw D.R D.host D.what₂ D.LL0 D.nd) (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X)
    (e : X.Tw ≃ D.ntw.Tw), (∀ i, X.NonzeroIndexPlace i ↔ D.ntw.NonzeroIndexPlace (e i)) ∧ (∀ i, Fintype.card (X.Sig i) = D.R.m * 2) ∧
      (∀ i, SigTiedAt Y i) ∧ SigTiedOf Y :=
  ⟨tw D, ex D, Equiv.refl _, fun _ => Iff.rfl, fun _ => by simp, sigTiedAt D, fun i _ => sigTiedAt D i⟩

example (i : D.ntw.Tw) (P : PlE D.host) :
    val D i 1 P = (D.R.r : D.ntw.O0 i) * Ring.inverse ((normV P : ℕ) : D.ntw.O0 i) ^ D.R.t := by simp [val]

variable {D}

theorem not_sigTiedAt_of_isEmpty {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X} {i : X.Tw}
    [IsEmpty (X.Sig i)] {j : ℕ} (hj : j ∈ Finset.Icc 1 D.R.m) {b ev} (h : IsEigSys Y i j b ev) : ¬ SigTiedAt Y i :=
  fun H => let ⟨s, _⟩ := H.all j hj b ev h; isEmptyElim s

theorem not_eigParAt (C : CharFrame D) (Rw : RowSide D) (h : ∀ σ, ¬ D.nd.goodRow σ) (i : D.ntw.Tw) :
    ¬ EigParAt C Rw (X := tw D) (ex D) i := fun H =>
  let s : (tw D).Sig i := (⟨0, by have := D.R.two_le_m; omega⟩, true)
  let ⟨σ, _, hσ, _⟩ := H.exists_row (sigTiedAt D i) s (Reading.nonempty (X := tw D) i true).some
  h σ hσ

end Model

end GlobalTheory.EigTie

end
