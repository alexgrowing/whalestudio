import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ApolarMonomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NatToBEquivariant

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.DeRham GlobalTheory.Cris
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

theorem mapLinear_coe {R S O : Type} [CommRing R] [CommRing S] [CommRing O] (f : R →+* S) {G B : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] {a : OAct O G} {b : OAct O B} {q : G ⟶ B}
    (hq : IsLinearHom a b q) (σ : O →+* S) (v : LieEig f a σ) :
    Lie.mapLinear (isLinearHom_pull f hq) v.1 = (eigMap f hq σ v).1 := rfl

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p}
  {P : PointsOfFlagModel.PtC Y C}

variable (C) in

theorem integers : (NormedField.valuation (K := ↥C.S)).Integers ↥(intO ↥C.S) :=
  ⟨Subtype.val_injective, fun x => x.2, fun {r} hr => ⟨⟨r, hr⟩, rfl⟩⟩

variable (P) in

def embP (τ : E →+* ℂ) : E →+* ↥C.S := P.fK.comp (embF c τ)

abbrev intEmb (φ : E →+* ↥C.S) : 𝓞 E →+* ↥(intO ↥C.S) := HTLat.embO (integers C) φ

theorem coe_intEmb_embP (τ : E →+* ℂ) (x : 𝓞 E) : (intEmb (embP P τ) x : ↥C.S) = P.emb τ x :=
  HTLat.algebraMap_embO (integers C) _ x

variable (A : DatAt Y P)

def ray : letI := H.starRing; Ray A.U.oD := letI := H.starRing; Classical.choice inferInstance

abbrev actGt := letI := H.starRing; (ray A).act

abbrev actAb := letI := H.starRing; Ray.actB A.U.oD

abbrev actT := letI := H.starRing; torAct A.U.D.toPre (𝓞 E)

def LieGt (τ : E →+* ℂ) : Type := LieEig A.f (actGt A) (intEmb (embP P τ))

instance (τ : E →+* ℂ) : AddCommGroup (LieGt A τ) :=
  inferInstanceAs (AddCommGroup (LieEig A.f (actGt A) (intEmb (embP P τ))))

instance (τ : E →+* ℂ) : Module ↥(intO ↥C.S) (LieGt A τ) :=
  inferInstanceAs (Module ↥(intO ↥C.S) (LieEig A.f (actGt A) (intEmb (embP P τ))))

def LieB (τ : E →+* ℂ) : Type := LieEig A.f (actAb A) (intEmb (embP P τ))

instance (τ : E →+* ℂ) : AddCommGroup (LieB A τ) :=
  inferInstanceAs (AddCommGroup (LieEig A.f (actAb A) (intEmb (embP P τ))))

instance (τ : E →+* ℂ) : Module ↥(intO ↥C.S) (LieB A τ) :=
  inferInstanceAs (Module ↥(intO ↥C.S) (LieEig A.f (actAb A) (intEmb (embP P τ))))

def LieT (τ : E →+* ℂ) : Type := LieEig A.f (actT A) (intEmb (embP P τ))

instance (τ : E →+* ℂ) : AddCommGroup (LieT A τ) :=
  inferInstanceAs (AddCommGroup (LieEig A.f (actT A) (intEmb (embP P τ))))

instance (τ : E →+* ℂ) : Module ↥(intO ↥C.S) (LieT A τ) :=
  inferInstanceAs (Module ↥(intO ↥C.S) (LieEig A.f (actT A) (intEmb (embP P τ))))

theorem q_lin : letI := H.starRing; IsLinearHom (actGt A) (actAb A) (ray A).q := letI := H.starRing; (ray A).q_linear

theorem i_lin : letI := H.starRing; IsLinearHom (actT A) (actGt A) (ray A).i := letI := H.starRing; (ray A).i_linear

def resB (τ : E →+* ℂ) : LieGt A τ →ₗ[↥(intO ↥C.S)] LieB A τ := eigMap A.f (q_lin A) _

def incT (τ : E →+* ℂ) : LieT A τ →ₗ[↥(intO ↥C.S)] LieGt A τ := eigMap A.f (i_lin A) _

abbrev Split : Type 1 := PolSplit ((actAb A).pullback (spMap A.f))
  (A.U.D.toPre.P.L.pull (pullback.fst A.U.D.toPre.P.A.hom (spMap A.f)))

open Classical in

def kapB (τ : E →+* ℂ) (u u' : LieB A τ) : ↥C.S :=
  if h : Nonempty (Split A) then kapAb h.some (HTLat.isSplitting_embO (integers C)) (embP P τ) u.1 u'.1 else 0

open Classical in

def kapGt (τ : E →+* ℂ) (u u' : LieGt A τ) : ↥C.S :=
  if h : Nonempty (Split A) then
    kapExt (isLinearHom_pull A.f (q_lin A)) h.some (HTLat.isSplitting_embO (integers C)) (embP P τ) u.1 u'.1
  else 0

open Classical in

theorem kapB_of (h : Nonempty (Split A)) (τ : E →+* ℂ) (u u' : LieB A τ) :
    kapB A τ u u' = kapAb h.some (HTLat.isSplitting_embO (integers C)) (embP P τ) u.1 u'.1 := dif_pos h

open Classical in

theorem kapGt_of (h : Nonempty (Split A)) (τ : E →+* ℂ) (u u' : LieGt A τ) : kapGt A τ u u' =
    kapExt (isLinearHom_pull A.f (q_lin A)) h.some (HTLat.isSplitting_embO (integers C)) (embP P τ) u.1 u'.1 :=
  dif_pos h

variable {T : Type} (emb : T × Bool → E →+* ℂ)

structure HarmAt : Type where

  a : ℕ

  b : ℕ

  n : ℕ

  u : ∀ t, Fin a → LieGt A (emb (t, false))

  w : ∀ t, Fin b → LieGt A (emb (t, true))

  P : Harm.Poly ↥C.S T a b (Fin n)
  harm : Harm.IsHarmonic P

abbrev xC : Sp ↥C.S ⟶ Sp A.R := spMap ((intO ↥C.S).subtype.comp A.f)

structure SecAt : Type where

  k : ℕ
  pos : 0 < k

  s : ∀ n, SecPw (xC A) A.U.U.LG.L n k

def SecAt.zero (k : ℕ) (hk : 0 < k) : SecAt A :=
  ⟨k, hk, fun _ => ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩⟩

theorem LG_eq : A.U.U.LG = A.t.PP := A.U.bundle

def HarmAt.pow (u : ∀ t, LieGt A (emb (t, false))) (n : ℕ) (t : T) (k : Fin n) (m : ℕ) : HarmAt A emb :=
  ⟨1, 0, n, fun t _ => u t, fun _ => Fin.elim0, MvPolynomial.X (Harm.xVar t 0 k) ^ m, fun _ _ b => b.elim0⟩

example (u : ∀ t, LieGt A (emb (t, false))) (w : ∀ t, LieGt A (emb (t, true))) (t : T) : HarmAt A emb :=
  ⟨1, 1, 2, fun t _ => u t, fun t _ => w t,
    MvPolynomial.X (Harm.xVar t 0 0) * MvPolynomial.X (Harm.yVar t 0 1), fun t' a b => by
      classical
      simp [Harm.laplacian_apply, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite (MvPolynomial.pderiv _)]⟩

variable {A emb}

namespace HarmAt

variable (Q : HarmAt A emb)

abbrev Row : Type := T × (Fin Q.a ⊕ Fin Q.b)

def vec : Q.Row → LieAt A.f (actGt A)
  | (t, .inl i) => (Q.u t i).1
  | (t, .inr j) => (Q.w t j).1

def chr (r : Q.Row) : 𝓞 E →+* ↥C.S := (embP P (emb (r.1, r.2.isRight))).comp (algebraMap (𝓞 E) E)

def col (k : Fin Q.n) (r : Q.Row) : Harm.Var T Q.a Q.b (Fin Q.n) := (r.1, r.2, k)

variable [Fintype T] [DecidableEq T]

def IsValA (s : SecAt A) (v : ↥C.S) : Prop :=
  letI := H.starRing
  ∃ u : Q.Row → (Over.mk ((epsR ↥(intO ↥C.S)).hom ≫ spMap A.f) ⟶ A.t.G),
    (∀ r, FormalPoint.IsPointOf A.U.U.toUnifPre ((ray A).Φ _ (tanPt A.f (Q.vec r))) (u r)) ∧
    IsVal A.t.act (xC A) Q.chr H.bar A.U.U.LG.L A.U.U.LG.rig
      (fun r => spMap (dualMap (intO ↥C.S).subtype) ≫ (u r).left) Q.col Q.P (s.s Q.n) v

def IsValG (s : SecAt A) (v : ↥C.S) : Prop :=
  letI := H.starRing
  IsValGt A.U.U.toUnifPre (ray A) (xC A) Q.chr
    (fun r => spMap (dualMap (intO ↥C.S).subtype) ≫ (tanPt A.f (Q.vec r)).left) Q.col Q.P (s.s Q.n) v

open Classical in

def evA (s : SecAt A) : ↥C.S := if h : ∃! v, Q.IsValA s v then h.choose else 0

open Classical in

def evGt (s : SecAt A) : ↥C.S := if h : ∃! v, Q.IsValG s v then h.choose else 1

theorem evA_eq {s : SecAt A} (h : ∃! v, Q.IsValA s v) {v : ↥C.S} : Q.evA s = v ↔ Q.IsValA s v := by
  rw [evA, dif_pos h]
  exact ⟨fun e => e ▸ h.choose_spec.1, fun e => (h.choose_spec.2 v e).symm⟩

theorem evGt_eq {s : SecAt A} (h : ∃! v, Q.IsValG s v) {v : ↥C.S} : Q.evGt s = v ↔ Q.IsValG s v := by
  rw [evGt, dif_pos h]
  exact ⟨fun e => e ▸ h.choose_spec.1, fun e => (h.choose_spec.2 v e).symm⟩

end HarmAt

variable (A)

theorem incT_exact (τ : E →+* ℂ) : Function.Injective (incT A τ) ∧ Function.Exact (incT A τ) (resB A τ) :=
  letI := H.starRing
  eigMap_exact A.f (i_lin A) (q_lin A) (ray A).isKernel _

theorem kapGt_eq (τ : E →+* ℂ) (u u' : LieGt A τ) : kapGt A τ u u' = kapB A τ (resB A τ u) (resB A τ u') := by
  classical
  by_cases h : Nonempty (Split A)
  · rw [kapGt_of A h, kapB_of A h, kapExt_eq]
    exact congrArg₂ (kapAb h.some _ _) (mapLinear_coe A.f (q_lin A) _ u) (mapLinear_coe A.f (q_lin A) _ u')
  · have e : ∀ v v', kapB A τ v v' = 0 := fun _ _ => dif_neg h
    exact (dif_neg h).trans (e _ _).symm

end Point

end GlobalTheory.RayEv
