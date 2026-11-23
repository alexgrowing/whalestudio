import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MapNatActR
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.CastGLApply

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure LocAt (n : ℕ) {p : ℕ} (G : GAtP p) where

  rk : G.P.m + 1 = n

  pl : Fin G.P.nV ≃ {v : HeightOneSpectrum (𝓞 F) // ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}

  eQ : ∀ v, G.P.Qq v ≃+* (pl v).1.adicCompletion F

  spl : ∀ v, E ⊗[F] (pl v).1.adicCompletion F ≃+* (pl v).1.adicCompletion F × (pl v).1.adicCompletion F

  B : GL (Fin n) E

  yG : G.comp → GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)

  gamI : ∀ i, (G.lev i).Γ →* GL (Fin n) E

namespace LocAt

variable {F E} {n p : ℕ} {G : GAtP p} (A : LocAt F E n G)

def ph (v : Fin G.P.nV) : E ⊗[F] (A.pl v).1.adicCompletion F →+* (A.pl v).1.adicCompletion F :=
  (RingHom.fst _ _).comp (A.spl v).toRingHom

def phE (v : Fin G.P.nV) : E →+* (A.pl v).1.adicCompletion F :=
  (A.ph v).comp (inclE (F := F) ((A.pl v).1.adicCompletion F))

def iw (v : Fin G.P.nV) : E →+* G.P.Qq v := ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp (A.phE v)

def IsPt (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Prop :=
  (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) x = bc (prV (E := E) w) (A.yG i)) ∧
  ∀ v, bc (A.ph v) (bc (prV (E := E) (A.pl v).1) x) =
    bc (A.phE v) A.B * bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) (g v)) *
      (bc (A.phE v) A.B)⁻¹

def IsAway (i : G.comp) (γ : (G.lev i).Γ) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Prop :=
  (∀ v, bc (prV (E := E) (A.pl v).1) κ = 1) ∧
  ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) κ =
    bc (prV (E := E) w) ((A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i)

def ActB : Prop :=
  ∀ i v (γ : (G.lev i).Γ), castGL A.rk (G.P.Qq v) ((G.lev i).act v γ) = bc (A.iw v) (A.B⁻¹ * A.gamI i γ * A.B)

end LocAt

variable {F E}
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}

def crdB (emb : Tau → E →+* ℂ) (B : GL (Fin n) E) : Tau → Matrix (Fin n) (Fin n) ℂ :=
  atInf emb ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)

structure CmpTie (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ) (tE : Tau → E →+* LL)
    (G : GAtP p) (e : LL →+* G.Kf) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    {V cls : Type} (embV : V → cls → Frames (gramC J emb) → ℂ) (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (cmp : V → G.Fn) where

  pos_emb : ∀ v (s : Fin (G.P.n' v)) (x : E),
    e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x))

  val : V → G.comp → G.P.Tup → XR G.P LL

  val_cmp : ∀ x i L, G.P.IsLatTup L → cmp x i L = MvPolynomial.map e (val x i L)

  val_emb : ∀ x i (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    ∀ (c : cls) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1) →
    ∀ z z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z →
    evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL (val x i L)) z = (S.chi κ : ℂ) * embV x c z'

  chi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
    ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1

theorem CmpTie.val_rat {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ} {tE : Tau → E →+* LL}
    {G : GAtP p} {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
    {V cls : Type} {embV : V → cls → Frames (gramC J emb) → ℂ} {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    {cmp : V → G.Fn} (K : CmpTie S emb embLL tE G e A pos embV yc cmp) (x : V) (i : G.comp) (L : G.P.Tup)
    (hL : G.P.IsLatTup L) : cmp x i L ∈ Set.range (MvPolynomial.map e : XR G.P LL → G.P.Xsp) :=
  ⟨K.val x i L, (K.val_cmp x i L hL).symm⟩

end Formalism.L2.G.Cmp

end
