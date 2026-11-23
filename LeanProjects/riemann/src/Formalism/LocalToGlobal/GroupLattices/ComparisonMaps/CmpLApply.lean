import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ColSpanMap

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Classical
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (e : LL →+* G.Kf) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def IsVal (x : V) (i : G.comp) (L : G.P.Tup) (Q : XR G.P LL) : Prop :=
  Q ∈ VtupR G.P LL ∧
  ∀ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    ∀ (c : cls) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1) →
    ∀ z z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z →
    evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q) z = (S.chi κ : ℂ) * embV x c z'

def valC (x : V) (i : G.comp) (L : G.P.Tup) : XR G.P LL :=
  if h : ∃ Q, IsVal S emb embLL G A pos embV yc x i L Q then Classical.choose h else 0

def cmpC (x : V) : G.Fn :=
  fun i L => if G.P.IsLatTup L then MvPolynomial.map e (valC S emb embLL G A pos embV yc x i L) else 0

def ValEx : Prop := ∀ x i L, G.P.IsLatTup L → ∃ Q, IsVal S emb embLL G A pos embV yc x i L Q

def ValUniq : Prop := ∀ x i L Q Q', G.P.IsLatTup L → IsVal S emb embLL G A pos embV yc x i L Q →
  IsVal S emb embLL G A pos embV yc x i L Q' → Q = Q'

variable {S emb embLL G e A pos embV yc}

theorem valC_spec (hex : ValEx S emb embLL G A pos embV yc) (x : V) (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    IsVal S emb embLL G A pos embV yc x i L (valC S emb embLL G A pos embV yc x i L) := by
  unfold valC
  rw [dif_pos (hex x i L hL)]
  exact Classical.choose_spec (hex x i L hL)

theorem map_smul' {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) (Q : MvPolynomial ι R) :
    MvPolynomial.map f (a • Q) = f a • MvPolynomial.map f Q := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem IsVal.add {x y : V} {i : G.comp} {L : G.P.Tup} {Q Q' : XR G.P LL}
    (h : IsVal S emb embLL G A pos embV yc x i L Q) (h' : IsVal S emb embLL G A pos embV yc y i L Q') :
    IsVal S emb embLL G A pos embV yc (x + y) i L (Q + Q') := by
  refine ⟨Submodule.add_mem _ h.1 h'.1, fun g hg c γ hγ κ hp z z' hz => ?_⟩
  rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, Pi.add_apply, h.2 g hg c γ hγ κ hp z z' hz,
    h'.2 g hg c γ hγ κ hp z z' hz, mul_add]

theorem IsVal.smul {x : V} {i : G.comp} {L : G.P.Tup} {Q : XR G.P LL} (a : LL)
    (h : IsVal S emb embLL G A pos embV yc x i L Q) : IsVal S emb embLL G A pos embV yc (a • x) i L (a • Q) := by
  refine ⟨Submodule.smul_mem _ a h.1, fun g hg c γ hγ κ hp z z' hz => ?_⟩
  rw [map_smul', map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    h.2 g hg c γ hγ κ hp z z' hz, smul_eq_mul, smul_eq_mul]
  ring

def cmpL (hex : ValEx S emb embLL G A pos embV yc) (hu : ValUniq S emb embLL G A pos embV yc) : V →ₛₗ[e] G.Fn where
  toFun := cmpC S emb embLL G e A pos embV yc
  map_add' x y := by
    funext i L
    show cmpC S emb embLL G e A pos embV yc (x + y) i L =
      cmpC S emb embLL G e A pos embV yc x i L + cmpC S emb embLL G e A pos embV yc y i L
    unfold cmpC
    by_cases hL : G.P.IsLatTup L
    · simp only [hL, if_true]
      rw [← map_add]
      congr 1
      exact hu (x + y) i L _ _ hL (valC_spec hex _ i L hL) ((valC_spec hex x i L hL).add (valC_spec hex y i L hL))
    · simp [hL]
  map_smul' a x := by
    funext i L
    show cmpC S emb embLL G e A pos embV yc (a • x) i L = e a • cmpC S emb embLL G e A pos embV yc x i L
    unfold cmpC
    by_cases hL : G.P.IsLatTup L
    · simp only [hL, if_true]
      rw [← map_smul']
      congr 1
      exact hu (a • x) i L _ _ hL (valC_spec hex _ i L hL) ((valC_spec hex x i L hL).smul a)
    · simp [hL]

theorem cmpL_apply (hex : ValEx S emb embLL G A pos embV yc) (hu : ValUniq S emb embLL G A pos embV yc) (x : V) :
    cmpL (e := e) hex hu x = cmpC S emb embLL G e A pos embV yc x := rfl

def cmpC_tie (tE : Tau → E →+* LL) (hex : ValEx S emb embLL G A pos embV yc)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hchi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
      ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1) :
    CmpTie S emb embLL tE G e A pos (fun x => embV x) yc (cmpC S emb embLL G e A pos embV yc) where
  pos_emb := hpos
  val := valC S emb embLL G A pos embV yc
  val_cmp := fun x i L hL => by unfold cmpC; rw [if_pos hL]
  val_emb := fun x i L g hg => (valC_spec hex x i L
    (fun v => ⟨(g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)),
      (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit, hg v⟩)).2 g hg
  chi := hchi

end Formalism.L2.G.Cmp

end
