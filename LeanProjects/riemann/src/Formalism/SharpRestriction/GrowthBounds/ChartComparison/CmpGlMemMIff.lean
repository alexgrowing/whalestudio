import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpCMemMIff
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CompFintype
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IsUnitDetBlockPreimage

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

abbrev gatCh {p : ℕ} (G : GAtP p) {α : Type} [Fintype α] (inc : α → G.comp) : GAtP p where
  O := G.O
  Kf := G.Kf
  P := G.P
  comp := α
  lev := fun a => G.lev (inc a)
  e := G.e

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}

structure Charts (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F)))
    (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ) (G : GAtP p) (V : Type) [AddCommGroup V] [Module LL V] where
  Cb : Type
  cmpt : Cb → Type
  [fin : ∀ β, Fintype (cmpt β)]
  eC : (Σ β, cmpt β) ≃ G.comp
  S : Cb → StepLevel F E σ J T f bad
  A : ∀ β, LocAt F E n (gatCh G fun a : cmpt β => eC ⟨β, a⟩)
  cls : Cb → Type
  yc : ∀ β, cls β → UPts σ J (FiniteAdeleRing (𝓞 F) F)
  embV : ∀ β, V →ₛₗ[embLL] (cls β → Frames (gramC J emb) → ℂ)

attribute [instance] Charts.fin

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ} {G : GAtP p} {V : Type} [AddCommGroup V] [Module LL V]

namespace Charts

variable (X : Charts σ J T f bad emb embLL G V) (e : LL →+* G.Kf) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)

abbrev gat (β : X.Cb) : GAtP p := gatCh G fun a : X.cmpt β => X.eC ⟨β, a⟩

def cmpB (β : X.Cb) (x : V) : (X.gat β).Fn :=
  cmpC (X.S β) emb embLL (X.gat β) e (X.A β) pos (X.embV β) (X.yc β) x

def cmpGl (x : V) : G.Fn := fun i L => X.cmpB e pos (X.eC.symm i).1 x (X.eC.symm i).2 L

theorem cmpGl_eC (x : V) (β : X.Cb) (a : X.cmpt β) (L : G.P.Tup) :
    X.cmpGl e pos x (X.eC ⟨β, a⟩) L = X.cmpB e pos β x a L := by
  unfold cmpGl
  rw [Equiv.symm_apply_apply]

structure Hyp (tE : Tau → E →+* LL) (β : X.Cb) : Prop where

  std : cT (σ : E →+* E) (X.A β).B.1 * J * (X.A β).B.1 = 1

  actB : (X.A β).ActB
  gamU : ∀ i (γ : ((X.gat β).lev i).Γ), (X.A β).gamI i γ ∈ UJ (σ : E →+* E) J
  away : ∀ i (γ : ((X.gat β).lev i).Γ), ∃ κ : (X.S β).U, (X.A β).IsAway i γ κ.1

  ex : ValEx (X.S β) emb embLL (X.gat β) (X.A β) pos (X.embV β) (X.yc β)

  pos_emb : ∀ v (s : Fin (G.P.n' v)) (x : E),
    e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) ((X.A β).iw v x))

  chi : ∀ i (γ : ((X.gat β).lev i).Γ) (κ : (X.S β).U), (X.A β).IsAway i γ κ.1 →
    ∃ r : LL, embLL r = ((X.S β).chi κ : ℂ) ∧ algebraMap G.O G.Kf (((X.gat β).lev i).χ γ : G.O) * e r = 1

  ptEx : PtEx (X.S β) (X.gat β) (X.A β) (X.yc β)
  ptAll : PtAll (X.S β) (X.gat β) (X.A β) (X.yc β)

variable {X e pos}

theorem Hyp.uniq {tE : Tau → E →+* LL} {β : X.Cb} (H : X.Hyp e pos tE β)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) :
    ValUniq (X.S β) emb embLL (X.gat β) (X.A β) pos (X.embV β) (X.yc β) :=
  valUniq_of hc (Formalism.L2.G.evInj_pf emb (X.gat β) (X.A β) pos) H.ptEx

def cmpBL {tE : Tau → E →+* LL} {β : X.Cb} (H : X.Hyp e pos tE β) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) :
    V →ₛₗ[e] (X.gat β).Fn :=
  cmpL (G := X.gat β) (e := e) H.ex (H.uniq hc)

theorem cmpB_add {tE : Tau → E →+* LL} {β : X.Cb} (H : X.Hyp e pos tE β) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x y : V) : X.cmpB e pos β (x + y) = X.cmpB e pos β x + X.cmpB e pos β y := (cmpBL H hc).map_add x y

theorem cmpB_smul {tE : Tau → E →+* LL} {β : X.Cb} (H : X.Hyp e pos tE β) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (a : LL) (x : V) : X.cmpB e pos β (a • x) = e a • X.cmpB e pos β x := (cmpBL H hc).map_smulₛₗ a x

def cmpGlL (tE : Tau → E →+* LL) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (H : ∀ β, X.Hyp e pos tE β) :
    V →ₛₗ[e] G.Fn where
  toFun := X.cmpGl e pos
  map_add' x y := by
    funext i L
    exact congrFun (congrFun (cmpB_add (H (X.eC.symm i).1) hc x y) (X.eC.symm i).2) L
  map_smul' a x := by
    funext i L
    exact congrFun (congrFun (cmpB_smul (H (X.eC.symm i).1) hc a x) (X.eC.symm i).2) L

theorem cmpGlL_apply (tE : Tau → E →+* LL) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (H : ∀ β, X.Hyp e pos tE β)
    (x : V) : cmpGlL tE hc H x = X.cmpGl e pos x := rfl

theorem cmpGl_rat (x : V) : RatFn G e (X.cmpGl e pos x) := fun i L =>
  cmpC_rat (S := X.S (X.eC.symm i).1) (G := X.gat (X.eC.symm i).1) (e := e) (A := X.A (X.eC.symm i).1) (pos := pos)
    (embV := X.embV (X.eC.symm i).1) (yc := X.yc (X.eC.symm i).1) x (X.eC.symm i).2 L

theorem embV_zero_of {tE : Tau → E →+* LL} {β : X.Cb} (H : X.Hyp e pos tE β)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (x : V) (hx : X.cmpB e pos β x = 0) : X.embV β x = 0 := by
  funext c z'
  obtain ⟨i, g, γ, κ, hγ, hpt⟩ := H.ptAll c
  obtain ⟨z, hz⟩ := frames_tr' emb hc γ hγ z'
  let L : G.P.Tup := fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))
  have hL : G.P.IsLatTup L := fun v => ⟨_, (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit, rfl⟩
  have h0 : MvPolynomial.map e (valC (X.S β) emb embLL (X.gat β) (X.A β) pos (X.embV β) (X.yc β) x i L) = 0 := by
    have := congrFun (congrFun hx i) L
    unfold cmpB cmpC at this
    rwa [if_pos hL] at this
  have h1 : valC (X.S β) emb embLL (X.gat β) (X.A β) pos (X.embV β) (X.yc β) x i L = 0 :=
    MvPolynomial.map_injective e e.injective (by rw [h0, map_zero])
  have h2 := (valC_spec H.ex x i L hL).2 g (fun _ => rfl) c γ hγ κ hpt z z' hz
  rw [h1, map_zero, map_zero] at h2
  have h3 : ((X.S β).chi κ : ℂ) ≠ 0 := ((X.S β).chi κ).ne_zero
  exact (mul_eq_zero.1 h2.symm).resolve_left h3

theorem cmpGl_inj (tE : Tau → E →+* LL) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (H : ∀ β, X.Hyp e pos tE β)
    (hinj : ∀ x : V, (∀ β, X.embV β x = 0) → x = 0) : Function.Injective (cmpGlL tE hc H) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => hinj x fun β => embV_zero_of (H β) hc x ?_
  funext a L
  rw [← X.cmpGl_eC e pos x β a L]
  exact congrFun (congrFun hx (X.eC ⟨β, a⟩)) L

theorem mem_M_iff (Fn : G.Fn) : Fn ∈ G.M ↔ ∀ β, (fun a : X.cmpt β => Fn (X.eC ⟨β, a⟩)) ∈ (X.gat β).M := by
  unfold GAtP.M GAtP.funMod
  simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h β a
    exact h (X.eC ⟨β, a⟩)
  · intro h i
    obtain ⟨⟨β, a⟩, rfl⟩ := X.eC.surjective i
    exact h β a

theorem cmpGl_mem_M_iff (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (H : ∀ β, X.Hyp e pos tE β)
    (IntAt : ∀ β, V → X.cls β → Prop)
    (hloc : ∀ β, ValIntAt (X.S β) emb embLL (X.gat β) e (X.A β) pos (X.embV β) (X.yc β) (IntAt β)) (x : V) :
    X.cmpGl e pos x ∈ G.M ↔ ∀ β c, IntAt β x c := by
  rw [X.mem_M_iff]
  refine forall_congr' fun β => ?_
  have h1 : (fun a : X.cmpt β => X.cmpGl e pos x (X.eC ⟨β, a⟩)) =
      cmpC (X.S β) emb embLL (X.gat β) e (X.A β) pos (X.embV β) (X.yc β) x := by
    funext a L
    exact X.cmpGl_eC e pos x β a L
  rw [h1]
  exact cmpC_mem_M_iff tE htE hc (H β).std (H β).actB (H β).ex (H β).pos_emb (H β).chi
    (Formalism.L2.G.evInj_pf emb (X.gat β) (X.A β) pos) (H β).ptEx (H β).ptAll (H β).gamU (H β).away (IntAt β) (hloc β) x

end Charts

end Formalism.MainNotions.G.CmpJ

end
