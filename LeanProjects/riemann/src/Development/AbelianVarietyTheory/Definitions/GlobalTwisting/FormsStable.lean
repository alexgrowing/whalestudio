import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

structure LocF (q : ℕ) (F : Type) [Field F] where
  K : Type
  [fld : Field K]
  O : Subring K
  frac : ∀ x : K, x ∈ O ∨ x⁻¹ ∈ O
  q_ne : (q : K) ≠ 0
  sep : ∀ x : K, x ≠ 0 → ∃ (n : ℤ) (y : K), y ∈ O ∧ y⁻¹ ∈ O ∧ x = (q : K) ^ n * y
  res : O →+* F
  res_surj : Function.Surjective res
  res_ker : ∀ x : O, res x = 0 ↔ ∃ y : O, (x : K) = (q : K) * y

attribute [instance] LocF.fld

namespace LocF

variable {q : ℕ} {F : Type} [Field F] (Lc : LocF q F) (n : ℕ)

def std : Submodule Lc.O (Fin n → Lc.K) := Submodule.pi Set.univ fun _ => (1 : Submodule Lc.O Lc.K)

def IsFrame (h : GL (Fin n) Lc.K) (Λ : Submodule Lc.O (Fin n → Lc.K)) : Prop :=
  ∀ x, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) x ∈ Λ ↔ x ∈ Lc.std n

@[ext] structure Raw where
  L : Submodule Lc.O (Fin n → Lc.K)
  f : (Fin n → Lc.K) → F

variable {Lc n}

structure Raw.Ok (p : Raw Lc n) : Prop where
  lat : ∃ h, Lc.IsFrame n h p.L
  add : ∀ x ∈ p.L, ∀ y ∈ p.L, p.f (x + y) = p.f x + p.f y
  smul : ∀ (a : Lc.O), ∀ x ∈ p.L, p.f (a • x) = Lc.res a * p.f x
  off : ∀ x, x ∉ p.L → p.f x = 0
  ne : ∃ x, p.f x ≠ 0

variable (Lc n) in

def PP : Type := {p : Raw Lc n // p.Ok}

def PP.ker (p : PP Lc n) : Set (Fin n → Lc.K) := {x | x ∈ p.1.L ∧ p.1.f x = 0}

def PP.IsAct (g : GL (Fin n) Lc.K) (p p' : PP Lc n) : Prop :=
  ∀ x, (Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x ∈ p'.1.L ↔ x ∈ p.1.L) ∧
    p'.1.f (Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x) = p.1.f x

def PP.IsUp (p : PP Lc n) (x : Fin n → Lc.K) (p₁ : PP Lc n) : Prop :=
  x ∈ p.1.L ∧ p₁.ker = (p.1.L : Set (Fin n → Lc.K)) ∧ p₁.1.f (((q : Lc.K))⁻¹ • x) = 1

def PP.IsDil (a : F) (p p' : PP Lc n) : Prop := p'.1.L = p.1.L ∧ ∀ x, p'.1.f x = a * p.1.f x

def PP.Inc (p p₁ : PP Lc n) : Prop := ∃ x, p.1.f x = 1 ∧ p.IsUp x p₁

example (p : PP Lc n) : p.IsAct 1 p := fun x => by simp

example (p : PP Lc n) : PP.IsDil 1 p p := ⟨rfl, fun x => (one_mul _).symm⟩

example (p : PP Lc n) : ¬ p.Inc p := by
  rintro ⟨x, h1, h2, h3, -⟩
  have : x ∈ p.ker := by rw [h3]; exact h2
  exact one_ne_zero (h1.symm.trans this.2)

end LocF

variable {D : D7} {u : D.what₂.Word}

structure PtModel (X : Ch D u) (i : ℕ) where
  Lc : ∀ v : X.A.vT, LocF X.A.T (X.A.Fv v)
  G : Type
  [grp : Group G]
  Z : Type
  [actP : MulAction G (Z × ∀ v, LocF.PP (Lc v) (D.R.N i))]
  loc : ∀ v, G →* GL (Fin (D.R.N i)) (Lc v).K
  smul_fst : ∀ (g : G) (p p' : Z × ∀ v, LocF.PP (Lc v) (D.R.N i)), p.1 = p'.1 → (g • p).1 = (g • p').1
  smul_snd : ∀ (g : G) (p : Z × ∀ v, LocF.PP (Lc v) (D.R.N i)) v, LocF.PP.IsAct (loc v g) (p.2 v) ((g • p).2 v)
  rep : X.C.cls i → Z × ∀ v, LocF.PP (Lc v) (D.R.N i)
  rep_surj : ∀ p, ∃ (c : X.C.cls i) (g : G), g • rep c = p
  rep_inj : ∀ (c c' : X.C.cls i) (g : G), g • rep c = rep c' → c = c'
  card_stab : ∀ c, Nat.card (X.C.stab i c) = Nat.card (MulAction.stabilizer G (rep c))
  Val : Submodule ℂ (X.C.Y i → ℂ)
  act : G →* Module.End ℂ Val
  H : Val →ₗ⋆[ℂ] Val →ₗ[ℂ] ℂ
  H_act : ∀ g y y', H (act g y) (act g y') = H y y'
  H_pos : ∀ y, y ≠ 0 → 0 < (H y y).re
  H_symm : ∀ y y', H y y' = starRingEnd ℂ (H y' y)
  ipV_eq : ∀ c (y y' : Val), X.fm.ipV i c y y' = H y y'
  mem_Fi : ∀ φ, φ ∈ X.fm.Fi i ↔ ∀ c, ∃ y : Val, φ c = y ∧ ∀ g : G, g • rep c = rep c → act g y = y
  piL : ∀ v c, (Fin (D.R.N i) → (Lc v).K) → X.fm.lv i v c
  piL_add : ∀ v c, ∀ x ∈ ((rep c).2 v).1.L, ∀ y ∈ ((rep c).2 v).1.L, piL v c (x + y) = piL v c x + piL v c y
  piL_smul : ∀ v c (a : (Lc v).O), ∀ x ∈ ((rep c).2 v).1.L, piL v c (a • x) = (Lc v).res a • piL v c x
  piL_surj : ∀ v c y, ∃ x ∈ ((rep c).2 v).1.L, piL v c x = y
  piL_f : ∀ v c, ∀ x ∈ ((rep c).2 v).1.L, X.fm.fv i v c (piL v c x) = ((rep c).2 v).1.f x
  piK : ∀ v c, (Fin (D.R.N i) → (Lc v).K) → X.fm.lk i v c
  piK_add : ∀ v c, ∀ x ∈ ((rep c).2 v).ker, ∀ y ∈ ((rep c).2 v).ker, piK v c (x + y) = piK v c x + piK v c y
  piK_smul : ∀ v c (a : (Lc v).O), ∀ x ∈ ((rep c).2 v).ker, piK v c (a • x) = (Lc v).res a • piK v c x
  piK_surj : ∀ v c y, ∃ x ∈ ((rep c).2 v).ker, piK v c x = y
  piK_te : ∀ v c e, ((rep c).2 v).1.f e = 1 → piK v c ((X.A.T : (Lc v).K) • e) = X.fm.te i v c
  up_eq : ∀ v c x p₁, ((rep c).2 v).1.f x = 1 → ((rep c).2 v).IsUp x p₁ →
    ∃ g : G, g • rep (X.fm.up i v c (piL v c x)) = ((rep c).1, Function.update (rep c).2 v p₁) ∧
      ∀ y : Val, X.fm.upT i v c (piL v c x) y = act g y
  dn_eq : ∀ v c (γ : Module.Dual (X.A.Fv v) (X.fm.lk i v c)) (p₀ : LocF.PP (Lc v) (D.R.N i)),
    (p₀.1.L : Set _) = ((rep c).2 v).ker → (∀ x ∈ p₀.1.L, p₀.1.f x = γ (piK v c x)) →
    ∃ g : G, g • rep (X.fm.dn i v c γ) = ((rep c).1, Function.update (rep c).2 v p₀) ∧
      ∀ y : Val, X.fm.dnT i v c γ y = act g y
  dil_eq : ∀ v c (a : (X.A.Fv v)ˣ) p', LocF.PP.IsDil (a : X.A.Fv v) ((rep c).2 v) p' →
    ∃ g : G, g • rep (X.fm.dil i v a c) = ((rep c).1, Function.update (rep c).2 v p') ∧
      ∀ y : Val, X.fm.dilT i v a c y = act g y

attribute [instance] PtModel.grp PtModel.actP

namespace PtModel

variable {X : Ch D u} {i : ℕ} (M : PtModel X i)

abbrev Pt : Type := M.Z × ∀ v, LocF.PP (M.Lc v) (D.R.N i)

def IsExt (φ : Fn X i) (Φ : M.Pt → M.Val) : Prop :=
  (∀ c, φ c = Φ (M.rep c)) ∧ ∀ (g : M.G) p, Φ (g • p) = M.act g (Φ p)

def Inc (v : X.A.vT) (p p₁ : M.Pt) : Prop :=
  p₁.1 = p.1 ∧ (∀ v', v' ≠ v → p₁.2 v' = p.2 v') ∧ (p.2 v).Inc (p₁.2 v)

def Dil (v : X.A.vT) (a : X.A.Fv v) (p p' : M.Pt) : Prop :=
  p'.1 = p.1 ∧ (∀ v', v' ≠ v → p'.2 v' = p.2 v') ∧ LocF.PP.IsDil a (p.2 v) (p'.2 v)

def WeakApprox : Prop := ∀ p : M.Pt, ∃ g : M.G, ∀ v, ((g • p).2 v).1.L = (M.Lc v).std (D.R.N i)

end PtModel

abbrev LevTie (X : Ch D u) : Type 1 := ∀ i, i ≤ D.R.m → PtModel X i

section

variable {D : D7} {u : D.what₂.Word}

namespace PtModel

variable {X : Ch D u} {i : ℕ} (M : PtModel X i)

def lamT (X : Ch D u) (i : ℕ) (τ : D.what₂.Tau) : DomWeight (D.R.N i) :=
  wSh (X.fm.lam i τ) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)

def IsFrameS (v : X.A.vT) (h : GL (Fin (D.R.N i)) (M.Lc v).K) (s : Set (Fin (D.R.N i) → (M.Lc v).K)) : Prop :=
  ∀ x, Matrix.mulVec (h : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (M.Lc v).K) x ∈ s ↔ x ∈ (M.Lc v).std (D.R.N i)

structure Coord where
  co : M.Val →ₗ[ℂ] MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ
  co_inj : Function.Injective co
  co_range : LinearMap.range co = CSpan (X.fm.lam i)
  j : D.what₂.places.Pl → ∀ v, (M.Lc v).K →+* D.what₂.LL
  j_int : ∀ w, OverT X w → ∀ v x, j w v x ∈ Ow D w ↔ x ∈ (M.Lc v).O
  Woff : D.what₂.places.Pl → M.Z → AddSubgroup M.Val

variable {M} (Co : M.Coord)

def Coord.mv (w : D.what₂.places.Pl) (h : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K) (τ : D.what₂.Tau) : GL (Fin (D.R.N i)) ℂ :=
  let v := (X.fm.tauOf w).symm τ
  let g : GL (Fin (D.R.N i)) ℂ := Matrix.GeneralLinearGroup.map (D.what₂.embLL.comp (Co.j w v)) (h v)
  if X.fm.seenP w then g else inside₂ ℂ _ g

def Coord.mov (w : D.what₂.places.Pl) (h : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ :=
  blk fun τ => roundAct ℂ _ (lamT X i τ) (Co.mv w h τ)

def Coord.valB (w : D.what₂.places.Pl) (V : Finset X.A.vT) (p : M.Pt) : Set M.Val :=
  {y | ∃ h : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K,
    (∀ v, M.IsFrameS v (h v) (if X.fm.seenP w = true ∧ v ∉ V then ((p.2 v).1.L : Set _) else (p.2 v).ker)) ∧
    ∃ z ∈ IntSpan D w (X.fm.lam i), Co.co y = Co.mov w h z}

def ValIn (M : PtModel X i) (W : M.Pt → Set M.Val) (φ : Fn X i) : Prop := ∀ c, ∃ y ∈ W (M.rep c), φ c = y

structure Coord.Ok : Prop where
  act_co : ∀ w, OverT X w → ∀ g : M.G, ∃ (ζ : D.what₂.LL) (k : ℕ), 0 < k ∧ ζ ^ k = 1 ∧
    ∀ y, Co.co (M.act g y) = D.what₂.embLL ζ • Co.mov w (fun v => M.loc v g) (Co.co y)
  S_on : ∀ w, OverT X w → ∀ φ ∈ X.fm.Fi i,
    (∃ x ∈ X.fm.S i w, X.fm.emb i x = φ) ↔ M.ValIn (Co.valB w ∅) φ
  B_on : ∀ w, OverT X w → X.fm.seenP w = true → ∀ v, ∀ φ ∈ X.fm.Fi i,
    (∃ x ∈ X.fm.Bw i w v, X.fm.emb i x = φ) ↔ M.ValIn (Co.valB w {v}) φ
  off_act : ∀ w, ¬ OverT X w → ∀ (g : M.G) (p : M.Pt) y, M.act g y ∈ Co.Woff w (g • p).1 ↔ y ∈ Co.Woff w p.1
  S_off : ∀ w, ¬ OverT X w → ∀ φ ∈ X.fm.Fi i,
    (∃ x ∈ X.fm.S i w, X.fm.emb i x = φ) ↔ M.ValIn (fun p => (Co.Woff w p.1 : Set M.Val)) φ

end PtModel

def ValTie {X : Ch D u} (Lv : LevTie X) : Type := ∀ i (h : i ≤ D.R.m), {Co : (Lv i h).Coord // Co.Ok}

end
section

variable {D : D7} {u : D.what₂.Word}

structure KerPt {X : Ch D u} {i : ℕ} (M : PtModel X i) (M' : PtModel X (i + 1)) where
  k : M.Pt → M'.Pt → (M.Val →ₗ[ℂ] M'.Val)
  src : ∀ (g : M.G) p p' y, k (g • p) p' (M.act g y) = k p p' y
  Kmap_eq : ∀ c c' (y : M.Val), X.C.Kmap i c c' y = k (M.rep c) (M'.rep c') y

namespace KerPt

variable {X : Ch D u} {i : ℕ} {M : PtModel X i} {M' : PtModel X (i + 1)} (K : KerPt M M')

def TgtEq : Prop := ∀ (g' : M'.G) p p' y, K.k p (g' • p') y = M'.act g' (K.k p p' y)

def DilLaw : Prop :=
  ∀ v (a : (X.A.Fv v)ˣ) p q p' q', M.Dil v a p q → M'.Dil v a p' q' → K.k q q' = K.k p p'

def UKLaw : Prop :=
  ∀ v p p' y, (∑ᶠ p₁ ∈ {p₁ | M'.Inc v p' p₁}, K.k p p₁ y) =
    ((X.A.T : ℂ) ^ ((D.R.t + 1) / 2)) • ∑ᶠ p₀ ∈ {p₀ | M.Inc v p₀ p}, K.k p₀ p' y

def IntBar (Co : M.Coord) (Co' : M'.Coord) : Prop :=
  ∀ w, OverT X w → X.fm.seenP w = false → ∀ p p', ∀ y ∈ Co.valB w ∅ p,
    ∃ y' ∈ Co'.valB w ∅ p', K.k p p' y = ((X.A.T : ℂ) ^ (D.R.f * ((D.R.t + 1) / 2))) • y'

def IntP (Co : M.Coord) (Co' : M'.Coord) : Prop :=
  ∀ w, OverT X w → X.fm.seenP w = true → ∀ p p', ∀ y ∈ Co.valB w ∅ p,
    ((X.A.T : ℂ) ^ ((D.R.f * D.R.N i : ℕ) + ∑ τ, X.C.sDiv i τ : ℤ)) • K.k p p' y ∈ Co'.valB w Finset.univ p'

end KerPt

def KerTie {X : Ch D u} (Lv : LevTie X) : Type :=
  ∀ i (h : i < D.R.m), KerPt (Lv i h.le) (Lv (i + 1) h)

structure KerLaws {X : Ch D u} {Lv : LevTie X} (Vt : ValTie Lv) (Kt : KerTie Lv) : Prop where
  tgt : ∀ i h, (Kt i h).TgtEq
  dil : ∀ i h, (Kt i h).DilLaw
  uk : ∀ i h, (Kt i h).UKLaw
  bar : ∀ i h, (Kt i h).IntBar (Vt i h.le).1 (Vt (i + 1) h).1
  intP : ∀ i h, (Kt i h).IntP (Vt i h.le).1 (Vt (i + 1) h).1

def StabUnit (X : Ch D u) : Prop := ∀ i, i ≤ D.R.m → ∀ c, ¬ X.A.T ∣ Nat.card (X.C.stab i c)

end
section

variable {D : D7} {u : D.what₂.Word}

def fnl {F V : Type} [Field F] [AddCommGroup V] [Module F V] {n : ℕ} (e : V ≃ₗ[F] (Fin n → F)) (f : Fin n → F) :
    Module.Dual F V :=
  (∑ a, f a • LinearMap.proj a : (Fin n → F) →ₗ[F] F) ∘ₗ e.toLinearMap

structure Unf (X : Ch D u) (i : ℕ) (v : X.A.vT) where
  Lc : Type
  [fin : Fintype Lc]
  nL : Lc → ℕ
  cf : Lc → (Fin (D.R.N i) → X.A.Fv v) → X.C.cls i
  cx : Lc → (Fin (D.R.N i) → X.A.Fv v) → X.C.cls i
  tf : Lc → (Fin (D.R.N i) → X.A.Fv v) → ((X.C.Y i → ℂ) →ₗ[ℂ] (X.C.Y i → ℂ))
  tx : Lc → (Fin (D.R.N i) → X.A.Fv v) → ((X.C.Y i → ℂ) →ₗ[ℂ] (X.C.Y i → ℂ))
  ipL : Lc → (X.C.Y i → ℂ) →ₗ⋆[ℂ] (X.C.Y i → ℂ) →ₗ[ℂ] ℂ

attribute [instance] Unf.fin

namespace Unf

variable {X : Ch D u} {i : ℕ} {v : X.A.vT} (s : Unf X i v)

def NLPos : Prop := ∀ Λ, 0 < s.nL Λ

def CfSurj : Prop := ∀ c, ∃ Λ f, f ≠ 0 ∧ s.cf Λ f = c

def CxSurj : Prop := ∀ c, ∃ Λ x, x ≠ 0 ∧ s.cx Λ x = c

def UpTie : Prop := ∀ Λ f, f ≠ 0 → ∃ e : X.fm.lv i v (s.cf Λ f) ≃ₗ[X.A.Fv v] (Fin (D.R.N i) → X.A.Fv v),
  X.fm.fv i v (s.cf Λ f) = fnl e f ∧
  ∀ φ ∈ X.fm.Fi i, ∀ x : X.fm.lv i v (s.cf Λ f), X.fm.fv i v (s.cf Λ f) x = 1 →
    s.tf Λ f (X.fm.upT i v (s.cf Λ f) x (φ (X.fm.up i v (s.cf Λ f) x))) = s.tx Λ (e x) (φ (s.cx Λ (e x)))

def DnTie : Prop := ∀ Λ x, x ≠ 0 → ∃ e : X.fm.lk i v (s.cx Λ x) ≃ₗ[X.A.Fv v] (Fin (D.R.N i) → X.A.Fv v),
  e (X.fm.te i v (s.cx Λ x)) = x ∧
  ∀ φ ∈ X.fm.Fi i, ∀ f : Fin (D.R.N i) → X.A.Fv v, f ≠ 0 →
    s.tx Λ x (X.fm.dnT i v (s.cx Λ x) (fnl e f) (φ (X.fm.dn i v (s.cx Λ x) (fnl e f)))) = s.tf Λ f (φ (s.cf Λ f))

def DilF : Prop := ∀ Λ f, f ≠ 0 → ∀ a : (X.A.Fv v)ˣ, ∀ φ ∈ X.fm.Fi i,
  s.tf Λ f (X.fm.dilT i v a (s.cf Λ f) (φ (X.fm.dil i v a (s.cf Λ f)))) =
    s.tf Λ ((a : X.A.Fv v) • f) (φ (s.cf Λ ((a : X.A.Fv v) • f)))

def DilX : Prop := ∀ Λ x, x ≠ 0 → ∀ a : (X.A.Fv v)ˣ, ∀ φ ∈ X.fm.Fi i,
  s.tx Λ x (X.fm.dilT i v a (s.cx Λ x) (φ (X.fm.dil i v a (s.cx Λ x)))) =
    s.tx Λ (((a⁻¹ : (X.A.Fv v)ˣ) : X.A.Fv v) • x) (φ (s.cx Λ (((a⁻¹ : (X.A.Fv v)ˣ) : X.A.Fv v) • x)))

def IpF : Prop := ∀ φ ∈ X.fm.Fi i, ∀ ψ ∈ X.fm.Fi i, X.fm.ipC i φ ψ =
  ∑ Λ, ((s.nL Λ : ℂ))⁻¹ * ∑ f ∈ Finset.univ.filter (fun f : Fin (D.R.N i) → X.A.Fv v => f ≠ 0),
    s.ipL Λ (s.tf Λ f (φ (s.cf Λ f))) (s.tf Λ f (ψ (s.cf Λ f)))

def IpX : Prop := ∀ φ ∈ X.fm.Fi i, ∀ ψ ∈ X.fm.Fi i, X.fm.ipC i φ ψ =
  ∑ Λ, ((s.nL Λ : ℂ))⁻¹ * ∑ x ∈ Finset.univ.filter (fun x : Fin (D.R.N i) → X.A.Fv v => x ≠ 0),
    s.ipL Λ (s.tx Λ x (φ (s.cx Λ x))) (s.tx Λ x (ψ (s.cx Λ x)))

def Ok : Prop := s.NLPos ∧ s.CfSurj ∧ s.CxSurj ∧ s.UpTie ∧ s.DnTie ∧ s.DilF ∧ s.DilX ∧ s.IpF ∧ s.IpX

end Unf

end
section
variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

def WtBounds (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧
  ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ ∧ X.C.sDiv i τ ≤ Wt X τ ∧
    (PtModel.lamT X (i + 1) τ).detShift = -X.C.sDiv i τ ∧
    (τ ∉ tops D → (PtModel.lamT X (i + 1) τ).w ⟨0, D.R.N_pos _⟩ ≤ Wt X τ)

def UKSharp (X : Ch D u) : Prop :=
  ∀ w, OverT X w → ∀ i, i < D.R.m →
    Into X w (fun φ => tpow X (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) •
      Uprod X (i + 1) w (KT X i φ)) (X.fm.S i w) (X.fm.S (i + 1) w)

def FormsStable (X : Ch D u) : Prop :=
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ X.fm.Fi i, Uop X i v φ ∈ X.fm.Fi i) ∧
  (∀ i, i ≤ D.R.m → ∀ v v', ∀ φ ∈ X.fm.Fi i, Uop X i v (Uop X i v' φ) = Uop X i v' (Uop X i v φ)) ∧
  ∀ i, i < D.R.m → ∀ φ ∈ X.fm.Fi i, KT X i φ ∈ X.fm.Fi (i + 1)

def Step0Tie (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ w, Formalism.MainNotions.product_first_zeroth_parts.OverT D u w → (Tw.fm u μ).seenP w = (D.fm u).seenP w ∧
    ∀ x ∈ LT.Nlam D u w, Tw.e0 u μ x ∈ Nlam (tw Tw u μ) w

def PtInt (X : Ch D u) : Prop :=
  (∀ φ ∈ X.fm.Fi D.R.m, Pt X φ ∈ X.fm.ptC) ∧ ∃ h : X.fm.PRat, X.fm.PtilIntegral h
end
end GlobalTheory.LvT
