import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPull

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

section Isogeny

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {G H : PDivGroup p k}

def IsIsog (f : G ⟶ H) : Prop :=
  ∃ (n : ℕ) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) ^ n • 𝟙 G ∧ g ≫ f = (p : ℤ_[p]) ^ n • 𝟙 H

def HasLogDeg (f : G ⟶ H) (e : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → Module.finrank k (G.A n ⧸ kerIdeal (f.app n)) = p ^ e

end Isogeny

structure IsDM {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (V : N →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] N) : Prop where
  free : Module.Free (WittVector p k) N
  finite : Module.Finite (WittVector p k) N
  F_V : ∀ x, F (V x) = p • x
  V_F : ∀ x, V (F x) = p • x

theorem p_eq_zero (p : ℕ) (k : Type) [Field k] [CharP k p] : (p : k) = 0 := CharP.cast_eq_zero k p

structure Base (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) : Type 1 where

  M : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), P k G →
    ModuleCat.{0} (WittVector p k)

  smap : ∀ {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (h' : P k' G') (h : P k G),
    SemiHom σ G' G → (M G h →+ M G' h')

  red : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G),
    M G h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt
  free : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G),
    Module.Free (WittVector p k) (M G h)
  finite : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G),
    Module.Finite (WittVector p k) (M G h)
  red_surjective : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G),
    Function.Surjective (red G h)
  red_eq_zero : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G)
    (m : M G h), red G h m = 0 ↔ ∃ n, m = p • n
  smap_smul : ∀ {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (h' : P k' G') (h : P k G) (s : SemiHom σ G' G)
    (a : WittVector p k) (m : M G h), smap h' h s (a • m) = WittVector.map σ a • smap h' h s m
  smap_id : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (m : M G h),
    smap h h (SemiHom.ofHom (𝟙 G)) m = m
  smap_add : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H : PDivGroup p k} (hG : P k G) (hH : P k H)
    (f g : G ⟶ H) (m : M H hH),
    smap hG hH (SemiHom.ofHom (f + g)) m = smap hG hH (SemiHom.ofHom f) m + smap hG hH (SemiHom.ofHom g) m
  smap_comp : ∀ {k k' k'' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] {σ : k →+* k'} {τ : k' →+* k''}
    {υ : k →+* k''} {G'' : PDivGroup p k''} {G' : PDivGroup p k'} {G : PDivGroup p k} (h'' : P k'' G'')
    (h' : P k' G') (h : P k G) (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G),
    (∀ n a, u.app n a = t.app n (s.app n a)) → ∀ m : M G h, smap h'' h u m = smap h'' h' t (smap h' h s m)
  red_smap : ∀ {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (h' : P k' G') (h : P k G) (s : SemiHom σ G' G)
    (m : M G h), red G' h' (smap h' h s m) = s.rig (red G h m)

namespace Base

variable {p : ℕ} [Fact p.Prime] {P Q : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def map {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) :
    B.M H hH →ₗ[WittVector p k] B.M G hG where
  toFun := B.smap hG hH (SemiHom.ofHom f)
  map_add' := map_add _
  map_smul' a m := by rw [B.smap_smul, WittVector.map_id]

def F (G : PDivGroup p k) (h : P k G) :
    B.M G h →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] B.M G h where
  toFun := B.smap h h (absFrob (p_eq_zero p k) G)
  map_add' := map_add _
  map_smul' a m := by
    rw [B.smap_smul, WittVector.frobenius_eq_map_frobenius]
    congr 3
    exact RingHom.ext fun r => frobRing_apply _ r

def Katz : Prop :=
  ∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) {d : ℕ}
      (c : Katz.Chart G d) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (hμ : Katz.IsLaw μ), c.IsLawOf μ →
      (B.M G h ≃ₗ[WittVector p k] Katz.Mod p hμ),
    ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) {d : ℕ}
      (c : Katz.Chart G d) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (hμ : Katz.IsLaw μ) (hc : c.IsLawOf μ),
      KatzF.IsF p hμ (fun x => e G h c hμ hc (B.F G h ((e G h c hμ hc).symm x))) ∧
      ∀ (H : PDivGroup p k) (h' : P k H) {d' : ℕ} (c' : Katz.Chart H d')
        {ν : Fin d' → MvPowerSeries (Fin d' ⊕ Fin d') k} (hν : Katz.IsLaw ν) (hc' : c'.IsLawOf ν) (f : G ⟶ H)
        (φ : Fin d' → MvPowerSeries (Fin d) k), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → c.IsMapOf c' f φ →
        KatzF.IsPull p hμ hν φ (fun x => e G h c hμ hc (B.map h h' f ((e H h' c' hν hc').symm x)))

def EtDual (C : Base p Q) : Prop :=
  ∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (hd : Q k G.dual),
      G.IsEt → (B.M G h ≃ₗ[WittVector p k] Module.Dual (WittVector p k) (C.M G.dual hd)),
    ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (hd : Q k G.dual)
      (hG : G.IsEt),
      (∀ x y, e G h hd hG (B.F G h x) (C.F G.dual hd y) = p * WittVector.frobenius (e G h hd hG x y)) ∧
      ∀ (H : PDivGroup p k) (h' : P k H) (hd' : Q k H.dual) (hH : H.IsEt) (f : G ⟶ H) x y,
        e G h hd hG (B.map h h' f x) y = e H h' hd' hH x (C.map hd' hd (dualHom G H f) y)

end Base

structure Theory (p : ℕ) [Fact p.Prime] : Type 1 where

  base : Base p fun _ _ _ => True
  katz : base.Katz
  etDual : base.EtDual base

  V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
    base.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)]
      base.M G trivial
  F_V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (m : base.M G trivial),
    base.F G trivial (V G m) = p • m
  V_F : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (m : base.M G trivial),
    V G (base.F G trivial m) = p • m

namespace Theory

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k k' : Type} [Field k] [CharP k p] [PerfectRing k p]
  [Field k'] [CharP k' p] [PerfectRing k' p]

abbrev M (G : PDivGroup p k) : Type := T.base.M G trivial

abbrev map {G H : PDivGroup p k} (f : G ⟶ H) : T.M H →ₗ[WittVector p k] T.M G := T.base.map trivial trivial f

abbrev smap {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (s : SemiHom σ G' G) : T.M G →+ T.M G' :=
  T.base.smap trivial trivial s

abbrev F (G : PDivGroup p k) :
    T.M G →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] T.M G := T.base.F G trivial

abbrev red (G : PDivGroup p k) :
    T.M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt := T.base.red G trivial

def IsLat {G : PDivGroup p k} (L : Submodule (WittVector p k) (T.M G)) : Prop :=
  (∃ n : ℕ, ∀ m, p ^ n • m ∈ L) ∧ (∀ m ∈ L, T.F G m ∈ L) ∧ ∀ m ∈ L, T.V G m ∈ L

def Duality : Prop :=
  ∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      T.M G ≃ₗ[WittVector p k] Module.Dual (WittVector p k) (T.M G.dual),
    ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      (∀ x y, e G (T.F G x) (T.F G.dual y) = p * WittVector.frobenius (e G x y)) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) x y, e G (T.map f x) y = e H x (T.map (dualHom G H f) y)

end Theory

section Examples

example {p : ℕ} [Fact p.Prime] {k : Type} [Field k] (G : PDivGroup p k) : IsIsog (𝟙 G) :=
  ⟨0, 𝟙 G, by simp, by simp⟩

example (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    IsDM ((WittVector.frobenius : WittVector p k →+* WittVector p k).toSemilinearMap)
      ((p : ℕ) • ((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k).toSemilinearMap) where
  free := inferInstance
  finite := inferInstance
  F_V x := by
    change WittVector.frobenius ((p : ℕ) • (WittVector.frobeniusEquiv p k).symm x) = p • x
    rw [nsmul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    congr 1
    exact (WittVector.frobeniusEquiv p k).apply_symm_apply x
  V_F x := by
    change (p : ℕ) • (WittVector.frobeniusEquiv p k).symm (WittVector.frobenius x) = p • x
    congr 1
    exact (WittVector.frobeniusEquiv p k).symm_apply_apply x

example : ((2 : ℕ) : ZMod 2) = 0 := p_eq_zero 2 (ZMod 2)

end Examples

end GlobalTheory.Dieu
