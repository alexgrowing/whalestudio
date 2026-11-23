import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

def Extra (S : Setup A n p) (j : GUf E n →* S.G.GAf) : Prop :=
  (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∃ P : Pl S.G (w.adicCompletion E), ∀ g, P.at (j g) = (comp w g).val) ∧
  ∀ q : ℕ, q.Prime → q ≠ p → ∀ g : GUf E n, (∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → (comp w g).val.charpoly.Separable) →
    GlobalTheory.LKCx.RegAf S.G (j g)

def PlTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (T : Tr S)
  (w : Plc E), (p : 𝓞 E) ∉ w.asIdeal → ∃ P : Pl S.G (w.adicCompletion E), ∀ g, P.at (T.j g) = (comp w g).val

def RegTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (T : Tr S)
  (q : ℕ), q.Prime → q ≠ p → ∀ g : GUf E n, (∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal → (comp w g).val.charpoly.Separable) →
    GlobalTheory.LKCx.RegAf S.G (T.j g)

def IsFac (F : Frame S) (w : Spl E p) (L : Loc S.G.GAf (GLw n w.1)) : Prop :=
  (∀ g, L.pr (F.j g) = comp w.1 g) ∧ ∀ y, L.loc y = F.j (CertificateRingHomMap.loc w.2.1 y)

def FacEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (w : Spl E p), ∃ L, IsFac F w L

def FacCont : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (w : Spl E p) (L : Loc S.G.GAf (GLw n w.1)), IsFac F w L → Continuous L.pr

def SplitC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Lv : G.Level) (k : Type) [Field k] [TopologicalSpace k] [T2Space k] [Algebra G.F k] (P : Pl G k)
    (L : Loc G.GAf (GL (Fin G.n) k)), Continuous L.pr → (∀ g, P.at g = (L.pr g : Matrix (Fin G.n) (Fin G.n) k)) →
    ∀ Kw : Subgroup (GL (Fin G.n) k), IsOpen (Kw : Set (GL (Fin G.n) k)) → IsCompact (Kw : Set (GL (Fin G.n) k)) →
    L.Fact Lv.K.toSubgroup Kw → ∃ (_ : TopologicalSpace L.pr.ker) (_ : IsTopologicalGroup L.pr.ker) (_ : T2Space L.pr.ker)
      (S : Split P Lv.K.toSubgroup L.pr.ker), ∀ g h, S.e.symm (g, h) = L.loc g * h

def SepConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n) (w : Plc E),
  (comp w g).val.charpoly.Separable → (comp (cj w) g).val.charpoly.Separable

variable {x : E} {U : Submodule ℂ (UA E n → ℂ)} {w₀ : Plc E} {Up : Plc E → Prop}

abbrev Iw (n : ℕ) (w : Plc E) : Subgroup (GLw n w) := GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)

structure SlopeTestRemainingChoices (S : Setup A n p) (V : Vec x U w₀ Up) (r : ℕ) (W : Finset (Spl E p)) : Prop where
  prime : r.Prime
  ne : r ≠ p
  good : A.Good r
  off : ∀ u ∈ V.S, (r : 𝓞 E) ∉ u.asIdeal
  half : Half r W
  nonempty : W.Nonempty

structure TyOK (F : Frame S) (V : Vec x U w₀ Up) (W : Finset (Spl E p)) (N : ℕ) (L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1))
    (hw : IsSplitAt w₀ ∧ (p : 𝓞 E) ∉ w₀.asIdeal) (Ty : TyLev S.G.GAf (GLw n w₀)) : Prop where
  fac : ∀ w, IsFac F w (L w)
  L_eq : Ty.L = L ⟨w₀, hw⟩
  K₀_eq : Ty.K₀ = S.L.KN N
  K_iff : ∀ k, k ∈ Ty.K ↔ (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1
  J_iff : ∀ y y' : GLw n w₀, y'.val = (y⁻¹).valᵀ → (y ∈ Ty.J ↔ y' ∈ V.J)
  ψ_eq : ∀ (y : Ty.J) (y' : V.J), (y' : GLw n w₀).val = ((y : GLw n w₀)⁻¹).valᵀ → Ty.ψ y = V.χ y'

def Off2 (W : Finset (Spl E p)) (L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)) (Ty : TyLev S.G.GAf (GLw n w₀)) :
    Submodule ℂ (S.G.GAf → ℂ) :=
  Submodule.span ℂ {f | ∃ h, Ty.L.pr h = 1 ∧ (∀ w ∈ W, (L w).pr h = 1) ∧ f = Ty.tf h}

def ForData (q : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (_ : Frame S) (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (_ : Vec x U w₀ Up) (_ : ℕ)
    (_ : Finset (Spl E p)) (_ : Lv p) (_ : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)) (_ : TyLev S.G.GAf (GLw n w₀)), Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Odd n → Sc S.D S.G → Gen A x → Off V p → (∃ q : ℕ, q.Prime ∧ A.Good q ∧ (q : 𝓞 E) ∈ w₀.asIdeal) →
    ∀ (r : ℕ) (W : Finset (Spl E p)), SlopeTestRemainingChoices S V r W → ∀ N : Lv p, r ∣ N.1 →
    (∀ k ∈ S.L.KN N.1, Stab F V k) → ∀ (L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)) hw (Ty : TyLev S.G.GAf (GLw n w₀)),
    TyOK F V W N.1 L hw Ty → q E A n p S F x U w₀ Up V r W N L Ty

def AuxiliaryInertOddPrime : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up), Gen A x → ∀ X : Finset ℕ,
  ∃ r W, r ∉ X ∧ SlopeTestRemainingChoices S V r W

def TyEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (F : Frame S) (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up), Off V p →
  ∀ (r : ℕ) (W : Finset (Spl E p)), SlopeTestRemainingChoices S V r W → ∀ N : Lv p, r ∣ N.1 → (∀ k ∈ S.L.KN N.1, Stab F V k) →
  ∃ L hw Ty, TyOK F V W N.1 L hw Ty

def TyTop : Prop := ForData fun _ _ _ _ _ n _ _ S _ _ _ w₀ _ _ _ _ N _ Ty =>
  (∃ Lv : S.G.Level, Lv.K.toSubgroup = S.L.KN N.1) ∧
  (∃ Kw : Subgroup (GLw n w₀), IsOpen (Kw : Set (GLw n w₀)) ∧ IsCompact (Kw : Set (GLw n w₀)) ∧ Ty.L.Fact Ty.K₀ Kw) ∧
  IsOpen (Ty.J : Set (GLw n w₀)) ∧ IsCompact (Ty.J : Set (GLw n w₀)) ∧ IsOpen (Ty.ψ.ker : Set Ty.J) ∧
  ∀ (σ : SmIrr (GLw n w₀)) (v : σ.V), v ≠ 0 → (∀ g : Ty.J, σ.ρ g v = ((Ty.ψ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ

def TyFact : Prop := ForData fun E _ _ _ _ n p _ S _ _ _ _ _ V _ W _ L Ty =>
  (∀ w ∈ W, (L w).Fact Ty.K (Iw n w.1) ∧ Ty.L.Apart (L w) ∧ ∀ w' ∈ W, w ≠ w' → (L w).Apart (L w')) ∧
  (∀ w : Spl E p, w.1 ∉ V.S → cj w.1 ∉ V.S → (∀ u ∈ W, GlobalTheory.Cong.Apart w.1 u.1) →
    (L w).Fact Ty.K (GlobalTheory.LFun.KGL w.1 n) ∧ Ty.L.Apart (L w)) ∧
  ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ ∀ k ∈ Ty.K, ∀ v ∈ LaHat S.D, c • S.L.actG k v ∈ LaHat S.D

def ExistsIdempotentHeckeOperatorWithRegularSupport : Prop := ForData fun E _ _ _ _ n p _ S _ _ _ _ _ _ _ W _ L Ty =>
  ∃ u ∈ Hecke ℂ Ty.K₀, ∃ u' ∈ Hecke ℂ Ty.K₀, conv Ty.K₀ (Ty.tf 1) u = u ∧ conv Ty.K₀ u (Ty.tf 1) = u ∧ conv Ty.K₀ u' u = Ty.tf 1 ∧
    (∀ f ∈ Off2 W L Ty, conv Ty.K₀ u f = conv Ty.K₀ f u) ∧
    ∀ m : ℕ, 1 ≤ m → ∃ X : ∀ w : Spl E p, Set (GLw n w.1),
      (∀ w ∈ W, ∀ y ∈ X w, y.val.charpoly.Separable ∧ ∀ a ∈ Iw n w.1, a * y ∈ X w) ∧
      ∀ g, powFn Ty.K₀ u (Ty.tf 1) m g ≠ 0 → Integ S.L g⁻¹ ∧ ∀ w ∈ W, (L w).pr g ∈ X w

def MemFn : Prop := ForData fun _ _ _ _ _ n _ _ S F _ _ _ _ V r W N L Ty => ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ →
  g.fn ∈ Hecke ℂ Ty.K₀ ∧ (∀ a, g.fn a ≠ 0 → ∀ w ∈ W, (L w).pr a ∈ Iw n w.1) ∧
  ((IsDeckM g ∧ θ = 1 ∧ conv Ty.K₀ g.fn (Ty.tf 1) = Ty.tf 1) ∨
    (Ty.L.pr g.h = 1 ∧ (∀ w ∈ W, (L w).pr g.h = 1) ∧
      conv Ty.K₀ g.fn (Ty.tf 1) = (idx g : ℂ) • Ty.tf g.h⁻¹))

def MemComm : Prop := ForData fun _ _ _ _ _ _ _ _ S F _ _ _ _ V r W N L Ty => ∀ (g g' : Mem S.L N) (θ θ' : ℂ),
  Seen F V r g θ → Seen F V r g' θ' → conv Ty.K₀ g.fn (Ty.tf 1) ∈ Off2 W L Ty ∧
    conv Ty.K₀ g.fn (conv Ty.K₀ g'.fn (Ty.tf 1)) = conv Ty.K₀ g'.fn (conv Ty.K₀ g.fn (Ty.tf 1))

def PhiEx : Prop := ForData fun E _ _ _ _ n p _ S F _ _ _ _ V r _ N _ Ty =>
  ∃ φ : S.G.GAf → Module.Dual ℂ V.W.Sp, φ ≠ 0 ∧ Ty.IsTy φ ∧
    (∀ g : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g ∈ GlobalTheory.LFun.KGL w n) → φ (F.j g) = V.Φ (F.th g)) ∧
    ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ → Formalism.UG.hAct Ty.K₀ g.fn φ = θ • φ

def EigEx : Prop := ForData fun E _ _ _ _ n _ _ S F _ _ _ _ V r _ N _ Ty =>
  ∃ thQ : GL (Fin n) E × ℚˣ →* GL (Fin n) E × ℚˣ, (∀ y, (thQ y).1.val = (y.1⁻¹).valᵀ ∧ (thQ y).2 = y.2⁻¹) ∧
    ∀ (J : Type) (g : J → Mem S.L N) (θ : J → ℂ), (∀ j, Seen F V r (g j) (θ j)) →
      HasEig S.G ((CertificateRingHomMap.xi V.W V.jz).comp thQ) Ty.K₀ (fun j => (g j).fn) θ (Ty.tf 1)

def SpecData : Prop := ForData fun _ _ _ _ _ _ _ _ S F _ _ _ _ V r _ N _ _ => Extra S F.j →
  ∀ (J : Type) (g : J → Mem S.L N) (θ : J → ℂ), (∀ j, Seen F V r (g j) (θ j)) →
    ∃ f, IsFnL S.L N.1 f ∧ Spec S.L V.lam (S.L.KN N.1) (fun j => (g j).fn) θ f

def SpecTopG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (F : Frame S) (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Odd n → Sc S.D S.G → Gen A x → Off V p → (∃ q : ℕ, q.Prime ∧ A.Good q ∧ (q : 𝓞 E) ∈ w₀.asIdeal) →
    ∀ X : Finset ℕ, ∃ r₀ : ℕ, r₀.Prime ∧ r₀ ∉ X ∧ r₀ ≠ p ∧
      ∀ N : Lv p, r₀ ∣ N.1 → (∀ k ∈ S.L.KN N.1, Stab F V k) → ∀ (J : Type) (g : J → Mem S.L N) (θ : J → ℂ),
        (∀ j, Seen F V r₀ (g j) (θ j)) → ∃ f, IsFnL S.L N.1 f ∧ Spec S.L V.lam (S.L.KN N.1) (fun j => (g j).fn) θ f

end UpperTheory.Gal.Spc
