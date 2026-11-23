import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.GlobIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.BridgeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ToUnitsTheta

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Model

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) {V : Type} [AddCommGroup V] [Module ℂ V]

def SD.lvS (y : DA Δ) : Subgroup (SA Δ) := (A.dat.U2.comap (MulAut.conj y⁻¹).toMonoidHom).subgroupOf (SA Δ)

structure SD.SF (ι : DX Δ →* DA Δ) (W : Representation ℂ (SU Δ) V) (y : DA Δ) (ψ : SA Δ → V) (a : Chs F) : Prop where
  left : ∀ (γ : SU Δ) (g g' : SA Δ), (g' : DA Δ) = ι γ * g → ψ g' = W γ (ψ g)
  level : ∀ u ∈ A.lvS y, ∀ g, ψ (g * u) = ψ g
  eig : ∀ t (g : SA Δ), A.DomS (SD.dS t) → A.IsElD g (SD.dS t) → dcF (A.lvS y) g ψ = A.exS a t • ψ

structure SD.Ext (A₀ : SD Δ) : Prop where
  sub : A₀.Sg ⊆ A.Sg
  s : ∀ v ∈ A₀.Sg, A.s v = A₀.s v
  V : ∀ v ∈ A₀.Sg, (A.V v).J 2 = (A₀.V v).J 2
  iw : ∀ v ∈ A.Sg, v ∉ A₀.Sg → (A.V v).J 2 = (Lev.iw _).J 2

def SD.Reps (ι : DX Δ →* DA Δ) (Y : Finset (DA Δ)) : Prop :=
  (∀ y ∈ Y, A.dat.Off y ∧ {v | y.1 v ≠ 1}.Finite) ∧ ∀ g : DA Δ, ∃ γ, ∃ s ∈ SA Δ, ∃ y ∈ Y, ∃ u ∈ A.dat.U2, g = ι γ * s * y * u

end Model

variable {L : Type} [Field L] [NumberField L] [IsCMField L] (B : Bridge L)

abbrev Spl : Type := ∀ w : Plc L, IsSplitAt w → B.toRingBr.Split w

def em (v : InfinitePlace L) : Lsq (Lp L) B.Δ →+* ℂ := v.embedding.comp B.e.toRingHom

variable {B} (T : Spl B)

abbrev iu (w : Plc L) (h : IsSplitAt w) : (Kv (un w))ˣ →* (Kw w)ˣ := Units.map ((T w h).i : Kv (un w) →* Kw w)

structure Fit (S : Finset (Plc L)) (V : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) : Prop where
  pl : Places (S : Set (Plc L))
  sg : ∀ v, v ∈ A.Sg ↔ ∃ w ∈ S, un w = v
  s : ∀ w ∈ S, ∀ h, A.s (un w) = (T w h).s
  c : ∀ w ∈ S, (A.V (un w)).c = (V w).c
  H : ∀ w ∈ S, ∀ h x, iu T w h x ∈ (V w).H ↔ x ∈ (A.V (un w)).H

def FitCh (S : Finset (Plc L)) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) : Prop :=
  ∀ w ∈ S, ∀ h, b (un w) = (a w).comp (iu T w h)

def IsCong {n : ℕ} (m : ℕ) (U : Subgroup (UA L n)) : Prop :=
  ∀ x, x ∈ U ↔ x ∈ Kall L n ∧ ∀ w i j, ∃ a ∈ w.adicCompletionIntegers L, (mL w x - 1) i j = (m : Kw w) * a

def OffS {n : ℕ} (S : Finset (Plc L)) (x : UA L n) : Prop := ∀ w ∈ S, ∀ u, un u = un w → cLoc u x = 1

def OnS {n : ℕ} (S : Finset (Plc L)) (x : UA L n) : Prop := x ∈ finU L n ∧ ∀ u, (∀ w ∈ S, un u ≠ un w) → cLoc u x = 1

def Full {n : ℕ} (U₀ : Subgroup (UA L n)) (S : Finset (Plc L)) : Prop := U₀ ≤ Kall L n ∧ ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U₀

def FitEx : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), B.Ok → ∀ (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)), Places (S : Set (Plc L)) → HasTwo S →
    (∃ A : SD B.Δ, A.Ok ∧ Fit T S VL A) ∧ ∀ a, ∃ b, FitCh T S a b

def FitExt : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L) (T : Spl B) (S₀ S : Finset (Plc L)) (V₀ VL : ∀ w : Plc L, Lev (Kw w)) (A₀ A : SD B.Δ),
    Fit T S₀ V₀ A₀ → Fit T S VL A → S₀ ⊆ S → (∀ w ∈ S₀, VL w = V₀ w) → (∀ w ∈ S, w ∉ S₀ → VL w = iw w) → A.Ext A₀

def LevG : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), B.Ok → ∀ (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ), A.Ok → Fit T S VL A →
    (∀ g : GA B.Δ, g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall L 3) S VL) ∧
    (∀ g : SA B.Δ, (g : DA B.Δ) ∈ A.dat.U2 ↔ (B.bS g : UA L 2) ∈ lev (Kall L 2) S VL) ∧
    (∀ (g : GA B.Δ) d, A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧ ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i)) ∧
    (∀ (g : SA B.Δ) d, A.IsElD g d ↔ OnS S (B.bS g : UA L 2) ∧ ∀ w ∈ S, ∀ h, cLoc w (B.bS g : UA L 2) = Sig.dg fun i => iu T w h (d (un w) i)) ∧
    ∀ w (h : IsSplitAt w) (n : ℕ) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) (d : Fin n → (Kv (un w))ˣ), n = 2 ∨ n = 3 →
      expo ψ (fun i => iu T w h (d i)) = expo (fun i => (ψ i).comp (iu T w h)) d

def DcAt : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U₀ : Subgroup (UA L n)) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)), Places (S : Set (Plc L)) → ∀ w ∈ S,
    Full U₀ {w} → ∀ d, AlgebraTools.FinOrb (lev U₀ S VL) (lev U₀ S VL) (secW n w (Sig.dg d)) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (φ : UA L n → V), (∀ u ∈ lev U₀ S VL, ∀ g, φ (g * u) = φ g) → ∀ c : ℂ,
      EigAt φ w (VL w) d c ↔ dcF (lev U₀ S VL) (secW n w (Sig.dg d)) φ = c • φ

def ProdEig : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U₀ : Subgroup (UA L n)) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)), Places (S : Set (Plc L)) → Full U₀ S →
    ∀ (d : ∀ w : Plc L, Fin n → (Kw w)ˣ) (x : UA L n), OnS S x → (∀ w ∈ S, cLoc w x = Sig.dg (d w)) →
    AlgebraTools.FinOrb (lev U₀ S VL) (lev U₀ S VL) x ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (φ : UA L n → V), (∀ u ∈ lev U₀ S VL, ∀ g, φ (g * u) = φ g) →
      ∀ c : Plc L → ℂ, (∀ w ∈ S, EigAt φ w (VL w) (d w) (c w)) → dcF (lev U₀ S VL) x φ = (∏ w ∈ S, c w) • φ

def TorUA : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (U₀ : Subgroup (UA L 2)) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)), Places (S : Set (Plc L)) → Full U₀ S →
    ∀ u ∈ lev U₀ S VL, ∃ c ∈ lev U₀ S VL, u * c⁻¹ ∈ finU L 2 ⊓ SUA L ∧ c⁻¹ * u ∈ finU L 2 ⊓ SUA L ∧
      ∀ (x : UA L 2) (d : ∀ w : Plc L, Fin 2 → (Kw w)ˣ), OnS S x → (∀ w ∈ S, cLoc w x = Sig.dg (d w)) → c * x = x * c

def WeakOne : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (S : Finset (Plc L)), Places (S : Set (Plc L)) → ∀ (x : ∀ w : Plc L, (Kw w)ˣ) (c : Plc L → ℕ),
    ∃ δ : Lˣ, (δ : L) * IsCMField.complexConj L δ = 1 ∧ ∀ w ∈ S, Units.map (algebraMap L (Kw w) : L →* Kw w) δ / x w ∈ Uc (Kw w) (c w)

def Translate : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)), Places (S : Set (Plc L)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (φ : UA L 2 → V), IsAF R (lev (Kall L 2) S VL) φ → φ ≠ 0 →
    ∃ x ∈ finU L 2, OffS S x ∧ ∃ s ∈ finU L 2 ⊓ SUA L, φ (s * x) ≠ 0

def InS : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), B.Ok → ∀ (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ), A.Ok → Fit T S VL A → ∀ (j : ℕ) (e : InfinitePlace L → ℤ) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)), FitCh T S a b →
    ∀ φ : UA L 2 → Wt.VD (InfinitePlace L) j, φ ≠ 0 → IsAF (repE j e) (lev (Kall L 2) S VL) φ → (∀ w ∈ S, EigS φ w (VL w) (a w)) →
    ∃ y : DA B.Δ, A.dat.Off y ∧ ∀ ch (C : Base (SU B.Δ) (SA B.Δ) (Wt.VD (InfinitePlace L) j)), A.dat.IsBS ch y C → C.W = Wt.cS (em B) j →
      ∃ ψ ∈ C.Forms, ψ ≠ 0 ∧ A.EigS C.U ψ b

def FinToAF : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)), U ≤ finU L n →
    ∀ Φ : finU L n → V, (∀ (f : finU L n), ∀ k ∈ infU L n, (f : UA L n) * k ∈ ratU L n → ∀ g, Φ (f * g) = R (infC L n k) (Φ g)) →
    (∀ u : finU L n, (u : UA L n) ∈ U → ∀ g, Φ (g * u) = Φ g) →
    ∃ φ : UA L n → V, IsAF R U φ ∧ (∀ g : finU L n, φ g = Φ g) ∧ ∀ (x : finU L n) (c : ℂ), AlgebraTools.FinOrb U U (x : UA L n) →
      dcF (U.subgroupOf (finU L n)) x Φ = c • Φ → dcF U (x : UA L n) φ = c • φ

def OutG : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), B.Ok → ∀ (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ), A.Ok → Fit T S VL A → ∀ (j : ℕ) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)), FitCh T S a b →
    ∀ ch (C : Base (U3 B.Δ) (GA B.Δ) (Wt.VG (InfinitePlace L) j)) (s : C.Tw), A.dat.IsBG ch C s → C.W = Wt.cG (em B) j →
    ∀ ψ ∈ C.Forms, ψ ≠ 0 → A.EigG ψ b →
    ∃ φ : UA L 3 → Wt.VG (InfinitePlace L) j, φ ≠ 0 ∧ IsAF (Wt.repG _ j) (lev (Kall L 3) S VL) φ ∧
      ∀ w ∈ S, EigT φ w (VL w) ![a w, 1, (a w)⁻¹]

def RepsEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ClassRep → ∀ ι, IsIotaD ι → ∃ Y, A.Reps ι Y

def KNon : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ A₀ : SD Δ, A₀.Ok → A.Ext A₀ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ) (C : Base (DX Δ) (DA Δ) V), A.dat.IsBK ch C →
    ∀ Y, A₀.Reps C.ι Y → (∀ y ∈ Y, A.dat.Off y) → ∀ φ ∈ C.Forms, φ ≠ 0 → ∃ y ∈ Y, ∃ s : SA Δ, φ (s * y) ≠ 0

def KRes : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ) (C : Base (DX Δ) (DA Δ) V), A.dat.IsBK ch C → ∀ y, A.dat.Off y → ∀ φ ∈ C.Forms, ∀ a, A.EigK φ a →
    A.SF C.ι (C.W.comp (SU Δ).subtype) y (fun g => φ (g * y)) a

def CongEx : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n m : ℕ), m ≠ 0 → ∃ U : Subgroup (UA L n), IsCong m U ∧ IsLevel U ∧
    (2 ≤ n → ∀ w, IsSplitAt w → locU n w ⊓ Kall L n ≤ U → (m : 𝓞 L) ∉ w.asIdeal)

def CongLev : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), B.Ok → ∀ (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ), A.Ok → Fit T S VL A → ∀ Y : Finset (DA B.Δ), (∀ y ∈ Y, {v | y.1 v ≠ 1}.Finite) → ∃ m : ℕ, 3 ≤ m ∧
    (∀ w : Plc L, (m : 𝓞 L) ∉ w.asIdeal → ∀ y ∈ Y, y.1 (un w) = 1) ∧
    ∀ U, IsCong m U → ∀ y ∈ Y, ∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ U → g ∈ A.lvS y

def LevExt : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), B.Ok → ∀ (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ), A.Ok → Fit T S VL A → ∀ A₀ : SD B.Δ, A₀.Ok → A.Ext A₀ → ∀ (S₁ : Finset (Plc L)), (∀ w ∈ S, w ∈ S₁ ∨ un w ∈ A₀.Sg) → (∀ w ∈ S₁, w ∈ S ∧ VL w = iw w) →
    ∀ (U : Subgroup (UA L 2)) (y : DA B.Δ), A.dat.Off y → (∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ U → g ∈ A₀.lvS y) →
    ∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ lev U S₁ iw → g ∈ A.lvS y

def DetRoot : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (m : ℕ), 3 ≤ m → ∀ U : Subgroup (UA L 2), IsCong m U → ∀ f ∈ finU L 2, ∀ k ∈ infU L 2, f * k ∈ ratU L 2 →
    ∀ u ∈ U, f * u ∈ SUA L → f ∈ SUA L ∧ k ∈ SUA L

def ExtF : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (W : Representation ℂ Γ V) (S U : Subgroup G) [S.Normal],
    (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) → (∀ γ, ∀ u ∈ U, ι γ * u ∈ S → ι γ ∈ S) → ∀ ψ : S → V,
    (∀ γ (g g' : S), (g' : G) = ι γ * g → ψ g' = W γ (ψ g)) → (∀ u : S, (u : G) ∈ U → ∀ g, ψ (g * u) = ψ g) →
    ∃ Φ : G → V, (∀ g : S, Φ g = ψ g) ∧ (∀ γ g, Φ (ι γ * g) = W γ (Φ g)) ∧ (∀ u ∈ U, ∀ g, Φ (g * u) = Φ g) ∧
      ∀ (a : S) (c : ℂ), AlgebraTools.FinOrb U U (a : G) → (∀ u ∈ U, ∃ z ∈ U, z * a = a * z ∧ u * z⁻¹ ∈ S ∧ z⁻¹ * u ∈ S) →
        dcF (U.subgroupOf S) a ψ = c • ψ → dcF U (a : G) Φ = c • Φ

def SLev : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), B.Ok → ∀ (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ), A.Ok → Fit T S VL A → ∀ w ∈ S, ∀ (h : IsSplitAt w) (S₁ : Finset (Plc L)), w ∈ S₁ → S₁ ⊆ S → VL w = iw w → ∀ U : Subgroup (UA L 2), Full U {w} →
    ∀ y : DA B.Δ, A.dat.Off y → (∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ lev U S₁ iw → g ∈ A.lvS y) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ψ : SA B.Δ → V), (∀ u ∈ A.lvS y, ∀ g, ψ (g * u) = ψ g) → ∀ (g : SA B.Δ) (d : Fin 2 → (Kw w)ˣ), (B.bS g : UA L 2) = secW 2 w (Sig.dg d) →
    dcF (((lev U S₁ iw).subgroupOf (finU L 2 ⊓ SUA L)).comap B.bS.toMonoidHom) g ψ = dcF (A.lvS y) g ψ

def OutS : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), B.Ok → ∀ (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ), A.Ok → Fit T S VL A → ∀ (S₁ : Finset (Plc L)), S₁ ⊆ S → (∀ w ∈ S₁, VL w = iw w) → ∀ (m : ℕ) (U : Subgroup (UA L 2)), 3 ≤ m → IsCong m U → Full U S₁ →
    ∀ (n : ℕ) (e : ℤ) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)), FitCh T S a b → ∀ ι, IsIotaD ι → ∀ y : DA B.Δ, A.dat.Off y →
    (∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ lev U S₁ iw → g ∈ A.lvS y) → ∀ ψ : SA B.Δ → Wt.VD (InfinitePlace L) n, ψ ≠ 0 →
    A.SF ι ((Wt.cD (em B) n e).comp (SU B.Δ).subtype) y ψ b →
    ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) n, φ ≠ 0 ∧ IsAF (repE n 0) (lev U S₁ iw) φ ∧ ∀ w ∈ S₁, EigS φ w (iw w) (a w)

end UpperTheory.V.Z.Sym.So

end
