import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.HermitianColumns.SymAll
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def untwistedPrimes (D : D7) : Set ℕ :=
  ((D.host.small : Set ℕ) ∪ {D.host.g 0, D.host.g 1}) ∪ Set.range fun u : D.what₂.Word => (D.mem u).A.T

def TupNarrow {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) : Prop :=
  ∀ μ, GlobalTheory.Mem.Chr.IsTwist D.host (untwistedPrimes D) (Tp.xi μ) ∧ (Tp.xi μ).ValuesIn 0 D.what₂.embLL

def PsiTied {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v, v ∉ nch.Q w →
    ∀ (A : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) A v →
      IsFrob (F := D.host.E) A (normV v) σ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = ((((Tp.psi w).val v)⁻¹ : ℂˣ) : ℂ) ∧
        nch.embW w y = algebraMap (nch.Oe w) (FractionRing (nch.Oe w))
          (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w)
            ((nch.psi' w (D.ntw.art (nch.twI w) (nch.Q w) σ) : (D.ntw.Ok (nch.twI w) (nch.k' w))ˣ) :
              D.ntw.Ok (nch.twI w) (nch.k' w)))

def DeltaCharacterCompatibility (C : CharFrame D) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ v, v ∉ D.ntw.pD i →
    ∀ (A : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) A v →
      IsFrob (F := D.host.E) A (normV v) σ →
      ∃ y : ↥D.LL0, embLL0 D y = ((((C.delAt (D.ntw.l i)).val v)⁻¹ : ℂˣ) : ℂ) ∧
        D.ntw.emb0 i y = algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
          ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)

def RepresentationCompatibility (C : CharFrame D) (EX : ErrX D) : Prop :=
  ∀ k : Fin 2, (EX.piG k - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)} ∧
    ∀ (y : 𝓞 D.host.E), (y : D.host.E) = D.host.conj (EX.piG k : D.host.E) →
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), C.P.Div k w ↔ y ∈ w.asIdeal

def RamificationCompatibility (X : DivX D) {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) : Prop :=
  ∀ μ, (∀ l : ℕ, l ∈ X.Qp μ ↔ l.Prime ∧ ∃ P, OverP D.host l P ∧ ¬ (Tp.xi μ).UnrAt P) ∧
    ∃ e : X.QPl μ ↪ HeightOneSpectrum (𝓞 D.host.F), (∀ v, X.qv μ v = Ideal.absNorm (e v).asIdeal) ∧
      ∀ v, v ∈ Set.range e ↔ ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v ∧ ¬ (Tp.xi μ).UnrAt P

def NuAt {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (μ : D.what₂.Tup) (P : HeightOneSpectrum (𝓞 D.host.E))
    (ν : ℕ → ℂ) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ j : Fin D.R.m, ν (j.1 + 1) * c = ((((Tp.tup μ j).val P)⁻¹ : ℂˣ) : ℂ)

def PlacesWith (X : DivX D) {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)
    (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  (∀ v, (Pv v).under (𝓞 D.host.F) = v) ∧
  (∀ p : ℕ, p = D.host.pde ∨ p = D.host.pde' → ∀ v v' : HeightOneSpectrum (𝓞 D.host.F),
    (p : 𝓞 D.host.F) ∈ v.asIdeal → (p : 𝓞 D.host.F) ∈ v'.asIdeal →
      (Pv v).under (𝓞 D.host.K) = (Pv v').under (𝓞 D.host.K)) ∧
  ∀ μ, ∃ e : X.QPl μ ↪ HeightOneSpectrum (𝓞 D.host.F), (∀ v, X.qv μ v = Ideal.absNorm (e v).asIdeal) ∧
    (∀ v, v ∈ Set.range e ↔ ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v ∧ ¬ (Tp.xi μ).UnrAt P) ∧
    ∀ v : X.QPl μ, NuAt Tp μ (Pv (e v)) (X.nu μ v)

def PlacesTied (X : DivX D) {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) : Prop :=
  ∃ Pv, PlacesWith X Tp Pv

def TameTied (C : CharFrame D) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), ∃ γ : (ZMod (D.host.g k))ˣ, Subgroup.zpowers γ = ⊤ ∧
    (∃ (β : D.nd.Om) (a : ℕ), β ^ (D.host.g k - 1) = (D.host.g k : D.nd.Om) ∧
      ((a : ZMod (D.host.g k)) = γ ∨ (a : ZMod (D.host.g k)) = (γ⁻¹ : (ZMod (D.host.g k))ˣ)) ∧
      (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v β - (a : D.nd.Om) * β) <
        (D.nd.plOm.1 (D.naut.plGw k v)).valuation β) ∧
    ∀ j : Fin D.R.m, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
        ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
        ((C.W.om k γ ^ (2 * (j.1 + 1)) : ℂˣ) : ℂ)

def FirstCharacterCompatibility (C : CharFrame D) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) (b : Bool) v, ¬ OverP D.host (D.ntw.l i) v →
    (∀ k, ¬ OverP D.host (D.host.g k) v) → v ∉ D.ntw.pD i →
    ∀ (A : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) A v →
      IsFrob (F := D.host.E) A (normV v) σ →
      ∃ y : ↥D.LL0, embLL0 D y = ((C.mu0 j * C.delAt (D.ntw.l i) * C.eta⁻¹).valTw
          (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) v)⁻¹ ∧
        (if b then D.ntw.emb0 i else D.ntw.emb0b i) y = algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
          ((D.ntw.chi1 i (j.1 + 1) b σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)

def TupFamilies (D : D7) : Prop := ∀ μ, DV.Used D μ

def CharAt (X : DivX D) (EX : ErrX D) (nch : NChoice D) (th : ThetaX D) (C : CharFrame D) (Tp : TupTied D C nch) : Prop :=
  ValLL0 D C ∧ Nonempty (DtTied D C) ∧ Nonempty (NCharTied D C nch Tp) ∧ Nonempty (ThetaChrTied D C nch Tp th) ∧
    TupNarrow Tp ∧ PsiTied Tp ∧ DeltaCharacterCompatibility C ∧ RepresentationCompatibility C EX ∧ RamificationCompatibility X Tp ∧
    PlacesTied X Tp ∧ TameTied C ∧ FirstCharacterCompatibility C ∧ TupFamilies D

def IsFurtherRealPlace (L : SizeData₂ D) (v0 : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  (Ideal.absNorm v0.asIdeal).Prime ∧ Ideal.absNorm v0.asIdeal % (D.host.QS * D.host.q * D.host.d) = 1 ∧
  Real.log (Ideal.absNorm v0.asIdeal : ℕ) ≤ L.sc.L ∧
  Ideal.absNorm v0.asIdeal ≠ D.host.pde ∧ Ideal.absNorm v0.asIdeal ≠ D.host.pde' ∧
  (∀ i, Ideal.absNorm v0.asIdeal ≠ D.host.g i) ∧ (∀ u, Ideal.absNorm v0.asIdeal ≠ (D.mem u).A.T) ∧
  ∀ p, p ∈ D.host.levelPrimes ↔ (∃ i, p = D.host.g i) ∨ p = D.host.pde ∨ p = D.host.pde' ∨
    p = Ideal.absNorm v0.asIdeal ∨ ∃ u, p = (D.mem u).A.T

def ClassReps {R : Ranks} (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (rep : ClassGroup (𝓞 H.K) → Ideal (𝓞 H.K)) : Prop :=
  rep 1 = ⊤ ∧ ∀ c, (∃ h : rep c ∈ (Ideal (𝓞 H.K))⁰, ClassGroup.mk0 ⟨rep c, h⟩ = c) ∧
    (∀ P : Ideal (𝓞 H.K), P.IsPrime → rep c ≤ P →
      (Ideal.absNorm P).Prime ∧ jacobiSym (-(H.d : ℤ)) (Ideal.absNorm P) = 1) ∧
    Nat.Coprime (Ideal.absNorm (rep c)) (30 * H.condN * H.g 0 * H.g 1 * H.pde * H.pde' * q0) ∧
    ((Ideal.absNorm (rep c) : ℕ) : ℝ) ≤ H.d * Real.log H.d ^ 3

def IsPrimVec {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (z : S.V) : Prop :=
  z ≠ 0 ∧ z ∈ S.L0 ∧ ∀ c : E, c • z ∈ S.L0 → c ∈ (algebraMap (𝓞 E) E).range

def LevelVectorCompatibility (lev : LevelData D) : Prop :=
  ∃ Wb : HSpace D.host.E, Wb.SigOK ∧ Wb.rank = D.R.k + 1 ∧ (∀ τ, Wb.sig τ = (D.R.k, 1)) ∧
    ∀ u : D.what₂.Word, ∃ (z : Wb.V) (φ : Wb.V →ₗ[D.host.E] (D.sp.Y 0).V),
      IsPrimVec Wb z ∧ Wb.hT z z = -((D.mem u).A.T : D.host.E) ∧ HSpace.IsIsomEmb Wb (D.sp.Y 0) φ ∧ φ z = D.zmOf u ∧
      LinearMap.range (D.sp.iXY 0) ≤ LinearMap.range φ ∧
      ∃ A₀ : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E),
        (∀ x : (D.sp.X 0).V, D.sp.crd0 x ∈ A₀ ↔ ∃ y ∈ Wb.L0, φ y = D.sp.iXY 0 x) ∧
        ∃ g₀ ∈ Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F), Formalism.L2.Herm.Carries g₀ (lev u).Lb A₀

def LevelAt (L : SizeData₂ D) (EX : ErrX D) (lev : LevelData D) (v0 : HeightOneSpectrum (𝓞 D.host.F))
    (rep : ClassGroup (𝓞 D.host.K) → Ideal (𝓞 D.host.K)) : Prop :=
  IsFurtherRealPlace L v0 ∧ ClassReps D.host (Ideal.absNorm v0.asIdeal) rep ∧
  (∀ u, Nat.Coprime (D.mem u).A.T (D.host.g 0 * D.host.g 1) ∧ ∀ c, Nat.Coprime (D.mem u).A.T (Ideal.absNorm (rep c))) ∧
  LevelVectorCompatibility lev ∧ (∀ u, D.cOf u * (EX.piT u : D.host.E) = (EX.piT D.u₀ : D.host.E)) ∧
  ChQD_at D L.sc.x L.sc.eps 4

def TwistedSetDef (L : SizeData₂ D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 ↔ ∃ w', GoodPairSystems.SamePair D w w' ∧ ∃ j ∈ Finset.Icc 1 D.R.m,
    D.what₂.Ij D.what₂.mu0 j w' ≠ 0 ∨ D.what₂.jw D.what₂.mu0 j w' ≠ 0 ∨ L.F j w' ≠ 0

def AvoidSet (v0 : HeightOneSpectrum (𝓞 D.host.F)) (rep : ClassGroup (𝓞 D.host.K) → Ideal (𝓞 D.host.K)) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ P : HeightOneSpectrum (𝓞 D.host.E),
    ((∃ p ∈ (D.host.small : Set ℕ) ∪ {D.host.q, D.host.d, D.host.pde, D.host.pde'}, OverP D.host p P) ∨
      (∃ u, OverP D.host (D.mem u).A.T P) ∨ P.under (𝓞 D.host.F) = v0 ∨
      ∃ c, ∃ p : ℕ, p.Prime ∧ p ∣ Ideal.absNorm (rep c) ∧ OverP D.host p P) → P ∈ D.ntw.S0 i

def ExactOrder (nch : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → nch.psi' w = 1 ∨ orderOf (nch.psi' w) = D.what₂.places.resChar w ^ nch.k' w

def TwistAt (L : SizeData₂ D) (nch : NChoice D) (xd : ThData D) (v0 : HeightOneSpectrum (𝓞 D.host.F))
    (rep : ClassGroup (𝓞 D.host.K) → Ideal (𝓞 D.host.K)) : Prop :=
  TwistedSetDef L ∧ GoodPairSystems.WithToricIntegralityConstant D (fun N0 => GoodPairSystems.TwGoodAt nch xd N0) ∧ AvoidSet v0 rep ∧ ExactOrder nch

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

def IsAdeleIso (κ : Formalism.L2.Theta.AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E) : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ ∀ x : D.host.E, κ (Formalism.L2.Theta.incA D x) = algebraMap D.host.E _ x

def finPartE (D : D7) : Formalism.L2.Theta.AE D →+* D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def SameChr {th : ThetaX D} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : Formalism.L2.Theta.ThetaTied D th)
    (Θ : ThetaChrTied D C nch Tp th) (κ : Formalism.L2.Theta.AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E) : Prop :=
  ∀ (c : th.Chr) (a : (Formalism.L2.Theta.AE D)ˣ),
    ((T.eChr c a : Circle) : ℂ) = (((Θ.eChr c).1 (Units.map κ.toRingHom.toMonoidHom a) : ℂˣ) : ℂ)

def SameDet {C : CharFrame D} (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (Dt : DtTied D C)
    (κ : Formalism.L2.Theta.AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E) : Prop :=
  ∀ (a : (Formalism.L2.Theta.AE D)ˣ) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
    ((Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) :
        (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) *
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (finPartE D a) = finPartE D a →
    dt x = Dt.eDt (Units.map κ.toRingHom.toMonoidHom a)

def StdSpaces (D : D7) : Prop :=
  (∀ j, 1 ≤ j → j ≤ D.R.m → D.sp.Vneg j = false) ∧ (∀ j, j ≤ D.R.m → Formalism.L2.Herm.IsStd (D.sp.X j)) ∧
    Formalism.L2.Herm.IsStd D.sp.X'

open Formalism.L2.Herm in

def DeterminantCompatibility (H : HermColsCh D) (dt : unitaryOneFiniteAdeles D.sp.cm →* D.Dt) : Prop :=
  Function.Surjective dt ∧
  (∀ x : unitaryOneFiniteAdeles D.sp.cm, dt x = 1 → (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) ∈ IntegralUnitGroup D.sp.cm) ∧
  (letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
   IsOpen {x : unitaryOneFiniteAdeles D.sp.cm | dt x = 1}) ∧
  D.UO = ((IntegralUnitGroup D.sp.cm).subgroupOf (unitaryOneFiniteAdeles D.sp.cm)).map dt ∧
  (∀ (z : unitary D.host.E) (x : unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) = unitaryOneRationalAdele D.host.F z →
    D.e1Dt z = dt x) ∧
  (∀ (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (x : unitaryOneFiniteAdeles D.sp.cm),
    IsDetOf D.sp.cm x ((H.lev0 u).y c : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] Af D.host.F)) → D.detCls u 0 c = dt x) ∧
  ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (c : (D.mem u).C.cls i) (x : unitaryOneFiniteAdeles D.sp.cm),
    IsDetOf D.sp.cm x ((H.cls u i h1 hm (H.chOf u i c)).y ⟨c, rfl⟩ :
      GL (Fin (D.sp.X i).rank) (D.host.E ⊗[D.host.F] Af D.host.F)) → D.detCls u i c = dt x

def SpaceWith (EX : ErrX D) (lev : LevelData D) {th : ThetaX D} {C : CharFrame D} {nch : NChoice D}
    {Tp : TupTied D C nch} (H : Formalism.L2.Herm.ColsHermS D) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)
    (T : Formalism.L2.Theta.ThetaTied D th) (Dt : DtTied D C)
    (Θ : ThetaChrTied D C nch Tp th) (κ : Formalism.L2.Theta.AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E) : Prop :=
  H.base.lev0 = lev ∧ (∀ u v, (H.base.vT u v).1 = EX.vPl u v) ∧ (∀ u, (H.atT u).piU = EX.piT u) ∧
    (∀ u, (H.levelZeroCompatibility u).piG = EX.piG) ∧ DeterminantCompatibility H.base dt ∧ IsAdeleIso κ ∧ SameChr T Θ κ ∧ SameDet dt Dt κ

def JetWith (idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D) (δ : ℂ) (B : Formalism.L2.Ker.Base D D.host.ccK δ) : Prop :=
  TaylorLogMetric.RelDetPinned D idl ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ TaylorLogMetric.JetTorsionCompatibility D B.tor (B.eNat (TaylorLogMetric.chiRec D idl))

def JetAt (D : D7) : Prop :=
  ∃ (idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D) (δ : ℂ) (B : Formalism.L2.Ker.Base D D.host.ccK δ), JetWith idl δ B

def SpaceAt (X : DivX D) (EX : ErrX D) (lev : LevelData D) (nch : NChoice D) (th : ThetaX D) (C : CharFrame D)
    (Tp : TupTied D C nch) : Prop :=
  StdSpaces D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.FrameTied D lev ∧ (∃ idl, TaylorLogMetric.RelDetPinned D idl) ∧ Formalism.L2.Theta.ThetaDivisorCompatibility th X ∧
    th.TieRowIsom ∧
    (∃ (Hm : Formalism.L2.Herm.ColsHermS D) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (A : TH.ProvA)
      (H : Formalism.L2.Theta.AllTied D th A) (Dt : DtTied D C)
      (Θ : ThetaChrTied D C nch Tp th) (κ : Formalism.L2.Theta.AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E),
      SpaceWith EX lev Hm dt H.T Dt Θ κ) ∧
    (∀ u, product_first_zeroth_parts.admB D u) ∧ JetAt D

section Point

variable {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}

def TieCoreWith (ex : Extra D L gatT Gx Gy K X cX) (C : CharFrame D) (Tp : TupTied D C ex.nch)
    (v0 : HeightOneSpectrum (𝓞 D.host.F)) (rep : ClassGroup (𝓞 D.host.K) → Ideal (𝓞 D.host.K)) : Prop :=
  CharAt X ex.errX ex.nch ex.th C Tp ∧ LevelAt L ex.errX ex.lev v0 rep ∧ TwistAt L ex.nch ex.xd v0 rep ∧
    SpaceAt X ex.errX ex.lev ex.nch ex.th C Tp

def TieCoreAt (ex : Extra D L gatT Gx Gy K X cX) (C : CharFrame D) (Tp : TupTied D C ex.nch) : Prop :=
  ∃ v0 rep, TieCoreWith ex C Tp v0 rep

end Point

def TieCore : PtProp := fun D _ _ _ _ _ _ _ ex => ∃ (C : CharFrame D) (Tp : TupTied D C ex.nch), TieCoreAt ex C Tp

theorem prime_eq_of_overP {R : Ranks} {H : Formalism.BasicNotions.Host R} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 H.E)} (h1 : OverP H p v) (h2 : OverP H q v) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h : ((a : 𝓞 H.E) * (p : 𝓞 H.E) + (b : 𝓞 H.E) * (q : 𝓞 H.E)) = 1 := by
    have := congrArg (fun z : ℤ => (z : 𝓞 H.E)) hab
    push_cast at this
    exact this
  rw [← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_overP {R : Ranks} (H : Formalism.BasicNotions.Host R) {p : ℕ} (hp : p.Prime) : ∃ v, OverP H p v := by
  have hnu : Ideal.span {((p : ℕ) : 𝓞 H.E)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    have h2 : 0 < Module.finrank ℤ (𝓞 H.E) := Module.finrank_pos
    exact absurd h1 (Nat.one_lt_pow h2.ne' hp.one_lt).ne'
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hpM : ((p : ℕ) : 𝓞 H.E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h0 => ?_⟩, hpM⟩
  rw [h0, Ideal.mem_bot] at hpM
  exact hp.ne_zero (by exact_mod_cast hpM)

theorem TupNarrow.unr {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (h : TupNarrow Tp) (μ : D.what₂.Tup) {p : ℕ}
    (hp : p.Prime) (hS : p ∈ untwistedPrimes D) {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : OverP D.host p v) :
    (Tp.xi μ).UnrAt v := by
  by_contra hr
  obtain ⟨-, h1, -, h2⟩ := (h μ).1.2.2.2 v hr
  exact h2 (prime_eq_of_overP h1 hp (Ideal.absNorm_mem _) hv ▸ hS)

theorem not_unr_of_isDelta {R : Ranks} {H : Formalism.BasicNotions.Host R} {p : ℕ} {χ : HChar H.E} (h : IsDelta (H := H) p χ)
    {v : HeightOneSpectrum (𝓞 H.E)} (hv : OverP H p v) : ¬ χ.UnrAt v := fun hu => by
  have := (h.ine v hv 1).1 fun x hx => by rw [hu x hx, one_pow]
  omega

theorem tuples_ne {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) :
    D.what₂.mu0 ≠ D.what₂.muStar ∧ D.what₂.mu0 ≠ D.what₂.muStar' ∧ D.what₂.muStar ≠ D.what₂.muStar' := by
  obtain ⟨v, hv⟩ := exists_overP D.host D.host.pde_prime
  obtain ⟨v', hv'⟩ := exists_overP D.host D.host.pde'_prime
  refine ⟨fun h => not_unr_of_isDelta C.isDel hv ?_, fun h => not_unr_of_isDelta C.isDel' hv' ?_,
    fun h => not_unr_of_isDelta C.isDel hv ?_⟩
  · rw [← Tp.xi_star, ← h, Tp.trueColumnChoices_heckeChar_reference_eq_one]; exact fun _ _ => rfl
  · rw [← Tp.xi_star', ← h, Tp.trueColumnChoices_heckeChar_reference_eq_one]; exact fun _ _ => rfl
  · rw [← Tp.xi_star, h, Tp.xi_star']
    exact C.isDel'.unr v fun h' => D.host.pde_ne (prime_eq_of_overP D.host.pde_prime D.host.pde'_prime hv h')

theorem TupFamilies.xi {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (h : TupFamilies D) (μ : D.what₂.Tup) :
    Tp.xi μ = 1 ∨ Tp.xi μ = C.del ∨ Tp.xi μ = C.del' ∨
      ∃ w, D.what₂.muAt w ≠ D.what₂.mu0 ∧ Tp.xi μ = C.delAt (D.what₂.places.resChar w) * Tp.psi w := by
  rcases h μ with e | e | e | ⟨w, e⟩
  · exact Or.inl (e ▸ Tp.trueColumnChoices_heckeChar_reference_eq_one)
  · exact Or.inr (Or.inl (e ▸ Tp.xi_star))
  · exact Or.inr (Or.inr (Or.inl (e ▸ Tp.xi_star')))
  · by_cases hw : D.what₂.muAt w = D.what₂.mu0
    · exact Or.inl (by rw [e, hw]; exact Tp.trueColumnChoices_heckeChar_reference_eq_one)
    · refine Or.inr (Or.inr (Or.inr ⟨w, hw, ?_⟩))
      rw [e, (D.what₂.muAt_or w).resolve_left hw]
      exact Tp.xi_tw w

theorem norm_xi_val {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (μ : D.what₂.Tup)
    (P : HeightOneSpectrum (𝓞 D.host.E)) : ‖(((Tp.xi μ).val P : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, h⟩ := Tp.xi_fin μ
  have key : ∀ k : ℕ, ((Tp.xi μ) ^ k).val P = (Tp.xi μ).val P ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero]; rfl
    | succ k ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]
  have h1 : (Tp.xi μ).val P ^ n = 1 := by
    rw [← key, show Tp.xi μ ^ n = 1 from h]; rfl
  have h2 := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) h1
  simp only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem nuAt_iff {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (μ : D.what₂.Tup)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (ν : ℕ → ℂ) :
    NuAt Tp μ P ν ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ j : Fin D.R.m, ν (j.1 + 1) = c * ((((C.mu0 j).val P)⁻¹ : ℂˣ) : ℂ) := by
  have hx := norm_xi_val Tp μ P
  have hx0 : (((Tp.xi μ).val P : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e : ∀ j, ((((Tp.tup μ j).val P)⁻¹ : ℂˣ) : ℂ) =
      ((((C.mu0 j).val P)⁻¹ : ℂˣ) : ℂ) * (((Tp.xi μ).val P : ℂˣ) : ℂ)⁻¹ := fun j => by
    show ((((C.mu0 j * Tp.xi μ).val P)⁻¹ : ℂˣ) : ℂ) = _
    rw [HChar.val_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val ((Tp.xi μ).val P)]
  constructor
  · rintro ⟨c, hc, h⟩
    have hc0 : c ≠ 0 := fun h0 => by simp [h0] at hc
    refine ⟨(c * (((Tp.xi μ).val P : ℂˣ) : ℂ))⁻¹, by rw [norm_inv, norm_mul, hc, hx]; simp, fun j => ?_⟩
    rw [eq_div_of_mul_eq hc0 (h j), e]
    field_simp
  · rintro ⟨c, hc, h⟩
    have hc0 : c ≠ 0 := fun h0 => by simp [h0] at hc
    refine ⟨(c * (((Tp.xi μ).val P : ℂˣ) : ℂ))⁻¹, by rw [norm_inv, norm_mul, hc, hx]; simp, fun j => ?_⟩
    rw [h j, e]
    field_simp

theorem NuAt.ratio {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} {μ : D.what₂.Tup}
    {P : HeightOneSpectrum (𝓞 D.host.E)} {ν : ℕ → ℂ} (h : NuAt Tp μ P ν) (i j : Fin D.R.m) :
    ν (i.1 + 1) / ν (j.1 + 1) = (((C.mu0 j).val P : ℂˣ) : ℂ) / (((C.mu0 i).val P : ℂˣ) : ℂ) := by
  obtain ⟨c, hc, h⟩ := (nuAt_iff Tp μ P ν).1 h
  have hc0 : c ≠ 0 := fun h0 => by simp [h0] at hc
  have hi : (((C.mu0 i).val P : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hj : (((C.mu0 j).val P : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [h i, h j, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  field_simp

theorem range_eq_of_faithful {Γ : Type*} [CommGroup Γ] [Finite Γ] (φ ψ : Γ →* ℂˣ) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) : φ.range = ψ.range := by
  haveI : NeZero (Nat.card Γ) := ⟨Nat.card_pos.ne'⟩
  have key : ∀ χ : Γ →* ℂˣ, Function.Injective χ → χ.range = rootsOfUnity (Nat.card Γ) ℂ := by
    intro χ hχ
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]
    · rw [← Nat.card_congr (MonoidHom.ofInjective hχ).toEquiv]
      exact card_rootsOfUnity ℂ (Nat.card Γ)
  rw [key φ hφ, key ψ hψ]

theorem TameTied.pow {C : CharFrame D} (h : TameTied C) (k : Fin 2) (v : D.nd.PlG k) :
    ∃ γ : (ZMod (D.host.g k))ˣ, Subgroup.zpowers γ = ⊤ ∧ ∀ j : Fin D.R.m, D.nd.chiT k v j = γ ^ (2 * (j.1 + 1)) := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ, -, h⟩ := h k v
  let T : (ZMod (D.host.g k))ˣ →* ℂˣ := Units.map ((D.ntypes.teichC k).comp
    (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) : ZMod (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.host.g k)))
  have hT : Function.Injective T := by
    intro y z e
    have hi := (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))).injective
    exact Units.ext (hi (D.ntypes.teichC_inj k _ _ ((map_ne_zero_iff _ hi).2 y.ne_zero)
      ((map_ne_zero_iff _ hi).2 z.ne_zero) (congrArg (fun u : ℂˣ => (u : ℂ)) e)))
  have hr := range_eq_of_faithful (C.W.om k) T (C.W.gen k) hT
  obtain ⟨γ', hγ'⟩ : C.W.om k γ ∈ T.range := hr ▸ ⟨γ, rfl⟩
  refine ⟨γ', ?_, fun j => ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz⟩ : T y ∈ (C.W.om k).range := hr.symm ▸ ⟨y, rfl⟩
    obtain ⟨n, rfl⟩ : z ∈ Subgroup.zpowers γ := hγ ▸ Subgroup.mem_top z
    refine ⟨n, hT ?_⟩
    rw [← hz, map_zpow, map_zpow, hγ']
  · apply hT
    rw [map_pow, hγ']
    exact Units.ext (h j)

theorem IsFurtherRealPlace.mem {L : SizeData₂ D} {v0 : HeightOneSpectrum (𝓞 D.host.F)} (h : IsFurtherRealPlace L v0) :
    Ideal.absNorm v0.asIdeal ∈ D.host.levelPrimes ∧ ((Ideal.absNorm v0.asIdeal : ℕ) : 𝓞 D.host.F) ∈ v0.asIdeal :=
  ⟨(h.2.2.2.2.2.2.2 _).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), Ideal.absNorm_mem _⟩

theorem TwistAt.disjoint_conductorPlaces_excludedSet {L : SizeData₂ D} {nch : NChoice D} {xd : ThData D} {v0 : HeightOneSpectrum (𝓞 D.host.F)}
    {rep : ClassGroup (𝓞 D.host.K) → Ideal (𝓞 D.host.K)} (h : TwistAt L nch xd v0 rep) {w : D.what₂.places.Pl}
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) : D.ntw.NonzeroIndexPlace (nch.twI w) ∧ Disjoint (nch.Q w) (D.ntw.S0 (nch.twI w)) := by
  classical
  obtain ⟨⟨N0, hN⟩, hall⟩ := h.2.1
  have hg := hall N0 hN
  obtain ⟨S, hS⟩ := hg.goodTw hw
  exact ⟨hg.1.1.inW1 hw, (Finset.disjoint_union_right.1 hS.1.2.1).1⟩

theorem SpaceAt.real {X : DivX D} {EX : ErrX D} {lev : LevelData D} {nch : NChoice D} {th : ThetaX D} {C : CharFrame D}
    {Tp : TupTied D C nch} (h : SpaceAt X EX lev nch th C Tp) :
    Formalism.L2.Theta.RealTied D ∧ Formalism.L2.Herm.VolumeCompatible D := by
  obtain ⟨-, -, -, -, -, ⟨Hm, dt, A, H, -⟩, -⟩ := h
  exact ⟨H.real, H.real.vol.hermVolTied⟩

theorem SpaceAt.base {X : DivX D} {EX : ErrX D} {lev : LevelData D} {nch : NChoice D} {th : ThetaX D} {C : CharFrame D}
    {Tp : TupTied D C nch} (h : SpaceAt X EX lev nch th C Tp) :
    (∀ (u : D.what₂.Word) (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj (EX.piT u : D.host.E) →
      (lev u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 D.host.E)
        (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (lev u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0) ∧
    ∃ dt : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt, ∀ (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
      Formalism.L2.Herm.IsDetOf D.sp.cm x
        ((lev u).y c : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) → D.detCls u 0 c = dt x := by
  obtain ⟨-, -, -, -, -, ⟨Hm, dt, A, H, Dt, Θ, κ, rfl, -, hπ, -, hd, -⟩, -⟩ := h
  exact ⟨fun u pb e => (Hm.baseL u pb (by rw [hπ u]; exact e)).1, dt, hd.2.2.2.2.2.1⟩

def oneChart (H : Formalism.L2.Herm.HermCols D) : Formalism.L2.Herm.HermColsCh D where
  lev0 := H.lev0
  Ch _ _ := Unit
  Ch_m _ := ⟨inferInstance⟩
  chOf _ _ _ := ()
  lev u i h1 hm _ := H.lev u i h1 hm
  cls u i h1 hm _ :=
    { y := fun c => (H.cls u i h1 hm).y c.1
      y_bij := (H.cls u i h1 hm).y_bij.comp ⟨Subtype.val_injective, fun c => ⟨⟨c, rfl⟩, rfl⟩⟩
      y_lat := fun c => (H.cls u i h1 hm).y_lat c.1
      stabI := fun c => (H.cls u i h1 hm).stabI c.1
      stabI_inj := fun c => (H.cls u i h1 hm).stabI_inj c.1
      stabI_range := fun c => (H.cls u i h1 hm).stabI_range c.1 }
  vT := H.vT
  Fv := H.Fv

section Point

variable {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
  {ex : Extra D L gatT Gx Gy K X cX}

theorem TieCoreAt.char {C : CharFrame D} {Tp : TupTied D C ex.nch} (h : TieCoreAt ex C Tp) :
    CharAt X ex.errX ex.nch ex.th C Tp := let ⟨_, _, h⟩ := h; h.1

theorem TieCoreAt.space {C : CharFrame D} {Tp : TupTied D C ex.nch} (h : TieCoreAt ex C Tp) :
    SpaceAt X ex.errX ex.lev ex.nch ex.th C Tp := let ⟨_, _, h⟩ := h; h.2.2.2

theorem TieCore.tuples_ne (h : TieCore D L gatT Gx Gy K X cX ex) :
    D.what₂.mu0 ≠ D.what₂.muStar ∧ D.what₂.mu0 ≠ D.what₂.muStar' ∧ D.what₂.muStar ≠ D.what₂.muStar' :=
  let ⟨_, Tp, _⟩ := h; GlobalTheory.EX.tuples_ne Tp

theorem TieCore.pde_mem_Qp (h : TieCore D L gatT Gx Gy K X cX ex) : D.host.pde ∈ X.Qp D.what₂.muStar := by
  obtain ⟨C, Tp, h⟩ := h
  obtain ⟨v, hv⟩ := exists_overP D.host D.host.pde_prime
  exact ((h.char.2.2.2.2.2.2.2.2.1 _).1 _).2 ⟨D.host.pde_prime, v, hv, Tp.xi_star ▸ not_unr_of_isDelta C.isDel hv⟩

theorem TieCore.used (h : TieCore D L gatT Gx Gy K X cX ex) (μ : D.what₂.Tup) : DV.Used D μ :=
  let ⟨_, _, h⟩ := h; h.char.2.2.2.2.2.2.2.2.2.2.2.2 μ

theorem TieCore.base (h : TieCore D L gatT Gx Gy K X cX ex) (u : D.what₂.Word) : product_first_zeroth_parts.admB D u :=
  let ⟨_, _, h⟩ := h; h.space.2.2.2.2.2.2.1 u

theorem TieCore.jet (h : TieCore D L gatT Gx Gy K X cX ex) : JetAt D :=
  let ⟨_, _, h⟩ := h; h.space.2.2.2.2.2.2.2

example (e : D.what₂.muStar = D.what₂.mu0) : ¬ TieCore D L gatT Gx Gy K X cX ex := fun h => h.tuples_ne.1 e.symm

example (e : ∀ μ, X.Qp μ = ∅) : ¬ TieCore D L gatT Gx Gy K X cX ex := fun h => by
  have := h.pde_mem_Qp
  rw [e] at this
  exact absurd this (Finset.notMem_empty _)

end Point

example {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (z : S.V) (hz : z ∈ S.L0) :
    ¬ IsPrimVec S ((2 : E) • z) := fun h => by
  obtain ⟨y, hy⟩ := h.2.2 2⁻¹ (by rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul])
  have h2 : (2 : 𝓞 E) * y = 1 := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, hy, map_ofNat, map_one, mul_inv_cancel₀ two_ne_zero]
  have h3 := congrArg Ideal.absNorm ((Ideal.span_singleton_eq_top (x := ((2 : ℕ) : 𝓞 E))).2 (IsUnit.of_mul_eq_one y (by exact_mod_cast h2)))
  rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h3
  exact absurd h3 (Nat.one_lt_pow (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne' one_lt_two).ne'

end GlobalTheory.EX

end
