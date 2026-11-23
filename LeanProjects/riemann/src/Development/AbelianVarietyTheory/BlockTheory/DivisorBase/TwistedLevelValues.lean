import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LogFactorialIndices.StatementSize

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def twVal {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (w : ℝ) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) : ℂ :=
  ((χ.locK P k : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-((w : ℂ) * ((Formalism.L2.Host.ordF P k : ℤ) : ℂ)))

def IsGalConj {E : Type} [Field E] [NumberField E] (s : ℂ ≃+* ℂ) (w : ℝ) (χ χ' : Formalism.L2.Host.HChar E) : Prop :=
  ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ), twVal χ' w P k = s (twVal χ w P k)

theorem isGalConj_refl {E : Type} [Field E] [NumberField E] (w : ℝ) (χ : Formalism.L2.Host.HChar E) :
    IsGalConj (RingEquiv.refl ℂ) w χ χ := fun _ _ => rfl

variable (D) in

def IsEmbOverK (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) : Prop :=
  (∀ a, σ a = s (D.what₂.embLL a)) ∧ ∀ x : D.host.E, x ∈ D.host.K → σ (D.embE x) = D.what₂.embLL (D.embE x)

theorem isEmbOverK_base : IsEmbOverK D D.what₂.embLL (RingEquiv.refl ℂ) := ⟨fun _ => rfl, fun _ _ => rfl⟩

def hookOf (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens (((List.range n).map a).insertionSort (· ≥ ·)) List.sortedGE_insertionSort)

variable (D) in

abbrev pW (i : Fin D.R.m) (ρ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D ρ)).1

variable (D) in

abbrev qW (i : Fin D.R.m) (ρ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D ρ)).2

variable (D) in

def aPlAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ → ℕ := aPl D i (pW D i ρ) (lab σ ρ)

variable (D) in

def aMiAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ → ℕ := aMi D i (pW D i ρ) (qW D i ρ) (lab σ ρ)

variable (D) in

def mainTerm (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℝ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℝ))

variable (D) in

def Lp (b : ℝ) : ℝ := Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ))

variable (D) in

def Sizes (i : Fin D.R.m) (b : ℝ) : Prop :=
  (∀ τ : D.what₂.Tau, 0 < (((D.hc τ).e i : ℚ) : ℝ) ∧ (((D.hc τ).e i : ℚ) : ℝ) ≤ 2 * b ∧
    (∀ l, 0 ≤ (((D.hc τ).v l : ℚ) : ℝ) ∧ (((D.hc τ).v l : ℚ) : ℝ) ≤ b) ∧
    ∀ l, |(((D.hc τ).b l : ℚ) : ℝ) - (((D.hc τ).e i : ℚ) : ℝ)| ≤ b) ∧
  ∀ l, ((D.R.k : ℝ) * b) ^ 8 ≤ (D.host.g l : ℝ)

variable (D) in

def deltaAtEmb (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : PolF D (Wc D i).rank (Vc D i).rank :=
  Formalism.IndefR.Datum.delta (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ)

def IsLocalLevel {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) : Prop :=
  ∃ Hl cl, P = LevelP.ofLocal Hl cl

def datV (i : Fin D.R.m) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : LevDat D.host.E ℂ (Vc D i).rank where
  r := D.R.r
  hr := r_le_V i
  t := D.R.t
  s := 1
  Pg := Pg
  Q := Q
  P := P
  cg := fun _ => m
  xq := m

def grpOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) : Subgroup (Bridge.Gf V) :=
  (Lev.toAfE V (lev D.sp.cm V.gram β L)).comap (finHom V).range.subtype

def chrOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) : grpOf V β L →* ℂˣ :=
  (Lev.levCharAfE V β L).comp ((finHom V).range.subtype.subgroupComap _)

open Classical in

def IsLevelVec (ψ : AddChar (AF D.host.F) ℂ) (θ : Datum.InfFam D) (S T : HSp D)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (f₀ f : Datum.WO S T → ℂ) : Prop :=
  Datum.IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f₀ ∧ ∃ e : AE D, Datum.IsIdemSum e (LT.Pg ∪ Q) ∧
    Datum.IsThetaAt ψ (Datum.symplO S T) (Datum.heisO ψ S T) (cA D e) (Datum.latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if Datum.IsHalf (cA D e) x ∧ Datum.IsIntM (Datum.frMapAdj S T βS βT x) then
        Datum.omegaG LT m (fun PP => Datum.redM PP (Datum.frMapAdj S T βS βT x)) *
          Datum.omegaQ Q T.rank m (-1) (fun PP => Datum.redM PP (Datum.frMapAdj S T βS βT x))
        else 0) f

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

open Classical in

def finS (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (R.Pg ∪ R.Q t).image fun PP => PP.under (𝓞 D.host.F)

def PrimeToHost (t : T) : Prop :=
  ∀ PP : Pl D.host.E, PP ∈ R.Pg ∨ PP ∈ R.Q t →
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def IsConjChars (i : Fin D.R.m) (t : T) (s : ℂ ≃+* ℂ) (cμ cη : (AE D)ˣ →* Circle)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∃ μ' η' : Formalism.L2.Host.HChar D.host.E,
    IsGalConj s 0 (R.C.mu0 i * R.xiH t) μ' ∧ IsGalConj s (1 / 2) R.C.eta η' ∧ ChrEq cμ μ' ∧ ChrEq cη η' ∧
      ∀ PP : Pl D.host.E, PP ∈ R.Pg ∨ PP ∈ R.Q t → IsRes μ' PP (m PP)

def ptAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (f : Datum.WO (Vc D i) (Wc D i) → ℂ) : PolF D (Wc D i).rank (Vc D i).rank → (Datum.WO (Vc D i) (Wc D i) → ℂ) :=
  Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f

def IsLift (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (pt : PolF D (Wc D i).rank (Vc D i).rank → (Datum.WO (Vc D i) (Wc D i) → ℂ)) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))) (HV : HMod (Bridge.Gf (Vc D i) → c.W))
    (th : HV.H →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ∀ (x : HV.H) (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)),
    IntegrableOn (fun h => Datum.thetaKO ω h g (pt (io (PiTensorProduct.tprod ℂ v) (c.ext (HV.e x) h)))) 𝓕 ν ∧
      (R.HW i σ).e (th x) (fun ρ => v ρ) g =
        Lift.thetaPInt ν 𝓕 (fun g h f => Datum.thetaKO ω h g f) pt io (c.ext (HV.e x)) (PiTensorProduct.tprod ℂ v) g

def typePart (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (t : T) (P : LevelP R.Pg D.R.r ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (R.HW i σ).H :=
  (partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) c).comap
    (R.HW i σ).e

def adjLev {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) : Y →ₗ[ℂ] X :=
  ((Nat.card P.H : ℂ))⁻¹ • LinearMap.adjoint th

def AdelicLiftScalar (F : Face D A) : Prop :=
  R.Char F → ∀ (i : Fin D.R.m) (b : ℝ), Sizes D i b → ∀ t : T, PrimeToHost R t →
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s →
  ∀ P : LevelP R.Pg D.R.r ℂ, IsLocalLevel P →
  ∀ (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), IsConjChars R i t s cμ cη m →
  ∀ ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ),
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω →
  ∀ BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) →
  ∀ f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ,
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f →
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) →
  ∀ c : CoefA (Vc D i), c.Is →
  ∀ io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io →
  ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))),
    IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)) ν 𝓕 →
  ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf (Vc D i)),
    Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y →
  ∀ HV : HMod (Bridge.Gf (Vc D i) → c.W),
    HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y) →
    (∃ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th) ∧
    ∀ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th →
      ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ t P ev, th (adjLev P th x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

end
