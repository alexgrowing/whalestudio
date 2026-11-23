import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.QbridgeOf
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.Chi0WeightedSum
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.abelian₂
open Formalism.MainNotions Formalism.BasicNotions

section Exponents

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev pairE {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X) (x : X) : E :=
  Formalism.L2.Pj.QAt.Arch.pairE (E := E) ξ x

def nrm (a : E) : E := a * FD.cc a

def TotNonneg (ν : E) : Prop := ∀ τ : E →+* ℂ, 0 ≤ (τ ν).re

def IsExponent {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (g : ℕ) (ξ : Module.Dual ℤ X)
    (β : LinearMap.BilinForm ℤ X) (ν : E) (j : ℤ) : Prop :=
  ∃ n : X →₀ ℤ, ν = (g : E)⁻¹ * ∑ x ∈ n.support, (n x : E) * nrm (pairE ξ x) ∧
    (j : ℚ) = (g : ℚ)⁻¹ * ∑ x ∈ n.support, (n x : ℚ) * (((β x x : ℤ) : ℚ) / 2)

def Separates {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (g : ℕ) (ξ : Module.Dual ℤ X)
    (β : LinearMap.BilinForm ℤ X) (ν₀ : E) (j : ℤ) : Prop :=
  TotNonneg ν₀ ∧ IsExponent g ξ β ν₀ j ∧ ∀ ν : E, TotNonneg ν → IsExponent g ξ β ν j → ν = ν₀

example {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (g : ℕ) (ξ : Module.Dual ℤ X) (β : LinearMap.BilinForm ℤ X) :
    IsExponent g ξ β (0 : E) 0 := ⟨0, by simp, by simp⟩

def TauPowCanonical {R : Type} [CommRing R] [IsDomain R] (D₀ : Out.DegPre R) (k : ℕ) : Prop :=
  ∀ y y' : D₀.X, LB.Gen.Corr D₀.P.L _ _ _ _ (D₀.tau (k • y) (k • y')) (LB.oneGen D₀.P.L)

end Exponents

variable {D : D7}

abbrev CMObj (T : Core D) (j : ℕ) : Type 1 :=
  @LamObj D.host.E _ _ _ T.Q.H.starRing T.Q.H T.Q.l T.Q.c ((T.Q.Dw j).p - 1) ((T.Q.Dw j).q - 1)

variable {T : Core D} {j : ℕ}

abbrev CMObj.fld (o : CMObj T j) : Type := @LamObj.K₁ _ _ _ _ T.Q.H.starRing _ _ _ _ _ o

instance (o : CMObj T j) : Field o.fld := @LamObj.fK _ _ _ _ T.Q.H.starRing _ _ _ _ _ o
instance (o : CMObj T j) : NumberField o.fld := @LamObj.nfK _ _ _ _ T.Q.H.starRing _ _ _ _ _ o
instance (o : CMObj T j) : Algebra T.Q.c.F o.fld := @LamObj.algK _ _ _ _ T.Q.H.starRing _ _ _ _ _ o

abbrev CMObj.abB (o : CMObj T j) : Out.PolAV (Sp (𝓞 o.fld)) := @LamObj.B _ _ _ _ T.Q.H.starRing _ _ _ _ _ o

def withMonomial {K₁ : Type} [Field K₁] [Algebra T.Q.c.F K₁] [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)]
    (d : ArcDatumAt T j K₁) (m : ArcLt (T.Q.Dw j) →₀ ℕ) : ArcDatumAt T j K₁ :=
  ⟨d.Wp, d.Y, d.a, d.χ, d.chiOver, d.W, d.e, d.yF, d.th, d.arcDatum_isArc_point_basis, d.isArc3, m, d.jj⟩

def IsSectionOver {R : Type} [CommRing R] [IsDomain R] (D₀ : Out.DegPre R) (n : ℕ)
    (s : ∀ Z : Over (Sp R), (Z ⟶ D₀.P.A) → Out.GtPt D₀ Z) : Prop :=
  (∀ Z b, (s Z b).b = b ^ n) ∧ (∀ Z b b', Out.GtPt.IsAdd (s Z b) (s Z b') (s Z (b * b'))) ∧
  ∀ (Z Z' : Over (Sp R)) (h : Z' ⟶ Z) b, Out.GtPt.IsPull h.left (s Z b) (s Z' (h ≫ b))

def IsTorusTangent {K₁ : Type} [Field K₁] {D₀ : Out.DegPre K₁} (v : Out.GtPt D₀ (epsR K₁)) (ℓ : D₀.X → K₁) : Prop :=
  v.b = Out.DegPre.zeroT D₀ (epsR K₁) ∧ ∀ χ i, LB.Coh D₀.P.L (Out.DegPre.gtφT D₀ (epsR K₁) v.b χ) i →
    ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (epsR K₁) v.b χ) i →
    valR (A := DualNumber K₁) (𝟙 _) _ ((v.s χ).s i).val = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (ℓ χ)

def IsEtaLetter {K₁ : Type} [Field K₁] [NumberField K₁] {D₀ : Out.DegPre K₁} (n : ℕ)
    (s : ∀ Z : Over (Sp K₁), (Z ⟶ D₀.P.A) → Out.GtPt D₀ Z) {A₀ B : Out.PolAV (Sp (𝓞 K₁))} (x : KeyIn K₁)
    (φx : x.P.A.left ⟶ A₀.A.left) (φ₀ : D₀.P.A.left ⟶ B.A.left) (ph : A₀.A ⟶ B.A) (v : epsR K₁ ⟶ x.P.A)
    (w : Out.GtPt D₀ (epsR K₁)) : Prop :=
  ∃ f : x.P.A ⟶ D₀.P.A, f.left ≫ φ₀ = φx ≫ ph.left ∧
    Out.GtPt.IsPull (spMap (epsScaleR ((n : K₁)⁻¹))) (s (epsR K₁) (v ≫ f)) w

def Built (n' : ℕ) (La c₁ : ℝ) (o : CMObj T j) (d : ArcDatumAt T j o.fld) (ξ : Module.Dual ℤ d.a.D₀.X) (ν : D.host.E)
    (φ₀ : d.a.D₀.P.A.left ⟶ o.abB.A.left) : Prop :=
  letI := T.Q.H.starRing

  LamObjGood o (FD.fdeg D.host.E) La ∧

  (∃ hg hth v hv, o.xB = ⟨d.a.D₀.P, hg, d.a.D₀.rig, d.a.D₀.rig_gen, d.th, hth, v, hv⟩) ∧ HEq φ₀ o.φB ∧
  (∀ a : 𝓞 D.host.E, (d.a.oa.onB.act a).left ≫ φ₀ = φ₀ ≫ (o.oa.act a).left) ∧
  (∀ y, ∃ cO : 𝟙_ (Over (Sp (𝓞 o.fld))) ⟶ o.B.A, (d.a.D₀.c y).left ≫ φ₀ = gmap o.fld ≫ cO.left) ∧

  Module.finrank (𝓞 D.host.E) d.a.D₀.X = 1 ∧ ξ ≠ 0 ∧ 0 < n' ∧ (∀ y, d.a.D₀.c y ^ n' = 1) ∧
  TauPowCanonical d.a.D₀ n' ∧

  Separates T.Q.l.M ξ d.a.be ν d.jj ∧ (Algebra.trace ℚ D.host.E ν : ℝ) / 2 ≤ c₁ ∧

  (∃ s : ∀ Z : Over (Sp o.fld), (Z ⟶ d.a.D₀.P.A) → Out.GtPt d.a.D₀ Z, IsSectionOver d.a.D₀ n' s ∧
    (∀ (τ : D.host.E →+* ℂ) (h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0),
      ∃ ε : Option (Fin ((T.Q.Dw j).p - 1)) ≃ Fin ((T.Q.Dw j).mult τ),
        IsTorusTangent (D₀ := d.a.D₀) (d.e τ (ε none)) (fun χ => labK T.Q.c o.fld (conjEmb τ) (pairE ξ χ)) ∧
        ∀ i, IsEtaLetter n' s o.xΨ o.φΨg φ₀ (o.φΨ i) (o.xΨ.v (o.τΨ.symm ⟨τ, h⟩)) (d.e τ (ε (some i)))) ∧
    ∀ (τ : D.host.E →+* ℂ) (h : τ (T.Q.H.rt : D.host.E) ≠ T.Q.H.rt0),
      ∃ ε : Option (Fin ((T.Q.Dw j).q - 1)) ≃ Fin ((T.Q.Dw j).mult τ),
        IsTorusTangent (D₀ := d.a.D₀) (d.e τ (ε none)) (fun χ => labK T.Q.c o.fld (conjEmb τ) (pairE ξ χ)) ∧
        ∀ i, IsEtaLetter n' s o.x' o.φ'g φ₀ (o.φ' i) (o.x'.v (o.τ'.symm ⟨τ, h⟩)) (d.e τ (ε (some i)))) ∧
  ArcLieBasis d.W d.e ∧

  d.χ ≫ d.Y.s = spMap (PowerSeries.C (R := o.fld)) ≫
    spMap ((algebraMap T.Q.c.F o.fld).comp (T.Q.c.V d.Wp).subtype) ∧
  (∀ x : Sp (PowerSeries o.fld), d.χ x ∈ abLocus d.Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧
  ∀ x : Sp (PowerSeries o.fld), PowerSeries.X ∉ x.asIdeal → d.χ x ∈ Set.range d.Y.j

def InFamilyOver (n' : ℕ) (La c₁ : ℝ) (o : CMObj T j) (d : ArcDatumAt T j o.fld) : Prop :=
  ∃ ξ ν φ₀, Built n' La c₁ o d ξ ν φ₀

def InFamily (T : Core D) (j : ℕ) (n' : ℕ) (La c₁ : ℝ) (K₁ : Type) [fK : Field K₁] [NumberField K₁]
    [alg : Algebra T.Q.c.F K₁] (d : ArcDatumAt T j K₁) : Prop :=
  letI := T.Q.H.starRing
  ∃ (o : CMObj T j) (d' : ArcDatumAt T j o.fld),
    o.fld = K₁ ∧ HEq o.fK fK ∧ HEq o.algK alg ∧ HEq d' d ∧ InFamilyOver n' La c₁ o d'

section Component

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def CuspGeom (X : FD.Data E r) (L' : Submodule (𝓞 E) (Fin r → E)) (n' : ℕ) (La : ℝ) (ξ : Fin r → E)
    (x : FD.Frame X.Ψ r) (lam : Fin (r - 2) → Fin r → E) : Prop :=
  X.IsIso ξ ∧ x ∈ X.dom ∧ 0 < n' ∧
  (∀ i, lam i ∈ L' ∧ FD.herm X.Gm (lam i) ξ = 0) ∧
  LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
  (∀ i k : Fin (r - 2), (i : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → FD.herm X.Gm (lam i) (lam k) = 0) ∧
  (∀ i : Fin (r - 2), (i : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (FD.herm X.Gm (lam i) (lam i))).re) ∧
    X.Jz x (X.ucomp x ξ (X.embV (lam i))) = Complex.I • X.ucomp x ξ (X.embV (lam i))) ∧
  (∀ i : Fin (r - 2), X.p0 - 1 ≤ (i : ℕ) → (∀ τ : X.Ψ, (τ.1 (FD.herm X.Gm (lam i) (lam i))).re < 0) ∧
    X.Jz x (X.ucomp x ξ (X.embV (lam i))) = -(Complex.I • X.ucomp x ξ (X.embV (lam i)))) ∧
  (∀ i (τ : X.Ψ), ‖τ.1 (FD.herm X.Gm (lam i) (lam i))‖ ≤ La ^ 2) ∧
  ∀ m ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧ (n' : ℂ) • X.aproj x ξ (X.embV m) = X.embV (e • ξ)

def LatExponent (X : FD.Data E r) (g : ℕ) (ξ : Fin r → E) (ν : X.Ψ → ℝ) : Prop :=
  (∀ τ, 0 ≤ ν τ) ∧ ∃ n : (Fin r → E) →₀ ℤ, (∀ v ∈ n.support, v ∈ X.Λ) ∧
    ∀ τ : X.Ψ, (ν τ : ℂ) = τ.1 ((g : E)⁻¹ * ∑ v ∈ n.support, (n v : E) * nrm (-X.ξ0 * FD.herm X.Gm v ξ))

end Component

section Comparison₂

variable {K₁ : Type} [Field K₁]

abbrev algAt (σ₁ : K₁ →+* ℂ) : Algebra (FractionRing K₁) ℂ :=
  (IsFractionRing.lift (K := FractionRing K₁) (g := σ₁) σ₁.injective).toAlgebra

variable [Algebra (FractionRing K₁) ℂ]

def coordVal {D₀ : Out.DegPre K₁} (g : Out.GtPtF D₀ ℂ) (χ : D₀.X) (i : Fin 4 → D₀.P.L.ι) : ℂ :=
  valR (A := ℂ) (𝟙 (Sp ℂ)) _ ((g.s χ).s i).val

def IsTorusPoint {D₀ : Out.DegPre K₁} (g : Out.GtPtF D₀ ℂ) (t : D₀.X → ℂ) : Prop :=
  g.b = Out.DegPre.zeroF D₀ ℂ ∧ ∀ χ i, LB.Coh D₀.P.L (Out.DegPre.gtφ D₀ ℂ g.b χ) i →
    ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ g.b χ) i → coordVal g χ i = t χ

def IsTorsionParam {E : Type} [Field E] [NumberField E] [NumberField K₁]
    (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {A₀ : Out.PolAV (Sp (𝓞 K₁))} (act : 𝓞 E → (A₀.A ⟶ A₀.A))
    (x : KeyIn K₁) (φx : x.P.A.left ⟶ A₀.A.left) (κ : E → (Out.TF (R := K₁) ℂ ⟶ x.P.A)) : Prop :=
  (∀ a b, κ (a + b) = κ a * κ b) ∧ (∀ a, κ a = 1 ↔ a ∈ 𝔄) ∧
  (∀ (z : Out.TF (R := K₁) ℂ ⟶ x.P.A) (n : ℕ), 0 < n → z ^ n = 1 → ∃ a, κ a = z) ∧
  ∀ (b : 𝓞 E) a, (κ ((b : E) * a)).left ≫ φx = (κ a).left ≫ φx ≫ (act b).left

end Comparison₂

def perVec {σ : T.Q.c.F →+* ℂ} (X : FD.Data D.host.E D.R.r) {g : ℕ}
    (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) (x : FD.Frame X.Ψ D.R.r) (v : Fin D.R.r → D.host.E) :
    Fin g → ℂ :=
  fun i => perFr X x v (relab T.Q.c σ (e i).1) (e i).2

def IsMarking {σ : T.Q.c.F →+* ℂ} (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom) {g : ℕ}
    (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
    (t : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ) : Prop :=
  ∃ ex : (Fin g → ℂ) → (Over.mk (show Sp ℂ ⟶ (T.Q.Xo j).X from ((T.U j σ).un k x).x) ⟶ (T.Q.Xo j).univ.t.G),
    (∀ z w, ex (z + w) = ex z * ex w) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).left)) ∧
    (∀ τ (i : Fin ((T.Q.Dw j).mult τ)), IsDerivAt0 (fun z => (ex z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      (((T.U j σ).un k x).u τ i)) ∧
    (∀ z, ex z = 1 ↔ ∃ v ∈ ((T.U j σ).X k).Λ, z = perVec (σ := σ) _ e x.1 v) ∧
    (∀ a, toUnit _ ≫ (T.Q.Xo j).univ.etaA a = ex ((T.Q.l.A : ℂ)⁻¹ • perVec (σ := σ) _ e x.1 (t a))) ∧
    ∀ a ∈ T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La),
      toUnit _ ≫ (T.Q.Xo j).univ.eta a = ex ((T.Q.l.M : ℂ)⁻¹ • perVec (σ := σ) _ e x.1 (t a))

def TiedAt (o : CMObj T j) (d : ArcDatumAt T j o.fld) (ξ₁ : Module.Dual ℤ d.a.D₀.X) (ν₁ : D.host.E)
    (φ₀ : d.a.D₀.P.A.left ⟶ o.abB.A.left)
    {σ : T.Q.c.F →+* ℂ} (σ₁ : o.fld →+* ℂ) (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom)
    (ξ : Fin D.R.r → D.host.E) (ν : ((T.U j σ).X k).Ψ → ℝ) (lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E) : Prop :=
  letI := T.Q.H.starRing
  letI := algAt σ₁
  let X := (T.U j σ).X k
  let EF : (Fin D.R.r → D.host.E) → (Fin D.R.r → D.host.E) → ℚ := FD.EFf X.ξ0 X.Gm
  σ₁.comp (algebraMap T.Q.c.F o.fld) = σ ∧
  ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) (s₀ : X.Ψ → ℂ)
    (P₀ : (Fin D.R.r → D.host.E) → (Fin g → ℂ)) (y : X.Λ →ₗ[𝓞 D.host.E] d.a.D₀.X)
    (ex₀ : (Fin g → ℂ) → Out.GtPtF d.a.D₀ ℂ) (t : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] X.Λ),
    P₀ = perVec (σ := σ) X e (X.flow ξ s₀ x.1) ∧

    Function.Surjective y ∧ (∀ v : X.Λ, y v = 0 ↔ FD.herm X.Gm (v : Fin D.R.r → D.host.E) ξ = 0) ∧

    (∀ z z', (ex₀ z).IsAdd (ex₀ z') (ex₀ (z + z'))) ∧ Function.Surjective ex₀ ∧
    (∀ (a : 𝓞 D.host.E) z,
      GtAct d.a.oa a (ex₀ z) (ex₀ (fun i => relab T.Q.c σ (e i).1 (a : D.host.E) * z i))) ∧
    IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex₀ z).b.left)) ∧
    (∀ χ i, DifferentiableOn ℂ (fun z => coordVal (ex₀ z) χ i)
      {z | ⊤ ≤ LB.wchart d.a.D₀.P.L (Out.DegPre.gtφ d.a.D₀ ℂ (ex₀ z).b χ) i}) ∧
    (∀ z, (ex₀ z).IsZero ↔ ∃ v : X.Λ, y v = 0 ∧ z = P₀ v) ∧

    (∀ v : X.Λ, Out.GtPtF.IsIota (y v) (ex₀ (P₀ v))) ∧
    (∀ a : D.host.E, a • ξ ∈ X.Λ → ∀ w : ℂ, ∃ tv, IsTorusPoint (ex₀ (w • P₀ (a • ξ))) tv ∧
      ∀ v' : X.Λ, tv (y v') = eTwoPi (-(w * (EF (a • ξ) v' : ℂ)))) ∧
    (∀ (n : ℕ) (v v' : X.Λ) (c : ℂˣ), 0 < n → y v = 0 → y v' = 0 →
      (c : ℂ) = eTwoPi (-((EF v v' : ℂ) / n)) →
      Out.WeilIs d.a.D₀.P.A d.a.D₀.P.L n (ex₀ ((n : ℂ)⁻¹ • P₀ v)).b (ex₀ ((n : ℂ)⁻¹ • P₀ v')).b (unitOn c)) ∧

    IsMarking k x e t ∧
    (∀ v, ∃ q : Out.QkPt d.a.D₀ ℂ T.Q.l.A, q.y = y (t v) ∧ q.g = ex₀ ((T.Q.l.A : ℂ)⁻¹ • P₀ (t v)) ∧
      ∀ q', QkExt (algebraMap _ ℂ) (d.a.etaA v) q' → Out.QkPt.Equiv d.a.D₀ ℂ q q') ∧
    (∀ v ∈ T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La),
      ∃ q : Out.QkPt d.a.D₀ ℂ T.Q.l.M, q.y = y (t v) ∧ q.g = ex₀ ((T.Q.l.M : ℂ)⁻¹ • P₀ (t v)) ∧
        ∀ q', QkExt (algebraMap _ ℂ) (d.a.eta v) q' → Out.QkPt.Equiv d.a.D₀ ℂ q q') ∧

    (∀ v : X.Λ, ((ξ₁ (y v) : ℤ) : ℚ) = -EF ξ v) ∧
    (∀ τ : X.Ψ, (ν τ : ℂ) = τ.1 ν₁) ∧

    ∃ (ε : Fin ((T.Q.Dw j).q - 1) ⊕ Fin ((T.Q.Dw j).p - 1) ≃ Fin (D.R.r - 2))
      (κΨ : D.host.E → (Out.TF (R := o.fld) ℂ ⟶ o.xΨ.P.A)) (κ' : D.host.E → (Out.TF (R := o.fld) ℂ ⟶ o.x'.P.A)),
      (∀ i, (ε (.inl i) : ℕ) = i) ∧ (∀ i, (ε (.inr i) : ℕ) = X.p0 - 1 + i) ∧
      IsTorsionParam D.host.AA o.oaΨ.act o.xΨ o.φΨg κΨ ∧ IsTorsionParam D.host.AA o.oa'.act o.x' o.φ'g κ' ∧
      (∀ i, (o.hΨ i : D.host.E) = -FD.herm X.Gm (lam (ε (.inr i))) (lam (ε (.inr i))) ∧
        ∀ a, (κΨ a).left ≫ o.φΨg ≫ (o.φΨ i).left = (ex₀ (P₀ (a • lam (ε (.inr i))))).b.left ≫ φ₀) ∧
      ∀ i, (o.h' i : D.host.E) = FD.herm X.Gm (lam (ε (.inl i))) (lam (ε (.inl i))) ∧
        ∀ a, (κ' a).left ≫ o.φ'g ≫ (o.φ' i).left = (ex₀ (P₀ (a • lam (ε (.inl i))))).b.left ≫ φ₀

def HasTiedMember (n' : ℕ) (La c₁ : ℝ) (Wp : ValuationSubring ℂ)
    (Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype) {σ : T.Q.c.F →+* ℂ} (k : (T.U j σ).Comp)
    (x : ((T.U j σ).X k).dom) (ξ : Fin D.R.r → D.host.E) (ν : ((T.U j σ).X k).Ψ → ℝ)
    (lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E) : Prop :=
  letI := T.Q.H.starRing
  ∃ (o : CMObj T j) (d : ArcDatumAt T j o.fld) (ξ₁ : Module.Dual ℤ d.a.D₀.X) (ν₁ : D.host.E)
    (φ₀ : d.a.D₀.P.A.left ⟶ o.abB.A.left) (σ₁ : o.fld →+* ℂ), d.Wp = Wp ∧ HEq d.Y Y ∧
    Built n' La c₁ o d ξ₁ ν₁ φ₀ ∧ TiedAt o d ξ₁ ν₁ φ₀ σ₁ k x ξ ν lam

def IsComponentData {σ : T.Q.c.F →+* ℂ} (k : (T.U j σ).Comp) (Xx : FD.DataX D.host.E D.R.r) : Prop :=
  Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧
    Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u}

def ExistsMemberSt : Prop :=
  ∀ (D : D7) (T : Core D) (j : ℕ), LawsCore T → InR D j →
    ∀ (Wp : ValuationSubring ℂ) (Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype), Y.N4 →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (Xx : FD.DataX D.host.E D.R.r),
      IsComponentData k Xx →
      ∀ (n' : ℕ) (La c₁ : ℝ) (ξ : Fin D.R.r → D.host.E) (x : ((T.U j σ).X k).dom) (ν : ((T.U j σ).X k).Ψ → ℝ)
        (lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E),
        CuspGeom ((T.U j σ).X k) Xx.L' n' La ξ x.1 lam → LatExponent ((T.U j σ).X k) T.Q.l.M ξ ν →
        ∑ τ, ν τ ≤ c₁ → HasTiedMember n' La c₁ Wp Y k x ξ ν lam

def SupportSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r) (Xx : FD.DataX E r), Xx.toData = X →
    ∀ (la : FD.Wt X.Ψ r) (P : FD.Frame X.Ψ r → ℂ), P ∈ X.SS la →
      (∀ gm ∈ X.Γ, (∀ v ∈ X.Λ, ∃ w ∈ X.Λ,
        Matrix.mulVec (gm : Matrix (Fin r) (Fin r) E) v - v = (Xx.g : E) • w) → X.χ la gm = 1) →
      ∀ (ξ : Fin r → E), X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → LatExponent X Xx.g ξ ν

def ExistsMemberOfCuspData : Prop :=
  ∀ (D : D7) (T : Core D) (j : ℕ), LawsCore T → InR D j →
    ∀ (Wp : ValuationSubring ℂ) (Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype), Y.N4 →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (Xx : FD.DataX D.host.E D.R.r),
      IsComponentData k Xx →
      ∀ (n' : ℕ) (La c₁ : ℝ) (ξ : Fin D.R.r → D.host.E) (x : ((T.U j σ).X k).dom) (ν : ((T.U j σ).X k).Ψ → ℝ)
        (lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E) (la : FD.Wt ((T.U j σ).X k).Ψ D.R.r)
        (P : FD.Frame ((T.U j σ).X k).Ψ D.R.r → ℂ),
        P ∈ ((T.U j σ).X k).SS la →
        (∀ gm ∈ ((T.U j σ).X k).Γ, (∀ v ∈ ((T.U j σ).X k).Λ, ∃ w ∈ ((T.U j σ).X k).Λ,
          Matrix.mulVec (gm : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) v - v = (Xx.g : D.host.E) • w) →
          ((T.U j σ).X k).χ la gm = 1) →
        CuspGeom ((T.U j σ).X k) Xx.L' n' La ξ x.1 lam → ((T.U j σ).X k).fj la ξ ν P x.1 ≠ 0 →
        ∑ τ, ν τ ≤ c₁ → HasTiedMember n' La c₁ Wp Y k x ξ ν lam

theorem realized_of (h : ExistsMemberSt) (hs : SupportSt) : ExistsMemberOfCuspData := by
  intro D T j hT hj Wp Y hY σ hσ k Xx hX n' La c₁ ξ x ν lam la P hP hχ hg hne hc
  refine h D T j hT hj Wp Y hY σ hσ k Xx hX n' La c₁ ξ x ν lam hg ?_ hc
  have := hs _ _ _ Xx hX.1 la P hP hχ ξ hg.1 ν x.1 x.2 hne
  rwa [hX.2.1] at this

end GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms
