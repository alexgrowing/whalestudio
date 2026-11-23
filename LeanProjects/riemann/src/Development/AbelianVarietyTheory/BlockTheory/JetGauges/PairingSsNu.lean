import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.abelian₂ Formalism.MainNotions Formalism.BasicNotions

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation

section Exponents

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

variable (E) in

def pairE (ξ : Module.Dual ℤ X) (x : X) : E :=
  ∑ i, (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) i *
    ((ξ ((RingOfIntegers.basis E i) • x) : ℤ) : E)

variable (E) in

def ssNu (g : ℕ) (ξ : Module.Dual ℤ X) (χ : X × X →₀ ℤ) : E :=
  (g : E)⁻¹ * χ.sum fun p n =>
    (n : E) * (pairE E ξ p.1 * cc (pairE E ξ p.2) + cc (pairE E ξ p.1) * pairE E ξ p.2)

def ssPair (g : ℕ) (be : LinearMap.BilinForm ℤ X) (χ : X × X →₀ ℤ) : ℚ :=
  (g : ℚ)⁻¹ * χ.sum fun p n => (n : ℚ) * ((be p.1 p.2 : ℤ) : ℚ)

variable (E) in

def SSPlus (g : ℕ) (ξ : Module.Dual ℤ X) (χ : X × X →₀ ℤ) : Prop :=
  ∀ τ : E →+* ℂ, 0 ≤ (τ (ssNu E g ξ χ)).re

variable (E) in

def Separates (g : ℕ) (ξ : Module.Dual ℤ X) (be : LinearMap.BilinForm ℤ X) (χ₀ : X × X →₀ ℤ) (j : ℤ) : Prop :=
  SSPlus E g ξ χ₀ ∧ ssPair g be χ₀ = j ∧
    ∀ χ, SSPlus E g ξ χ → ssPair g be χ = j → ssNu E g ξ χ = ssNu E g ξ χ₀

example (g : ℕ) (ξ : Module.Dual ℤ X) : SSPlus E g ξ 0 := fun τ => by simp [ssNu]

example (be : LinearMap.BilinForm ℤ X) (x y : X) : ssPair 1 be (Finsupp.single (x, y) 1) = be x y := by
  simp [ssPair]

end Exponents

section Ext

variable {K : Type} [Field K] (D₀ : Out.DegPre K)

def IsLiftOver (n : ℕ) (s : ∀ Z : Over (Sp K), (Z ⟶ D₀.P.A) → Out.GtPt D₀ Z) : Prop :=
  (∀ Z b, (s Z b).b = b ^ n) ∧ (∀ Z b b', Out.GtPt.IsAdd (s Z b) (s Z b') (s Z (padd D₀.P.A b b'))) ∧
    ∀ (Z Z' : Over (Sp K)) (h : Z' ⟶ Z) b, Out.GtPt.IsPull h.left (s Z b) (s Z' (h ≫ b))

def IsDsDiv (n : ℕ) (s : ∀ Z : Over (Sp K), (Z ⟶ D₀.P.A) → Out.GtPt D₀ Z) (v : epsR K ⟶ D₀.P.A)
    (e : Out.GtPt D₀ (epsR K)) : Prop :=
  Out.GtPt.IsPull (spMap (epsScaleR ((n : K)⁻¹))) (s (epsR K) v) e

def IsTorusTan (e : Out.GtPt D₀ (epsR K)) (y : D₀.X → K) : Prop :=
  e.b = Out.DegPre.zeroT D₀ (epsR K) ∧
    ∀ χ jj, LB.Coh D₀.P.L (Out.DegPre.gtφT D₀ (epsR K) e.b χ) jj →
      ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (epsR K) e.b χ) jj →
      valR (A := DualNumber K) (𝟙 _) _ ((e.s χ).s jj).val = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (y χ)

def TauCan (k : ℕ) : Prop :=
  (∀ y, D₀.c y ^ k = 1) ∧
    ∀ y y' : D₀.X, LB.Gen.Corr D₀.P.L _ _ _ _ (D₀.tau (k • y) (k • y')) (LB.oneGen D₀.P.L)

def IsSameAV (th : D₀.P.L.Sec) (x : KeyIn K) (ψ : D₀.P.A.left ⟶ x.P.A.left) : Prop :=
  ∃ (he : eSec D₀.P.A ≫ ψ = 𝟙 _ ≫ eSec x.P.A) (w : LB.Iso D₀.P.L (x.P.L.pull ψ)),
    IsGrpPullback D₀.P.A x.P.A (𝟙 _) ψ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D₀.P.A) (fun _ => 1)) D₀.rig
      (rigPullOf ψ (𝟙 _) he x.P.L x.rig) ∧
    ∀ (jj : (x.P.L.pull ψ).ι) (i : D₀.P.L.ι)
      (h : (x.P.L.pull ψ).U jj ⊓ D₀.P.L.U i ≤ ψ ⁻¹ᵁ x.P.L.U (jj PUnit.unit)),
      (ψ.appLE _ _ h).hom (x.th.f (jj PUnit.unit)) =
        (show Γ(D₀.P.A.left, (x.P.L.pull ψ).U jj ⊓ D₀.P.L.U i) from (w.s (jj, i)).val) *
          resG _ inf_le_right (th.f i)

@[reducible] def fracAlg (σ : K →+* ℂ) : Algebra (FractionRing K) ℂ :=
  (IsFractionRing.lift (A := K) (K := FractionRing K) (g := σ) σ.injective).toAlgebra

variable {D₀} [Algebra (FractionRing K) ℂ]

def chiAt (g : Out.GtPtF D₀ ℂ) (χ : D₀.X) (jj : Fin 4 → D₀.P.L.ι) : ℂ :=
  valR (A := ℂ) (𝟙 (Sp ℂ)) _ ((g.s χ).s jj).val

def IsTorusAt (g : Out.GtPtF D₀ ℂ) (x : D₀.X → ℂ) : Prop :=
  g.b = Out.DegPre.zeroF D₀ ℂ ∧ ∀ χ jj, LB.Coh D₀.P.L (Out.DegPre.gtφ D₀ ℂ g.b χ) jj →
    ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ g.b χ) jj → chiAt g χ jj = x χ

end Ext

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

abbrev CMObj (Dw : Datum H) (c : Coeff l) : Type 1 :=
  @LamObj E _ _ _ H.starRing H l c (Dw.p - 1) (Dw.q - 1)

variable {c : Coeff l}

abbrev InputOver (o : CMObj Dw c) : Type 1 :=
  letI := H.starRing; ArcIn Dw l (RingHom.id c.F) o.K₁ (algebraMap c.F o.K₁)

def InputBuilt (n' : ℕ) (La c₁ : ℝ) (o : CMObj Dw c) (a : InputOver o) (th : a.D₀.P.L.Sec) (jj : ℤ)
    (ψ : letI := H.starRing; a.D₀.P.A.left ⟶ o.xB.P.A.left) (ξ : Module.Dual ℤ a.D₀.X)
    (χ₀ : a.D₀.X × a.D₀.X →₀ ℤ) : Prop :=
  letI := H.starRing
  0 < n' ∧ LamObjGood o (fdeg E) La ∧ IsSameAV a.D₀ th o.xB ψ ∧
  (∀ x : 𝓞 E, (a.oa.onB.act x).left ≫ ψ ≫ o.φB = ψ ≫ o.φB ≫ (o.oa.act x).left) ∧
  Module.finrank (𝓞 E) a.D₀.X = 1 ∧ ξ ≠ 0 ∧ TauCan a.D₀ n' ∧
  Separates E l.M ξ a.be χ₀ jj ∧ ((Algebra.trace ℚ E (ssNu E l.M ξ χ₀) / 2 : ℚ) : ℝ) ≤ c₁

def AreLetters (n' : ℕ) (o : CMObj Dw c) (a : InputOver o)
    (ψ : letI := H.starRing; a.D₀.P.A.left ⟶ o.xB.P.A.left) (ξ : Module.Dual ℤ a.D₀.X)
    (e : letI := H.starRing; ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR o.K₁)) : Prop :=
  letI := H.starRing
  ∃ s, IsLiftOver a.D₀ n' s ∧
    (∀ m : Fin o.xΨ.P.g, ∃ ord : Option (Fin (Dw.p - 1)) ≃ Fin (Dw.mult (o.τΨ m).1),
      IsTorusTan a.D₀ (e _ (ord none)) (fun χ => labK c o.K₁ (o.τΨ m).1 (cc (pairE E ξ χ))) ∧
      ∀ i, ∃ v : epsR o.K₁ ⟶ a.D₀.P.A,
        v.left ≫ ψ ≫ o.φB = (o.xΨ.v m).left ≫ o.φΨg ≫ (o.φΨ i).left ∧ IsDsDiv a.D₀ n' s v (e _ (ord (some i)))) ∧
    ∀ m : Fin o.x'.P.g, ∃ ord : Option (Fin (Dw.q - 1)) ≃ Fin (Dw.mult (o.τ' m).1),
      IsTorusTan a.D₀ (e _ (ord none)) (fun χ => labK c o.K₁ (o.τ' m).1 (cc (pairE E ξ χ))) ∧
      ∀ i, ∃ v : epsR o.K₁ ⟶ a.D₀.P.A,
        v.left ≫ ψ ≫ o.φB = (o.x'.v m).left ≫ o.φ'g ≫ (o.φ' i).left ∧ IsDsDiv a.D₀ n' s v (e _ (ord (some i)))

end Family

section AtRun

variable {D : D7} {T : Core D} {j : ℕ}

def IsArcOver {K₁ : Type} [Field K₁] [Algebra T.Q.c.F K₁] (d : ArcDatumAt T j K₁) : Prop :=
  d.χ ≫ d.Y.s = spMap (PowerSeries.C (R := K₁)) ≫
      spMap ((algebraMap T.Q.c.F K₁).comp (T.Q.c.V d.Wp).subtype) ∧
    (∀ x : Sp (PowerSeries K₁), d.χ x ∈ abLocus d.Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧
    ∀ x : Sp (PowerSeries K₁), PowerSeries.X ∉ x.asIdeal → d.χ x ∈ Set.range d.Y.j

def BuiltFrom (n' : ℕ) (La c₁ : ℝ) (o : CMObj (T.Q.Dw j) T.Q.c)
    (d : letI := T.Q.H.starRing; ArcDatumAt T j o.K₁)
    (ψ : letI := T.Q.H.starRing; d.a.D₀.P.A.left ⟶ o.xB.P.A.left) (ξ : Module.Dual ℤ d.a.D₀.X)
    (χ₀ : d.a.D₀.X × d.a.D₀.X →₀ ℤ) : Prop :=
  InputBuilt n' La c₁ o d.a d.th d.jj ψ ξ χ₀ ∧ AreLetters n' o d.a ψ ξ d.e ∧ IsArcOver d

def InFamOf (n' : ℕ) (La c₁ : ℝ) (o : CMObj (T.Q.Dw j) T.Q.c)
    (d : letI := T.Q.H.starRing; ArcDatumAt T j o.K₁) : Prop :=
  ∃ ψ ξ χ₀, BuiltFrom n' La c₁ o d ψ ξ χ₀

def InFam (n' : ℕ) (La c₁ : ℝ) {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : ArcDatumAt T j K₁) : Prop :=
  letI := T.Q.H.starRing
  ∃ B oa AΨ oaΨ A' oa' φΨ φ' hΨ h' xB xΨ x' φB φΨg φ'g τΨ τ' ℓΨ ℓ' Tl LamL,
    InFamOf n' La c₁ (LamObj.mk K₁ B oa AΨ oaΨ A' oa' φΨ φ' hΨ h' xB xΨ x' φB φΨg φ'g τΨ τ' ℓΨ ℓ' Tl LamL) d

end AtRun

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsCuspData {r : ℕ} (X : Data E r) (L' : Submodule (𝓞 E) (Fin r → E)) (g n' : ℕ) (La c₁ : ℝ) (ξ : Fin r → E)
    (x : Frame X.Ψ r) (ν : X.Ψ → ℝ) (lam : Fin (r - 2) → Fin r → E) : Prop :=
  0 < n' ∧ X.IsIso ξ ∧ x ∈ X.dom ∧ ∑ τ, ν τ ≤ c₁ ∧
  (∀ i, lam i ∈ L' ∧ herm X.Gm (lam i) ξ = 0) ∧
  LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
  (∀ i k : Fin (r - 2), (i : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam i) (lam k) = 0) ∧
  (∀ i : Fin (r - 2), (i : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam i) (lam i))).re) ∧
    X.Jz x (X.ucomp x ξ (X.embV (lam i))) = Complex.I • X.ucomp x ξ (X.embV (lam i))) ∧
  (∀ i : Fin (r - 2), X.p0 - 1 ≤ (i : ℕ) → (∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam i) (lam i))).re < 0) ∧
    X.Jz x (X.ucomp x ξ (X.embV (lam i))) = -(Complex.I • X.ucomp x ξ (X.embV (lam i)))) ∧
  (∀ i (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam i) (lam i))‖ ≤ La ^ 2) ∧
  (∀ w ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧ (n' : ℂ) • X.aproj x ξ (X.embV w) = X.embV (e • ξ)) ∧
  ∃ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la ∧
    (∀ ga ∈ X.Γ, (∀ v ∈ X.Λ, ∃ w ∈ X.Λ,
      Matrix.mulVec (ga : Matrix (Fin r) (Fin r) E) v - v = (g : E) • w) → X.χ la ga = 1) ∧
    X.fj la ξ ν P x ≠ 0

abbrev cPt {K : Type} [Field K] (σ : K →+* ℂ) : Over (Sp (𝓞 K)) :=
  Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K)))

def IsTorsionParam [StarRing (𝓞 E)] {K : Type} [Field K] (σ : K →+* ℂ) (A : Out.PolAV (Sp (𝓞 K)))
    (oa : A.OAct (𝓞 E)) (AA : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (pa : E → (cPt σ ⟶ A.A)) : Prop :=
  (∀ a b, pa (a + b) = padd A.A (pa a) (pa b)) ∧ (∀ (x : 𝓞 E) a, pa ((x : E) * a) = pa a ≫ oa.act x) ∧
    (∀ a, pa a = 1 ↔ a ∈ AA) ∧ ∀ (z : cPt σ ⟶ A.A) (k : ℕ), 0 < k → z ^ k = 1 → ∃ a, pa a = z

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l}

def IsMotiveOf {K : Type} [Field K] {bF : c.F →+* K} (a : ArcIn Dw l (RingHom.id c.F) K bF) (σ : K →+* ℂ)
    {r : ℕ} (X : Data E r) (ξ : Fin r → E) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P₀ : (Fin r → E) → Fin g → ℂ)
    (t : Dw.La → X.Λ) (y : X.Λ →ₗ[𝓞 E] a.D₀.X)
    (ex : letI := fracAlg σ; (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) : Prop :=
  letI := fracAlg σ
  letI := H.starRing
  Function.Surjective y ∧ (∀ v, y v = 0 ↔ herm X.Gm v ξ = 0) ∧
  (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) ∧ Function.Surjective ex ∧
  (∀ (x : 𝓞 E) z, GtAct a.oa x (ex z) (ex (fun k => ty k (x : E) * z k))) ∧
  IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) ∧
  (∀ χ jj, DifferentiableOn ℂ (fun z => chiAt (ex z) χ jj)
    {z | ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (ex z).b χ) jj}) ∧
  (∀ z, (ex z).IsZero ↔ ∃ v : X.Λ, y v = 0 ∧ z = P₀ v) ∧
  (∀ v : X.Λ, Out.GtPtF.IsIota (y v) (ex (P₀ v))) ∧
  (∀ v : X.Λ, (∃ b : E, (v : Fin r → E) = b • ξ) → ∀ s : ℂ, ∃ x, IsTorusAt (ex (s • P₀ v)) x ∧
    ∀ v' : X.Λ, x (y v') = eTwoPi (-(s * (EFf X.ξ0 X.Gm v v' : ℂ)))) ∧
  (∀ (k : ℕ) (v v' : X.Λ) (z : ℂˣ), 0 < k → y v = 0 → y v' = 0 →
    (z : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EFf X.ξ0 X.Gm v v' : ℂ) / k) →
    Out.WeilIs a.D₀.P.A a.D₀.P.L k (ex ((k : ℂ)⁻¹ • P₀ v)).b (ex ((k : ℂ)⁻¹ • P₀ v')).b (unitOn z)) ∧
  (∀ v, ∃ q : Out.QkPt a.D₀ ℂ l.A, q.y = y (t v) ∧ q.g = ex ((l.A : ℂ)⁻¹ • P₀ (t v)) ∧
    ∀ q', QkExt (algebraMap _ ℂ) (a.etaA v) q' → Out.QkPt.Equiv a.D₀ ℂ q q') ∧
  ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
    ∃ q : Out.QkPt a.D₀ ℂ l.M, q.y = y (t v) ∧ q.g = ex ((l.M : ℂ)⁻¹ • P₀ (t v)) ∧
      ∀ q', QkExt (algebraMap _ ℂ) (a.eta v) q' → Out.QkPt.Equiv a.D₀ ℂ q q'

variable {Xo : Moduli Dw l} {σ₀ : c.F →+* ℂ} {r : ℕ}

def IsMarkingAt (U : Unf Xo c σ₀ r) (k : U.Comp) (x : (U.X k).dom) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (t : Dw.La → (U.X k).Λ) : Prop :=
  ∃ (F : FamilyUnif Xo (σ₀.comp (IntermediateField.inclusion c.le).toRingHom) (fun m => relab c σ₀ (e m).1))
    (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 E] (U.X k).Λ) (Pm : (F.Di i).La →+ (Fin g → ℂ)),
    (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = EFf (U.X k).ξ0 (U.X k).Gm (φ a) (φ b)) ∧
    (∀ a m, Pm a m = perFr (U.X k) x.1 (φ a : Fin r → E) (relab c σ₀ (e m).1) (e m).2) ∧
    IsPeriod (F.Di i) (fun m => relab c σ₀ (e m).1) Pm ∧ (U.un k x).x = F.u i Pm ∧
    (∀ τ (n : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single (e.symm ⟨τ, n⟩) 1)
      ((U.un k x).u τ n)) ∧
    ∀ v, t v = φ (F.t i v)

def TiedAt (AA : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (U : Unf Xo c σ₀ r) (k : U.Comp) (x : (U.X k).dom)
    (ξ : Fin r → E) (ν : (U.X k).Ψ → ℝ) (lam : Fin (r - 2) → Fin r → E) (o : CMObj Dw c) (a : InputOver o)
    (ψ : letI := H.starRing; a.D₀.P.A.left ⟶ o.xB.P.A.left) (ξ' : Module.Dual ℤ a.D₀.X)
    (χ₀ : a.D₀.X × a.D₀.X →₀ ℤ) (σ₁ : letI := H.starRing; o.K₁ →+* ℂ) : Prop :=
  letI := H.starRing
  letI := fracAlg σ₁
  σ₁.comp (algebraMap c.F o.K₁) = σ₀ ∧
  ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (t : Dw.La → (U.X k).Λ) (s₀ : (U.X k).Ψ → ℂ)
    (P₀ : (Fin r → E) → Fin g → ℂ) (y : (U.X k).Λ →ₗ[𝓞 E] a.D₀.X) (ex : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ)
    (paΨ : E → (cPt σ₁ ⟶ o.AΨ.A)) (pa' : E → (cPt σ₁ ⟶ o.A'.A)),
    IsMarkingAt U k x e t ∧
    (∀ v m, P₀ v m = perFr (U.X k) ((U.X k).flow ξ s₀ x.1) v (relab c σ₀ (e m).1) (e m).2) ∧
    IsMotiveOf a σ₁ (U.X k) ξ (fun m => relab c σ₀ (e m).1) P₀ t y ex ∧
    (∀ v : (U.X k).Λ, ((ξ' (y v) : ℤ) : ℚ) = EFf (U.X k).ξ0 (U.X k).Gm v ξ) ∧
    (∀ τ : (U.X k).Ψ, ν τ = (τ.1 (ssNu E l.M ξ' χ₀)).re) ∧
    IsTorsionParam σ₁ o.AΨ o.oaΨ AA paΨ ∧ IsTorsionParam σ₁ o.A' o.oa' AA pa' ∧
    r - 2 = (Dw.q - 1) + (Dw.p - 1) ∧
    (∀ (i : Fin (Dw.q - 1)) (m : Fin (r - 2)), (m : ℕ) = i →
      (o.h' i : E) = herm (U.X k).Gm (lam m) (lam m) ∧
      ∀ b : E, (pa' b ≫ o.φ' i).left = (ex (P₀ (b • lam m))).b.left ≫ ψ ≫ o.φB) ∧
    ∀ (i : Fin (Dw.p - 1)) (m : Fin (r - 2)), (m : ℕ) = (Dw.q - 1) + i →
      (o.hΨ i : E) = -herm (U.X k).Gm (lam m) (lam m) ∧
      ∀ b : E, (paΨ b ≫ o.φΨ i).left = (ex (P₀ (b • lam m))).b.left ≫ ψ ≫ o.φB

end Comparison₂

section Claims

variable {D : D7}

def CuspDataOn (T : Core D) (j : ℕ) (σ₀ : T.Q.c.F →+* ℂ) (k : (T.U j σ₀).Comp) (n' : ℕ) (La c₁ : ℝ)
    (ξ : Fin D.R.r → D.host.E) (x : ((T.U j σ₀).X k).dom) (ν : ((T.U j σ₀).X k).Ψ → ℝ)
    (lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E) : Prop :=
  GoodEmb T.Q.c σ₀ ∧ ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ₀).X k ∧ Xx.g = T.Q.l.M ∧
    Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧
    IsCuspData ((T.U j σ₀).X k) Xx.L' T.Q.l.M n' La c₁ ξ x.1 ν lam

def InputExists (T : Core D) (j : ℕ) : Prop :=
  LawsCore T → InR D j → ∀ σ₀ k n' La c₁ ξ x ν lam, CuspDataOn T j σ₀ k n' La c₁ ξ x ν lam →
    ∃ (o : CMObj (T.Q.Dw j) T.Q.c) (a : InputOver o) (th : a.D₀.P.L.Sec) (jj : ℤ) (ψ : _) (ξ' : _) (χ₀ : _) (σ₁ : _),
      InputBuilt n' La c₁ o a th jj ψ ξ' χ₀ ∧ (∃ e, AreLetters n' o a ψ ξ' e) ∧
      TiedAt D.host.AA (T.U j σ₀) k x ξ ν lam o a ψ ξ' χ₀ σ₁

def MemberExists (T : Core D) (j : ℕ) : Prop :=
  LawsCore T → InR D j → ∀ (Wp : ValuationSubring ℂ) (Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype), Y.N4 →
    ∀ σ₀ k n' La c₁ ξ x ν lam, CuspDataOn T j σ₀ k n' La c₁ ξ x ν lam →
      letI := T.Q.H.starRing
      ∃ (o : CMObj (T.Q.Dw j) T.Q.c) (d : ArcDatumAt T j o.K₁) (ψ : _) (ξ' : _) (χ₀ : _) (σ₁ : _),
        (⟨d.Wp, d.Y⟩ : Σ W : ValuationSubring ℂ, Model (T.Q.Xo j) T.Q.c (T.Q.c.V W).subtype) = ⟨Wp, Y⟩ ∧
        (∀ mu, BuiltFrom n' La c₁ o { d with «μ» := mu } ψ ξ' χ₀) ∧
        TiedAt D.host.AA (T.U j σ₀) k x ξ ν lam o d.a ψ ξ' χ₀ σ₁

def CuspFamilySt : Prop := ∀ (D : D7) (T : Core D) (j : ℕ), InputExists T j ∧ MemberExists T j

end Claims

end GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation
