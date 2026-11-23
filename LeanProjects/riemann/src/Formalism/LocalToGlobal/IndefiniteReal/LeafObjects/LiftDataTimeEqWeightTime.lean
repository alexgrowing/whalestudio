import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.OnObjOf3XEq
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.LeafMeans.LeastMultipleEightGeBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import Development.WeilBound.SupplementaryPages.FaceFrameMatrix

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace Formalism.IndefR.Obj.SlopeGeometry

section Tuple

open ReciprocityTheory.ChartRestriction.G.T0 (TVar OmS sImg)

variable (K : Type) [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  {Ω : Type} [Field Ω] [Algebra K Ω]

def rkL (M : Submodule (𝓞 K) V) : ℕ := Module.finrank K (Submodule.span K (M : Set V))

def IsFull (M : Submodule (𝓞 K) V) (x : Fin (rkL K M) → V) : Prop := (∀ i, x i ∈ M) ∧ LinearIndependent K x

def degAt (M : Submodule (𝓞 K) V) (ip : (K →+* ℂ) → V → V → ℂ) (x : Fin (rkL K M) → V) : ℝ :=
  (Real.log ((Submodule.span (𝓞 K) (Set.range x)).toAddSubgroup.relIndex M.toAddSubgroup : ℕ) -
    ∑ σ : K →+* ℂ, Real.log ‖(Matrix.of fun a b => ip σ (x a) (x b)).det‖ / 2) / (Module.finrank ℚ K : ℝ)

def degL (M : Submodule (𝓞 K) V) (ip : (K →+* ℂ) → V → V → ℂ) : ℝ := degAt K M ip (Classical.epsilon (IsFull K M))

abbrev Gens (V : Type) : Type := Σ n : ℕ, Fin (n + 1) → V

instance : Nonempty (Gens V) := ⟨⟨0, fun _ => 0⟩⟩

def IsGen (W : Submodule (𝓞 K) V) (ev : V → Ω) (g : Gens V) : Prop :=
  Submodule.span (𝓞 K) (Set.range g.2) = W ∧ ev (g.2 0) ≠ 0

def xs (ev : V → Ω) (g : Gens V) (k : Fin g.1) : Ω := ev (g.2 k.succ) / ev (g.2 0)

def delAt (Dn : ℕ) (ev : V → Ω) (g : Gens V) : ℕ :=
  Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := Dn) (0 : Fin (g.1 + 1)) (xs ev g)))) (OmS Ω Dn g.1)

open Classical in

def delL (Dn : ℕ) (W : Submodule (𝓞 K) V) (ev : V → Ω) : ℕ :=
  if ∃ g, IsGen K W ev g then delAt K Dn ev (Classical.epsilon (IsGen K W ev)) else 0

def cImg {Dn N : ℕ} (x : Fin N → Ω) (p : TVar Dn N) : MvPolynomial (Fin (Dn + 1) × Fin N) Ω :=
  Fin.cases (motive := fun _ => MvPolynomial (Fin (Dn + 1) × Fin N) Ω)
    (-∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (x k)) (fun k => MvPolynomial.X (p.1, k)) p.2

def IsChow (Dn : ℕ) {N : ℕ} (x : Fin N → Ω) (f : MvPolynomial (TVar Dn N) K) : Prop :=
  f ≠ 0 ∧ RingHom.ker (MvPolynomial.aeval (R := K) (cImg (Dn := Dn) x)) = Ideal.span {f}

def finHt {σ : Type} (f : MvPolynomial σ K) : ℝ :=
  -Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanFinset (𝓞 K) f.support fun m => f.coeff m) : ℚ) : ℝ) /
    (Module.finrank ℚ K : ℝ)

def sphP (n : ℕ) : Measure (Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :=
  ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ • (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere

def onbMat (n : ℕ) (g : Gens V) (ipσ : V → V → ℂ) : Matrix (Fin (g.1 + 1)) (Fin n) ℂ :=
  Classical.epsilon fun A : Matrix (Fin (g.1 + 1)) (Fin n) ℂ =>
    A.conjTranspose * (Matrix.of fun k l => ipσ (g.2 l) (g.2 k)) * A = 1

def archHt (Dn n : ℕ) (g : Gens V) (σ : K →+* ℂ) (ipσ : V → V → ℂ) (f : MvPolynomial (TVar Dn g.1) K) : ℝ :=
  ∫ t : Fin (Dn + 1) → Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
    Real.log ‖MvPolynomial.eval (fun p : TVar Dn g.1 =>
      (onbMat n g ipσ).mulVec (fun a => (t p.1 : EuclideanSpace ℂ (Fin n)) a) p.2) (MvPolynomial.map σ f)‖
    ∂(Measure.pi fun _ => sphP n)

def htAt (Dn n : ℕ) (g : Gens V) (ip : (K →+* ℂ) → V → V → ℂ) (f : MvPolynomial (TVar Dn g.1) K) : ℝ :=
  (finHt K f + (∑ σ : K →+* ℂ, archHt K Dn n g σ (ip σ) f) / (Module.finrank ℚ K : ℝ)) / (f.totalDegree : ℝ) +
    ((harmonic (n - 1) : ℚ) : ℝ) / 2

open Classical in

def htL (Dn : ℕ) (W : Submodule (𝓞 K) V) (ev : V → Ω) (ip : (K →+* ℂ) → V → V → ℂ) : ℝ :=
  if (∃ g, IsGen K W ev g) ∧ ∃ f, IsChow K Dn (xs ev (Classical.epsilon (IsGen K W ev))) f then
    htAt K Dn (rkL K W) (Classical.epsilon (IsGen K W ev)) ip
      (Classical.epsilon (IsChow K Dn (xs ev (Classical.epsilon (IsGen K W ev)))))
  else 0

end Tuple

section Forms

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

abbrev WZ (E : Type) [Field E] : Type := (E →+* ℂ) × ℕ → ℤ

def exZ (Dw : Datum H) (a : WZ E) : Ix Dw → ℤ
  | none => 0
  | some x => a (x.1, x.2)

def secWZ {K : Type} [Field K] {ι : Type} [Fintype ι] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop) (e : ι → ℤ) :
    Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
    f p y' = (∏ i, ((t i ^ e i : (p.R)ˣ) : p.R)) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

def latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]
    (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) :
    Submodule (𝓞 K) R :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (f : R) : f ∈ latIn C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f :=
  ⟨fun ⟨g, hg, e⟩ => e ▸ ⟨g.2, hg⟩, fun h => ⟨⟨f, h.1⟩, h.2, rfl⟩⟩

variable (Xo : Moduli Dw l) (c : Coeff l)

def secZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secWZ (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (exZ Dw a)

theorem secZ_nat (a : (E →+* ℂ) × ℕ → ℕ) : secZ Xo c (fun x => (a x : ℤ)) = sec Xo c a 0 := by
  have h : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      (∏ i, ((t i ^ exZ Dw (fun x => (a x : ℤ)) i : Sˣ) : S)) = wchar (ex Dw a 0) t := by
    intro S _ t
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, ex]
  ext f
  refine and_congr Iff.rfl (forall_congr' fun p => forall_congr' fun t => forall_congr' fun y => forall_congr' fun y' =>
    forall_congr' fun _ => ?_)
  rw [h]

variable {Xo c} in
open Classical in

def laZ {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : WZ E) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0)
    else -a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ))

theorem laZ_nat {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) :
    laZ U (fun x => (a x : ℤ)) = laU U a 0 := by
  funext k τ j
  simp [laZ, laU]

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secZ Xo c a ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a)).comap (rdU (U σ))

theorem cuspZ_nat (a : (E →+* ℂ) × ℕ → ℕ) : cuspZ Xo c U (fun x => (a x : ℤ)) = cusp Xo c U a 0 := by
  unfold cuspZ cusp
  simp only [secZ_nat, laZ_nat]

variable {Xo c}

def evL (h : GenFrEx Xo c) (Z : Comp Xo c) : Rul Xo c →ₗ[c.F] Om Z :=
  evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)

theorem evL_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : evL h Z f = evC h Z f := rfl

def cuspOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule c.F (Rul Xo c) :=
  cuspZ Xo c U a ⊓ ⨅ (Z' : Comp Xo c) (_ : Z' ≠ Z), LinearMap.ker (evL h Z')

def latOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule (𝓞 c.F) (Rul Xo c) :=
  latIn (cuspOn U h a Z) (valSet Xo c (algCls Xo c)) isVal_valSet

def volL (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) (Dn : ℕ) : ℝ :=
  limsup (fun n : ℕ => (Dn.factorial : ℝ) * (Module.finrank c.F (cuspOn U h (n • a) Z) : ℝ) / (n : ℝ) ^ Dn) atTop

def lieFacZ (Dw : Datum H) (x : ℝ) (a : WZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

variable {D : D7} (W : HSp D) (dict : ∀ σ, GA D W → Σ k, Frame ((U σ).X k).Ψ r)

def ipAll (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  ∫ q, jFn W σ (rdU (U σ)) (dict σ) (fun _ => 1) f q * conj (jFn W σ (rdU (U σ)) (dict σ) (fun _ => 1) g q) ∂(muQ1 W)

open Classical in

def ipOn (x : ℝ) (a : WZ E) (e : Rul Xo c) (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  let z : ℂ := ((lieFacZ Dw x a ^ 2 : ℝ) : ℂ) * ipAll U W dict (goodOf c σ) f g / ipAll U W dict (goodOf c σ) e e
  if GoodEmb c σ then z else conj z

end Forms

section Numbers

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef.Tree Formalism.IndefR.Links IxMeans IxMeans.MeansTie IxMeans.MeansTie2
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb)

variable (D : D7) (P : SlopeBoundParameters) (i : Fin D.R.m)

def jp : ℕ := D.R.m - ((i : ℕ) + 1)

def pp : ℕ := (D.R.sigW ((i : ℕ) + 1)).1

theorem pp_add_jp : pp D i + jp D i = D.R.r := by
  have := i.2
  have := D.R.m_add_three_le_k
  simp only [pp, jp, Ranks.sigW, Ranks.r]; omega

def anc : ℕ := D.R.k - 2

def Dn : ℕ := D.R.f * D.R.r.choose 2

def Tn : ℕ := ⌈P.PPT ^ 2 * (Dn D : ℝ) ^ 2 * P.k / P.m⌉₊

def c0n : ℕ := leastMultipleEightBound D.R.f D.R.r (jp D i)

def kappaZ (τ : D.what₂.Tau) (n : ℕ) : ℤ :=
  if n < pp D i then (aPl D i (pp D i) τ n : ℤ) + ((D.R.nV / 2 : ℕ) : ℤ)
  else -(aMi D i (pp D i) (jp D i) τ (D.R.r - 1 - n) : ℤ) - ((D.R.nV / 2 : ℕ) : ℤ)

def uZ (τ : D.what₂.Tau) (n : Fin D.R.r) : ℤ := kappaZ D i τ n - kappaZ D i τ (anc D)

def uR (τ : D.what₂.Tau) (n : Fin D.R.r) : ℝ := (uZ D i τ n : ℝ)

def u1R (τ : D.what₂.Tau) : Fin D.R.r → ℝ := firstGapVector D.R.r (pp D i) (anc D) (Tn D P) (Dn D) (c0n D i) (uR D i τ)

def upR (τ : D.what₂.Tau) : Fin D.R.r → ℝ := upDef D.R.r (pp D i) (anc D) (Tn D P) (Dn D) (c0n D i) (uR D i τ)

def remR (τ : D.what₂.Tau) : Fin D.R.r → ℝ :=
  anchored (fun k => gap (fun n => uMinus D.R.r (pp D i) (c0n D i) (uR D i τ) n - MeansTie.kap D.R.r (pp D i) n) k -
    ((Tn D P : ℝ) + Dn D + 1) * firstVectorGaps D.R.r (pp D i) (Tn D P) (Dn D) (c0n D i) (uR D i τ) k) (anc D)

def uTR (τ : D.what₂.Tau) (n : Fin D.R.r) : ℝ :=
  MeansTie.kap D.R.r (pp D i) n + (u1R D P i τ n + remR D P i τ n) + ((Dn D : ℝ) + Tn D P) * u1R D P i τ n

theorem anchored_int {N : ℕ} (G : ℕ → ℝ) (hG : ∀ k, ∃ z : ℤ, G k = z) (A : ℕ) (n : Fin N) :
    ∃ z : ℤ, anchored G A n = z := by
  choose g hg using hG
  unfold anchored
  split_ifs
  · exact ⟨∑ k ∈ Finset.Ico (n : ℕ) A, g k, by simp [hg]⟩
  · exact ⟨-∑ k ∈ Finset.Ico A (n : ℕ), g k, by simp [hg]⟩

theorem weights_int (τ : D.what₂.Tau) (n : Fin D.R.r) :
    (∃ z : ℤ, u1R D P i τ n = z) ∧ (∃ z : ℤ, upR D P i τ n = z) ∧ ∃ z : ℤ, uTR D P i τ n = z := by
  obtain ⟨a, ha⟩ : ∃ z : ℤ, u1R D P i τ n = z := anchored_int _ (fun _ => ⟨_, rfl⟩) _ _
  have hk : ∀ n : Fin D.R.r, ∃ z : ℤ, MeansTie.kap D.R.r (pp D i) n = z := fun n => by
    unfold MeansTie.kap
    split_ifs
    · exact ⟨(D.R.r : ℤ) - 2 * (pp D i : ℤ) + 1 + 2 * ((n : ℕ) : ℤ), by push_cast; ring⟩
    · exact ⟨-(2 * (pp D i : ℤ)) - (D.R.r : ℤ) + 1 + 2 * ((n : ℕ) : ℤ), by push_cast; ring⟩
  have hd : ∀ n : Fin D.R.r, ∃ z : ℤ, de D.R.r (pp D i) n = z := fun n => by
    unfold de
    split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by simp⟩
  choose kz hkz using hk
  choose dz hdz using hd
  obtain ⟨b, hb⟩ : ∃ z : ℤ, remR D P i τ n = z := by
    refine anchored_int _ (fun k => ?_) _ _
    obtain ⟨g, hg⟩ : ∃ z : ℤ, gap (fun n => uMinus D.R.r (pp D i) (c0n D i) (uR D i τ) n - MeansTie.kap D.R.r (pp D i) n) k = z := by
      unfold gap
      split_ifs with h
      · exact ⟨uZ D i τ ⟨k, by omega⟩ - (c0n D i : ℤ) * dz ⟨k, by omega⟩ - kz ⟨k, by omega⟩ -
          (uZ D i τ ⟨k + 1, h⟩ - (c0n D i : ℤ) * dz ⟨k + 1, h⟩ - kz ⟨k + 1, h⟩), by simp [uMinus, uR, hkz, hdz]⟩
      · exact ⟨0, by simp⟩
    obtain ⟨w, hw⟩ : ∃ z : ℤ, firstVectorGaps D.R.r (pp D i) (Tn D P) (Dn D) (c0n D i) (uR D i τ) k = z := ⟨_, rfl⟩
    exact ⟨g - ((Tn D P : ℤ) + (Dn D : ℤ) + 1) * w, by rw [hg, hw]; push_cast; ring⟩
  refine ⟨⟨a, ha⟩, ⟨a - 3 * (D.R.r : ℤ) * dz n, ?_⟩, ⟨kz n + (a + b) + ((Dn D : ℤ) + (Tn D P : ℤ)) * a, ?_⟩⟩
  · show u1R D P i τ n - 3 * (D.R.r : ℝ) * de D.R.r (pp D i) n = _
    rw [ha, hdz]; push_cast; ring
  · unfold uTR
    rw [ha, hb, hkz]; push_cast; ring

theorem uTR_gap (τ : D.what₂.Tau) (k : ℕ) (h : k + 1 < D.R.r) :
    uTR D P i τ ⟨k, by omega⟩ - uTR D P i τ ⟨k + 1, h⟩ =
      uMinus D.R.r (pp D i) (c0n D i) (uR D i τ) ⟨k, by omega⟩ - uMinus D.R.r (pp D i) (c0n D i) (uR D i τ) ⟨k + 1, h⟩ := by
  have h1 : u1R D P i τ ⟨k, by omega⟩ - u1R D P i τ ⟨k + 1, h⟩ =
      firstVectorGaps D.R.r (pp D i) (Tn D P) (Dn D) (c0n D i) (uR D i τ) k := anchored_gap _ _ _ h
  have h2 := anchored_gap (N := D.R.r) (fun k => gap (fun n => uMinus D.R.r (pp D i) (c0n D i) (uR D i τ) n -
    MeansTie.kap D.R.r (pp D i) n) k - ((Tn D P : ℝ) + Dn D + 1) *
      firstVectorGaps D.R.r (pp D i) (Tn D P) (Dn D) (c0n D i) (uR D i τ) k) (anc D) k h
  have h3 : gap (fun n => uMinus D.R.r (pp D i) (c0n D i) (uR D i τ) n - MeansTie.kap D.R.r (pp D i) n) k =
      (uMinus D.R.r (pp D i) (c0n D i) (uR D i τ) ⟨k, by omega⟩ - MeansTie.kap D.R.r (pp D i) ⟨k, by omega⟩) -
        (uMinus D.R.r (pp D i) (c0n D i) (uR D i τ) ⟨k + 1, h⟩ - MeansTie.kap D.R.r (pp D i) ⟨k + 1, h⟩) := by
    unfold gap; rw [dif_pos h]
  change remR D P i τ ⟨k, _⟩ - remR D P i τ ⟨k + 1, h⟩ = gap _ k - _ at h2
  rw [h3] at h2
  unfold uTR
  linear_combination h2 + ((Tn D P : ℝ) + Dn D + 1) * h1

def degW {Tau : Type} [Fintype Tau] {N : ℕ} (lam : Tau → Fin N → ℝ) : ℝ :=
  ∏ τ, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (lam τ a - lam τ b)

def rhoB : ℝ := 1 - degW (upR D P i) / degW (u1R D P i)

def entZ {N : ℕ} (v : Fin N → ℝ) (n : ℕ) : ℤ := if h : n < N then ⌊v ⟨n, h⟩⌋ else 0

open Classical in

def wtZ' (lam : D.what₂.Tau → Fin D.R.r → ℝ) : WZ D.host.E := fun x =>
  ∑ t : D.what₂.Tau, ((if x.1 = DV.tauEmb D t ∧ x.2 < pp D i then entZ (lam t) x.2 else 0) +
    if x.1 = conjEmb (DV.tauEmb D t) ∧ x.2 < jp D i then -entZ (lam t) (D.R.r - 1 - x.2) else 0)

def Np : ℕ := 8 * ((max (D.R.f * (pp D i * (pp D i + 1) + jp D i * (jp D i + 1))) (8 * D.R.f * D.R.r + 4) + 7) / 8)

theorem Np_bounds : 8 * D.R.f * D.R.r + 4 ≤ Np D i ∧ Np D i ≤ 16 * D.R.f * D.R.r ^ 2 + 8 := by
  have h := pp_add_jp D i
  have hk := D.R.m_add_three_le_k
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hf : 1 ≤ D.R.f := by
    have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)
    unfold Ranks.f Ranks.n; omega
  have h1 : pp D i * (pp D i + 1) + jp D i * (jp D i + 1) ≤ 2 * D.R.r ^ 2 := by rw [← h] at hr ⊢; nlinarith
  have h2 : D.R.f * (pp D i * (pp D i + 1) + jp D i * (jp D i + 1)) ≤ D.R.f * (2 * D.R.r ^ 2) := Nat.mul_le_mul_left _ h1
  have h3 : D.R.f * D.R.r ≤ D.R.f * D.R.r ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  have h4 : 1 ≤ D.R.f * D.R.r := Nat.mul_pos hf hr
  have e1 : D.R.f * (2 * D.R.r ^ 2) = 2 * (D.R.f * D.R.r ^ 2) := by ring
  have e2 : 16 * D.R.f * D.R.r ^ 2 = 16 * (D.R.f * D.R.r ^ 2) := by ring
  have e3 : 8 * D.R.f * D.R.r = 8 * (D.R.f * D.R.r) := by ring
  unfold Np
  rw [e2, e3]
  rw [e1] at h2
  omega

def DF : ℝ := ∑ τ, ∑ n : Fin D.R.r,
  if (n : ℕ) < pp D i then u1R D P i τ n - (entZ (u1R D P i τ) (pp D i - 1) : ℝ) + 1
  else (entZ (u1R D P i τ) (pp D i - 1) : ℝ) - u1R D P i τ n - 1 - Np D i

def Rd : ℝ := P.rd ^ 7
def DFs : ℝ := 7 * P.f * P.k * P.b

def cP : ℕ := sInf {n : ℕ | Rd P ^ 7 * DFs P ^ 2 ≤ (3 : ℝ) ^ (2 * n)}

def cS : ℕ := sInf {n : ℕ | Rd P ^ 8 * DFs P ^ 2 ≤ (3 : ℝ) ^ n ∧ max 4 (2 * cP P) ≤ n}

def Msh : ℕ := D.host.g 0 * D.host.g 1 * 3 ^ cS P * 5 ^ cS P

def dE : ℕ := (discr D.host.E).natAbs

def eE : ℕ := sInf {n : ℕ | 0 < n ∧ ((n : ℕ) : 𝓞 D.host.E) ∈ differentIdeal ℤ (𝓞 D.host.E)}

def n0 : ℕ := 5 ^ (2 * D.R.f * D.R.r ^ 2)

def cubicPeriodConstant : ℝ :=
  let Pq : ℝ := 8 * (D.R.f : ℝ) ^ 3 * (D.R.m : ℝ) ^ 2
  let A : ℝ := 16 * 5 ^ 4 * (eE D : ℝ) * P.rd ^ D.R.f * (2 * (D.R.f : ℝ) * D.R.m) ^ 2
  2 * ((D.R.f : ℝ) * D.R.m * D.R.r + Pq * Real.log A + Pq * Real.log Pq + 3) + 4 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log 5

def P0 : ℝ :=
  let gA : ℝ := (D.R.f : ℝ) * D.R.r
  let ds : ℝ := 2 * (D.R.f : ℝ) * (min (pp D i) (jp D i) : ℕ)
  let p1 : ℝ := 1 + gA * Real.log (1 + 6 * Real.sqrt (gA * 3 ^ (2 * cP P)))
  let A' : ℝ := max 1 ((D.R.r : ℝ) * ds / 4)
  if jp D i = 0 then (D.R.r : ℝ) * p1
  else (D.R.r : ℝ) * (p1 + (1 + ds * Real.log (3 * ds)) + ds) + A' * Real.log (4 * Rd P * ds ^ 2 * A' * 5 ^ 4)

def Ncn : ℕ := classNumber D.host.E * (D.host.g 0 * D.host.g 1 * 5 ^ 4) ^ (2 * D.R.f)

def c1n : ℝ := |((pp D i : ℝ) - jp D i) / 2 * P.logOm + (jp D i : ℝ) * (2 * Real.log (Real.sqrt P.dK) - Real.log P.rd)|

def lvOf (lmu : ℝ) (eloc : ℕ → Finset ℝ) : Leaves D.what₂.Tau where
  dE := dE D
  level := Msh D P
  q1 := D.host.QS / 2 * D.host.q
  d := D.host.d
  g1 := D.host.g 0
  g2 := D.host.g 1
  rr := 3
  rr' := 5
  r0 := n0 D
  P0 := P0 D P i
  logmu := lmu
  cubicPeriodConstant := cubicPeriodConstant D P
  c1 := c1n D P i
  Nc := Ncn D
  bigp := fun _ => pp D i
  A := anc D
  eloc := eloc

theorem lvOf_ram (lmu : ℝ) (eloc : ℕ → Finset ℝ) :
    2 * (lvOf D P i lmu eloc).q1 * (lvOf D P i lmu eloc).d = D.host.QS * D.host.q * D.host.d := by
  have h2 : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
  show 2 * (D.host.QS / 2 * D.host.q) * D.host.d = _
  rw [← mul_assoc 2, Nat.mul_div_cancel' h2]

variable (r4 : ℝ) {ι : Type} [Fintype ι] (sl : ι → ℝ)

def pack0 : MeansPack D.what₂.Tau ι where
  N := D.R.r
  f := D.R.f
  T := Tn D P
  D := Dn D
  jp := jp D i
  m := D.R.m
  nc := Np D i
  u := uR D i
  u1 := u1R D P i
  up := upR D P i
  c0 := c0n D i
  b := P.b
  rd := P.rd
  x := P.x
  Lp := P.Lc
  h0 := P.η / P.m
  fourthRootConstant := r4
  sl := sl
  e := 0
  SB := ∅
  cpp := cppDef
  vdd := fun q => (padicValNat q (dE D) : ℝ) / (2 * (D.R.f : ℝ))
  Pinf := 0
  PPe := 0
  XW := 0

def packOf (lmu : ℝ) (eloc : ℕ → Finset ℝ) (e : ℕ →₀ ℝ) : MeansPack D.what₂.Tau ι :=
  { pack0 D P i r4 sl with
    e := e
    SB := (lvOf D P i lmu eloc).SBDef (pack0 D P i r4 sl)
    PPe := (lvOf D P i lmu eloc).PPeDef (pack0 D P i r4 sl)
    XW := XWDef (pack0 D P i r4 sl)
    Pinf := (lvOf D P i lmu eloc).PinfDef (pack0 D P i r4 sl) }

def baseErrorConstant : ℝ := (pack0 D P i 0 (fun _ : Unit => 0)).E0

def Xn : ℝ := (pack0 D P i r4 (fun _ : Unit => 0)).X

def Qccn (lmu : ℝ) : ℝ := (packOf D P i 0 (fun _ : Unit => 0) lmu (fun _ => ∅) 0).Qcc

theorem base_error_constant_eq : baseErrorConstant D P i = (D.R.f : ℝ) * D.R.r * ((c0n D i : ℝ) + 4 * D.R.r) := rfl

theorem Xn_eq : Xn D P i r4 = (100 + 9 * |r4|) * P.LL0 * ∑ τ, ∑ n, |upR D P i τ n| := rfl

end Numbers

section Geo

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Indef.Tree IxMeans IxMeans.MeansTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure SharpGeo (Q : Par D) (M : ℕ) : Type 1 where
  l : Level Q.H
  c : Coeff l
  Xo : ∀ i : Fin D.R.m, Moduli (Q.Dw ((i : ℕ) + 1)) l
  U : ∀ i (σ : c.F →+* ℂ), Unf (Xo i) c σ D.R.r
  dict : ∀ (i : Fin D.R.m) σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U i σ).X k).Ψ D.R.r

  e : ∀ i, Comp (Xo i) c → Rul (Xo i) c
  gen : ∀ i, GenFrEx (Xo i) c
  pins : Q.Pins
  level : l.M = M ∧ l.A = 1 ∧ l.Mb ≤ Q.l.Mb
  field : Q.c.F ≤ c.F

  comps : ∀ i, Nat.card (Comp (Xo i) c) = Fintype.card (U i c.F.val.toRingHom).Comp
  genT : ∀ i, GenFromTest (Xo i) c (gen i)
  evalWD : ∀ i, EvalWD (K := c.F) (fun S _ _ => FrPt (Xo i) c S) (fun φ y z => FrMap φ y z)
  unf : ∀ i σ, GoodEmb c σ → IsUnf (U i σ)
  unTest : ∀ i σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt (Xo i) c S) (fun φ y z => FrMap φ y z) ((U i σ).un k x)
  chiTriv : ∀ i σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U i σ).X k).Γ,
    ((U i σ).X k).χ (laU (U i σ) a n k) γ = 1

  dictU : ∀ (i : Fin D.R.m) σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK (D.sp.W ((i : ℕ) + 1)) l.M Kf ∧
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W ((i : ℕ) + 1)) (dict i σ) Kf th hr ∧
    ∀ g τ k, ‖dmin ((U i σ).X (dict i σ g).1).Gm (dict i σ g).2 τ k‖ = 1
  modelW : ∀ (i : Fin D.R.m) σ, GoodEmb c σ → ∃ hr : (D.sp.W ((i : ℕ) + 1)).rank = D.R.r,
    ∀ k, ModelW (D.sp.W ((i : ℕ) + 1)) hr ((U i σ).X k)
  xiAbs : ∀ i σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U i σ).X k).ξ0‖ = xiR D
  finVol : ∀ i : Fin D.R.m, FinVol (D.sp.W ((i : ℕ) + 1))
  ptNe : ∀ i, IntFrNe (Xo i) c (algCls (Xo i) c)
  intAll : ∀ i, IntAll (Xo i) c
  e_sec : ∀ i Z, e i Z ∈ sec (Xo i) c 0 0
  e_val : ∀ i Z, evC (gen i) Z (e i Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC (gen i) Z' (e i Z) = 0

theorem SharpGeo.card_pos {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : 0 < Nat.card (Comp (S.Xo i) S.c) := by
  rw [S.comps i]
  exact Fintype.card_pos_iff.mpr ⟨(S.dict i _ 1).1⟩

instance SharpGeo.ne {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : Nonempty (Comp (S.Xo i) S.c) :=
  (Nat.card_pos_iff.mp (S.card_pos i)).1

instance SharpGeo.fin {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : Fintype (Comp (S.Xo i) S.c) :=
  @Fintype.ofFinite _ (Nat.card_pos_iff.mp (S.card_pos i)).2

variable {Q : Par D} (P : SlopeBoundParameters) (S : SharpGeo Q (Msh D P)) (i : Fin D.R.m)

abbrev Cmp : Type := Comp (S.Xo i) S.c

abbrev latW (lam : D.what₂.Tau → Fin D.R.r → ℝ) (Z : Cmp P S i) : Submodule (𝓞 S.c.F) (Rul (S.Xo i) S.c) :=
  latOn (S.U i) (S.gen i) (wtZ' D i lam) Z

abbrev ipW (lam : D.what₂.Tau → Fin D.R.r → ℝ) (Z : Cmp P S i) :
    (S.c.F →+* ℂ) → Rul (S.Xo i) S.c → Rul (S.Xo i) S.c → ℂ :=
  ipOn (S.U i) (D.sp.W ((i : ℕ) + 1)) (S.dict i) (xiR D) (wtZ' D i lam) (S.e i Z)

def delC (Z : Cmp P S i) : ℝ := (delL S.c.F (Dn D) (latW P S i (u1R D P i) Z) (evC (S.gen i) Z) : ℝ)

def htC (Z : Cmp P S i) : ℝ := htL S.c.F (Dn D) (latW P S i (u1R D P i) Z) (evC (S.gen i) Z) (ipW P S i (u1R D P i) Z)

def rkC (Z : Cmp P S i) : ℝ := (rkL S.c.F (latW P S i (uTR D P i) Z) : ℝ)

def degC (Z : Cmp P S i) : ℝ := degL S.c.F (latW P S i (uTR D P i) Z) (ipW P S i (uTR D P i) Z)

def volC (Z : Cmp P S i) : ℝ := volL (S.U i) (S.gen i) (wtZ' D i (upR D P i)) Z (Dn D)

def delP : ℝ := volC P S i (Classical.arbitrary _)

structure MbarIn where
  top : Cmp P S i → ℚ → ℝ
  dg : Cmp P S i → ℚ → ℝ
  dg_lim : ∀ Z, Tendsto (dg Z) (𝓝[>] 0) (𝓝 (volC P S i Z))
  conv : ∀ Z, ∃ y, Tendsto (fun s => top Z s / (((Dn D : ℝ) + 1) * dg Z s)) (𝓝[>] 0) (𝓝 y)

def slC (B : MbarIn P S i) (Z : Cmp P S i) : ℝ :=
  limUnder (𝓝[>] (0 : ℚ)) fun s => B.top Z s / (((Dn D : ℝ) + 1) * B.dg Z s)

theorem slC_tendsto (B : MbarIn P S i) (Z : Cmp P S i) :
    Tendsto (fun s => B.top Z s / (((Dn D : ℝ) + 1) * B.dg Z s)) (𝓝[>] 0) (𝓝 (slC P S i B Z)) :=
  tendsto_nhds_limUnder (B.conv Z)

def rndDown {K : Type} [Field K] (la : HeightOneSpectrum (𝓞 K)) (q : ℕ) (m : ℝ) : ℝ :=
  (⌊(multiplicity la.asIdeal (Ideal.span {((q : ℕ) : 𝓞 K)}) : ℝ) * m⌋ : ℝ) /
    (multiplicity la.asIdeal (Ideal.span {((q : ℕ) : 𝓞 K)}) : ℝ)

structure ELocIn where
  supNu : HeightOneSpectrum (𝓞 S.c.F) → Cmp P S i → ℝ
  mEta : HeightOneSpectrum (𝓞 S.c.F) → Cmp P S i → ℝ
  fin : {la : HeightOneSpectrum (𝓞 S.c.F) | ∃ (q : ℕ) (Z : Cmp P S i), q.Prime ∧ ((q : ℕ) : 𝓞 S.c.F) ∈ la.asIdeal ∧
    0 < supNu la Z - rndDown la q (mEta la Z)}.Finite

variable (El : ELocIn P S i)

def eLa (q : ℕ) (la : HeightOneSpectrum (𝓞 S.c.F)) (Z : Cmp P S i) : ℝ :=
  if q = D.host.g 0 ∨ q = D.host.g 1 then DF D P i / ((q : ℝ) - 1) + 1
  else El.supNu la Z - rndDown la q (El.mEta la Z)

theorem over_finite {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q.Prime) :
    {la : HeightOneSpectrum (𝓞 K) | ((q : ℕ) : 𝓞 K) ∈ la.asIdeal}.Finite := by
  have h0 : Ideal.span {((q : ℕ) : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero
  refine (Ideal.finite_factors h0).subset fun la hla => ?_
  exact Ideal.dvd_span_singleton.mpr hla

open Classical in

def elocOf (q : ℕ) : Finset ℝ :=
  if hq : q.Prime then ((over_finite (K := S.c.F) hq).toFinset ×ˢ Finset.univ).image fun x => eLa P S i El q x.1 x.2 else ∅

theorem elocOf_nonempty {q : ℕ} (hq : q.Prime) : (elocOf P S i El q).Nonempty := by
  classical
  have hu : Ideal.span {((q : ℕ) : 𝓞 S.c.F)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have h1 : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 S.c.F)}) = 1 := by
      rw [Ideal.span_singleton_eq_top.mpr h, Ideal.absNorm_top]
    rw [Ideal.absNorm_span_natCast] at h1
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact hq.one_lt.ne' h2
    · exact Module.finrank_pos.ne' h2
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hu
  have hmem : ((q : ℕ) : 𝓞 S.c.F) ∈ m := hle (Ideal.subset_span rfl)
  have hb : m ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hmem
    exact hq.ne_zero (by exact_mod_cast hmem)
  unfold elocOf
  rw [dif_pos hq]
  refine Finset.Nonempty.image ⟨(⟨m, hm.isPrime, hb⟩, Classical.arbitrary _), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩⟩ _
  simpa using hmem

theorem prime_unique {K : Type} [Field K] (la : HeightOneSpectrum (𝓞 K)) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (h : ((q : ℕ) : 𝓞 K) ∈ la.asIdeal) (h' : ((q' : ℕ) : 𝓞 K) ∈ la.asIdeal) : q = q' := by
  by_contra hne
  have hc : IsCoprime ((q : ℕ) : 𝓞 K) ((q' : ℕ) : 𝓞 K) := ((Nat.coprime_primes hq hq').mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hab ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left a h)
    (la.asIdeal.mul_mem_left b h')))

theorem Msh_pos : 0 < Msh D P := by
  have h0 := (D.host.g_prime 0).pos
  have h1 := (D.host.g_prime 1).pos
  unfold Msh; positivity

theorem e_finite (r4 lmu : ℝ) (sl : Cmp P S i → ℝ) :
    (Function.support ((lvOf D P i lmu (elocOf P S i El)).eDef (pack0 D P i r4 sl))).Finite := by
  classical
  have hd : 0 < dE D := Int.natAbs_pos.mpr (discr_ne_zero _)
  have hM := Msh_pos P (D := D)
  have hq1 : 0 < D.host.q := by have := D.host.qd_big.1; omega
  have hd1 : 0 < D.host.d := by have := D.host.qd_big.2; omega
  have hS1 : 0 < D.host.QS := D.host.QS_pos
  have hB : {q : ℕ | ∃ la ∈ El.fin.toFinset, q.Prime ∧ ((q : ℕ) : 𝓞 S.c.F) ∈ la.asIdeal}.Finite := by
    have : {q : ℕ | ∃ la ∈ El.fin.toFinset, q.Prime ∧ ((q : ℕ) : 𝓞 S.c.F) ∈ la.asIdeal} =
        ⋃ la ∈ ((El.fin.toFinset : Finset (HeightOneSpectrum (𝓞 S.c.F))) : Set (HeightOneSpectrum (𝓞 S.c.F))),
          {q : ℕ | q.Prime ∧ ((q : ℕ) : 𝓞 S.c.F) ∈ la.asIdeal} := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    rw [this]
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun la _ => Set.Subsingleton.finite fun q hq q' hq' => ?_
    exact prime_unique la hq.1 hq'.1 hq.2 hq'.2
  refine (((hB.union (Set.finite_le_nat (2 * dE D * Msh D P))).union
    (Set.finite_le_nat (D.host.QS * D.host.q * D.host.d))).union (Set.toFinite {D.host.g 0, D.host.g 1})).subset fun q hq => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, not_le] at hn
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩ := hn
  apply hq
  have hr : (lvOf D P i lmu (elocOf P S i El)).rnd (pack0 D P i r4 sl) q = 0 := by
    have a1 : ¬ q ∣ 2 * dE D * Msh D P := fun h => absurd (Nat.le_of_dvd (by positivity) h) (by omega)
    have a2 : ¬ q ∣ D.host.QS * D.host.q * D.host.d := fun h => absurd (Nat.le_of_dvd (by positivity) h) (by omega)
    unfold Leaves.rnd
    rw [lvOf_ram, if_neg a2, add_zero]
    exact if_neg a1
  refine le_antisymm ?_ ((Finset.le_fold_max (0 : ℝ)).mpr (Or.inl le_rfl))
  refine (Finset.fold_max_le (0 : ℝ)).mpr ⟨le_rfl, fun x hx => ?_⟩
  rw [hr, add_zero]
  change x ∈ elocOf P S i El q at hx
  unfold elocOf at hx
  split_ifs at hx with hp
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy1 : ((q : ℕ) : 𝓞 S.c.F) ∈ y.1.asIdeal := by
      have := (Finset.mem_product.mp hy).1
      simpa using this
    unfold eLa
    rw [if_neg (not_or.mpr ⟨h4, h5⟩)]
    by_contra hpos
    exact h1 ⟨y.1, El.fin.mem_toFinset.mpr ⟨q, y.2, hp, hy1, not_le.mp hpos⟩, hp, hy1⟩
  · simp at hx

variable (B : MbarIn P S i) (r4 lmu : ℝ)

def packGeo : MeansPack D.what₂.Tau (Cmp P S i) :=
  packOf D P i r4 (slC P S i B) lmu (elocOf P S i El)
    (Finsupp.ofSupportFinite _ (e_finite P S i El r4 lmu (slC P S i B)))

def ccG : ℝ := (packGeo P S i El B r4 lmu).cc

theorem defTie (hrd : P.rd = (dE D : ℝ) ^ ((1 : ℝ) / (2 * (D.R.f : ℝ)))) :
    DefTie (packGeo P S i El B r4 lmu) (lvOf D P i lmu (elocOf P S i El)) :=
  ⟨fun _ => rfl, fun _ => rfl, hrd, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem package_base_error_eq : (packGeo P S i El B r4 lmu).E0 = baseErrorConstant D P i := rfl
theorem pack_X : (packGeo P S i El B r4 lmu).X = Xn D P i r4 := rfl
theorem pack_Qcc : (packGeo P S i El B r4 lmu).Qcc = Qccn D P i lmu := rfl

end Geo

section Build

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Links Formalism.L2.Pj IxMeans IxMeans.MeansTie IxMeans.MeansTie2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure GeoIn (Q : Par D) (P : SlopeBoundParameters) : Type 1 where
  S : SharpGeo Q (Msh D P)
  B : ∀ i, MbarIn P S i
  El : ∀ i, ELocIn P S i
  mass : Fin D.R.m → ℝ
  mass_pos : ∀ i, 0 < mass i

def withGeo {A' : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A' Ks} (J : SlopeArithmeticParameters R) (P : SlopeBoundParameters) {Q : Par D} (Γ : GeoIn Q P)
    (r4 : ℝ) : SlopeArithmeticParameters R :=
  { J with
    ι := fun i => Cmp P Γ.S i
    fι := fun i => Γ.S.fin i
    nι := fun i => Γ.S.ne i
    X := fun i => Xn D P i r4
    cc := fun i => ccG P Γ.S i (Γ.El i) (Γ.B i) r4 (Real.log (Γ.mass i))
    E0 := fun i => baseErrorConstant D P i
    Qcc := fun i => Qccn D P i (Real.log (Γ.mass i))
    ρ := fun i => rhoB D P i
    δ' := fun i => delP P Γ.S i
    h := fun i => htC P Γ.S i
    sl := fun i => slC P Γ.S i (Γ.B i)
    δc := fun i => delC P Γ.S i
    dc := fun i => rkC P Γ.S i
    degc := fun i => degC P Γ.S i }

variable (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat) (hd : NeZero D.host.d)
  {Q : Par D} (Γ : GeoIn Q (faceLiftPage R F I J hd)) (r4 : ℝ)

abbrev geoJ : SlopeArithmeticParameters R.toRealDat := withGeo J (faceLiftPage R F I J hd) Γ r4

theorem page_geo : faceLiftPage R F I (geoJ R F I J hd Γ r4) hd = faceLiftPage R F I J hd := rfl

variable (i : Fin D.R.m)

theorem fac_ι : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).ι = Cmp _ Γ.S i := rfl
theorem fac_h : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).h = htC _ Γ.S i := rfl
theorem fac_sl : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).sl = slC _ Γ.S i (Γ.B i) := rfl
theorem fac_δc : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).δc = delC _ Γ.S i := rfl
theorem fac_dc : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).dc = rkC _ Γ.S i := rfl
theorem fac_degc : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).degc = degC _ Γ.S i := rfl
theorem fac_δ' : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).δ' = delP _ Γ.S i := rfl
theorem fac_ρ : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).ρ = rhoB D (faceLiftPage R F I J hd) i := rfl
theorem fac_cc : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).cc = ccG _ Γ.S i (Γ.El i) (Γ.B i) r4 (Real.log (Γ.mass i)) := rfl
theorem fac_Qcc : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).Qcc = Qccn D (faceLiftPage R F I J hd) i (Real.log (Γ.mass i)) := rfl
theorem fac_X : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).X = Xn D (faceLiftPage R F I J hd) i r4 := rfl
theorem lift_data_base_error_eq : (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).E0 = baseErrorConstant D (faceLiftPage R F I J hd) i := rfl

theorem lift_data_time_eq_weight_time (hD : J.DY i = (Dn D : ℝ)) :
    (faceLiftFactor R F I (geoJ R F I J hd Γ r4) hd i).T = (Tn D (faceLiftPage R F I J hd) : ℝ) := by
  show ((⌈(faceLiftPage R F I J hd).PPT ^ 2 * J.DY i ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉ : ℤ) : ℝ) =
    ((⌈(faceLiftPage R F I J hd).PPT ^ 2 * (Dn D : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℕ) : ℝ)
  rw [hD, ← Int.natCast_ceil_eq_ceil (by positivity), Int.cast_natCast]

theorem recTie (hD : J.DY i = (Dn D : ℝ)) (hu : ∀ τ, J.ua i τ = ∑ n, |uR D i τ n|) :
    RecTie R F I (geoJ R F I J hd Γ r4) hd i (packGeo _ Γ.S i (Γ.El i) (Γ.B i) r4 (Real.log (Γ.mass i))) where
  hX := rfl
  hsl := rfl
  hT := lift_data_time_eq_weight_time R F I J hd Γ r4 i hD
  hLL := rfl
  hU := Finset.sum_congr rfl fun τ _ => hu τ
  hE := rfl
  hcc := rfl
  hQ := rfl

theorem packPage (hD : J.DY i = (Dn D : ℝ)) :
    PackPage r4 (packGeo _ Γ.S i (Γ.El i) (Γ.B i) r4 (Real.log (Γ.mass i))) (pgOf R F I (geoJ R F I J hd Γ r4) hd i) where
  hN := rfl
  hf := rfl
  hm := rfl
  hjp := rfl
  hD := hD.symm
  hT := (lift_data_time_eq_weight_time R F I J hd Γ r4 i hD).symm
  hb := rfl
  hx := rfl
  hrd := rfl
  hLp := rfl
  hh0 := rfl
  hc0 := rfl
  hnc8 := Dvd.intro _ rfl
  hnc1 := (Np_bounds D i).1
  hnc2 := (Np_bounds D i).2
  fourth_root_eq := rfl

theorem leafTie : LeafTie (packGeo _ Γ.S i (Γ.El i) (Γ.B i) r4 (Real.log (Γ.mass i)))
    (lvOf D (faceLiftPage R F I J hd) i (Real.log (Γ.mass i)) (elocOf _ Γ.S i (Γ.El i))) (pgOf R F I (geoJ R F I J hd Γ r4) hd i) where
  hbigp := fun _ => by
    show pp D i = D.R.r - jp D i
    have := pp_add_jp D i
    omega
  hA := by
    show ((D.R.k - 2 : ℕ) : ℝ) + 2 = (D.R.k : ℝ)
    have := D.R.m_add_three_le_k
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  heloc := fun q hq => elocOf_nonempty _ Γ.S i (Γ.El i) hq
  heloc0 := fun q hq => by
    show elocOf _ Γ.S i (Γ.El i) q = ∅
    unfold elocOf
    rw [dif_neg hq]
  hlevel := Msh_pos _

end Build

end Formalism.IndefR.Obj.SlopeGeometry
