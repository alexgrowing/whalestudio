import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.NormEucSq

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

def ScaleFull : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ], Scale (fun x : Λ => ‖x.1‖ ^ 2) (Module.finrank ℝ V)

def ScaleGen : Prop :=
  ∀ (A V : Type) [AddCommGroup A] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (φ : A →+ V)
    (ε : ℝ), 0 < ε → (∀ x, x ≠ 0 → ε ≤ ‖φ x‖) → Scale (fun x => ‖φ x‖ ^ 2) (Module.finrank ℝ V)

def Moment : Prop :=
  ∀ N k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) (q : ι → ℝ), Scale q N →
    (Summable fun i => (1 + q i) ^ k * Real.exp (-Real.pi * q i)) ∧
      ∑' i, (1 + q i) ^ k * Real.exp (-Real.pi * q i) ≤ C * ∑' i, Real.exp (-Real.pi * q i)

def LogTaylor : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Nonempty ι] (q u : ι → ℝ) (ε : ℝ), Scale q N → 0 ≤ ε → ε ≤ 1 / 4 →
    (∀ i, |u i| ≤ ε * q i) →
    |Real.log (∑' i, Real.exp (-Real.pi * (q i + u i))) - Real.log (∑' i, Real.exp (-Real.pi * q i)) +
      Real.pi * ((∑' i, u i * Real.exp (-Real.pi * q i)) / ∑' i, Real.exp (-Real.pi * q i))| ≤ C * ε ^ 2

def MeanLow : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A V : Type) [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V] (φ : A →+ V),
    Function.Injective φ → (Summable fun x => Real.exp (-Real.pi * ‖φ x‖ ^ 2)) →
    (Summable fun x => ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) → 2 ≤ ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) →
    c * ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)

def ThetaUp : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) (q : ι → ℝ) (i₀ : ι) (μ : ℝ), Scale q N → 0 < μ → μ ≤ 1 →
    (∀ i, i ≠ i₀ → μ ≤ q i) → ∑' i, Real.exp (-Real.pi * q i) ≤ C / μ ^ N

def ThetaLow : Prop :=
  ∀ (A V : Type) [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V] (φ : A →+ V),
    (Summable fun x => Real.exp (-Real.pi * ‖φ x‖ ^ 2)) → ∀ v, φ v ≠ 0 →
    Real.exp (-Real.pi) ≤ ‖φ v‖ * ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2)

def QfFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), (∀ x : Fin a → Cinf E, quad 1 x = qf x) ∧
    (∀ (p p' : Matrix (Fin a) (Fin a) (Cinf E)) (c : ℝ) x, quad (p + p') x = quad p x + quad p' x ∧ quad (c • p) x = c * quad p x) ∧
    (∀ (h : Matrix (Fin a) (Fin a) (Cinf E)) x, qf (x ᵥ* h) = quad (h * star h) x) ∧
    (∀ (c : ℝ) (x : Fin a → Cinf E), qf (c • x) = c ^ 2 * qf x) ∧
    (∀ (p : Matrix (Fin a) (Fin a) (Cinf E)) x, |quad p x| ≤ a * ‖toL p‖ * qf x) ∧
    ∀ x : Fin a → Cinf E, ‖x‖ ^ 2 ≤ qf x ∧ qf x ≤ a * Fintype.card (InfinitePlace E) * ‖x‖ ^ 2

def RankOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : Fin a → Cinf E), trF 1 (vecMulVec w (star w)) = qf w ∧
    (∀ M : Herm E a, trF M.1 (vecMulVec w (star w)) ^ 2 ≤ trF M.1 M.1 * qf w ^ 2) ∧
    ∀ x : Fin a → Cinf E, ‖x ⬝ᵥ w‖ ^ 2 ≤ quad (vecMulVec w (star w)) x ∧ quad (vecMulVec w (star w)) x ≤ qf w * qf x ∧
      (x ⬝ᵥ w = 0 → quad (vecMulVec w (star w)) x = 0)

def ScSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ContDiffOn ℝ ∞ (fun y : Lie E a => sc (Matrix.of y)) (invSet E a) ∧ sc (1 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 ∧
    (∀ X : Lie E a, fderiv ℝ (fun y : Lie E a => sc (Matrix.of y)) (oneL E a) X = -ell E a X) ∧
    (∀ h : GL (Fin a) (Cinf E), sc (h.val * star h.val) = sc h.val ^ 2) ∧ ∀ k : Kinf E a, sc k.1 = 1

def ScTaylor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ Y : Matrix (Fin a) (Fin a) (Cinf E), ‖toL Y‖ ≤ ε →
    |sc (1 + Y) - 1 + ell E a (toL Y)| ≤ C * ‖toL Y‖ ^ 2

def RootEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ ε C : ℝ, 0 < ε ∧ ∀ Y : Herm E a, ‖toL Y.1‖ ≤ ε → ∃ h : GL (Fin a) (Cinf E),
    h.val * star h.val = 1 + Y.1 ∧ ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C

def PolyBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ P ∈ poly E a, ContDiff ℝ ∞ P ∧ (∃ (C : ℝ) (k : ℕ), ∀ x, ‖P x‖ ≤ C * (1 + qf x) ^ k) ∧
    ∀ T : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E), (fun x => fderiv ℝ P x (T x)) ∈ poly E a ∧ (fun x => P (T x)) ∈ poly E a ∧
      ∀ u, (fun x => fderiv ℝ P x u) ∈ poly E a

def PolyD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ P ∈ poly E a, ContDiff ℝ ∞ (pg P) ∧
    (∃ (C : ℝ) (k : ℕ), ∀ x, ‖fderiv ℝ (pg P) x‖ ≤ C * (1 + qf x) ^ k * gauss x) ∧
    ∀ T : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E), ∃ Q ∈ poly E a, ∀ x, fderiv ℝ (pg P) x (T x) = pg Q x

def SumDer : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ι : Type) (x : ι → Fin a → Cinf E) (N : ℕ), Scale (fun i => qf (x i)) N → ∀ P ∈ poly E a, ∀ y ∈ invSet E a,
    (Summable fun i => pg P (x i ᵥ* Matrix.of y)) ∧ DifferentiableAt ℝ (msum x P) y ∧
      ∀ Z : Lie E a, fderiv ℝ (msum x P) y Z = ∑' i, fderiv ℝ (pg P) (x i ᵥ* Matrix.of y) (x i ᵥ* Matrix.of Z)

def SumSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ι : Type) (x : ι → Fin a → Cinf E) (N : ℕ), Scale (fun i => qf (x i)) N → ∀ P ∈ poly E a,
    ContDiffOn ℝ ∞ (msum x P) (invSet E a)

def LatEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∃ L : AddSubgroup (Fin a → Af E), IsLat L ∧ ∀ u ∈ U, ∀ x ∈ L, x ᵥ* u.val ∈ L

def LatMin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ (C : ℝ) (N : ℕ), 1 ≤ C ∧ ∀ g : GA E a, ∀ v ∈ lat L g, v ≠ 0 →
    1 ≤ C * AutomorphicForm.height (K := E) g ^ N * qf (pt g v)

def LatScale : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ N : ℕ, ∀ g : GA E a, Scale (fun v : lat L g => qf (pt (rt g) v.1)) N

def RtFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → (∀ γ t (g : GA E a), rt (ratGL E a γ * splitCentre E a t * g) = ratGL E a γ * rt g) ∧
    (∀ g : GA E a, rt (rt g) = rt g ∧ qht (rt g) = qht g ∧ ptF (rt g) = ptF g) ∧
    (∀ (γ : GL (Fin a) E) (g : GA E a) v, ptF (ratGL E a γ * g) v = ptF g (v ᵥ* γ.val) ∧ pt (ratGL E a γ * g) v = pt g (v ᵥ* γ.val)) ∧
    ∀ U : Subgroup (GL (Fin a) (Af E)), IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ u ∈ U, ∀ g : GA E a,
      rt (g * finGL E a u) = rt g * finGL E a u

def RtInf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (g : GA E a) (h : GL (Fin a) (Cinf E)) v,
    pt (rt (g * infGL E a h)) v = sc h.val • (pt (rt g) v ᵥ* h.val)

def SumInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (L : AddSubgroup (Fin a → Af E)) (M : Type) [AddCommMonoid M] [TopologicalSpace M] (F : (Fin a → Cinf E) → M),
    (∀ γ t g, gsum L F (ratGL E a γ * splitCentre E a t * g) = gsum L F g) ∧
    (∀ g (h : GL (Fin a) (Cinf E)), gsum L F (g * infGL E a h) = ∑' v : lat L g, F (sc h.val • (pt (rt g) v.1 ᵥ* h.val))) ∧
    ∀ U : Subgroup (GL (Fin a) (Af E)), IsCompact (U : Set (GL (Fin a) (Af E))) → (∀ u ∈ U, ∀ x ∈ L, x ᵥ* u.val ∈ L) →
      ∀ u ∈ U, ∀ g, gsum L F (g * finGL E a u) = gsum L F g

def FnInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (L : AddSubgroup (Fin a → Af E)),
    (∀ γ t g, fn L (ratGL E a γ * splitCentre E a t * g) = fn L g ∧ dev L (ratGL E a γ * splitCentre E a t * g) = dev L g) ∧
    (∀ U : Subgroup (GL (Fin a) (Af E)), IsCompact (U : Set (GL (Fin a) (Af E))) → (∀ u ∈ U, ∀ x ∈ L, x ᵥ* u.val ∈ L) →
      ∀ u ∈ U, ∀ g, fn L (g * finGL E a u) = fn L g ∧ dev L (g * finGL E a u) = dev L g) ∧
    ∀ (k : Kinf E a) g, Th L (g * infGL E a (Unitary.toUnits k)) = Th L g

def DevCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∀ (k : Kinf E a) g, adHerm k (dev L (g * infGL E a (Unitary.toUnits k))) = dev L g

def MeanBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → (∀ g, 1 ≤ Th L g ∧ gsum L (pg 1) g = (Th L g : ℝ)) ∧ ∀ P ∈ poly E a,
    (∀ g, Summable fun v : lat L g => pg P (pt (rt g) v.1)) ∧ ∃ C : ℝ, ∀ g, ‖mean L P g‖ ≤ C

def ThSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∀ P ∈ poly E a, ∃ φ : Sm E a, φ.1 = gsum L (pg P) ∧
    ∀ X : Lie E a, ∃ Q ∈ poly E a, (lie E a X φ).1 = gsum L (pg Q)

def BddAlg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Set (GA E a → ℂ)), (∀ f ∈ S, (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧
      ∃ φ : Sm E a, φ.1 = f ∧ ∀ X, (lie E a X φ).1 ∈ Algebra.adjoin ℂ S) →
    (∀ f ∈ Algebra.adjoin ℂ S, ∃ φ : Sm E a, φ.1 = f ∧ BddDer φ) ∧
      ∀ ψ : Sm E a, (∀ X, (lie E a X ψ).1 ∈ Algebra.adjoin ℂ S) → BddDer ψ

def MeanSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → (∀ P ∈ poly E a, ∃ φ : Sm E a, φ.1 = mean L P ∧ ∀ X, (lie E a X φ).1 ∈ meanAlg L) ∧
    ∃ φ : Sm E a, (∀ g, φ.1 g = fn L g) ∧ ∀ X, (lie E a X φ).1 ∈ meanAlg L

def MomQuad : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∀ g (p : Matrix (Fin a) (Fin a) (Cinf E)),
    trF (mom L g).1 p = (∑' v : lat L g, quad p (pt (rt g) v.1) * gauss (pt (rt g) v.1)) / Th L g

def DevFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → (∀ i j w, (fun g => (dev L g).1 i j w) ∈ meanAlg L) ∧
    (∃ B : ℝ, 0 < B ∧ ∀ g, ‖toL (mom L g).1‖ ≤ B ∧ ‖toL (dev L g).1‖ ≤ B ∧ |trF (dev L g).1 (dev L g).1| ≤ B) ∧
    ∀ g, ell E a (toL (dev L g).1) = 0 ∧ trF (mom L g).1 (dev L g).1 = trF (dev L g).1 (dev L g).1

def FnTaylor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ g (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : GL (Fin a) (Cinf E)),
    ell E a (toL Y) = 0 → ‖toL Y‖ ≤ ε → h.val * star h.val = 1 + Y →
    |fn L (g * infGL E a h) - fn L g + Real.pi * trF (mom L g).1 Y| ≤ C * ‖toL Y‖ ^ 2

def SiegelHt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (Ω : Set (GA E a)) (C : ℝ) (N : ℕ), IsCompact Ω ∧ (∀ b ∈ Ω, b ∈ Reduction.adelicBorel (K := E) (n := a)) ∧
    ∀ g : KernelIndexFullLattice.G1 E a, ∃ (γ : GL (Fin a) E) (b k : GA E a) (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), b ∈ Ω ∧
      k ∈ Reduction.maxCompact (K := E) (n := a) ∧
      ratGL E a γ * g.1 = b * Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∧
      ∀ i : Fin a, (i.val + 1 = a → qht (E := E) (a := a) g.1 * ρ i ^ (2 * N) ≤ C) ∧
        (i.val = 0 → qht (E := E) (a := a) g.1 ≤ C * ρ i ^ (2 * N))

def SiegelRow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∃ (T : Set (Fin a → Af E)) (C : ℝ) (N : ℕ), IsCompact T ∧ ∀ g : KernelIndexFullLattice.G1 E a, ∃ v : Fin a → E, v ≠ 0 ∧
    ptF (E := E) (a := a) g.1 v ∈ T ∧ qht (E := E) (a := a) g.1 * qf (pt (E := E) (a := a) g.1 v) ^ N ≤ C

def SiegelCol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∃ (T : Set (Fin a → Af E)) (C : ℝ) (N : ℕ), IsCompact T ∧ ∀ g : KernelIndexFullLattice.G1 E a, ∃ ξ : Fin a → E, ξ ≠ 0 ∧
    (GeneralLinearGroup.map (pFin E) (g.1⁻¹ : GA E a)).val *ᵥ vFin ξ ∈ T ∧
    qht (E := E) (a := a) g.1 * qf ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf ξ) ^ N ≤ C

def ShortRow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ (C : ℝ) (N : ℕ), ∀ g : GA E a, ∃ v ∈ lat L g, v ≠ 0 ∧ qht g * qf (pt (rt g) v) ^ N ≤ C

def ShortCol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ (c C : ℝ) (N : ℕ), 0 < c ∧ ∀ g : GA E a, ∃ w : Fin a → Cinf E, w ≠ 0 ∧ qht g * qf w ^ N ≤ C ∧
    ∀ v ∈ lat L g, pt (rt g) v ⬝ᵥ w = 0 ∨ c ≤ ‖pt (rt g) v ⬝ᵥ w‖

def FnLe : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ C : ℝ, ∀ g, fn L g ≤ C * (1 + Real.log (qht g))

def LeFn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ C : ℝ, ∀ g, Real.log (qht g) ≤ C * (1 + fn L g)

def GradA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ c : ℝ, 0 < c ∧ ∀ g, 2 ≤ Th L g → c ≤ ell E a (toL (mom L g).1)

def GradB : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ C : ℝ, ∀ g (w : Fin a → Cinf E) (c : ℝ), 0 < c →
    (∀ v ∈ lat L g, pt (rt g) v ⬝ᵥ w = 0 ∨ c ≤ ‖pt (rt g) v ⬝ᵥ w‖) →
    trF (mom L g).1 (vecMulVec w (star w)) ≤ C * qf w ^ 2 / c ^ 2

def Grad : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ L : AddSubgroup (Fin a → Af E), IsLat L → ∃ c f₀ : ℝ, 0 < c ∧ ∀ g, f₀ ≤ fn L g → c ≤ trF (dev L g).1 (dev L g).1

end UpperTheory.V.Lit.Geo
