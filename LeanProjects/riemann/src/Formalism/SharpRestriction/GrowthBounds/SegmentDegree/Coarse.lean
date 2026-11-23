import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NonemptyDvrSettingOfStandard

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

open Classical in

def toLate (j : ℤ) : Finset ℤ := (X.F.letters j).filter fun x => ¬ X.F.IsW j x

open Classical in

def row (j x : ℤ) (i : Fin r) : ℤ :=
  let l := ((X.F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)
  l.getD (l.length - r + i.val) 0

def detPl (O : Type) [CommRing O] (j x : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  Matrix.det (Matrix.of fun a b : Fin r => (MvPolynomial.X (X.row j x a, b) : MvPolynomial (ℤ × Fin r) O))

def DlSeg (O : Type) [CommRing O] (j : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  ∏ x ∈ X.toLate j, X.detPl O j x ^ X.sg p K j x

def Dl (O : Type) [CommRing O] : RRing O n' (r + K) :=
  ∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (plEmb O r K (X.DlSeg p K O j))

def Et (t : Fin n') : ℕ :=
  ∑ j ∈ Finset.range X.F.J, ∑ x ∈ X.toLate j, X.sg p K j x *
    ∑ i : Fin r, if posOf n' (X.row j x i) = t then p ^ X.F.dist j (X.row j x i) else 0

def a' (t : Fin n') : ℕ := X.d t - X.Et p K t

def Rj (j : ℤ) : ℕ :=
  Nat.log p ⌊X.a / (8 * X.Y * k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))⌋₊

def Qc (j : ℤ) : ℕ :=
  p ^ (X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat

def m0 : ℕ := (r + K) * X.Ns + 1

def phc (O : Type) [CommRing O] (j : ℤ) : SegRing O r K →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => MvPolynomial.X (posOf n' v.1, v.2) ^ (p ^ (X.F.dist j v.1 + X.Rj p K j))

def IsCLabel (l : Fin n' × Fin (r + K) →₀ ℕ) : Prop :=
  ∀ j : ℤ, ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → ∀ c, l (posOf n' x, c) < p ^ (X.F.dist j x + X.Rj p K j)

def resSet (j : ℤ) : Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {m | ∀ i < r, ∀ c : Fin r, m (X.F.fr j i, Fin.castAdd K c) < X.Qc p K j}

def segDegSet (b : ℤ → ℕ) : Set (ℤ × Fin (r + K) →₀ ℕ) := {m | ∀ x, ∑ c : Fin (r + K), m (x, c) = b x}

def Bw (j y : ℤ) : ℤ :=
  ((X.a' p K (posOf n' y) / p ^ (X.F.dist j y + X.Rj p K j) : ℕ) : ℤ) - ((r + K + r + 1 : ℕ) : ℤ)

open Classical in

def thc (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℝ :=
  (2 / 3) * (if X.F.IsW j (X.F.oldest j x) then ((X.Bw p K j (X.F.oldest j x) - (X.m0 K : ℤ) : ℤ) : ℝ)
    else (b (X.F.oldest j x) : ℝ))

def oc (j x : ℤ) : ℝ :=
  X.La * X.a / ((p : ℝ) * k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j)) +
    (if Even x then 4 * X.a * (p : ℝ) ^ (-((X.F.dist j (X.F.oldest j x) : ℤ) + (X.Rj p K j : ℤ))) else 0)

variable [NeZero r] [NeZero K]

def Mj (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) : Submodule O (SegRing O r K) :=
  XX' O r K X.F j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) ⊓
    restrictSupport O (segDegSet (r := r) K b) ⊓ restrictSupport O (X.resSet p K j)

def lamGen (O : Type) [CommRing O] : Set (RRing O n' (r + K)) :=
  {u | ∃ (b : ℤ → ℤ → ℕ) (y : ℤ → SegRing O r K) (l : Fin n' × Fin (r + K) →₀ ℕ),
      (∀ j, y j ∈ X.Mj p K O j (b j)) ∧ X.IsCLabel p K l ∧
      u = (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ∧
      u ∈ RRdeg O n' (r + K) (X.a' p K)}

def LamBar (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Submodule (FF O) (RRing (FF O) n' (r + K)) :=
  Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' X.lamGen p K O)

end Dat

def DiscriminantNonzeroModUniformiser : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], X.Hyp p K →
    MvPolynomial.map (IsLocalRing.residue O) (X.Dl p K O) ≠ 0

def GeneratorModuloUniformiser (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ u ∈ X.lamGen p K O, ∃ g ∈ X.gen p K O,
      MvPolynomial.map (IsLocalRing.residue O) (X.Dl p K O * u) = MvPolynomial.map (IsLocalRing.residue O) g

def RestCount (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank (FF O) (X.LamBar p K O) : ℝ)

theorem finite_restrictSupport (Fd : Type) [Field Fd] (σ : Type) (s : Set (σ →₀ ℕ)) (hs : s.Finite) :
    Module.Finite Fd (restrictSupport Fd s : Submodule Fd (MvPolynomial σ Fd)) := by
  have hle : (restrictSupport Fd s : Submodule Fd (MvPolynomial σ Fd)) ≤
      Submodule.span Fd ((fun m => (monomial m (1 : Fd) : MvPolynomial σ Fd)) '' s) := by
    intro P hP
    rw [MvPolynomial.mem_restrictSupport_iff] at hP
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have : (monomial m (coeff m P) : MvPolynomial σ Fd) = coeff m P • monomial m (1 : Fd) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)
  have : Module.Finite Fd (Submodule.span Fd ((fun m => (monomial m (1 : Fd) : MvPolynomial σ Fd)) '' s)) :=
    FiniteDimensional.span_of_finite Fd (hs.image _)
  exact Submodule.finiteDimensional_of_le hle

theorem map_mem_restrictSupport {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (s : Set (σ →₀ ℕ))
    {P : MvPolynomial σ R} (hP : P ∈ restrictSupport R s) : MvPolynomial.map f P ∈ restrictSupport S s := by
  rw [MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  intro m hm
  exact hP (by exact_mod_cast MvPolynomial.support_map_subset f P (by exact_mod_cast hm))

theorem restRank_of (C₀ Crk : ℝ) (h1 : DiscriminantNonzeroModUniformiser) (h5 : GeneratorModuloUniformiser C₀) (hc : RestCount C₀ Crk) : RestRank C₀ Crk := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk
  refine le_trans (hc p n' r K X O S hX hLa hk) ?_
  have hD := h1 p n' r K X O hX
  have h45 := h5 p n' r K X O S hX hLa hk
  set res := MvPolynomial.map (σ := Fin n' × Fin (r + K)) (IsLocalRing.residue O) with hres
  let f : RRing (FF O) n' (r + K) →ₗ[FF O] RRing (FF O) n' (r + K) := LinearMap.mulLeft (FF O) (res (X.Dl p K O))
  have hf : Function.Injective f := by
    intro a b hab
    exact mul_left_cancel₀ hD hab
  have hmap : (X.LamBar p K O).map f ≤ X.NNbar p K O := by
    unfold Dat.LamBar
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨g, hg, hgu⟩ := h45 u hu
    have : f (res u) = res g := by
      rw [← hgu]; simp [f, hres]
    rw [this]
    exact Submodule.subset_span ⟨g, hg, rfl⟩
  have hfin : Module.Finite (FF O) (X.NNbar p K O) := by
    have := finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) X.d)
    refine Submodule.finiteDimensional_of_le
      (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.d t}) ?_
    unfold Dat.NNbar
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, -, l, -, -, h⟩ := hg
    exact map_mem_restrictSupport _ _ h
  have h1' : Module.finrank (FF O) ((X.LamBar p K O).map f) = Module.finrank (FF O) (X.LamBar p K O) :=
    (Submodule.equivMapOfInjective f hf (X.LamBar p K O)).finrank_eq.symm
  have h2 := Submodule.finrank_mono hmap
  rw [h1'] at h2
  exact_mod_cast h2

end Formalism.MainNotions.SelectionLemmas.Pf
