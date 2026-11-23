import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Coarse

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def zSeg (O : Type) [CommRing O] (j : ℤ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) : SegRing O r K :=
  plEmb O r K (X.DlSeg p K O j) * expand (p ^ X.Rj p K j) y * monomial e 1

def IsEll (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : Prop :=
  (∀ v, e v ≠ 0 → v.1 ∈ X.toLate j) ∧ ∀ v, e v < p ^ X.Rj p K j

def Step2 (j : ℤ) (b : ℤ → ℕ) : Prop :=
  ∀ z ∈ X.F.LLset j,
    (X.a' p K (posOf n' z) : ℝ) / (p : ℝ) ^ (X.F.dist j z + X.Rj p K j) - k (r := r) K < (b z : ℝ)

end Dat

def CoarseLabelFactorisation : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O],
    X.Hyp p K → ∀ l, X.IsCLabel p K l →
    ∃ (l0 : Fin n' × Fin (r + K) →₀ ℕ) (e : ℤ → (ℤ × Fin (r + K) →₀ ℕ)), IsLabel p X.F l0 ∧
      (∀ j, X.IsEll p K j (e j)) ∧
      (monomial l 1 : RRing O n' (r + K)) =
        monomial l0 1 * ∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (monomial (e j) 1)

def TopDegreeComparison : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O],
    X.Hyp p K → ∀ (b : ℤ → ℤ → ℕ) (y : ℤ → SegRing O r K) (l : Fin n' × Fin (r + K) →₀ ℕ),
      (∀ j, y j ∈ X.Mj p K O j (b j)) → X.IsCLabel p K l →
      (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ∈ RRdeg O n' (r + K) (X.a' p K) →
      (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ≠ 0 →
      ∀ j ∈ Finset.range X.F.J, X.Step2 p K (j : ℤ) (b j)

def DiscriminantMultihomogeneous : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O],
    X.Dl p K O ∈ RRdeg O n' (r + K) (X.Et p K)

def DiscriminantNeZero : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], X.Hyp p K → X.Dl p K O ≠ 0

theorem discriminant_ne_zero_of_residue_ne_zero (h : DiscriminantNonzeroModUniformiser) : DiscriminantNeZero := by
  intro p n' r K _ _ _ X O _ _ _ hX h0
  exact h p n' r K X O hX (by rw [h0, map_zero])

def TopCountLowerBounds (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    (∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ)) ∧ ∀ t, X.Et p K t ≤ X.d t

def SegmentReductionLiftsMultihomogeneous (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ),
      y ∈ X.Mj p K O j b → X.IsEll p K j e → X.Step2 p K j b →
      ∀ β : ℤ → ℕ, X.zSeg p K O j y e ∈ Pol O (r + K) β →
      ∃ x ∈ X.XXs p K O j, x ∈ Pol O (r + K) β ∧
        MvPolynomial.map (IsLocalRing.residue O) x = MvPolynomial.map (IsLocalRing.residue O) (X.zSeg p K O j y e)

def SegmentImageMultihomogeneous : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O]
    (j : ℤ) (b : ℤ → ℕ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ),
    y ∈ Pol O (r + K) b → ∃ β : ℤ → ℕ, X.zSeg p K O j y e ∈ Pol O (r + K) β

def SegmentProductDegreeDetermined : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] (F : Frames n' r) (O : Type) [CommRing O]
    (x z : ℤ → SegRing O r K) (β : ℤ → ℤ → ℕ) (l0 : Fin n' × Fin (r + K) →₀ ℕ) (d : Fin n' → ℕ),
    (∀ j, x j ∈ Pol O (r + K) (β j)) → (∀ j, z j ∈ Pol O (r + K) (β j)) →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1 ∈ RRdeg O n' (r + K) d →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1 ≠ 0 →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1 ∈ RRdeg O n' (r + K) d

theorem RRdeg_eq_Pol (O : Type) [CommRing O] (n' k : ℕ) (d : Fin n' → ℕ) : RRdeg O n' k d = Pol O k d := rfl

theorem segDeg_eq_Pol (O : Type) [CommRing O] (r K : ℕ) (b : ℤ → ℕ) :
    restrictSupport O (Dat.segDegSet (r := r) K b) = Pol O (r + K) b := rfl

theorem map_phSeg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (K p : ℕ) {n' r : ℕ} [NeZero n']
    (F : Frames n' r) (j : ℤ) (P : SegRing R r K) :
    MvPolynomial.map f (phSeg R K p F j P) = phSeg S K p F j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [phSeg]
  | add u v hu hv => simp only [map_add, hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [phSeg]

theorem phc_eq {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ) (y : SegRing O r K) :
    X.phc p K O j y = phSeg O K p X.F j (expand (p ^ X.Rj p K j) y) := by
  have : X.phc p K O j = (phSeg O K p X.F j).comp (expand (p ^ X.Rj p K j)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Dat.phc, phSeg, AlgHom.comp_apply, expand_X, aeval_X, map_pow]
    rw [← pow_mul, ← pow_add]
  rw [this]; rfl

theorem generator_of_segment_reductions (C₀ : ℝ) (hLab : CoarseLabelFactorisation) (hDeg2 : TopDegreeComparison) (hDlHom : DiscriminantMultihomogeneous) (hDlNe : DiscriminantNeZero)
    (h41b : TopCountLowerBounds C₀) (hSeg : SegmentReductionLiftsMultihomogeneous C₀) (hZ : SegmentImageMultihomogeneous) (hHom : SegmentProductDegreeDetermined) : GeneratorModuloUniformiser C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk u hu
  obtain ⟨b, y, l, hy, hl, hueq, hdeg⟩ := hu
  have hJ : 1 ≤ X.F.J := hX.valid.1
  have hp0 : 0 < p := hX.prime.pos
  by_cases hu0 : u = 0
  · refine ⟨0, ⟨fun _ => 0, fun _ => Submodule.zero_mem _, 0, ?_, ?_, Submodule.zero_mem _⟩, by simp [hu0]⟩
    · intro j x _ _ c
      simpa using Nat.pow_pos hp0
    · have h0 : (∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) ((fun _ : ℤ => (0 : SegRing O r K)) (j : ℤ))) = 0 :=
        Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hJ) (map_zero _)
      rw [h0, zero_mul]
  obtain ⟨l0, e, hl0, he, hmon⟩ := hLab p n' r K X O hX l hl
  set z : ℤ → SegRing O r K := fun j => X.zSeg p K O j (y j) (e j) with hz
  have hDu : X.Dl p K O * u = (∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (z j)) * monomial l0 1 := by
    rw [hueq, hmon]
    simp only [hz, Dat.zSeg, Dat.Dl, map_mul, Finset.prod_mul_distrib, phc_eq]
    ring
  have hβ : ∀ j, ∃ β : ℤ → ℕ, z j ∈ Pol O (r + K) β := fun j =>
    hZ p n' r K X O j (b j) (y j) (e j) (by rw [← segDeg_eq_Pol]; exact (hy j).1.2)
  choose β hβ using hβ
  have h2 := hDeg2 p n' r K X O hX b y l hy hl (hueq ▸ hdeg) (hueq ▸ hu0)
  have hx : ∀ j : ℤ, ∃ x, x ∈ X.XXs p K O j ∧ x ∈ Pol O (r + K) (β j) ∧
      ((∃ i ∈ Finset.range X.F.J, (i : ℤ) = j) →
        MvPolynomial.map (IsLocalRing.residue O) x = MvPolynomial.map (IsLocalRing.residue O) (z j)) := by
    intro j
    by_cases hj : ∃ i ∈ Finset.range X.F.J, (i : ℤ) = j
    · obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨x, h1, h2', h3⟩ := hSeg p n' r K X O S hX hLa hk (i : ℤ) (b i) (y i) (e i) (hy i) (he i) (h2 i hi)
        (β i) (hβ i)
      exact ⟨x, h1, h2', fun _ => h3⟩
    · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, fun h => absurd h hj⟩
  choose x hx1 hx2 hx3 using hx
  have hsum : X.Et p K + X.a' p K = X.d := by
    funext t
    have := (h41b p n' r K X hX hLa hk).2 t
    simp only [Pi.add_apply, Dat.a']
    omega
  have hDdeg : X.Dl p K O * u ∈ RRdeg O n' (r + K) X.d := by
    have h1 : X.Dl p K O ∈ Pol O (r + K) (X.Et p K) := by
      rw [← RRdeg_eq_Pol]; exact hDlHom p n' r K X O
    have h2 : u ∈ Pol O (r + K) (X.a' p K) := by
      rw [← RRdeg_eq_Pol]; exact hdeg
    have := hom_Pol_mul O h1 h2
    rw [hsum] at this
    rw [RRdeg_eq_Pol]
    exact this
  have hDne : X.Dl p K O * u ≠ 0 := mul_ne_zero (hDlNe p n' r K X O hX) hu0
  refine ⟨(∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (x j)) * monomial l0 1,
    ⟨x, hx1, l0, hl0, rfl, ?_⟩, ?_⟩
  · exact hHom p n' r K X.F O x z β l0 X.d hx2 hβ (hDu ▸ hDdeg) (hDu ▸ hDne)
  · rw [hDu]
    simp only [map_mul, map_prod, map_phSeg]
    rw [Finset.prod_congr rfl fun i hi => by rw [← hx3 (i : ℤ) ⟨i, hi, rfl⟩]]

end Formalism.MainNotions.SelectionLemmas.Pf
