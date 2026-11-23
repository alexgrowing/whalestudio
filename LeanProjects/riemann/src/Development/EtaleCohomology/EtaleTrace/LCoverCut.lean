import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def kHom {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) : k →+* X.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom

def loc (X : Scheme.{0}) [IsIntegral X] (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

def jet (k : Type) [Field k] {K : Type} [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K) (j : Fin n) : K × Ω[K⁄k] :=
  (v j, KaehlerDifferential.D k K (v j))

def Gen {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    (genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) v f ≠ 0) ∧
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen _ f),
      (show X.functionField from X.presheaf.germ _ (genericPoint X) h (ι.app _
        (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg)))) * eval₂ (kHom p) v f ^ m =
        eval₂ (kHom p) v g

structure Coord {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) : Prop where
  opens : ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k, f.IsHomogeneous n → ∀ x : X,
    (x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) v f ≠ 0 ∧
      ∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x)
  range : ∀ z : X.functionField, z ∈ (ι.stalkMap (genericPoint X)).hom.range ↔
    ∃ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n ∧ g.IsHomogeneous n ∧
      eval₂ (kHom p) v f ≠ 0 ∧ z = eval₂ (kHom p) v g / eval₂ (kHom p) v f

def PNBasic : Prop := ∀ (k : Type) [Field k] (d : ℕ),
  IsIntegral (PN k d) ∧ IsSeparated (PNto k d) ∧ LocallyOfFiniteType (PNto k d)

def GenIn : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∃ (v : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), v i = 1 ∧ Gen p ι v

def GenOut : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField), (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x) →
  ∃ π : X ⟶ PN k N, π ≫ PNto k N = p ∧ Gen p π w

def GenUse : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → Coord p ι v

def JetSpan : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (n : ℕ) (v : Fin n → K) (i : Fin n), v i = 1 →
  (∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) →
  Submodule.span K (Set.range (jet k v)) = ⊤ ∧ Algebra.EssFiniteType k K

def TrdegLe : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
  Algebra.trdeg k K ≤ (Module.finrank K Ω[K⁄k] : ℕ)

def HomRel : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (d : ℕ), Algebra.trdeg k K ≤ (d : ℕ) →
  ∀ (n : ℕ), d + 1 < n → ∀ v : Fin n → K, ∃ (m : ℕ) (F : MvPolynomial (Fin n) k), F ≠ 0 ∧ F.IsHomogeneous m ∧ aeval v F = 0

def Step : Prop := ∀ (k K : Type) [Field k] [Infinite k] [Field K] [Algebra k K] (n : ℕ) (v : Fin (n + 1) → K)
  (m : ℕ) (F : MvPolynomial (Fin (n + 1)) k), F ≠ 0 → F.IsHomogeneous m → aeval v F = 0 → ¬ LinearIndependent K (jet k v) →
  ∃ w : Fin n → K, (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
    Submodule.span K (Set.range (jet k w)) = Submodule.span K (Set.range (jet k v)) ∧
    ∀ O : Subring K, IsLocalRing O → (∀ c : k, algebraMap k K c ∈ O) → (∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ O) →
      ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ O

def Project : Prop := ∀ (k K : Type) [Field k] [Infinite k] [Field K] [Algebra k K] (d : ℕ), Module.finrank K Ω[K⁄k] = d →
  Algebra.trdeg k K ≤ (d : ℕ) → ∀ (n : ℕ) (v : Fin n → K), Submodule.span K (Set.range (jet k v)) = ⊤ →
  ∃ w : Fin (d + 1) → K, (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
    Submodule.span K (Set.range (jet k w)) = ⊤ ∧ LinearIndependent K (jet k w) ∧
    ∀ O : Subring K, IsLocalRing O → (∀ c : k, algebraMap k K c ∈ O) → (∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ O) →
      ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ O

def JetIndep : Prop := ∀ (k K : Type) [Field k] [PerfectField k] [Field K] [Algebra k K] (n : ℕ) (w : Fin n → K),
  LinearIndependent K (jet k w) → ∀ (m : ℕ) (F : MvPolynomial (Fin n) k), F.IsHomogeneous m → aeval w F = 0 → F = 0

def JetUnram : Prop := ∀ (k K O : Type) [Field k] [Field K] [Algebra k K] [CommRing O] (φ : O →+* K) (n : ℕ) (w : Fin n → K)
  (i : Fin n), w i ≠ 0 → Submodule.span K (Set.range (jet k w)) = ⊤ → (∀ c : k, algebraMap k K c ∈ φ.range) →
  (∀ j, w j / w i ∈ φ.range) → φ.FormallyUnramified

def FieldDim : Prop := ∀ (k : Type) [Field k] (d : ℕ) {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  SmoothOfRelativeDimension d p → letI := (kHom p).toAlgebra; Module.finrank X.functionField Ω[X.functionField⁄k] = d

def FinSurj : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k), IsProper p →
  ∀ (N d : ℕ) (ι : X ⟶ PN k N) (π : X ⟶ PN k d) (v : Fin (N + 1) → X.functionField) (w : Fin (d + 1) → X.functionField),
  IsClosedImmersion ι → π ≫ PNto k d = p → Coord p ι v → Coord p π w →
  (∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j) →
  (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x) →
  (∀ (m : ℕ) (F : MvPolynomial (Fin (d + 1)) k), F.IsHomogeneous m → eval₂ (kHom p) w F = 0 → F = 0) →
  IsFinite π ∧ Surjective π

def Fibre : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (p : X ⟶ S k)
  (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified → ∃ t : Pt r, Etale (equalizer.ι π (p ≫ t.1) ≫ p)

theorem kHom_mem_loc {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (x : X) (c : k) :
    kHom p c ∈ loc X x := by
  refine ⟨X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)), ?_⟩
  exact X.presheaf.germ_stalkSpecializes_apply _ _ _

theorem loc_local (X : Scheme.{0}) [IsIntegral X] (x : X) : IsLocalRing (loc X x) :=
  IsLocalRing.of_surjective' (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    (RingHom.rangeRestrict_surjective _)

theorem goal_of (h1 : PNBasic) (h2 : GenIn) (h3 : GenOut) (h4 : GenUse) (h5 : JetSpan) (h6 : TrdegLe) (h7 : Project)
    (h8 : JetIndep) (h9 : JetUnram) (h10 : FieldDim) (h11 : FinSurj) (h12 : Fibre) : LCover := by
  intro k _ _ d X p hsp ⟨N, ι, hι, hιp⟩ hX
  let _ : Algebra k X.functionField := (kHom p).toAlgebra
  obtain ⟨v, i₀, hv1, hv⟩ := h2 k p N ι hιp
  have cv := h4 k p N ι v hv
  have hgen : ∀ z : X.functionField, ∃ f g : MvPolynomial (Fin (N + 1)) k, z = aeval v g / aeval v f := by
    intro z
    obtain ⟨n, f, g, -, -, -, h⟩ := (cv.range z).1 (ι.stalkMap_surjective (genericPoint X) z)
    exact ⟨f, g, h⟩
  obtain ⟨hspan, hess⟩ := h5 k X.functionField _ v i₀ hv1 hgen
  have hd := h10 k d p hsp.2
  have htr := h6 k X.functionField
  rw [hd] at htr
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := h7 k X.functionField d hd htr _ v hspan
  have hfree : ∀ x : X, ∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ loc X x := by
    intro x
    have htop : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
      apply Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, isHomogeneous_X k i⟩)
      rw [eq_top_iff]
      rintro f -
      induction f using MvPolynomial.induction_on with
      | C a => exact Subalgebra.algebraMap_mem _ (⟨C a, isHomogeneous_C _ a⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add f g hf hg => exact add_mem hf hg
      | mul_X f i hf => exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
    have hx : ι x ∈ ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
      rw [htop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨a, b⟩ := (cv.opens 1 one_pos _ (isHomogeneous_X k i) x).1 hi
    exact ⟨i, by simpa using a, fun j => by simpa using b _ (isHomogeneous_X k j)⟩
  have hwx : ∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x := fun x =>
    hw4 _ (loc_local X x) (kHom_mem_loc p x) (hfree x)
  have hc : ∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 (hw1 i)
    exact ⟨c, by rw [← hc]; exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _⟩
  have hww : ∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x := by
    intro x
    obtain ⟨i, hi, h⟩ := hwx x
    refine ⟨i, hi, fun j => ?_⟩
    obtain ⟨c, hc⟩ := hc j
    rw [hc, Finset.sum_div]
    exact sum_mem fun l _ => by rw [mul_div_assoc]; exact mul_mem (kHom_mem_loc p x _) (h l)
  obtain ⟨π, hπ, hg⟩ := h3 k p d w hww
  have cw := h4 k p d π w hg
  obtain ⟨hfin, hsurj⟩ := h11 k p hsp.1 N d ι π v w hι hπ cv cw hc hwx (h8 k X.functionField _ w hw3)
  obtain ⟨hint, -, hft⟩ := h1 k d
  obtain ⟨i, hi, -⟩ := hwx (genericPoint X)
  have hun := h9 k X.functionField _ (π.stalkMap (genericPoint X)).hom _ w i hi hw2
    (fun c => (cw.range _).2 ⟨0, 1, C c, isHomogeneous_one _ _, isHomogeneous_C _ c, by simp, by simp; rfl⟩)
    (fun j => (cw.range _).2 ⟨1, MvPolynomial.X i, MvPolynomial.X j, isHomogeneous_X k i, isHomogeneous_X k j,
      by simpa using hi, by simp⟩)
  obtain ⟨t, ht⟩ := h12 k p (PNto k d) π hπ hft hfin hsurj hun
  exact ⟨π, t, hπ, hfin, hsurj, ht⟩

end LateralTheory.EtaleTrace.Cov

end
