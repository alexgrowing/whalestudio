import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraPropertiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRingStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.OrbitSection

section Alg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def rowOf (τ : A →+* A) (J : Matrix n n A) (d : n → A) : n → A :=
  Matrix.vecMul (fun k => τ (d k)) J

def reflM (τ : A →+* A) (J : Matrix n n A) (a : A) (d : n → A) : Matrix n n A :=
  1 - a • Matrix.vecMulVec d (rowOf τ J d)

theorem rowOf_dot (τ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    rowOf τ J x ⬝ᵥ y = hform τ J x y := by
  simp only [rowOf, hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_sub_left (τ : A →+* A) (J : Matrix n n A) (x y z : n → A) :
    hform τ J (x - y) z = hform τ J x z - hform τ J y z := by
  simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (τ : A →+* A) (J : Matrix n n A) (x y z : n → A) :
    hform τ J x (y - z) = hform τ J x y - hform τ J x z := by
  simp only [hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem map_hform (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) (J : Matrix n n A)
    (hJ : ∀ i j, τ (J j i) = J i j) (x y : n → A) : τ (hform τ J x y) = hform τ J y x := by
  simp only [hform, map_sum, map_mul, hτ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]; ring

theorem reflM_mul (τ : A →+* A) (J : Matrix n n A) (a b : A) (d : n → A)
    (h : a + b = a * b * hform τ J d d) : reflM τ J a d * reflM τ J b d = 1 := by
  have hP : Matrix.vecMulVec d (rowOf τ J d) * Matrix.vecMulVec d (rowOf τ J d)
      = hform τ J d d • Matrix.vecMulVec d (rowOf τ J d) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, rowOf_dot]
    ext i j; simp [Matrix.vecMulVec_apply]; ring
  simp only [reflM, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul]
  calc _ = (1 : Matrix n n A) - (a + b - a * b * hform τ J d d) • Matrix.vecMulVec d (rowOf τ J d) := by
        module
    _ = 1 := by rw [sub_eq_zero.2 h]; simp

theorem reflM_unitary (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) (J : Matrix n n A)
    (hJ : ∀ i j, τ (J j i) = J i j) (a : A) (d : n → A)
    (h : a + τ a = a * τ a * hform τ J d d) :
    cT τ (reflM τ J a d) * J * reflM τ J a d = J := by
  set w := rowOf τ J d with hw
  set Q : Matrix n n A := Matrix.vecMulVec (fun i => τ (w i)) w with hQ
  have hc : cT τ (reflM τ J a d) = 1 - τ a • Matrix.vecMulVec (fun i => τ (w i)) (fun k => τ (d k)) := by
    ext i j
    simp [cT, reflM, Matrix.one_apply, Matrix.vecMulVec_apply, ← hw, apply_ite τ, mul_comm, eq_comm]
  have h1 : Matrix.vecMulVec (fun i => τ (w i)) (fun k => τ (d k)) * J = Q := by
    rw [Matrix.vecMulVec_mul]; rfl
  have hJd : J.mulVec d = fun i => τ (w i) := by
    ext i
    simp only [hw, rowOf, Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, hτ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ i j]; ring
  have h2 : J * Matrix.vecMulVec d w = Q := by
    rw [Matrix.mul_vecMulVec, hJd]
  have h3 : Q * Matrix.vecMulVec d w = hform τ J d d • Q := by
    rw [hQ, Matrix.vecMulVec_mul_vecMulVec, hw, rowOf_dot]
    ext i j; simp [Matrix.vecMulVec_apply]; ring
  have h4 : cT τ (reflM τ J a d) * J = J - τ a • Q := by
    rw [hc, sub_mul, one_mul, Matrix.smul_mul, h1]
  rw [h4]
  simp only [reflM, ← hw, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h2, h3, smul_smul]
  calc _ = J - (a + τ a - a * τ a * hform τ J d d) • Q := by module
    _ = J := by rw [sub_eq_zero.2 h]; simp

theorem reflM_mulVec (τ : A →+* A) (J : Matrix n n A) (a : A) (d p : n → A) :
    (reflM τ J a d).mulVec p = p - (a * hform τ J d p) • d := by
  simp only [reflM, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, rowOf_dot]
  ext i; simp [Matrix.vecMulVec_apply, mul_comm, mul_left_comm, mul_assoc]

theorem refl_facts (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) (J : Matrix n n A)
    (hJ : ∀ i j, τ (J j i) = J i j) (p y : n → A) (hyp : hform τ J y y = hform τ J p p)
    (ci : A) (hci : (hform τ J p p - hform τ J y p) * ci = 1) :
    reflM τ J ci (y - p) * reflM τ J (τ ci) (y - p) = 1 ∧
      reflM τ J (τ ci) (y - p) * reflM τ J ci (y - p) = 1 ∧
      cT τ (reflM τ J ci (y - p)) * J * reflM τ J ci (y - p) = J ∧
      (reflM τ J ci (y - p)).mulVec p = y := by
  have hτc : τ (hform τ J p p - hform τ J y p) * τ ci = 1 := by
    rw [← map_mul, hci, map_one]
  rw [map_sub, map_hform τ hτ J hJ, map_hform τ hτ J hJ] at hτc
  have hH : hform τ J (y - p) (y - p) =
      (hform τ J p p - hform τ J y p) + (hform τ J p p - hform τ J p y) := by
    rw [hform_sub_left, hform_sub_right, hform_sub_right, hyp]; ring
  have key : ci + τ ci = ci * τ ci * hform τ J (y - p) (y - p) := by
    rw [hH]; linear_combination (-(τ ci)) * hci - ci * hτc
  refine ⟨reflM_mul τ J _ _ _ key, reflM_mul τ J _ _ _ ?_, reflM_unitary τ hτ J hJ _ _ key, ?_⟩
  · rw [add_comm, key]; ring
  · rw [reflM_mulVec, hform_sub_left]
    have : ci * (hform τ J y p - hform τ J p p) = -1 := by linear_combination -hci
    rw [this]; simp

end Alg

section Sel

def selP {W : Type*} (Z : Set W) (V : ℕ → Set W) : ℕ → W → Prop
  | 0, y => y ∉ Z
  | k + 1, y => y ∈ V k

open Classical in

def selT {W G : Type*} (g₁ : G) (Z : Set W) (V : ℕ → Set W) (f : ℕ → W → G) : ℕ → W → G
  | 0, _ => g₁
  | k + 1, y => (V k ∩ Z).piecewise (f k) (fun _ => g₁) y

theorem selT_of_mem {W G : Type*} (g₁ : G) (Z : Set W) (V : ℕ → Set W) (f : ℕ → W → G) (k : ℕ) {y : W}
    (h : y ∈ V k ∩ Z) : selT g₁ Z V f (k + 1) y = f k y := by
  classical
  simp only [selT]
  exact Set.piecewise_eq_of_mem _ _ _ h

theorem exists_section {W G : Type*} [TopologicalSpace W] [LocallyCompactSpace W]
    [SecondCountableTopology W] [T2Space W] [MeasurableSpace W] [BorelSpace W]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] (g₁ : G) (Z : Set W) (hZ : IsClosed Z)
    (P : G → W → Prop)
    (loc : ∀ y₀ ∈ Z, ∃ U : Set W, IsOpen U ∧ y₀ ∈ U ∧ ∃ f : W → G,
      ContinuousOn f (U ∩ Z) ∧ ∀ y ∈ U ∩ Z, P (f y) y) :
    ∃ s : W → G, Measurable s ∧ (∀ y ∈ Z, P (s y) y) ∧
      ∀ C : Set W, IsCompact C → ∃ C' : Set G, IsCompact C' ∧ ∀ y ∈ C, y ∈ Z → s y ∈ C' := by
  classical
  rcases Z.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => g₁, measurable_const, by simp, fun C _ => ⟨∅, isCompact_empty, by simp⟩⟩
  have loc' : ∀ y₀ : Z, ∃ L : Set W, IsCompact L ∧ y₀.1 ∈ interior L ∧ ∃ f : W → G,
      ContinuousOn f (L ∩ Z) ∧ ∀ y ∈ L ∩ Z, P (f y) y := by
    rintro ⟨y₀, hy₀⟩
    obtain ⟨U, hU, hyU, f, hf, hP⟩ := loc y₀ hy₀
    obtain ⟨L, hL, hyL, hLU⟩ := exists_compact_between (isCompact_singleton (x := y₀)) hU
      (Set.singleton_subset_iff.2 hyU)
    have hsub : L ∩ Z ⊆ U ∩ Z := Set.inter_subset_inter_left _ hLU
    exact ⟨L, hL, hyL (Set.mem_singleton _), f, hf.mono hsub, fun y hy => hP y (hsub hy)⟩
  choose L hLc hLi f hfc hfP using loc'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun y₀ : Z => interior (L y₀))
    (fun _ => isOpen_interior)
  have hcov : ∀ y ∈ Z, ∃ i ∈ T, y ∈ interior (L i) := by
    intro y hy
    have : y ∈ ⋃ i ∈ T, interior (L i) := by
      rw [hTU]; exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hLi _⟩
    simpa using this
  have hTne : T.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨i, hi, -⟩ := hcov y hy
    exact ⟨i, hi⟩
  obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
  set V : ℕ → Set W := fun k => interior (L (e k)) with hV
  have hVo : ∀ k, IsOpen (V k) := fun k => isOpen_interior
  have hcov' : ∀ y ∈ Z, ∃ k, y ∈ V k := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := hcov y hy
    rw [he] at hi
    obtain ⟨k, rfl⟩ := hi
    exact ⟨k, hyi⟩
  have hVL : ∀ k, V k ∩ Z ⊆ L (e k) ∩ Z := fun k =>
    Set.inter_subset_inter_left _ interior_subset
  set p := selP Z V with hpdef
  set t := selT g₁ Z V (fun k => f (e k)) with htdef
  have ht : ∀ n, Measurable (t n) := by
    rintro (_ | k)
    · exact measurable_const
    · exact (ContinuousOn.measurable_piecewise ((hfc _).mono (hVL k)) continuousOn_const
        ((hVo k).measurableSet.inter hZ.measurableSet) :)
  have hp : ∀ n, MeasurableSet {y | p n y} := by
    rintro (_ | k)
    · exact hZ.measurableSet.compl
    · exact (hVo k).measurableSet
  have hex : ∀ y, ∃ n, p n y := by
    intro y
    by_cases hy : y ∈ Z
    · obtain ⟨k, hk⟩ := hcov' y hy
      exact ⟨k + 1, hk⟩
    · exact ⟨0, hy⟩
  have hfind : ∀ y : W, y ∈ Z → ∃ k : ℕ, Nat.find (hex y) = k + 1 ∧ y ∈ V k := by
    intro y hy
    have hs := Nat.find_spec (hex y)
    rcases hn : Nat.find (hex y) with _ | k
    · rw [hn] at hs; exact absurd hy hs
    · rw [hn] at hs; exact ⟨k, rfl, hs⟩
  have hval : ∀ y : W, y ∈ Z → ∃ k : ℕ, Nat.find (hex y) = k + 1 ∧ y ∈ V k ∧
      t (Nat.find (hex y)) y = f (e k) y := by
    intro y hy
    obtain ⟨k, hk, hyk⟩ := hfind y hy
    refine ⟨k, hk, hyk, ?_⟩
    rw [hk]
    exact selT_of_mem g₁ Z V _ k ⟨hyk, hy⟩
  refine ⟨fun y => t (Nat.find (hex y)) y, Measurable.find ht hp hex, ?_, ?_⟩
  · intro y hy
    obtain ⟨k, -, hyk, h⟩ := hval y hy
    simp only [h]
    exact hfP _ y (hVL k ⟨hyk, hy⟩)
  · intro C hC
    have hCZ : IsCompact (C ∩ Z) := hC.inter_right hZ
    obtain ⟨S, hS⟩ := hCZ.elim_finite_subcover V hVo (fun y hy => by
      obtain ⟨k, hk⟩ := hcov' y hy.2
      exact Set.mem_iUnion.2 ⟨k, hk⟩)
    refine ⟨⋃ k ∈ Finset.range (S.sup id + 1), f (e k) '' (L (e k) ∩ Z),
      (Finset.range _).isCompact_biUnion fun k _ =>
        ((hLc _).inter_right hZ).image_of_continuousOn (hfc _), ?_⟩
    intro y hyC hyZ
    obtain ⟨k, hk, hyk, h⟩ := hval y hyZ
    have hmem := hS ⟨hyC, hyZ⟩
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨j, hj, hyj⟩ := hmem
    have hle : Nat.find (hex y) ≤ j + 1 := Nat.find_min' (hex y) hyj
    have hkj : k ≤ S.sup id := by
      have : j ≤ S.sup id := Finset.le_sup (f := id) hj
      omega
    simp only [h]
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (by omega)))
      ⟨y, hVL k ⟨hyk, hyZ⟩, rfl⟩

end Sel

section Local

variable {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_neg_neg (τ : K →+* K) (J : Matrix n n K) (u : n → K) :
    hform τ J (-u) (-u) = hform τ J u u := by
  simp [hform]

theorem hform_neg_right (τ : K →+* K) (J : Matrix n n K) (u v : n → K) :
    hform τ J u (-v) = -hform τ J u v := by
  simp [hform]

theorem reflM_cont [TopologicalSpace K] [IsTopologicalRing K] {X : Type*} [TopologicalSpace X]
    (τ : K →+* K) (hτ : Continuous τ) (J : Matrix n n K) {a : X → K} {d : X → n → K}
    (ha : Continuous a) (hd : Continuous d) : Continuous fun x => reflM τ J (a x) (d x) := by
  have hd' : ∀ i, Continuous fun x => d x i := fun i => (continuous_apply i).comp hd
  refine continuous_matrix fun i j => ?_
  simp only [reflM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, rowOf,
    Matrix.vecMul, dotProduct]
  exact continuous_const.sub (ha.mul ((hd' i).mul
    (continuous_finset_sum _ fun k _ => (hτ.comp (hd' k)).mul continuous_const)))

theorem continuousAt_ringInverse [TopologicalSpace K] [IsTopologicalRing K]
    (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {a : K} (ha : IsUnit a) :
    ContinuousAt (Ring.inverse : K → K) a := by
  obtain ⟨u, rfl⟩ := ha
  rw [← hU.continuousAt_iff]
  have : (Ring.inverse : K → K) ∘ (Units.val : Kˣ → K) = fun v : Kˣ => ((v⁻¹ : Kˣ) : K) := by
    funext v; simp
  rw [this]
  exact (Units.continuous_val.comp continuous_inv).continuousAt

theorem local_refl [TopologicalSpace K] [IsTopologicalRing K] (τ : K →+* K) (hτc : Continuous τ)
    (hτ : ∀ a, τ (τ a) = a) (J : Matrix n n K) (hJ : ∀ i j, τ (J j i) = J i j)
    (hU : IsOpenEmbedding (Units.val : Kˣ → K)) (h2 : IsUnit (2 : K)) (u : n → K)
    (hu : IsUnit (hform τ J u u)) :
    ∃ U : Set (n → K), IsOpen U ∧ u ∈ U ∧
      ∃ t : {v : n → K // v ∈ U ∧ hform τ J v v = hform τ J u u} → UJ τ J, Continuous t ∧
        ∀ v, (((t v : UJ τ J) : GL n K) : Matrix n n K).mulVec (-u) = v.1 := by
  have hneg := hform_neg_neg τ J u
  let cf : (n → K) → K := fun v => hform τ J (-u) (-u) - hform τ J v (-u)
  have hcf : Continuous cf := by
    refine continuous_const.sub ?_
    simp only [hform]
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      ((hτc.comp (continuous_apply i)).mul continuous_const).mul continuous_const
  have hopen : IsOpen {a : K | IsUnit a} := by
    have : {a : K | IsUnit a} = Set.range (Units.val : Kˣ → K) := by
      ext a; exact Iff.rfl
    rw [this]; exact hU.isOpen_range
  have hmem : cf u = 2 * hform τ J u u := by
    simp only [cf, hform_neg_right, hneg]; ring
  have hfacts : ∀ v : {v : n → K // v ∈ cf ⁻¹' {a : K | IsUnit a} ∧ hform τ J v v = hform τ J u u}, _ :=
    fun v => refl_facts τ hτ J hJ (-u) v.1 (by rw [hneg]; exact v.2.2) (Ring.inverse (cf v.1))
      (Ring.mul_inverse_cancel _ v.2.1)
  refine ⟨cf ⁻¹' {a : K | IsUnit a}, hopen.preimage hcf, ?_,
    fun v => ⟨⟨reflM τ J (Ring.inverse (cf v.1)) (v.1 - -u),
      reflM τ J (τ (Ring.inverse (cf v.1))) (v.1 - -u), (hfacts v).1, (hfacts v).2.1⟩, (hfacts v).2.2.1⟩,
    ?_, fun v => (hfacts v).2.2.2⟩
  · show IsUnit (cf u)
    rw [hmem]; exact h2.mul hu
  · have hci : Continuous fun v : {v : n → K // v ∈ cf ⁻¹' {a : K | IsUnit a} ∧ hform τ J v v = hform τ J u u} =>
        Ring.inverse (cf v.1) :=
      continuous_iff_continuousAt.2 fun v =>
        ContinuousAt.comp (f := fun v : {v : n → K // v ∈ cf ⁻¹' {a : K | IsUnit a} ∧ hform τ J v v = hform τ J u u} => cf v.1)
          (continuousAt_ringInverse hU v.2.1) (hcf.comp continuous_subtype_val).continuousAt
    have hd : Continuous fun v : {v : n → K // v ∈ cf ⁻¹' {a : K | IsUnit a} ∧ hform τ J v v = hform τ J u u} =>
        v.1 - -u := continuous_subtype_val.sub continuous_const
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact reflM_cont τ hτc J hci hd
    · exact reflM_cont τ hτc J (hτc.comp hci) hd

end Local

theorem orbit_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin M → R ⊗[F] E, IsUnit (gramR R σ J x).det → ∃ s : (Fin 1 → Fin M → R ⊗[F] E) → HA R σ J, Measurable s ∧ (∀ y, gramR R σ J y = gramR R σ J x → actW R σ J (s y) x = y) ∧ ∀ C : Set (Fin 1 → Fin M → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ J), IsCompact C' ∧ ∀ y ∈ C, gramR R σ J y = gramR R σ J x → s y ∈ C' := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hLoc x hx
  obtain ⟨hTR, hLC, hSC, hT2, hArt, hRed, -, -⟩ := id hLoc
  haveI := hTR; haveI := hLC; haveI := hSC; haveI := hT2; haveI := hArt; haveI := hRed
  obtain ⟨hKr, hKl, hKs, hKt, hσc, -, -, hBor, -, hgram⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := hKr; haveI := hKl; haveI := hKs; haveI := hKt
  obtain ⟨hHg, -, -, -, hHb, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ R
  haveI := hHg; haveI := hHb
  obtain ⟨-, -, h2, hinv, -, -, -⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hCM R
  have hUe := GlobalTheory.T.units_open_embedding_local_tensor F E σ hCM R hLoc
  haveI := hBor 1 M
  have hZ : IsClosed {y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J y = gramR R σ J x} :=
    isClosed_eq (hgram 1 M J) continuous_const
  have hJk : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    simp [sigR, inclR, JR, Matrix.map_apply, hJ.1 i j]
  have hdet : IsUnit (hform (sigR R σ) (JR R J) (x 0) (x 0)) := by
    have := hx
    rw [Matrix.det_fin_one] at this
    exact this
  obtain ⟨s, hs, hsP, hsC⟩ := exists_section (1 : HA R σ J)
    {y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J y = gramR R σ J x} hZ
    (fun g y => actW R σ J g x = y) (by
      intro y₀ hy₀
      have hZ0 : ∀ y : Fin 1 → Fin M → R ⊗[F] E, gramR R σ J y = gramR R σ J x →
          hform (sigR R σ) (JR R J) (y 0) (y 0) = hform (sigR R σ) (JR R J) (x 0) (x 0) :=
        fun y hy => congrFun (congrFun hy 0) 0
      have hβ := hZ0 y₀ hy₀
      obtain ⟨U, hUo, huU, t, ht, htv⟩ := local_refl (sigR R σ) hσc hinv (JR R J) hJk hUe h2 (y₀ 0)
        (hβ ▸ hdet)
      have hgp : gramR R σ J x = gramR R σ J (fun a => - y₀ a) := by
        ext a b
        rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
        show hform (sigR R σ) (JR R J) (x 0) (x 0) = hform (sigR R σ) (JR R J) (- y₀ 0) (- y₀ 0)
        rw [hform_neg_neg, hβ]
      obtain ⟨h₀, hh₀⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hCM M J hJ R 1 x _ hgp hx
      have hmem : ∀ y ∈ (fun y : Fin 1 → Fin M → R ⊗[F] E => y 0) ⁻¹' U ∩
          {y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J y = gramR R σ J x},
          y 0 ∈ U ∧ hform (sigR R σ) (JR R J) (y 0) (y 0) = hform (sigR R σ) (JR R J) (y₀ 0) (y₀ 0) :=
        fun y hy => ⟨hy.1, (hZ0 y hy.2).trans hβ.symm⟩
      classical
      let g : ((fun y : Fin 1 → Fin M → R ⊗[F] E => y 0) ⁻¹' U ∩
          {y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J y = gramR R σ J x} : Set _) → HA R σ J :=
        fun y => t ⟨y.1 0, hmem y.1 y.2⟩
      have hg : Continuous g := ht.comp (Continuous.subtype_mk
        ((continuous_apply 0).comp continuous_subtype_val) _)
      refine ⟨_, hUo.preimage (continuous_apply 0), huU,
        fun y => if hy : y ∈ (fun y : Fin 1 → Fin M → R ⊗[F] E => y 0) ⁻¹' U ∩
          {y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J y = gramR R σ J x} then g ⟨y, hy⟩ * h₀ else 1,
        ?_, ?_⟩
      · rw [continuousOn_iff_continuous_restrict]
        refine (hg.mul (continuous_const (y := h₀))).congr fun y => ?_
        show g y * h₀ = (if hy : y.1 ∈ (fun y : Fin 1 → Fin M → R ⊗[F] E => y 0) ⁻¹' U ∩
          {y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J y = gramR R σ J x} then g ⟨y.1, hy⟩ * h₀ else 1)
        rw [dif_pos y.2]
      · intro y hy
        simp only [dif_pos hy]
        rw [(hact 1).2.2.1, hh₀]
        funext a
        rw [Fin.fin_one_eq_zero a]
        exact htv ⟨y 0, hmem y hy⟩)
  exact ⟨s, hs, fun y hy => hsP y hy, fun C hC => hsC C hC⟩

end GlobalTheory.CompanionTheory.SW.OrbitSection
