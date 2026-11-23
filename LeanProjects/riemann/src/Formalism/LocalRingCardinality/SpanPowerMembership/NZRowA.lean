import Formalism.LocalRingCardinality.DataRows
import Formalism.LocalRingCardinality.DataForms

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

abbrev stdH : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))

theorem mem_stdL (x : Fin n → K) : x ∈ (stdH K n).L ↔ ∀ i, ∃ c : 𝓞 K, x i = (c : K) := by
  show x ∈ Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) ↔ _
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      intro i
      by_cases h : i = k
      · exact ⟨1, by subst h; simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => exact fun _ => ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro i
      obtain ⟨a, ha⟩ := hy i
      obtain ⟨b, hb⟩ := hz i
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul a y _ hy =>
      intro i
      obtain ⟨c, hc⟩ := hy i
      exact ⟨a * c, by rw [Pi.smul_apply, hc, Algebra.smul_def]; simp⟩
  · intro h
    choose c hc using h
    have : x = ∑ i, c i • Pi.basisFun K (Fin n) i := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same, hc k, Algebra.smul_def, mul_one]
      · intro i _ hi
        rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem stdH_span : Submodule.span K ((stdH K n).L : Set (stdH K n).V) = ⊤ := by
  show Submodule.span K ((Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) :
    Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = ⊤
  rw [Submodule.span_span_of_tower]
  exact (Pi.basisFun K (Fin n)).span_eq

theorem stdH_frames (v : InfinitePlace K) : IsUnit ((stdH K n).X v).det := by
  rw [show (stdH K n).X v = 1 from rfl, Matrix.det_one]
  exact isUnit_one

theorem stdH_good : (stdH K n).Good :=
  ⟨stdH_frames K n, Submodule.fg_span (Set.finite_range _), stdH_span K n⟩

end Std

section JB0

variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)

def jB : (Fin n → K) →ₛₗ[σ] V where
  toFun x := ∑ i, σ (x i) • b i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

theorem jB_apply (x : Fin n → K) : jB σ b x = ∑ i, σ (x i) • b i := rfl

theorem jB_single (i : Fin n) : jB σ b (Pi.basisFun K (Fin n) i) = b i := by
  rw [jB_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Pi.basisFun_apply, Pi.single_eq_of_ne hk, map_zero, zero_smul]
  · simp

theorem jB_basis0 : LinearIndependent ℂ (fun i => jB σ b (Pi.basisFun K (Fin n) i)) ∧
    Submodule.span ℂ (Set.range (fun i => jB σ b (Pi.basisFun K (Fin n) i))) = ⊤ := by
  have h : (fun i => jB σ b (Pi.basisFun K (Fin n) i)) = b := funext fun i => jB_single σ b i
  rw [h]
  exact ⟨b.orthonormal.linearIndependent, by
    have := b.toBasis.span_eq
    rwa [b.coe_toBasis] at this⟩

theorem jB_inj : Function.Injective (jB σ b) :=
  inj_of_li σ (jB σ b) (Pi.basisFun K (Fin n)) (jB_basis0 σ b).1

theorem repr_jB (x : Fin n → K) (i : Fin n) : b.repr (jB σ b x) i = σ (x i) := by
  rw [jB_apply, map_sum, WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, b.repr_self]; simp
  · intro k _ hk
    rw [map_smul, b.repr_self]; simp [hk]
  · simp

theorem norm_jB (x : Fin n → K) : ‖jB σ b x‖ = Real.sqrt (∑ i, ‖σ (x i)‖ ^ 2) := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_eq]
  simp only [repr_jB]

open Classical in

def genB : Finset V := Finset.univ.image b

theorem generators_mem_range : ∀ v ∈ genB b, v ∈ Set.range (jB σ b) := fun v hv => by
  classical
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact ⟨_, jB_single σ b i⟩

end JB0

section JB

variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)

theorem jB_basis : LinearIndependent ℂ (fun i => jB σ b ((stdH K n).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jB σ b ((stdH K n).b i))) = ⊤ := by
  have h : (fun i => jB σ b ((stdH K n).b i)) = b := funext fun i => jB_single σ b i
  rw [h]
  exact ⟨b.orthonormal.linearIndependent, by
    have := b.toBasis.span_eq
    rwa [b.coe_toBasis] at this⟩

theorem fcoord_stdF (v : InfinitePlace K) (x : Fin n → K) (i : Fin n) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v x i =
      v.embedding (x i) := by
  simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt]

theorem jB_norm (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (stdH K n).b (stdH K n).X (InfinitePlace.mk σ) x = ‖jB σ b x‖ := by
  rw [norm_jB]
  show Real.sqrt (∑ i, ‖Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) (fun _ => 1) _ x i‖ ^ 2) = _
  simp only [fcoord_stdF, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

theorem b_inj : Function.Injective b := by
  have := b.toBasis.injective
  rwa [b.coe_toBasis] at this

theorem sum_genB (f : V → V) : ∑ v ∈ genB b, f v = ∑ i, f (b i) := by
  classical
  exact Finset.sum_image fun i _ k _ h => b_inj b h

theorem genB_span : Submodule.span ℂ (genB b : Set V) = ⊤ := by
  have := b.toBasis.span_eq
  rw [b.coe_toBasis] at this
  classical
  rw [genB, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact this

def oB {O : Type} [CommRing O] (φ : O →+* ℂ) : Rows.OLat O φ V := ⟨genB b, genB_span b⟩

theorem mem_oB {O : Type} [CommRing O] (φ : O →+* ℂ) (x : V) :
    x ∈ (oB b φ).carrier ↔ ∃ c : Fin n → O, x = ∑ i, φ (c i) • b i := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c (b i), sum_genB b fun v => φ (c v) • v⟩
  · rintro ⟨c, rfl⟩
    classical
    refine ⟨fun v => if h : ∃ i, b i = v then c h.choose else 0, ?_⟩
    rw [show (oB b φ).gen = genB b from rfl, sum_genB b fun v => φ (if h : ∃ i, b i = v then c h.choose else 0) • v]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : ∃ k, b k = b i := ⟨i, rfl⟩
    rw [dif_pos h, b_inj b h.choose_spec]

theorem jB_gen : ∀ v ∈ genB b, v ∈ Set.range (jB σ b) := generators_mem_range σ b

theorem jB_lat (x : Fin n → K) : x ∈ (stdH K n).L ↔ ∃ c : V → 𝓞 K,
    jB σ b x = ∑ v ∈ genB b, σ ((c v : 𝓞 K) : K) • v := by
  rw [mem_stdL]
  constructor
  · intro h
    choose c hc using h
    classical
    refine ⟨fun v => if h : ∃ i, b i = v then c h.choose else 0, ?_⟩
    rw [sum_genB b fun v => σ (((if h : ∃ i, b i = v then c h.choose else 0 : 𝓞 K)) : K) • v, jB_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : ∃ k, b k = b i := ⟨i, rfl⟩
    rw [dif_pos h, b_inj b h.choose_spec, hc i]
  · rintro ⟨c, hc⟩ i
    refine ⟨c (b i), σ.injective ?_⟩
    rw [sum_genB b fun v => σ ((c v : 𝓞 K) : K) • v] at hc
    have h1 := congrArg (fun y => b.repr y i) hc
    have h2 : (∑ k, σ ((c (b k) : 𝓞 K) : K) • b k) = jB σ b (fun k => ((c (b k) : 𝓞 K) : K)) := rfl
    simp only [h2, repr_jB] at h1
    exact h1

end JB

theorem mem_of_local {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Λ : Submodule A M) (x : M)
    (h : ∀ P : Ideal A, P.IsMaximal → ∃ d : A, d ∉ P ∧ d • x ∈ Λ) : x ∈ Λ := by
  let I : Ideal A :=
    { carrier := {d | d • x ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • x ∈ Λ
        rw [add_smul]; exact Λ.add_mem ha hb
      zero_mem' := by
        show (0 : A) • x ∈ Λ
        rw [zero_smul]; exact Λ.zero_mem
      smul_mem' := fun c {a} ha => by
        show (c • a) • x ∈ Λ
        rw [smul_eq_mul, mul_smul]; exact Λ.smul_mem c ha }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨d, hd, hx⟩ := h P hP
    exact hd (hle hx)
  have : (1 : A) ∈ I := by rw [hI]; trivial
  simpa using (show (1 : A) • x ∈ Λ from this)

theorem basis_of_basis {K W M ι κ : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module ℂ M] [Fintype ι] [Fintype κ] (σ : K →+* ℂ) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent ℂ (fun i => e (b i)) ∧ Submodule.span ℂ (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent ℂ (fun i => e (b' i)) ∧ Submodule.span ℂ (Set.range fun i => e (b' i)) = ⊤ := by
  have hexp : ∀ (c : Module.Basis ι K W) (x : W), e x = ∑ i, σ (c.repr x i) • e (c i) := fun c x => by
    conv_lhs => rw [← c.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hexp' : ∀ x : W, e x = ∑ i, σ (b'.repr x i) • e (b' i) := fun x => by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hspan : Submodule.span ℂ (Set.range fun i => e (b' i)) = ⊤ := by
    rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (b i) ∈ _
    rw [hexp' (b i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨?_, hspan⟩
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis b]
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hfin : Module.finrank ℂ M = Fintype.card κ := by
    rw [Module.finrank_eq_card_basis B, hcard]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hfin.symm

end Formalism.BasicNotions.Examples₂.NZ
