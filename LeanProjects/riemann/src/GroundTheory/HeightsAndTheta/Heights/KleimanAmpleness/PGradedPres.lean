import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsPres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace GradedPres

theorem iSupIndep_of_coords {R X Y ι : Type*} [Ring R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] {p : ℤ → Submodule R X} {q : ℤ → Submodule R Y}
    (hq : iSupIndep q) (π : ι → X →ₗ[R] Y) (σ : ι → ℤ → ℤ) (hσ : ∀ i, Function.Injective (σ i))
    (hp : ∀ i c, p c ≤ (q (σ i c)).comap (π i)) (hπ : ∀ x, (∀ i, π i x = 0) → x = 0) :
    iSupIndep p := by
  rw [iSupIndep_def]
  intro c
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply hπ
  intro i
  have h1 : π i x ∈ q (σ i c) := hp i c hx
  have hle : Submodule.map (π i) (⨆ (c' : ℤ) (_ : c' ≠ c), p c') ≤
      ⨆ (e : ℤ) (_ : e ≠ σ i c), q e := by
    rw [Submodule.map_iSup]
    refine iSup_le fun c' => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hc' => ?_
    rw [Submodule.map_le_iff_le_comap]
    exact (hp i c').trans (Submodule.comap_mono
      (le_iSup₂_of_le (f := fun (e : ℤ) (_ : e ≠ σ i c) => q e) (σ i c')
        (fun h => hc' (hσ i h)) le_rfl))
  have h2 : π i x ∈ ⨆ (e : ℤ) (_ : e ≠ σ i c), q e := hle (Submodule.mem_map_of_mem hx')
  exact Submodule.disjoint_def.mp ((iSupIndep_def.mp hq) (σ i c)) _ h1 h2

section Free

variable {S : Type u} [CommRing S] {N : ℕ}

theorem smul_mem_piece {M : Type w} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
    [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M) {a c : ℤ} {p : Poly S N} {m : M}
    (hp : p ∈ (polyGraded S N).piece a) (hm : m ∈ 𝓜.piece c) : p • m ∈ 𝓜.piece (c + a) := by
  change p ∈ weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) a at hp
  rw [mem_weightedHomogeneousSubmodule] at hp
  rcases le_or_gt 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    refine 𝓜.smul_mem n c p m ?_ hm
    intro μ hμ
    have h := hp hμ
    simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one,
      nsmul_eq_mul] at h ⊢
    exact_mod_cast h
  · have hp0 : p = 0 := by
      by_contra hne
      obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hne
      have h := hp hμ
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_one] at h
      have : (0 : ℤ) ≤ ∑ i ∈ μ.support, (μ i : ℤ) :=
        Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
      omega
    rw [hp0, zero_smul]
    exact zero_mem _

variable {r : ℕ}

def freePiece (d : Fin r → ℤ) (c : ℤ) : Submodule S (ULift.{v} (Fin r → Poly S N)) where
  carrier := {x | ∀ j, x.down j ∈ (polyGraded S N).piece (c - d j)}
  add_mem' ha hb j := add_mem (ha j) (hb j)
  zero_mem' _ := zero_mem _
  smul_mem' s _ hx j := Submodule.smul_mem _ s (hx j)

def coordIncl (j : Fin r) : Poly S N →ₗ[S] ULift.{v} (Fin r → Poly S N) :=
  (ULift.moduleEquiv (R := S)).symm.toLinearMap ∘ₗ LinearMap.single S (fun _ : Fin r => Poly S N) j

theorem coordIncl_down (j : Fin r) (p : Poly S N) :
    (coordIncl.{u, v} j p).down = Pi.single j p := rfl

theorem coordIncl_mem {d : Fin r → ℤ} (j : Fin r) {e : ℤ} {p : Poly S N}
    (hp : p ∈ (polyGraded S N).piece e) : coordIncl.{u, v} j p ∈ freePiece d (e + d j) := by
  intro i
  rw [coordIncl_down]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, add_sub_cancel_right]
    exact hp
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

variable (N) in

def freeGraded (d : Fin r → ℤ) : GradedPMod S N (ULift.{v} (Fin r → Poly S N)) where
  piece := freePiece d
  isInternal := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · exact iSupIndep_of_coords (polyGraded S N).isInternal.submodule_iSupIndep
        (fun j => (LinearMap.proj j : (Fin r → Poly S N) →ₗ[S] Poly S N) ∘ₗ
          (ULift.moduleEquiv (R := S)).toLinearMap)
        (fun j c => c - d j) (fun j => sub_left_injective) (fun j c x hx => hx j)
        (fun x hx => ULift.ext _ _ (funext hx))
    · rw [eq_top_iff]
      intro x _
      have hx : x = ∑ j, coordIncl.{u, v} j (x.down j) := by
        apply (ULift.moduleEquiv (R := S)).injective
        rw [map_sum]
        exact (Finset.univ_sum_single x.down).symm
      rw [hx]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hp : x.down j ∈ ⨆ e, (polyGraded S N).piece e := by
        rw [(polyGraded S N).isInternal.submodule_iSup_eq_top]
        trivial
      refine Submodule.iSup_induction _ (motive := fun p => coordIncl.{u, v} j p ∈ ⨆ c, freePiece d c)
        hp (fun e p hp => Submodule.mem_iSup_of_mem (e + d j) (coordIncl_mem j hp)) ?_ ?_
      · rw [map_zero]
        exact zero_mem _
      · intro a b ha hb
        rw [map_add]
        exact add_mem ha hb
  smul_mem n c p x hp hx j := by
    change p * x.down j ∈ (polyGraded S N).piece (c + n - d j)
    have h := smul_mem_piece (polyGraded S N) (a := n) (c := c - d j)
      (isWeightedHomogeneous_int_of_isHomogeneous hp) (hx j)
    rw [smul_eq_mul, show c - d j + n = c + n - d j by ring] at h
    exact h

variable (S N) in

def freeBasis (r : ℕ) : Module.Basis (Fin r) (Poly S N) (ULift.{v} (Fin r → Poly S N)) :=
  (Pi.basisFun (Poly S N) (Fin r)).map (ULift.moduleEquiv (R := Poly S N)).symm

theorem freeBasis_down (j : Fin r) : (freeBasis.{u, v} S N r j).down = Pi.single j 1 := by
  rw [freeBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

theorem freeBasis_mem (d : Fin r → ℤ) (j : Fin r) :
    freeBasis.{u, v} S N r j ∈ (freeGraded.{u, v} N d).piece (d j) := by
  intro i
  rw [freeBasis_down]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, sub_self]
    show (1 : Poly S N) ∈ weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) 0
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one S _
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

variable {M : Type w} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

def genMap (𝓜 : GradedPMod S N M) (d : Fin r → ℤ) (m : Fin r → M) (hm : ∀ j, m j ∈ 𝓜.piece (d j)) :
    GradedHom (freeGraded.{u, v} N d) 𝓜 where
  toLin := Fintype.linearCombination (Poly S N) m ∘ₗ (ULift.moduleEquiv (R := Poly S N)).toLinearMap
  map_piece c x hx := by
    change Fintype.linearCombination (Poly S N) m x.down ∈ 𝓜.piece c
    rw [Fintype.linearCombination_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h := smul_mem_piece 𝓜 (hx j) (hm j)
    rwa [add_sub_cancel] at h

theorem genMap_basis (𝓜 : GradedPMod S N M) (d : Fin r → ℤ) (m : Fin r → M)
    (hm : ∀ j, m j ∈ 𝓜.piece (d j)) (j : Fin r) :
    (genMap.{u, v} 𝓜 d m hm).toLin (freeBasis.{u, v} S N r j) = m j := by
  classical
  change Fintype.linearCombination (Poly S N) m (freeBasis.{u, v} S N r j).down = m j
  rw [freeBasis_down, Fintype.linearCombination_apply_single, one_smul]

end Free

section Ker

variable {S : Type u} [CommRing S] {N : ℕ}
variable {F : Type v} [AddCommGroup F] [Module (Poly S N) F] [Module S F]
  [IsScalarTower S (Poly S N) F]
variable {M : Type w} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {𝓕 : GradedPMod S N F} {𝓜 : GradedPMod S N M}

omit [IsScalarTower S (Poly S N) F] [IsScalarTower S (Poly S N) M] in

theorem component_map (g : GradedHom 𝓕 𝓜) (y : DirectSum ℤ fun c => 𝓕.piece c) (c : ℤ) :
    (((LinearEquiv.ofBijective (DirectSum.coeLinearMap 𝓜.piece) 𝓜.isInternal).symm
      (g.toLin (DirectSum.coeLinearMap 𝓕.piece y))) c : M) = g.toLin (y c) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [DirectSum.coeLinearMap_of]
    by_cases h : i = c
    · subst h
      rw [𝓜.isInternal.ofBijective_coeLinearMap_of_mem (g.map_piece i x x.2), DirectSum.of_eq_same]
    · rw [𝓜.isInternal.ofBijective_coeLinearMap_of_mem_ne h (g.map_piece i x x.2)]
      simp [DirectSum.of_apply, h]
  | add a b ha hb =>
    simp only [map_add, DirectSum.add_apply, Submodule.coe_add, ha, hb]

def kerGraded (g : GradedHom 𝓕 𝓜) : GradedPMod S N (LinearMap.ker g.toLin) where
  piece c := (𝓕.piece c).comap ((LinearMap.ker g.toLin).subtype.restrictScalars S)
  isInternal := by
    classical
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · exact iSupIndep_of_coords 𝓕.isInternal.submodule_iSupIndep
        (fun _ : Unit => (LinearMap.ker g.toLin).subtype.restrictScalars S) (fun _ => id)
        (fun _ => Function.injective_id) (fun _ _ _ hx => hx) (fun x hx => Subtype.ext (hx ()))
    · rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      set y := (LinearEquiv.ofBijective (DirectSum.coeLinearMap 𝓕.piece) 𝓕.isInternal).symm x
      have hxy : DirectSum.coeLinearMap 𝓕.piece y = x :=
        (LinearEquiv.ofBijective (DirectSum.coeLinearMap 𝓕.piece) 𝓕.isInternal).apply_symm_apply x
      have hy : ∀ c, g.toLin (y c) = 0 := by
        intro c
        rw [← component_map g y c, hxy, LinearMap.mem_ker.mp hx, map_zero]
        rfl
      have hsum : (⟨x, hx⟩ : LinearMap.ker g.toLin) =
          ∑ c ∈ y.support,
            (⟨(y c : F), LinearMap.mem_ker.mpr (hy c)⟩ : LinearMap.ker g.toLin) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        show x = ∑ c ∈ y.support, (y c : F)
        conv_lhs => rw [← hxy]
        rw [DirectSum.coeLinearMap_eq_dfinsuppSum]
        rfl
      rw [hsum]
      exact Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (y c).2
  smul_mem n c p k hp hk := 𝓕.smul_mem n c p k hp hk

def kerIncl (g : GradedHom 𝓕 𝓜) : GradedHom (kerGraded g) 𝓕 where
  toLin := (LinearMap.ker g.toLin).subtype
  map_piece _ _ hk := hk

end Ker

theorem exists_homogeneous_generators {S : Type u} [CommRing S] {N : ℕ} {M : Type w}
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M) (hfin : Module.Finite (Poly S N) M) :
    ∃ (r : ℕ) (m : Fin r → M) (d : Fin r → ℤ), (∀ j, m j ∈ 𝓜.piece (d j)) ∧
      Submodule.span (Poly S N) (Set.range m) = ⊤ := by
  classical
  let H : Set M := ⋃ c, (𝓜.piece c : Set M)
  have hH : Submodule.span (Poly S N) H = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ c, 𝓜.piece c := by
      rw [𝓜.isInternal.submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction _ (motive := fun y => y ∈ Submodule.span (Poly S N) H) hx
      (fun c y hy => Submodule.subset_span (Set.mem_iUnion.mpr ⟨c, hy⟩)) (zero_mem _)
      (fun a b ha hb => add_mem ha hb)
  have hcomp := (Submodule.fg_iff_compact (⊤ : Submodule (Poly S N) M)).mp hfin.fg_top
  have hle : (⊤ : Submodule (Poly S N) M) ≤ ⨆ h : H, Submodule.span (Poly S N) {(h : M)} := by
    rw [← hH, Submodule.span_le]
    intro y hy
    exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : H) (Submodule.mem_span_singleton_self y)
  obtain ⟨t, ht⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hcomp _ hle
  let e := t.equivFin
  refine ⟨t.card, fun j => ((e.symm j : H) : M),
    fun j => Classical.choose (Set.mem_iUnion.mp (e.symm j : H).2),
    fun j => Classical.choose_spec (Set.mem_iUnion.mp (e.symm j : H).2), ?_⟩
  rw [eq_top_iff]
  refine ht.trans (iSup₂_le fun h hh => ?_)
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact Submodule.subset_span ⟨e ⟨h, hh⟩, by simp⟩

end GradedPres

theorem GradedPres.proof : GradedPres.Statement.{u, v} := by
  intro S _ _ N M _ _ _ _ 𝓜 hfin
  classical
  obtain ⟨r, m, d, hm, hspan⟩ := GradedPres.exists_homogeneous_generators 𝓜 hfin
  let g := GradedPres.genMap.{u, max u v} 𝓜 d m hm
  have : Module.Finite (Poly S N) (ULift.{max u v} (Fin r → Poly S N)) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := Poly S N)).symm
  refine ⟨ULift.{max u v} (Fin r → Poly S N), inferInstance, inferInstance, inferInstance,
    inferInstance, LinearMap.ker g.toLin, inferInstance, inferInstance, inferInstance, inferInstance,
    GradedPres.freeGraded N d, GradedPres.kerGraded g, r, GradedPres.freeBasis S N r, d,
    GradedPres.kerIncl g, g, GradedPres.freeBasis_mem d, inferInstance, ?_, ?_,
    LinearMap.exact_subtype_ker_map _⟩
  · exact Subtype.val_injective
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨_, GradedPres.genMap_basis 𝓜 d m hm j⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
