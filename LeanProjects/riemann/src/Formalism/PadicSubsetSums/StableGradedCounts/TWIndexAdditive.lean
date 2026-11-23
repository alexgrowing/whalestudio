import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral

open Module

namespace Formalism.IrreducibleCountingLemmas.TW

namespace Idx

section General

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

theorem relLen_of_le {M N : Submodule O V} (h : M ≤ N) : relLen M N = 0 := by
  unfold relLen
  have : N.comap M.subtype = ⊤ := by
    rw [eq_top_iff]; intro x _; exact h x.2
  rw [this]
  exact Module.length_eq_zero

theorem relLen_inf (M N : Submodule O V) : relLen M (M ⊓ N) = relLen M N := by
  unfold relLen
  have : (M ⊓ N).comap M.subtype = N.comap M.subtype := by
    ext x; simp
  rw [this]

theorem relLen_tower {A B C : Submodule O V} (hAB : A ≤ B) (hBC : B ≤ C) :
    relLen C A = relLen B A + relLen C B := by
  unfold relLen
  have h1 : A.comap B.subtype ≤ (A.comap C.subtype).comap (Submodule.inclusion hBC) := by
    intro x hx; exact hx
  have h2 : A.comap C.subtype ≤ B.comap C.subtype := Submodule.comap_mono hAB
  refine Module.length_eq_add_of_exact (Submodule.mapQ _ _ (Submodule.inclusion hBC) h1)
    (Submodule.factor h2) ?_ (Submodule.factor_surjective h2) ?_
  · rw [injective_iff_map_eq_zero]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    intro hx
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hfac : Submodule.factor h2 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := rfl
    rw [hfac, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      exact ⟨Submodule.Quotient.mk ⟨y.1, hy⟩, by rw [Submodule.mapQ_apply]; rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      have h3 : (x : V) - y ∈ A := hx
      have h4 : (y : V) = x - (x - y) := by abel
      show (y : V) ∈ B
      rw [h4]
      exact B.sub_mem x.2 (hAB h3)

end General

section LenDet

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]

theorem ord_prod {ι : Type} (s : Finset ι) (a : ι → O) (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]

theorem length_quot_range {B ι : Type} [AddCommGroup B] [Module O B] [Fintype ι]
    (b : Basis ι O B) (f : B →ₗ[O] B) (hf : Function.Injective f) :
    Module.length O (B ⧸ LinearMap.range f) = Ring.ord O (LinearMap.det f) := by
  classical
  have h : finrank O (LinearMap.range f) = finrank O B :=
    (LinearEquiv.ofInjective f hf).finrank_eq.symm
  rw [(Submodule.quotientEquivPiSpan _ b h).length_eq, Module.length_pi_of_fintype]
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  have hne := Submodule.smithNormalFormCoeffs_ne_zero b h
  generalize Submodule.smithNormalFormCoeffs b h = a at *
  generalize Submodule.smithNormalFormTopBasis b h = b' at *
  generalize Submodule.smithNormalFormBotBasis b h = ab at *
  let e' : B ≃ₗ[O] LinearMap.range f := b'.equiv ab (Equiv.refl _)
  have hass : Associated (LinearMap.det f)
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f))) := by
    have := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
      (LinearEquiv.ofInjective f hf) e'
    convert this using 2
    ext x; rfl
  have hg : LinearMap.det ((LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f))
      = ∏ i, a i := by
    have : (LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f)
        = Matrix.toLin b' b' (Matrix.diagonal a) := by
      apply b'.ext; intro i
      simp [e', ab_eq, Matrix.toLin_self, Matrix.diagonal_apply]
    rw [this, LinearMap.det_toLin, Matrix.det_diagonal]
  rw [Ring.ord_eq_of_associated hass, hg, ord_prod _ _ hne]
  rfl

end LenDet

section Lat

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem isLattice_of_isLat {M : Submodule O V} (h : IsLat O K M) : Submodule.IsLattice K M :=
  ⟨h.1, h.2⟩

theorem isLat_of_isLattice (M : Submodule O V) [Submodule.IsLattice K M] : IsLat O K M :=
  ⟨Submodule.IsLattice.fg, Submodule.IsLattice.span_eq_top⟩

theorem ord_unit_mul_pow {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (n : ℕ) :
    Ring.ord O ((u : O) * ϖ ^ n) = n := by
  rw [Ring.ord_mul_of_isUnit_left u.isUnit,
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]
  simp

theorem exists_basis {M : Submodule O V} (h : IsLat O K M) :
    ∃ (n : ℕ) (β : Basis (Fin n) K V), Submodule.span O (Set.range β) = M := by
  have := isLattice_of_isLat h
  have : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O K V
  obtain ⟨n, c⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := M)
  refine ⟨n, c.extendOfIsLattice K, ?_⟩
  have : Set.range (c.extendOfIsLattice K) = M.subtype '' Set.range c := by
    rw [← Set.range_comp]; congr 1; ext i; simp
  rw [this, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem isLat_span_basis {d : ℕ} (b : Basis (Fin d) K V) :
    IsLat O K (Submodule.span O (Set.range b)) := by
  refine ⟨Submodule.fg_span (Set.finite_range b), ?_⟩
  rw [Submodule.span_span_of_tower, b.span_eq]

theorem relLen_span_of_le {d : ℕ} (b : Basis (Fin d) K V) (w : Fin d → V)
    (hw : Submodule.span O (Set.range w) ≤ Submodule.span O (Set.range b))
    (hdet : b.det w ≠ 0) :
    ∃ D : O, algebraMap O K D = b.det w ∧
      relLen (Submodule.span O (Set.range b)) (Submodule.span O (Set.range w)) = Ring.ord O D := by
  let bO := b.restrictScalars O
  let w' : Fin d → Submodule.span O (Set.range b) :=
    fun i => ⟨w i, hw (Submodule.subset_span ⟨i, rfl⟩)⟩
  let f : Submodule.span O (Set.range b) →ₗ[O] Submodule.span O (Set.range b) := bO.constr O w'
  have hD : algebraMap O K (LinearMap.det f) = b.det w := by
    rw [← LinearMap.det_toMatrix bO, RingHom.map_det, Basis.det_apply]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, f, w', bO]
  have hne : LinearMap.det f ≠ 0 := by
    intro h; rw [h, map_zero] at hD; exact hdet hD.symm
  have hinj : Function.Injective f := by
    intro x y hxy
    have hM : (LinearMap.toMatrix bO bO f).det ≠ 0 := by rwa [LinearMap.det_toMatrix]
    have := Matrix.mulVec_injective_of_det_ne_zero hM (a₁ := bO.repr x) (a₂ := bO.repr y)
      (by rw [LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_mulVec_repr, hxy])
    exact bO.repr.injective (DFunLike.coe_injective this)
  have hrange : (Submodule.span O (Set.range w)).comap (Submodule.span O (Set.range b)).subtype
      = LinearMap.range f := by
    rw [Basis.constr_range]
    apply Submodule.map_injective_of_injective (Submodule.span O (Set.range b)).injective_subtype
    rw [Submodule.map_comap_subtype, Submodule.map_span, ← Set.range_comp, inf_eq_right.2 hw]
    rfl
  refine ⟨_, hD, ?_⟩
  unfold relLen
  rw [hrange]
  exact length_quot_range bO f hinj

theorem ord_ne_top' {D : O} (hD : D ≠ 0) : Ring.ord O D ≠ ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD hϖ
  rw [ord_unit_mul_pow hϖ]
  exact ENat.natCast_ne_top n

theorem relLen_ne_top_of_le {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N)
    (hle : N ≤ M) : relLen M N ≠ ⊤ := by
  obtain ⟨n, β, rfl⟩ := exists_basis hM
  obtain ⟨n', γ, rfl⟩ := exists_basis hN
  have hn : n' = n := by
    have h1 := Module.finrank_eq_card_basis β
    have h2 := Module.finrank_eq_card_basis γ
    simpa using h2.symm.trans h1
  subst hn
  obtain ⟨D, hD, hlen⟩ := relLen_span_of_le (O := O) β γ hle (β.isUnit_det γ).ne_zero
  rw [hlen]
  apply ord_ne_top'
  rintro rfl
  rw [map_zero] at hD
  exact (β.isUnit_det γ).ne_zero hD.symm

variable [FiniteDimensional K V]

theorem isLat_inf {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N) :
    IsLat O K (M ⊓ N) := by
  have := isLattice_of_isLat hM
  have := isLattice_of_isLat hN
  exact isLat_of_isLattice _

theorem relLen_ne_top {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N) :
    relLen M N ≠ ⊤ := by
  rw [← relLen_inf]
  exact relLen_ne_top_of_le hM (isLat_inf hM hN) inf_le_left

theorem sIdx_eq_sub {M N Q : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N)
    (hQ : IsLat O K Q) (hQM : Q ≤ M) (hQN : Q ≤ N) :
    sIdx M N = ((relLen M Q).toNat : ℤ) - ((relLen N Q).toNat : ℤ) := by
  have h1 := relLen_tower (le_inf hQM hQN) (inf_le_left : M ⊓ N ≤ M)
  have h2 := relLen_tower (le_inf hQM hQN) (inf_le_right : M ⊓ N ≤ N)
  rw [relLen_inf] at h1
  rw [inf_comm, relLen_inf] at h2
  have f0 := relLen_ne_top (isLat_inf hN hM) hQ
  have f1 := relLen_ne_top hM hN
  have f2 := relLen_ne_top hN hM
  rw [inf_comm] at h1
  unfold sIdx
  rw [h1, h2, ENat.toNat_add f0 f1, ENat.toNat_add f0 f2]
  push_cast
  ring

end Lat

end Idx

theorem index_additive : IndexAdditive := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M N P hM hN hP
  refine ⟨Idx.relLen_ne_top hM hN, ?_⟩
  have hQ := Idx.isLat_inf (Idx.isLat_inf hM hN) hP
  have q1 : M ⊓ N ⊓ P ≤ M := inf_le_left.trans inf_le_left
  have q2 : M ⊓ N ⊓ P ≤ N := inf_le_left.trans inf_le_right
  have q3 : M ⊓ N ⊓ P ≤ P := inf_le_right
  rw [Idx.sIdx_eq_sub hM hN hQ q1 q2, Idx.sIdx_eq_sub hN hP hQ q2 q3, Idx.sIdx_eq_sub hM hP hQ q1 q3]
  ring

end Formalism.IrreducibleCountingLemmas.TW
