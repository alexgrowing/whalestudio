import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice

universe u

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

open Module

namespace Lat2

section SlopeTestRemainingChoices

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem map_frac_smul {V W : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup W] [Module O W] [Module (FractionRing O) W]
    [IsScalarTower O (FractionRing O) W] (f : V →ₗ[O] W) (c : FractionRing O) (x : V) :
    f (c • x) = c • f x :=
  (f.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)).map_smul c x

section One

variable {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V']
  [IsScalarTower O (FractionRing O) V']

theorem exists_basis_of_lattice {T : Submodule O V} (hT : IsLatticeIn T) :
    ∃ (n : ℕ) (e : Basis (Fin n) (FractionRing O) V),
      T = Submodule.span O (Set.range e) ∧ finrank O T = n := by
  have : Submodule.IsLattice (FractionRing O) T := ⟨hT.1, hT.2⟩
  let B := Module.finBasis O T
  refine ⟨_, B.extendOfIsLattice (FractionRing O), ?_, rfl⟩
  have h : Set.range (B.extendOfIsLattice (FractionRing O)) = T.subtype '' Set.range B := by
    rw [← Set.range_comp]
    congr 1
    ext i
    simp
  rw [h, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem isLatticeIn_span_basis {n : ℕ} (e : Basis (Fin n) (FractionRing O) V) :
    IsLatticeIn (Submodule.span O (Set.range e)) := by
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  rw [Submodule.span_span_of_tower, e.span_eq]

theorem finrank_span_basis {n : ℕ} (e : Basis (Fin n) (FractionRing O) V) :
    finrank O (Submodule.span O (Set.range e)) = n := by
  have h : LinearIndependent O e :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).2 e.linearIndependent
  rw [finrank_span_eq_card h, Fintype.card_fin]

theorem exists_dual_basis {b : V →ₗ[O] V' →ₗ[O] FractionRing O} (hb : PerfectRight b) {n : ℕ}
    (e : Basis (Fin n) (FractionRing O) V) :
    ∃ f : Basis (Fin n) (FractionRing O) V',
      (∀ i x, e.repr x i = b x (f i)) ∧ (∀ i w, f.repr w i = b (e i) w) := by
  choose f hf using fun i => (hb (e.coord i)).exists
  have hexp : ∀ w : V', w = ∑ i, b (e i) w • f i := by
    intro w
    refine (hb ((b.flip w).extendScalarsOfIsLocalization (nonZeroDivisors O)
      (FractionRing O))).unique (fun x => rfl) (fun x => ?_)
    rw [LinearMap.extendScalarsOfIsLocalization_apply', LinearMap.flip_apply, map_sum]
    conv_rhs => rw [← e.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_frac_smul, hf, map_frac_smul b, LinearMap.smul_apply, Basis.coord_apply, smul_eq_mul,
      smul_eq_mul, mul_comm]
  have hli : LinearIndependent (FractionRing O) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := congrArg (b (e j)) hc
    rw [map_sum, map_zero] at h
    rw [← h, Finset.sum_eq_single j]
    · rw [map_frac_smul, hf, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    · intro i _ hij
      rw [map_frac_smul, hf, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hij,
        smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range f) := by
    intro w _
    rw [hexp w]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨Basis.mk hli hsp, fun i x => ?_, fun i w => ?_⟩
  · rw [Basis.mk_apply, hf, Basis.coord_apply]
  · conv_lhs => rw [hexp w]
    have : ∑ i, b (e i) w • f i = ∑ i, b (e i) w • (Basis.mk hli hsp) i := by
      simp only [Basis.mk_apply]
    rw [this, Basis.repr_sum_self]

omit [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] in

theorem dualLat_span {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {n : ℕ} (e : Fin n → V)
    (f : Basis (Fin n) (FractionRing O) V') (h : ∀ i w, f.repr w i = b (e i) w) :
    dualLat b (Submodule.span O (Set.range e)) = Submodule.span O (Set.range f) := by
  ext w
  rw [Basis.mem_span_iff_repr_mem]
  constructor
  · intro hw i
    rw [h]
    exact Submodule.mem_one.1 (hw (e i) (Submodule.subset_span (Set.mem_range_self i)))
  · intro hw
    have hle : Submodule.span O (Set.range e) ≤
        (1 : Submodule O (FractionRing O)).comap (b.flip w) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have := hw i
      rw [h] at this
      exact Submodule.mem_one.2 this
    exact fun x hx => hle hx

theorem dualLat_props {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V}
    (hT : IsLatticeIn T) (hb : PerfectRight b) :
    IsLatticeIn (dualLat b T) ∧ finrank O (dualLat b T) = finrank O T ∧
      dualLat b.flip (dualLat b T) = T := by
  obtain ⟨n, e, hTe, hn⟩ := exists_basis_of_lattice hT
  obtain ⟨f, h1, h2⟩ := exists_dual_basis hb e
  have hd : dualLat b T = Submodule.span O (Set.range f) := by
    rw [hTe]; exact dualLat_span e f h2
  refine ⟨?_, ?_, ?_⟩
  · rw [hd]; exact isLatticeIn_span_basis f
  · rw [hd, hn]; exact finrank_span_basis f
  · rw [hd, hTe]; exact dualLat_span (b := b.flip) f e h1

omit [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
  [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V'] in

theorem dualLat_stable {G : Type u} [Group G] {ε : G →* Oˣ} {ρ : Representation O G V}
    {ρ' : Representation O G V'} {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V}
    (hs : StableUnder ρ T) (he : EquivPair ε ρ ρ' b) : StableUnder ρ' (dualLat b T) := by
  intro g f hf x hx
  have hx' : x = ρ g (ρ g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hx', he]
  exact Submodule.smul_mem _ _ (hf _ (hs g⁻¹ x hx))

end One

end SlopeTestRemainingChoices

end Lat2

open Lat2

theorem dualLattice : StatDualLattice.{u} := by
  intro O G V V' _ _ _ _ _ _ _ _ _ _ _ _ ε ρ ρ' b T hT hs hb he
  obtain ⟨h1, h2, h3⟩ := dualLat_props hT hb
  exact ⟨h1, h2, dualLat_stable hs he, h3⟩

namespace Lat2

section Fib

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {VY VT VY' VT' : Type u}
  [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY] [IsScalarTower O (FractionRing O) VY]
  [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT'] [Module O VT']

omit [IsDomain O] [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in
theorem zero_mem_fibre {Y : Submodule O VY} {T : Submodule O VT} (φ : Y →ₗ[O] VT ⧸ T) {x : VT}
    (hx : x ∈ T) : ((0 : VY), x) ∈ fibre Y T φ := by
  refine ⟨Y.zero_mem, ?_⟩
  have : (⟨((0 : VY), x).1, Y.zero_mem⟩ : Y) = 0 := rfl
  rw [this, map_zero]
  exact ((Submodule.Quotient.mk_eq_zero T).2 hx).symm

def pairB (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O) (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) :
    (VY × VT) →ₗ[O] (VT' × VY') →ₗ[O] FractionRing O :=
  bY.compl₁₂ (LinearMap.fst O VY VT) (LinearMap.snd O VT' VY') -
    bT.compl₁₂ (LinearMap.snd O VY VT) (LinearMap.fst O VT' VY')

omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in
theorem pairB_apply (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (p : VY × VT) (q : VT' × VY') :
    pairB bY bT p q = bY p.1 q.2 - bT p.2 q.1 := rfl

omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in

theorem fibreDual_eq (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (Y : Submodule O VY) (T : Submodule O VT)
    (φ : Y →ₗ[O] VT ⧸ T) :
    fibreDual bY bT Y T φ = dualLat (pairB bY bT) (fibre Y T φ) := by
  ext ⟨f, g⟩
  constructor
  · rintro ⟨_, h2⟩ ⟨y, x⟩ ⟨hy, hφ⟩
    rw [pairB_apply]
    exact h2 ⟨y, hy⟩ x hφ
  · intro h
    refine ⟨fun x hx => ?_, fun y x hyx => ?_⟩
    · have := h (0, x) (zero_mem_fibre φ hx)
      rw [pairB_apply] at this
      simp only [map_zero, LinearMap.zero_apply, zero_sub] at this
      exact (Submodule.neg_mem_iff _).1 this
    · have := h (y, x) ⟨y.2, hyx⟩
      rw [pairB_apply] at this
      exact this

omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in

theorem zero_mem_fibreDual_iff (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (Y : Submodule O VY) (T : Submodule O VT)
    (φ : Y →ₗ[O] VT ⧸ T) (g : VY') :
    ((0 : VT'), g) ∈ fibreDual bY bT Y T φ ↔ g ∈ dualLat bY Y := by
  constructor
  · rintro ⟨_, h⟩ y hy
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective T (φ ⟨y, hy⟩)
    have := h ⟨y, hy⟩ x hx.symm
    simpa using this
  · intro h
    refine ⟨Submodule.zero_mem _, fun y x _ => ?_⟩
    have := h y y.2
    simpa using this

end Fib

end Lat2

end Formalism.RepresentationBoundsCohomology.LOC
