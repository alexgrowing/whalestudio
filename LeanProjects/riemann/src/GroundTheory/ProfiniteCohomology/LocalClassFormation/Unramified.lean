import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.IntegerUnitsToUnitsHomApply
import GroundTheory.LocalFields.UnramifiedNorms
import GroundTheory.LocalFields.UnramifiedGalois
import GroundTheory.TateCohomology.Herbrand
import GroundTheory.TateCohomology.TateLow
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits GroundTheory.LocalField ValuativeRel

section Cyclic

variable {G M : Type} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

theorem isZero_tateCohomology_zero_of_subsingleton (h : Subsingleton (TateZero G M)) :
    IsZero (tateCohomology (Rep.ofMulDistribMulAction G M) 0) := by
  rw [GroundTheory.GroupCoh.isZero_tateCohomology_zero_iff_forall]
  intro x hx
  obtain ⟨y, hy⟩ := (subsingleton_tateZero_iff.1 h) x.toMul fun g =>
    congrArg Additive.toMul (hx g)
  exact ⟨Additive.ofMul y, Additive.toMul.injective
    ((Representation.norm_ofMulDistribMulAction_eq (G := G) (M := M) (Additive.ofMul y)).trans hy)⟩

theorem isZero_tateCohomology_neg_one_of_subsingleton (h : Subsingleton (TateNegOne G M)) :
    IsZero (tateCohomology (Rep.ofMulDistribMulAction G M) (-1)) := by
  rw [GroundTheory.GroupCoh.isZero_tateCohomology_neg_one_iff]
  refine le_antisymm (fun x hx => ?_) (GroundTheory.GroupCoh.coinvariantsKer_le_ker_norm _)
  have hx' : tateNorm G M (Additive.toMul (x : Additive M)) = 1 :=
    (Representation.norm_ofMulDistribMulAction_eq (G := G) (M := M) x).symm.trans
      (congrArg Additive.toMul hx)
  have hmem := (subsingleton_tateNegOne_iff.1 h) _ hx'
  suffices H : ∀ y ∈ augmentation G M,
      Additive.ofMul y ∈ Representation.Coinvariants.ker (Rep.ofMulDistribMulAction G M).ρ from
    H _ hmem
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨g, z, rfl⟩ := hy
    exact Representation.Coinvariants.sub_mem_ker g (Additive.ofMul z)
  | one => exact Submodule.zero_mem _
  | mul a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | inv a _ ha => exact Submodule.neg_mem _ ha

theorem isZero_groupCohomology_of_subsingleton_tate [IsCyclic G]
    (h0 : Subsingleton (TateZero G M)) (h1 : Subsingleton (TateNegOne G M)) {q : ℕ} (hq : 1 ≤ q) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction G M) q) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := G)
  set A := Rep.ofMulDistribMulAction G M
  have key : ∀ n : ℕ, IsZero (tateCohomology A (n : ℤ)) ∧ IsZero (tateCohomology A ((n : ℤ) - 1)) := by
    intro n
    induction n with
    | zero =>
      exact ⟨isZero_tateCohomology_zero_of_subsingleton h0,
        isZero_tateCohomology_neg_one_of_subsingleton h1⟩
    | succ n ih =>
      refine ⟨?_, by simpa using ih.1⟩
      have e : ((n + 1 : ℕ) : ℤ) = ((n : ℤ) - 1) + 2 := by push_cast; ring
      rw [e]
      exact ih.2.of_iso (GroundTheory.GroupCoh.tateCohomologyPeriodicIso A hσ _)
  have : NeZero q := ⟨by omega⟩
  exact (key q).1.of_iso ((TateCohomology.isoGroupCohomology q).app A).symm

end Cyclic

section Local

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isZero_groupCohomology_integerUnits [IsUnramified K L] {q : ℕ} (hq : 1 ≤ q) :
    IsZero (groupCohomology (galIntegerUnitsZ K L) q) := by
  have he := (isUnramified_iff K L).1 inferInstance
  have := isGalois_of_unramified K L he
  have := isCyclic_of_unramified K L he
  exact isZero_groupCohomology_of_subsingleton_tate subsingleton_tateZero_integerUnits
    subsingleton_tateNegOne_integerUnits hq

end Local

section Characters

variable {G : Type} [Group G]

noncomputable def evalCharQZ (σ : G) : (Additive G →+ AddCircle (1 : ℚ)) →+ QZ where
  toFun χ := QZ.toAddCircle.symm (χ (Additive.ofMul σ))
  map_zero' := by simp
  map_add' χ ψ := by simp

theorem evalCharQZ_apply (σ : G) (χ : Additive G →+ AddCircle (1 : ℚ)) :
    evalCharQZ σ χ = QZ.toAddCircle.symm (χ (Additive.ofMul σ)) :=
  rfl

theorem evalCharQZ_injective {σ : G} (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    Function.Injective (evalCharQZ σ) := by
  refine (injective_iff_map_eq_zero _).2 fun χ hχ => ?_
  have h0 : χ (Additive.ofMul σ) = 0 :=
    QZ.toAddCircle.symm.injective (hχ.trans (map_zero _).symm)
  refine AddMonoidHom.ext fun g => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ g.toMul)
  have hg : g = k • Additive.ofMul σ := by rw [← ofMul_zpow, hk, ofMul_toMul]
  rw [hg, map_zsmul, h0, smul_zero, AddMonoidHom.zero_apply]

end Characters

section Naturality

variable {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (ρ : G' →* G)

noncomputable def intMulRes (m : ℤ) : Rep.res ρ (Rep.trivial ℤ G ℤ) ⟶ Rep.trivial ℤ G' ℤ :=
  Rep.ofHom ⟨m • LinearMap.id, fun _ => by
    ext
    rfl⟩

omit [Fintype G] [Fintype G'] in
@[simp]
theorem intMulRes_hom_apply (m : ℤ) (x : ℤ) : (intMulRes ρ m).hom x = m * x :=
  rfl

theorem h2IntAddEquiv_map_intMulRes (m : ℤ) (z : groupCohomology (Rep.trivial ℤ G ℤ) 2) :
    GroundTheory.GroupCoh.h2IntAddEquiv G' ((groupCohomology.map ρ (intMulRes ρ m) 2).hom z) =
      m • (GroundTheory.GroupCoh.h2IntAddEquiv G z).comp (MonoidHom.toAdditive ρ) := by
  obtain ⟨χ, rfl⟩ := (GroundTheory.GroupCoh.h2IntAddEquiv G).symm.surjective z
  rw [AddEquiv.apply_symm_apply]
  choose y hy using fun g : G => QuotientAddGroup.mk_surjective (χ (Additive.ofMul g))
  have hx : ∀ g h : G, ∃ n : ℤ, (n : ℚ) = y g + y h - y (g * h) := by
    intro g h
    have h0 : ((y g + y h - y (g * h) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      have e1 := hy g
      have e2 := hy h
      have e3 := hy (g * h)
      change (QuotientAddGroup.mk (y g + y h - y (g * h)) : AddCircle (1 : ℚ)) = 0
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, e1, e2, e3, ofMul_mul, map_add, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℚ))).1 h0
    exact ⟨n, by simpa using hn⟩
  choose x hxeq using hx
  obtain ⟨hc, hz⟩ := GroundTheory.GroupCoh.h2IntAddEquiv_symm_apply_eq_H2_class G χ y hy
    (fun p => x p.1 p.2) fun g h => hxeq g h
  obtain ⟨hc', hz'⟩ := GroundTheory.GroupCoh.h2IntAddEquiv_symm_apply_eq_H2_class G'
    (m • χ.comp (MonoidHom.toAdditive ρ)) (fun g => m * y (ρ g)) (fun g => by
      change (QuotientAddGroup.mk (m * y (ρ g)) : AddCircle (1 : ℚ)) =
        m • χ (Additive.ofMul (ρ g))
      rw [← hy, ← zsmul_eq_mul, QuotientAddGroup.mk_zsmul])
    (fun p => m * x (ρ p.1) (ρ p.2)) fun g h => by
      push_cast
      rw [hxeq, map_mul]
      ring
  apply (GroundTheory.GroupCoh.h2IntAddEquiv G').symm.injective
  rw [AddEquiv.symm_apply_apply, hz', hz, groupCohomology.H2π_comp_map_apply]
  congr 1

end Naturality

section Invariant

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

noncomputable def h2Valuation :
    groupCohomology (galUnitsZ K L) 2 ⟶ groupCohomology (Rep.trivial ℤ Gal(L/K) ℤ) 2 :=
  (groupCohomology.functor ℤ Gal(L/K) 2).map (unitsValuation K L)

instance isIso_h2Valuation [IsUnramified K L] : IsIso (h2Valuation K L) := by
  have hX := unitsValuationSES_shortExact K L
  have h2 := isZero_groupCohomology_integerUnits K L (q := 2) (by norm_num)
  have h3 := isZero_groupCohomology_integerUnits K L (q := 3) (by norm_num)
  have hm : Mono ((groupCohomology.mapShortComplex₂ (unitsValuationSES K L) 2).g) :=
    (groupCohomology.mapShortComplex₂_exact hX 2).mono_g (h2.eq_of_src _ _)
  have hep : Epi ((groupCohomology.mapShortComplex₃ hX (i := 2) (j := 3) rfl).f) :=
    (groupCohomology.mapShortComplex₃_exact hX (i := 2) (j := 3) rfl).epi_f (h3.eq_of_tgt _ _)
  exact (isIso_iff_mono_and_epi _).2 ⟨hm, hep⟩

noncomputable def h2UnitsIsoInt [IsUnramified K L] :
    groupCohomology (galUnitsZ K L) 2 ≅ groupCohomology (Rep.trivial ℤ Gal(L/K) ℤ) 2 :=
  asIso (h2Valuation K L)

theorem h2UnitsIsoInt_hom [IsUnramified K L] : (h2UnitsIsoInt K L).hom = h2Valuation K L :=
  rfl

theorem h2Valuation_injective [IsUnramified K L] : Function.Injective (h2Valuation K L).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

theorem h2Valuation_surjective [IsUnramified K L] : Function.Surjective (h2Valuation K L).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

variable [IsUnramified K L]

noncomputable abbrev frob : Gal(L/K) :=
  frobenius K L (IsUnramified.ramificationIndex_eq_one (K := K) (L := L))

noncomputable def unramifiedInv : groupCohomology (galUnitsZ K L) 2 →+ QZ :=
  (evalCharQZ (frob K L)).comp ((GroundTheory.GroupCoh.h2IntAddEquiv Gal(L/K)).toAddMonoidHom.comp
    (h2Valuation K L).hom.toAddMonoidHom)

theorem unramifiedInv_apply (x : groupCohomology (galUnitsZ K L) 2) :
    unramifiedInv K L x = QZ.toAddCircle.symm (GroundTheory.GroupCoh.h2IntAddEquiv Gal(L/K)
      ((h2Valuation K L).hom x)
      (Additive.ofMul (frob K L))) :=
  rfl

theorem forall_mem_zpowers_frob : ∀ g : Gal(L/K), g ∈ Subgroup.zpowers (frob K L) := fun g => by
  rw [zpowers_frobenius]
  exact Subgroup.mem_top g

theorem unramifiedInv_injective : Function.Injective (unramifiedInv K L) :=
  (evalCharQZ_injective (forall_mem_zpowers_frob K L)).comp
  ((GroundTheory.GroupCoh.h2IntAddEquiv _).injective.comp (h2Valuation_injective K L))

theorem mem_range_unramifiedInv_iff (x : QZ) :
    x ∈ (unramifiedInv K L).range ↔ Module.finrank K L • x = 0 := by
  have he := IsUnramified.ramificationIndex_eq_one (K := K) (L := L)
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  constructor
  · rintro ⟨y, rfl⟩
    rw [unramifiedInv_apply, ← map_nsmul, ← map_nsmul, ← ofMul_pow, ← orderOf_frobenius K L he,
      pow_orderOf_eq_one, ofMul_one, map_zero, map_zero]
  · intro hx
    obtain ⟨m, rfl⟩ := QZ.exists_eq_nsmul_mk_one_div hn hx
    obtain ⟨y, hy⟩ := h2Valuation_surjective K L ((GroundTheory.GroupCoh.h2IntAddEquiv Gal(L/K)).symm
      (m • GroundTheory.GroupCoh.cyclicChar (frob K L) (forall_mem_zpowers_frob K L)))
    refine ⟨y, ?_⟩
    rw [unramifiedInv_apply, hy, AddEquiv.apply_symm_apply, AddMonoidHom.smul_apply, map_nsmul,
      GroundTheory.GroupCoh.cyclicChar_apply_gen, card_algEquiv_of_unramified K L he]
    rfl

theorem range_unramifiedInv :
    (unramifiedInv K L).range = AddSubgroup.zmultiples (QZ.mk (1 / Module.finrank K L)) := by
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  ext x
  rw [mem_range_unramifiedInv_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := QZ.exists_eq_nsmul_mk_one_div hn hx
    exact ⟨m, natCast_zsmul _ _⟩
  · rintro ⟨k, rfl⟩
    rw [smul_comm, QZ.nsmul_mk_one_div, smul_zero]

end Invariant

end GroundTheory.ProfCoh
