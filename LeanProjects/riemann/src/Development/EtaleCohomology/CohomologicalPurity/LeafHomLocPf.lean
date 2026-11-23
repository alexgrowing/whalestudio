import Development.EtaleCohomology.CohomologicalPurity.LeafAugLocalPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace HomLocPf

variable {R : Type} [CommRing R]

lemma exact_cyc (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) :
    ((ShortComplex.mk (K.iCycles n) (K.d n ((ComplexShape.down ℕ).next n)) (K.iCycles_d _ _)).map
      ((evaluation _ _).obj T)).Exact :=
  (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel n _ rfl)).map _

lemma exact_bdy (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) :
    ((ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
      (K.toCycles_comp_homologyπ _ _)).map ((evaluation _ _).obj T)).Exact :=
  (ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel _ n (ChainComplex.prev ℕ n))).map _

lemma iCyc_inj (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Function.Injective ((K.iCycles n).app T).hom := by
  rw [← ModuleCat.mono_iff_injective]
  exact (inferInstance : Mono (((evaluation _ _).obj T).map (K.iCycles n)))

lemma π_surj (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Function.Surjective ((K.homologyπ n).app T).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  exact (inferInstance : Epi (((evaluation _ _).obj T).map (K.homologyπ n)))

lemma lift_cyc (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) (hx : Cyc K n T x) :
    ∃ y, ((K.iCycles n).app T).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (exact_cyc K n T) x (hx _)

lemma cyc_i (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) : Cyc K n T (((K.iCycles n).app T).hom y) := by
  intro m
  change ((K.iCycles n ≫ K.d n m).app T).hom y = 0
  rw [K.iCycles_d]; rfl

lemma π_zero_iff (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((K.homologyπ n).app T).hom y = 0 ↔ Bdy K n T (((K.iCycles n).app T).hom y) := by
  have ti : ∀ z, ((K.iCycles n).app T).hom (((K.toCycles (n + 1) n).app T).hom z) = ((K.d (n + 1) n).app T).hom z := by
    intro z
    change ((K.toCycles (n + 1) n ≫ K.iCycles n).app T).hom z = _
    rw [K.toCycles_i]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (exact_bdy K n T) y h
    exact ⟨z, (ti z).symm.trans (congrArg _ hz)⟩
  · rintro ⟨z, hz⟩
    rw [← ti] at hz
    rw [← iCyc_inj K n T hz]
    change ((K.toCycles (n + 1) n ≫ K.homologyπ n).app T).hom z = 0
    rw [K.toCycles_comp_homologyπ]; rfl

lemma nat_i (K : PCx R) (n : ℕ) {T U : Scheme.{0}ᵒᵖ} (g : T ⟶ U) (y) :
    ((K.X n).map g).hom (((K.iCycles n).app T).hom y) = ((K.iCycles n).app U).hom (((K.cycles n).map g).hom y) := by
  change (((K.iCycles n).app T ≫ (K.X n).map g)).hom y = (((K.cycles n).map g ≫ (K.iCycles n).app U)).hom y
  rw [(K.iCycles n).naturality]

lemma nat_π (K : PCx R) (n : ℕ) {T U : Scheme.{0}ᵒᵖ} (g : T ⟶ U) (y) :
    ((K.homology n).map g).hom (((K.homologyπ n).app T).hom y) = ((K.homologyπ n).app U).hom (((K.cycles n).map g).hom y) := by
  change (((K.homologyπ n).app T ≫ (K.homology n).map g)).hom y = (((K.cycles n).map g ≫ (K.homologyπ n).app U)).hom y
  rw [(K.homologyπ n).naturality]

lemma cm_i {K L : PCx R} (φ : K ⟶ L) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((L.iCycles n).app T).hom (((HomologicalComplex.cyclesMap φ n).app T).hom y) =
      ((φ.f n).app T).hom (((K.iCycles n).app T).hom y) := by
  change ((HomologicalComplex.cyclesMap φ n ≫ L.iCycles n).app T).hom y = ((K.iCycles n ≫ φ.f n).app T).hom y
  rw [HomologicalComplex.cyclesMap_i]

lemma hm_π {K L : PCx R} (φ : K ⟶ L) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((HomologicalComplex.homologyMap φ n).app T).hom (((K.homologyπ n).app T).hom y) =
      ((L.homologyπ n).app T).hom (((HomologicalComplex.cyclesMap φ n).app T).hom y) := by
  change ((K.homologyπ n ≫ HomologicalComplex.homologyMap φ n).app T).hom y =
    ((HomologicalComplex.cyclesMap φ n ≫ L.homologyπ n).app T).hom y
  rw [HomologicalComplex.homologyπ_naturality]

end HomLocPf

open HomLocPf in
theorem LeafHomLoc_of : LeafHomLoc := by
  intro R _ K L φ n hinj hsurj
  refine ⟨⟨fun {X} a b h => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · change ((HomologicalComplex.homologyMap φ n).app X).hom a = ((HomologicalComplex.homologyMap φ n).app X).hom b at h
    obtain ⟨y, hy⟩ := π_surj K n X (a - b)
    have hb : Bdy L n X (((φ.f n).app X).hom (((K.iCycles n).app X).hom y)) := by
      rw [← cm_i, ← π_zero_iff, ← hm_π, hy, map_sub, h, sub_self]
    obtain ⟨S, hS, hSx⟩ := hinj X _ (cyc_i K n X y) hb
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V f hf
    rw [Presheaf.equalizerSieve_apply]
    change ((K.homology n).map f.op).hom a = ((K.homology n).map f.op).hom b
    rw [← sub_eq_zero, ← map_sub, ← hy, nat_π, π_zero_iff, ← nat_i]
    exact hSx f hf
  · obtain ⟨y, rfl⟩ := π_surj L n _ s
    obtain ⟨S, hS, hSx⟩ := hsurj (op U) _ (cyc_i L n _ y)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V f hf
    obtain ⟨x', hx', hb⟩ := hSx f hf
    obtain ⟨y', rfl⟩ := lift_cyc K n _ x' hx'
    refine ⟨((K.homologyπ n).app (op V)).hom y', ?_⟩
    change ((HomologicalComplex.homologyMap φ n).app (op V)).hom (((K.homologyπ n).app (op V)).hom y') =
      ((L.homology n).map f.op).hom (((L.homologyπ n).app (op U)).hom y)
    rw [hm_π, nat_π, ← sub_eq_zero, ← map_sub, π_zero_iff, map_sub, cm_i, ← nat_i]
    exact hb

end LateralTheory.CohomologicalPurity.TubeCut
