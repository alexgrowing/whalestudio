import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionMulCardToricTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusOpen

theorem exists_sections {S : Scheme.{0}} (X T : Over S) [Etale X.hom] (n : ℕ) (x : Fin n → (T ⟶ X)) :
    ∃ (Z : Over S) (_ : Etale Z.hom) (z : T ⟶ Z) (σ : Fin n → (Z ⟶ X)), ∀ i, z ≫ σ i = x i := by
  induction n with
  | zero => exact ⟨𝟙_ _, inferInstanceAs (Etale (𝟙 S)), toUnit _, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨Z, hZ, z, σ, h⟩ := ih fun i => x i.succ
    refine ⟨Z ⊗ X, inferInstanceAs (Etale (pullback.fst Z.hom X.hom ≫ Z.hom)), lift z (x 0),
      Fin.cons (snd Z X) fun i => fst Z X ≫ σ i, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp [h]

theorem comp_eq_iff {S : Scheme.{0}} {X Z : Over S} [Etale X.hom] [IsSeparated X.hom] (a b : Z ⟶ X)
    {K : Type} [Field K] {t : Sp K ⟶ S} (z : Over.mk t ⟶ Z) (p : Sp K) :
    z ≫ a = z ≫ b ↔ z.left p ∈ Set.range (equalizer.ι a b).left := by
  constructor
  · intro h
    refine ⟨(equalizer.lift z h).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · rintro ⟨e, he⟩
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := z.left) (g := (equalizer.ι a b).left) p e he.symm
    have : Nonempty ↥(pullback z.left (equalizer.ι a b).left) := ⟨w⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have : PreconnectedSpace (Over.mk t).left := inferInstanceAs (PreconnectedSpace (Sp K))
    refine Over.OverMorphism.ext (eq_of_preconnected_of_unramified X.hom
      ((Over.w (z ≫ a)).trans (Over.w (z ≫ b)).symm) (pullback.fst z.left (equalizer.ι a b).left) ?_)
    rw [Over.comp_left, Over.comp_left, pullback.condition_assoc, pullback.condition_assoc, ← Over.comp_left,
      ← Over.comp_left, equalizer.condition]

theorem exists_open_injective {S : Scheme.{0}} (X : Over S) [Etale X.hom] [IsSeparated X.hom]
    {K : Type} [Field K] (t : Sp K ⟶ S) (p : Sp K) (n : ℕ) (x : Fin n → (Over.mk t ⟶ X))
    (hx : Function.Injective x) :
    ∃ U : Set S, IsOpen U ∧ t p ∈ U ∧ ∀ s ∈ U, ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (t' : Sp K' ⟶ S),
      s ∈ Set.range t' ∧ ∃ x' : Fin n → (Over.mk t' ⟶ X), Function.Injective x' := by
  obtain ⟨Z, hZ, z, σ, h⟩ := exists_sections X (Over.mk t) n x
  let V : Set Z.left := ⋂ (i : Fin n) (j : Fin n) (_ : i ≠ j), (Set.range (equalizer.ι (σ i) (σ j)).left)ᶜ
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => by
      have := isClosedImmersion_equalizer_ι_left (σ i) (σ j)
      exact (equalizer.ι (σ i) (σ j)).left.isClosedEmbedding.isClosed_range.isOpen_compl
  refine ⟨Z.hom '' V, Z.hom.isOpenMap V hV, ⟨z.left p, ?_, ?_⟩, ?_⟩
  · refine Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => Set.mem_iInter.2 fun hij hm => hij (hx ?_)
    rw [← h, ← h]
    exact (comp_eq_iff _ _ z p).2 hm
  · rw [← Scheme.Hom.comp_apply, Over.w]; rfl
  · rintro _ ⟨v, hv, rfl⟩
    let K' := AlgebraicClosure (Z.left.residueField v)
    let u : Sp K' ⟶ Z.left := spMap (algebraMap (Z.left.residueField v) K') ≫ Z.left.fromSpecResidueField v
    have q : Sp K' := (default : PrimeSpectrum K')
    have hu : u q = v := Scheme.fromSpecResidueField_apply v _
    let u' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk u rfl
    refine ⟨K', inferInstance, inferInstance, u ≫ Z.hom, ⟨q, congrArg (fun y => Z.hom y) hu⟩,
      fun i => u' ≫ σ i, fun i j hij => by_contra fun hne => ?_⟩
    have hm := (comp_eq_iff _ _ u' q).1 hij
    exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hv i) j) hne (hu ▸ hm)

theorem isProper_of_subsingleton {K : Type} [Field K] (G : Over (Sp K)) [GrpObj G] (T : TorusExtension G)
    (hT : Subsingleton T.X) : IsProper G.hom := by
  letI := T.addCommGroup
  letI := T.grpB
  have := T.q_hom
  have := T.i_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have hp := T.isKernel
  have : Mono T.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ T.q = toUnit _ ≫ η[T.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := (GlobalTheory.splitTorusPointsEquiv (Sp K) T.X Y).injective (Subsingleton.elim _ _)
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono T.q.left := inferInstanceAs (Mono ((Over.forget _).map T.q))
  have : EffectiveEpi T.q.left := inferInstance
  have : IsIso T.q.left := isIso_of_mono_of_strongEpi _
  have := T.isAbelian.proper
  rw [← Over.w T.q]
  infer_instance

theorem isProper_of_injective {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G)
    (T : TorusExtension G) {g n : ℕ} (hg : SmoothOfRelativeDimension g G.hom) (h2 : 2 ≤ n) (hn : (n : k) ≠ 0)
    (x : Fin (n ^ (2 * g)) → {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1}) (hx : Function.Injective x) :
    IsProper G.hom := by
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := T.i_hom
  have hc := card_torsion_mul_card_toric_torsion k G T g n hG hg hn
  have h0 : n ^ (2 * g) ≠ 0 := pow_ne_zero _ (by omega)
  have f₁ := Nat.finite_of_card_ne_zero (left_ne_zero_of_mul (hc ▸ h0))
  have f₂ := Nat.finite_of_card_ne_zero (right_ne_zero_of_mul (hc ▸ h0))
  have hle := Nat.card_le_card_of_injective x hx
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  have hd : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1 ∧ ∃ y, x = y ≫ T.i} ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by rw [hc, Nat.mul_one]; exact hle) (Nat.pos_of_ne_zero (left_ne_zero_of_mul (hc ▸ h0)))
  obtain ⟨e⟩ := SemiAbTorsionCount.nonempty_torus_points_mulEquiv k T.X
  have hcard := (SemiAbTorsionCount.divisible_and_card e n hn).2
  let i := IsMonHom.monoidHom T.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => T.isKernel.hom_ext h (toUnit_unique _ _)
  have h3 := Nat.card_le_card_of_injective
    (fun t : {t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X // t ^ n = 1} =>
      (⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩ :
        {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1 ∧ ∃ y, x = y ≫ T.i}))
    fun a b h => Subtype.ext (hi (congrArg Subtype.val h))
  rw [hcard] at h3
  have h4 : Module.finrank ℤ T.X = 0 := by
    by_contra hne
    exact absurd (h3.trans hd) (not_le.2 (Nat.one_lt_pow hne h2))
  exact isProper_of_subsingleton G T (Module.finrank_zero_iff.1 h4)

theorem nonempty_torsion_equiv {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) {K : Type} [Field K] (t : Sp K ⟶ S) :
    Nonempty ((Over.mk t ⟶ torsion G n) ≃ {x : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G // x ^ n = 1}) := by
  obtain ⟨e, -⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G t) (𝟙 _) t (Category.id_comp t).symm
  refine ⟨(TorsionUnram.torsionEquiv G n _).trans (e.toEquiv.subtypeEquiv fun x => ?_).symm⟩
  show x ^ n = 1 ↔ e x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem isOpen_abLocus {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) {g n : ℕ}
    (hg : SmoothOfRelativeDimension g G.hom) (h2 : 2 ≤ n) (hn : IsUnit (n : Γ(S, ⊤))) : IsOpen (abLocus G) := by
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.geomConnected
  have := GrpTangent.etale_torsion G hn
  have hm : IsSeparated ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have hm' : IsSeparated (mulN G n).left := IsSeparated.of_comp _ G.hom
  have : IsSeparated (torsion G n).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (GrpTangent.isPullback_torsion G n) hm'
  have hK : ∀ (K : Type) [Field K] (t : Sp K ⟶ S), (n : K) ≠ 0 := fun K _ t => by
    have := ((hn.map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom).ne_zero
    simpa using this
  have hd : ∀ (K : Type) [Field K] (t : Sp K ⟶ S), SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    fun K _ t => (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  let K := AlgebraicClosure (S.residueField s)
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s
  have p : Sp K := (default : PrimeSpectrum K)
  have ht : t p = s := Scheme.fromSpecResidueField_apply s _
  have hB : IsAbelianScheme ((Over.pullback t).obj G) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), hs K t ⟨p, ht⟩,
      inferInstanceAs (GeometricallyConnected (pullback.snd _ _))⟩
  have hc := GlobalTheory.T.card_torsion_eq_pow_two_mul_dim K _ g n hB (hd K t) (hK K t)
  have := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (by omega : n ≠ 0))
  obtain ⟨e⟩ := nonempty_torsion_equiv G n t
  let x := ((Finite.equivFinOfCardEq hc).symm.trans e.symm)
  obtain ⟨U, hU, hp, h⟩ := exists_open_injective (torsion G n) t p _ x x.injective
  refine ⟨U, fun s' hs' => ?_, hU, ht ▸ hp⟩
  obtain ⟨K', _, _, t', hr, x', hx'⟩ := h s' hs'
  obtain ⟨e'⟩ := nonempty_torsion_equiv G n t'
  obtain ⟨T⟩ := hG.fibres K' t'
  exact abLocusOne S G hG K' t' (isProper_of_injective _ (IsSemiAbelian.pullback _ G hG) T (hd K' t') h2 (hK K' t')
    (e' ∘ x') (e'.injective.comp hx')) hr

theorem isOpen_abLocus_local {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    (hG : IsSemiAbelian G) : IsOpen (abLocus G) := by
  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty G.left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom x₀
  obtain ⟨n, h2, hn⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by exact_mod_cast h⟩
    · exact ⟨2, le_rfl, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  exact isOpen_abLocus G hG hg h2 (by simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

end GlobalTheory.AbLocusOpen
