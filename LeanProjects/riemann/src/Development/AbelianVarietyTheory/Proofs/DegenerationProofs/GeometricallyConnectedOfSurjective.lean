import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.DivisiblePart

open RationalPoint

theorem surjective_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {X Y : Over (Sp k)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (f : X ⟶ Y)
    (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ Y, ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = y) :
    Surjective f.left := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hC := (isConstructible_image_of_isClosed f isClosed_univ).compl
  obtain ⟨V, hV, h1, h2⟩ := exists_isOpen_inter_closure_subset_of_isConstructible
    continuous_id hC
  rw [Set.preimage_id] at h1 h2
  have hne : (V ∩ closure (f.left '' Set.univ)ᶜ).Nonempty := by
    rw [← closure_nonempty_iff, h2, closure_nonempty_iff]
    exact ⟨y, fun ⟨x, _, hx⟩ => hy ⟨x, hx⟩⟩
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne
    (hV.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  obtain ⟨z, hz⟩ := exists_pt_mem (X := Y) (Z := {c}) hc ⟨c, rfl⟩
  obtain ⟨x, rfl⟩ := h z
  exact h1 hcZ ⟨pt x, trivial, hz⟩

theorem geometricallyConnected_of_surjective {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [GeometricallyConnected (f ≫ g)] : GeometricallyConnected g := by
  refine ⟨fun K _ y W fst snd hW => ?_⟩
  have h1 := (IsPullback.of_hasPullback f fst).paste_vert hW
  have : ConnectedSpace ↥(pullback f fst) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h1
  exact (pullback.snd f fst).surjective.connectedSpace (pullback.snd f fst).continuous

theorem isIso_of_dim_le {k : Type} [Field k] {N G : Scheme.{0}} (ν : N ⟶ G) (s : G ⟶ Sp k)
    [IsClosedImmersion ν] [IsIntegral G] [IsReduced N] [Nonempty N] {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g s) (hg' : SmoothOfRelativeDimension g' (ν ≫ s))
    (hle : g ≤ g') : IsIso ν := by
  suffices Surjective ν from isIso_of_isClosedImmersion_of_surjective ν
  refine ⟨fun y => ?_⟩
  by_contra hy
  obtain ⟨n⟩ := ‹Nonempty N›
  obtain ⟨_, ⟨U, hU, rfl⟩, hnU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ν n)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let W : G.Opens := ⟨(Set.range ν)ᶜ, ν.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨z, hzU, hzW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨_, hnU⟩ ⟨y, hy⟩
  obtain ⟨r, hrW, hzr⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hzU
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hzr
  have hr1 : (ν.app U).hom r = 0 := by
    rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
    intro t ht
    exact (hrW ht ⟨t, rfl⟩).elim
  have : Nonempty U := ⟨⟨_, hnU⟩⟩
  have h1 := ringKrullDim_succ_le_of_surjective (ν.app U).hom (ν.app_surjective U hU)
    (mem_nonZeroDivisors_of_ne_zero hr0) hr1
  rw [SmoothDim.ringKrullDim_affineOpen k G s g hg U hU ⟨_, hnU⟩,
    SmoothDim.ringKrullDim_affineOpen k N _ g' hg' _ (hU.preimage ν) ⟨n, hnU⟩] at h1
  have : g' + 1 ≤ g := by exact_mod_cast h1
  omega

theorem exists_divisiblePart : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ G), SmConn N ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ (∀ y : (𝟙_ (Over (Sp k)) ⟶ N), ∃ x : (𝟙_ (Over (Sp k)) ⟶ N), x ^ p = y) ∧ (∀ (x : (𝟙_ (Over (Sp k)) ⟶ G)) (n : ℕ), n.Coprime p → n ≠ 0 → x ^ n = 1 → ∃ y, y ≫ ν = x) ∧ (∀ F : G ⟶ G, IsMonHom F → ∃ F' : N ⟶ N, IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ g', SmoothOfRelativeDimension g' N.hom ∧ (g ≤ g' → IsIso ν) := by
  intro k _ _ p G _ ⟨hc, hs, hsep, hqc, hgc⟩
  obtain ⟨a, ha⟩ := TorsionDense.exists_pow_stable G p ⊤ Set.univ isClosed_univ (by simp)
  have hpow : ∀ n : ℕ, IsMonHom (𝟙 G ^ n) := fun n => by
    induction n with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ n) (𝟙 G) ≫ μ[G]))
  obtain ⟨Z, hZ, h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (𝟙 G ^ (p ^ a))
    (hpow _) inferInstance inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ
    (by simp)
  replace h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ G, (∃ x, x ^ (p ^ a) = y) ↔ Set.range y.left ⊆ Z := by
    intro y
    rw [← h]
    simp only [MonObj.comp_pow, Category.comp_id, Subgroup.mem_top, true_and]
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    have := hpow (p ^ a)
    MonoidHom.mk' (fun x => x ≫ 𝟙 G ^ (p ^ a)) fun x y => MonObj.mul_comp x y _
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    ReducedSubgroup.exists_smooth_closed_subgroup k G inferInstance φ.range Z hZ (fun x => by
      rw [← h, MonoidHom.mem_range]
      simp only [φ, MonoidHom.mk'_apply, MonObj.comp_pow, Category.comp_id])
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hw : N.hom = ν.left ≫ G.hom := (Over.w ν).symm
  have hNsep : IsSeparated N.hom := by rw [hw]; infer_instance
  have hNqc : QuasiCompact N.hom := by rw [hw]; infer_instance
  have hGi : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  have hNr : IsReduced N.left :=
    have := isNormalScheme_of_smooth N.hom
    IsNormalScheme.isReduced
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ G),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, ∃ y, y ^ (p ^ a) = x ≫ g) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    obtain ⟨l, hl⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset g.left ν.left
      (hr ▸ ReducedSubgroup.range_subset_of_points g hZ fun x => (h _).1 (hg x))
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← ν.w, ← Category.assoc, hl, g.w]
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, ∃ y, y ^ (p ^ a) = x ≫ ν := fun x => by
    rw [h, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  obtain ⟨l, hl⟩ := hlift (𝟙 G ^ (p ^ a)) fun x => ⟨x, by rw [MonObj.comp_pow, Category.comp_id]⟩
  have hl' : ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (x ≫ l) ≫ ν = x ^ (p ^ a) := fun x => by
    rw [Category.assoc, hl, MonObj.comp_pow, Category.comp_id]
  have : Surjective l.left := surjective_of_rationalPoints l fun y => by
    obtain ⟨x, hx⟩ := hmem y
    exact ⟨x, by rw [← cancel_mono ν, hl', hx]⟩
  have hNgc : GeometricallyConnected N.hom := by
    have : GeometricallyConnected (l.left ≫ N.hom) := by rw [Over.w l]; exact hgc
    exact geometricallyConnected_of_surjective l.left N.hom
  refine ⟨N, _, ν, ⟨AbelianSubgroupFinite.isCommMonObj_of_mono ν, hNs, hNsep, hNqc, hNgc⟩, hν, hνc,
    fun y => ?_, fun x n hn hn0 hx => ?_, fun F hF => ?_, fun g hg => ?_⟩
  · obtain ⟨x, hx⟩ := hmem y
    obtain ⟨z, -, hz⟩ := ha x trivial
    refine ⟨z ≫ l, ?_⟩
    rw [← cancel_mono ν, MonObj.pow_comp, hl', ← pow_mul, ← pow_succ, hz, hx]
  · have hco : (p ^ a).Coprime (orderOf x) :=
      (Nat.Coprime.pow_left a hn.symm).coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
    exact ⟨(x ^ m) ≫ l, by rw [hl', ← pow_mul, mul_comm, pow_mul, hm]⟩
  · obtain ⟨F', hF'⟩ := hlift (ν ≫ F) fun x => by
      obtain ⟨y, hy⟩ := hmem x
      exact ⟨y ≫ F, by rw [← MonObj.pow_comp, hy, Category.assoc]⟩
    refine ⟨F', ⟨?_, ?_⟩, hF'⟩
    · rw [← cancel_mono ν, Category.assoc, hF', IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono ν, Category.assoc, hF', IsMonHom.mul_hom, Category.assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hF']
  · have hNi : IsIntegral N.left := isIntegral_of_smooth_of_geometricallyConnected N.hom
    obtain ⟨g', hg'⟩ := exists_dim_of_preconnected N.hom (Classical.arbitrary _)
    refine ⟨g', hg', fun hle => ?_⟩
    have : IsIso ν.left := isIso_of_dim_le ν.left G.hom hg (hw ▸ hg') hle
    have : IsIso ((Over.forget _).map ν) := this
    exact isIso_of_reflects_iso ν (Over.forget _)

end GlobalTheory.DivisiblePart
