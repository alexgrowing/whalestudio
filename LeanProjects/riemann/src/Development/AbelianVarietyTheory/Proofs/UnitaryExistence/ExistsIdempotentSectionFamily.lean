import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfRatPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CompIdem

theorem exists_factor {L : Type} [Field L] {R : CommRingCat.{0}} {Z : Scheme.{0}} (i : Spec R ⟶ Z)
    [IsOpenImmersion i] (x : Sp L ⟶ Z) (hx : x (IsLocalRing.closedPoint L) ∈ Set.range i) :
    ∃ φ : R →+* L, spMap φ ≫ i = x := by
  have h : Set.range x ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum L) z (IsLocalRing.closedPoint L)]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift i x h)).hom, ?_⟩
  show Spec.map (Spec.preimage (IsOpenImmersion.lift i x h)) ≫ i = x
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

open GlobalTheory.AffinePoints in

theorem const_of_connected {Z : Scheme.{0}} (g : Z ⟶ Sp ℂ) [Smooth g] [ConnectedSpace Z]
    (t : (Sp ℂ ⟶ Z) → ℕ)
    (ht : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Z)), IsOpen B →
      (∀ b ∈ B, y b ≫ g = 𝟙 _) → IsHolTo B y → ContinuousOn (fun b => t (y b)) B)
    (p q : Sp ℂ ⟶ Z) (hp : p ≫ g = 𝟙 _) (hq : q ≫ g = 𝟙 _) : t p = t q := by
  have hirr : IrreducibleSpace Z := by
    obtain ⟨z⟩ : Nonempty Z := inferInstance
    have := GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth g z
    rw [PreconnectedSpace.connectedComponent_eq_univ] at this
    exact { isPreirreducible_univ := this, toNonempty := ⟨z⟩ }
  have hK : GlobalTheory.IsNormalScheme (Spec (.of ℂ)) := inferInstance
  have : GlobalTheory.IsNormalScheme Z := (GlobalTheory.isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((GlobalTheory.isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsIntegral Z := GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace Z
  have key : ∀ (R : CommRingCat.{0}) (i : Spec R ⟶ Z) [IsOpenImmersion i] (p q : Sp ℂ ⟶ Z),
      p ≫ g = 𝟙 _ → q ≫ g = 𝟙 _ → p (IsLocalRing.closedPoint ℂ) ∈ Set.range i →
      q (IsLocalRing.closedPoint ℂ) ∈ Set.range i → t p = t q := by
    intro R i _ p q hp hq hpi hqi
    have : Nonempty (Spec R) := ⟨hpi.choose⟩
    have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion i
    have : IsDomain R := (affine_isIntegral_iff R).1 this
    let c : CommRingCat.of ℂ ⟶ R := Spec.preimage (i ≫ g)
    have hc : Spec.map c = i ≫ g := Spec.map_preimage _
    have hsm : Smooth (Spec.map c) := by rw [hc]; infer_instance
    letI : Algebra ℂ R := c.hom.toAlgebra
    have : Algebra.Smooth ℂ R := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hsm
    have halg : ∀ φ : R →+* ℂ, (spMap φ ≫ i) ≫ g = 𝟙 _ ↔ ∀ a, φ (algebraMap ℂ R a) = a := by
      intro φ
      rw [Category.assoc, ← hc]
      show Spec.map (CommRingCat.ofHom φ) ≫ Spec.map c = 𝟙 _ ↔ _
      rw [← Spec.map_comp, ← Spec.map_id, Spec.map_injective.eq_iff]
      constructor
      · intro h a
        exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => f.hom a) h
      · intro h
        ext a
        exact h a
    obtain ⟨φ, rfl⟩ := exists_factor i p hpi
    obtain ⟨ψ, rfl⟩ := exists_factor i q hqi
    have := GlobalTheory.RootConst.preconnectedSpace_algHom R
    have hcont := GlobalTheory.RootConst.continuous_of_holomorphic_families R
      (fun s => (t (spMap s.toRingHom ≫ i) : ℂ)) (fun m B s hB hs => by
        have h1 := ht m B (fun b => spMap (s b).toRingHom ≫ i) hB
          (fun b _ => (halg _).2 fun a => (s b).commutes a)
          (GlobalTheory.LocLift.isHolTo_comp_hom (GlobalTheory.ThetaValueCont.isHolTo_spMap hB (fun b => (s b).toRingHom) hs) i)
        exact (continuous_of_discreteTopology (f := fun n : ℕ => (n : ℂ))).comp_continuousOn h1)
    have hdisc : IsDiscrete (Set.range fun n : ℕ => (n : ℂ)) :=
      by
        have h0 : Topology.IsEmbedding (fun n : ℕ => (n : ℂ)) := by
          have h := Complex.isometry_ofReal.isEmbedding.comp Nat.isClosedEmbedding_coe_real.isEmbedding
          exact h
        exact h0.isDiscrete_range
    have := isPreconnected_univ.constant_of_mapsTo hdisc hcont.continuousOn (fun s _ => ⟨_, rfl⟩)
      (x := { φ with commutes' := (halg φ).1 hp }) (y := { ψ with commutes' := (halg ψ).1 hq }) trivial trivial
    exact_mod_cast this
  obtain ⟨R, i, _, hi, -⟩ := Z.exists_affine_mem_range_and_range_subset
    (x := p (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  obtain ⟨R', i', _, hi', -⟩ := Z.exists_affine_mem_range_and_range_subset
    (x := q (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  have := LocallyOfFiniteType.jacobsonSpace g
  have ho := i.isOpenEmbedding.isOpen_range
  have ho' := i'.isOpenEmbedding.isOpen_range
  have hne : (Set.range i ∩ Set.range i').Nonempty := nonempty_preirreducible_inter ho ho' ⟨_, hi⟩ ⟨_, hi'⟩
  obtain ⟨x, ⟨h1, h2⟩, hx⟩ := nonempty_inter_closedPoints hne (ho.inter ho').isLocallyClosed
  have hr := pointOfClosedPoint_comp g x hx
  have hra := pointOfClosedPoint_apply g x hx (IsLocalRing.closedPoint ℂ)
  exact (key R i p _ hp hr hi (by rw [hra]; exact h1)).trans (key R' i' _ q hr hq (by rw [hra]; exact h2) hi')

theorem const_of_section {k : Type} [Field k] (σ : k →+* ℂ) {Y : Scheme.{0}} (s : Y ⟶ Sp k) [Smooth s]
    [ConnectedSpace Y] (r : Sp k ⟶ Y) (hr : r ≫ s = 𝟙 _) (t : (Sp ℂ ⟶ Y) → ℕ)
    (ht : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y)), IsOpen B →
      (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ContinuousOn (fun b => t (y b)) B)
    (p q : Sp ℂ ⟶ Y) (hp : p ≫ s = spMap σ) (hq : q ≫ s = spMap σ) : t p = t q := by
  have := GlobalTheory.RatPointConn.of_section s r hr
  have : ConnectedSpace ↥(pullback s (spMap σ)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := s) _ _ _ (IsPullback.of_hasPullback _ _)
  have h := const_of_connected (pullback.snd s (spMap σ)) (fun x => t (x ≫ pullback.fst _ _))
    (fun m B y hB hy hh => ht m B _ hB (fun b hb => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy b hb, Category.id_comp])
      (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
    (pullback.lift p (𝟙 _) (by simpa using hp)) (pullback.lift q (𝟙 _) (by simpa using hq))
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
  simpa only [pullback.lift_fst] using h

theorem const_on_component {k : Type} [Field k] (σ : k →+* ℂ) {Y : Scheme.{0}} (s : Y ⟶ Sp k) [Smooth s]
    [TopologicalSpace.NoetherianSpace Y] (r : Sp k ⟶ Y) (hr : r ≫ s = 𝟙 _) (t : (Sp ℂ ⟶ Y) → ℕ)
    (ht : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y)), IsOpen B →
      (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ContinuousOn (fun b => t (y b)) B)
    (p q : Sp ℂ ⟶ Y) (hp : p ≫ s = spMap σ) (hq : q ≫ s = spMap σ)
    (hpr : p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (r (IsLocalRing.closedPoint k)))
    (hqr : q (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (r (IsLocalRing.closedPoint k))) : t p = t q := by
  let U : Y.Opens := ⟨connectedComponent (r (IsLocalRing.closedPoint k)),
    isOpen_connectedComponent_of_noetherianSpace _⟩
  have : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.1 (isConnected_connectedComponent (x := r (IsLocalRing.closedPoint k)))
  have lf : ∀ (L : Type) [Field L] (x : Sp L ⟶ Y), x (IsLocalRing.closedPoint L) ∈ U →
      ∃ x' : Sp L ⟶ U.toScheme, x' ≫ U.ι = x := by
    intro L _ x hx
    refine ⟨IsOpenImmersion.lift U.ι x ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum L) z (IsLocalRing.closedPoint L), Scheme.Opens.range_ι]
    exact hx
  obtain ⟨p', rfl⟩ := lf ℂ p hpr
  obtain ⟨q', rfl⟩ := lf ℂ q hqr
  obtain ⟨r', hr'⟩ := lf k r mem_connectedComponent
  exact const_of_section σ (U.ι ≫ s) r' (by rw [← Category.assoc, hr', hr]) (fun x => t (x ≫ U.ι))
    (fun m B y hB hy hh => ht m B _ hB (fun b hb => by rw [Category.assoc, hy b hb])
      (GlobalTheory.LocLift.isHolTo_comp_hom hh _)) p' q' (by simpa using hp) (by simpa using hq)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_descent {K L : IntermediateField ℚ ℂ} (hKL : K ≤ L) {X : Scheme.{0}} (s : X ⟶ Sp K)
    [LocallyOfFiniteType s] (x : Sp L ⟶ X) (hx : x ≫ s = spMap (IntermediateField.inclusion hKL).toRingHom) :
    ∃ S : Finset ℂ, (∀ z ∈ S, z ∈ L) ∧ ∀ (F : IntermediateField ℚ ℂ) (hK : K ≤ F) (hL : F ≤ L), (∀ z ∈ S, z ∈ F) →
      ∃ x' : Sp F ⟶ X, x' ≫ s = spMap (IntermediateField.inclusion hK).toRingHom ∧
        spMap (IntermediateField.inclusion hL).toRingHom ≫ x' = x := by
  classical
  obtain ⟨R, i, _, hi, -⟩ := X.exists_affine_mem_range_and_range_subset
    (x := x (IsLocalRing.closedPoint L)) (U := ⊤) trivial
  obtain ⟨φ, rfl⟩ := exists_factor i x hi
  let c : CommRingCat.of K ⟶ R := Spec.preimage (i ≫ s)
  have hc : Spec.map c = i ≫ s := Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map c) := by rw [hc]; infer_instance
  letI : Algebra K R := c.hom.toAlgebra
  have : Algebra.FiniteType K R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
  obtain ⟨G, hG⟩ := this.out
  have hcomp : ∀ (F : Type) [CommRing F] (ψ : R →+* F) (j : K →+* F),
      (spMap ψ ≫ i) ≫ s = spMap j ↔ ∀ a, ψ (algebraMap K R a) = j a := by
    intro F _ ψ j
    rw [Category.assoc, ← hc]
    show Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map c = _ ↔ _
    rw [← Spec.map_comp, Spec.map_injective.eq_iff]
    constructor
    · intro h a
      exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of F => f.hom a) h
    · intro h
      ext a
      exact h a
  have hφ := (hcomp L φ _).1 hx
  refine ⟨G.image fun a => (φ a : ℂ), ?_, fun F hK hL hS => ?_⟩
  · intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
    exact (φ a).2
  have hmem : ∀ a : R, (φ a : ℂ) ∈ F := by
    intro a
    have ha : a ∈ Algebra.adjoin K (G : Set R) := hG ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact hS _ (Finset.mem_image_of_mem _ ha)
    | algebraMap a => rw [hφ]; exact hK a.2
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let ψ : R →+* F := (L.val.toRingHom.comp φ).codRestrict F.toSubfield.toSubring hmem
  refine ⟨spMap ψ ≫ i, (hcomp F ψ _).2 fun a => Subtype.ext ?_, ?_⟩
  · show (φ (algebraMap K R a) : ℂ) = a
    rw [hφ]; rfl
  · rw [← Category.assoc, spMap_comp]
    rfl

theorem exists_rational_components {K : IntermediateField ℚ ℂ} (hKL : K ≤ algebraicClosure ℚ ℂ) {X : Scheme.{0}}
    (s : X ⟶ Sp K) [LocallyOfFiniteType s] [QuasiCompact s] :
    ∃ S : Finset ℂ, (∀ z ∈ S, z ∈ algebraicClosure ℚ ℂ) ∧
      ∀ (F : IntermediateField ℚ ℂ) (hK : K ≤ F), F ≤ algebraicClosure ℚ ℂ → (∀ z ∈ S, z ∈ F) →
      ∀ z : ↥(pullback s (spMap (IntermediateField.inclusion hK).toRingHom)),
        ∃ r : Sp F ⟶ pullback s (spMap (IntermediateField.inclusion hK).toRingHom),
          r ≫ pullback.snd _ _ = 𝟙 _ ∧ z ∈ connectedComponent (r (IsLocalRing.closedPoint F)) := by
  classical
  let L := algebraicClosure ℚ ℂ
  have : IsAlgClosed L := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  let Z := pullback s (spMap (IntermediateField.inclusion hKL).toRingHom)
  let g : Z ⟶ Sp L := pullback.snd _ _
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Z := {}
  have := LocallyOfFiniteType.jacobsonSpace g
  have : Finite (irreducibleComponents Z) := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  have := Fintype.ofFinite (irreducibleComponents Z)
  have h1 : ∀ C : irreducibleComponents Z, ∃ x : Sp L ⟶ Z, x ≫ g = 𝟙 _ ∧ x (IsLocalRing.closedPoint L) ∈ C.1 := by
    intro C
    obtain ⟨x, hx, hc⟩ := nonempty_inter_closedPoints (C.2.1 : IsIrreducible C.1).nonempty
      (isClosed_of_mem_irreducibleComponents _ C.2).isLocallyClosed
    exact ⟨pointOfClosedPoint g x hc, pointOfClosedPoint_comp g x hc,
      (congrArg (· ∈ C.1) (pointOfClosedPoint_apply g x hc _)).mpr hx⟩
  choose x hx hxC using h1
  have h2 := fun C => exists_descent hKL s (x C ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx C, Category.id_comp])
  choose S hS hSF using h2
  refine ⟨Finset.univ.biUnion S, ?_, fun F hK hL hF z => ?_⟩
  · intro z hz
    obtain ⟨C, -, h⟩ := Finset.mem_biUnion.1 hz
    exact hS C z h
  have hcomp : spMap (IntermediateField.inclusion hL).toRingHom ≫ spMap (IntermediateField.inclusion hK).toRingHom =
      spMap (IntermediateField.inclusion hKL).toRingHom := by
    rw [spMap_comp]; rfl
  let π : Z ⟶ pullback s (spMap (IntermediateField.inclusion hK).toRingHom) :=
    pullback.lift (pullback.fst _ _) (g ≫ spMap (IntermediateField.inclusion hL).toRingHom)
      (by rw [Category.assoc, hcomp, pullback.condition])
  have hπ : IsPullback π g (pullback.snd _ _) (spMap (IntermediateField.inclusion hL).toRingHom) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := s)
      (h₂₂ := spMap (IntermediateField.inclusion hK).toRingHom) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, hcomp]
    exact IsPullback.of_hasPullback _ _
  have hy : Surjective (spMap (IntermediateField.inclusion hL).toRingHom) :=
    ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim (α := PrimeSpectrum F) _ _⟩⟩
  have hs : Surjective π := MorphismProperty.of_isPullback hπ.flip hy
  obtain ⟨w, rfl⟩ := π.surjective z
  let C : irreducibleComponents Z := ⟨irreducibleComponent w, irreducibleComponent_mem_irreducibleComponents w⟩
  obtain ⟨x', hx1, hx2⟩ := hSF C F hK hL fun z hz => hF z (Finset.mem_biUnion.2 ⟨C, Finset.mem_univ _, hz⟩)
  let r : Sp F ⟶ pullback s (spMap (IntermediateField.inclusion hK).toRingHom) :=
    pullback.lift x' (𝟙 _) (by rw [hx1, Category.id_comp])
  have hr : spMap (IntermediateField.inclusion hL).toRingHom ≫ r = x C ≫ π := by
    apply pullback.hom_ext
    · simp only [r, π, Category.assoc, pullback.lift_fst, hx2]
    · simp only [r, π, Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [← Category.assoc, hx C, Category.id_comp]
  refine ⟨r, pullback.lift_snd _ _ _, ?_⟩
  have e : r (IsLocalRing.closedPoint F) = π (x C (IsLocalRing.closedPoint L)) := by
    have e1 : r (spMap (IntermediateField.inclusion hL).toRingHom (IsLocalRing.closedPoint L)) =
        π (x C (IsLocalRing.closedPoint L)) := congrArg (fun f : Sp L ⟶ _ => f (IsLocalRing.closedPoint L)) hr
    rw [← e1]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum F) _ _
  rw [e]
  exact ((isIrreducible_irreducibleComponent (x := w)).isConnected.isPreconnected.image _
    π.continuous.continuousOn).subset_connectedComponent ⟨_, hxC C, rfl⟩ ⟨w, mem_irreducibleComponent, rfl⟩

section Rule

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def basePt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by rw [y.x_over, spMap_comp]; rfl)

theorem basePt_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (h : z.x = spMap φ.toRingHom ≫ y.x) :
    basePt z = spMap φ.toRingHom ≫ basePt y := by
  apply pullback.hom_ext
  · simp only [basePt, Category.assoc, pullback.lift_fst, h]
  · simp only [basePt, Category.assoc, pullback.lift_snd, spMap_comp]
    congr 1
    exact φ.comp_algebraMap.symm

theorem basePt_congr {S : Type} [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (h : z.x = y.x) :
    basePt z = basePt y := by
  apply pullback.hom_ext
  · simp only [basePt, pullback.lift_fst, h]
  · simp only [basePt, pullback.lift_snd]

theorem exists_indicator (hA : AllTest Xo c) (U : Set (Xo.XF c)) (hU : IsClopen U) :
    ∃ χ ∈ sec Xo c 0 0, χ * χ = χ ∧ ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S),
      IsIdempotentElem (evR Xo c χ y) ∧
        ∀ z : PrimeSpectrum S, evR Xo c χ y ∉ z.asIdeal ↔ basePt y z ∈ U := by
  have hex : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃ e : p.R, IsIdempotentElem e ∧
      ∀ z : PrimeSpectrum p.R, e ∉ z.asIdeal ↔ basePt y z ∈ U := by
    intro p y
    obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (hU.preimage (basePt y).continuous)
    exact ⟨e, he, fun z => (Set.ext_iff.1 h z).symm⟩
  choose χ hi hχ using hex
  have hmap : ∀ (p : TRing c.F) (S : Type) [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R)
      (w : FrPt Xo c S), w.x = spMap φ.toRingHom ≫ y.x →
      ∀ z : PrimeSpectrum S, φ (χ p y) ∉ z.asIdeal ↔ basePt w z ∈ U := by
    intro p S _ _ φ y w h z
    rw [basePt_map φ y w h]
    exact hχ p y (PrimeSpectrum.comap φ.toRingHom z)
  have hw : ∀ (p : TRing c.F) (t : Ix Dw → (p.R)ˣ), wchar (ex Dw 0 0) t = 1 := by
    intro p t
    refine Finset.prod_eq_one fun i _ => ?_
    have : ex Dw 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
    rw [this, pow_zero]
  refine ⟨χ, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, ?_, fun S _ _ _ y => ?_⟩
  · refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi q z) ((hi p y).map φ) ?_
    ext w
    exact (hχ q z w).trans (hmap p q.R φ y z h.1 w).symm
  · rw [hw, _root_.one_mul]
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi p y') (hi p y) ?_
    ext w
    have := hχ p y' w
    rw [basePt_congr y y' h.1] at this
    exact this.trans (hχ p y w).symm
  · funext p y
    exact (hi p y).eq
  · have h := hA S y
    have e : evR Xo c χ y = h.choose_spec.choose (χ h.choose h.choose_spec.choose_spec.choose) := dif_pos h
    rw [e]
    exact ⟨(hi _ _).map _, hmap _ S _ _ y h.choose_spec.choose_spec.choose_spec.1⟩

theorem exists_index {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) :
    ∃ t : (Sp ℂ ⟶ Xo.X) → ℕ, (∀ i P, IsPeriod (F.Di i) ty P → t (F.u i P) = i) ∧
      ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B →
        (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ContinuousOn (fun b => t (y b)) B := by
  classical
  let t : (Sp ℂ ⟶ Xo.X) → ℕ := fun x =>
    if h : ∃ i P, IsPeriod (F.Di i) ty P ∧ F.u i P = x then (h.choose : ℕ) else 0
  have ht : ∀ i P, IsPeriod (F.Di i) ty P → t (F.u i P) = i := by
    intro i P hP
    have h : ∃ j Q, IsPeriod (F.Di j) ty Q ∧ F.u j Q = F.u i P := ⟨i, P, hP, rfl⟩
    obtain ⟨Q, hQ, e⟩ := h.choose_spec
    exact (dif_pos h).trans (congrArg _ (F.disj _ _ _ _ hQ hP e))
  refine ⟨t, ht, fun m B y hB hs hy b₀ hb₀ => ?_⟩
  obtain ⟨B', i, P, ho, hm, -, hP, hu⟩ := F.lift m B y hB hs hy b₀ hb₀
  have hev : (fun b => t (y b)) =ᶠ[nhds b₀] fun _ => (i : ℕ) :=
    Filter.eventually_of_mem (ho.mem_nhds hm) fun b hb => by
      show t (y b) = i
      rw [← hu b hb]
      exact ht i _ (hP.1 b hb)
  exact (continuousAt_const.congr hev.symm).continuousWithinAt

theorem coeff_le_algebraicClosure (c : Coeff l) : c.F ≤ algebraicClosure ℚ ℂ := by
  intro z hz
  have := c.fin
  exact mem_algebraicClosure_iff'.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : c.F)).map c.F.val)

end Rule

theorem exists_coeff_idempotent_sections :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (KA l).val.toRingHom ty), IsTypeFn H Dw.p Dw.q ty → ∃ c' : Coeff l, c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → ∀ i : Fin F.n, ∃ χ ∈ sec Xo c'' 0 0, χ * χ = χ ∧ ∀ (y : FrPt Xo c'' (CAt c''.F.val.toRingHom)) (i' : Fin F.n) P, IsPeriod (F.Di i') ty P → y.x = F.u i' P → evR Xo c'' χ y = if i' = i then 1 else 0 := by
  intro E _ _ _ H Dw l Xo c _ g ty F _
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  obtain ⟨S, hS, hrat⟩ := exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s
  have := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact mem_algebraicClosure_iff.1 (hS z h)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))
  refine ⟨c', fun z hz => ?_, fun c'' hle i => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)
    rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have hr := hrat c''.F c''.le (coeff_le_algebraicClosure c'') fun z hz =>
    hle (hc' z (Finset.mem_union_left _ hz))
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c''
  let σ : c''.F →+* ℂ := c''.F.val.toRingHom
  let s : Xo.XF c'' ⟶ Sp c''.F := pullback.snd _ _
  let pr : Xo.XF c'' ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c'', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, spMap_comp]
    rfl
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c'', p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    intro p q hp hq hpq
    obtain ⟨r, hr1, hr2⟩ := hr (q (IsLocalRing.closedPoint ℂ))
    exact const_on_component σ s r hr1 (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
      p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2
  let U : Set (Xo.XF c'') := {z | ∃ p : Sp ℂ ⟶ Xo.XF c'', p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨χ, h1, h2, h3⟩ := exists_indicator
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.allSixLaws.1.secBaseChange E H Dw l Xo c'') U hU
  refine ⟨χ, h1, h2, fun y i' P hP hy => ?_⟩
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨h4, h5⟩ := h3 (CAt σ) y
  let p : Sp ℂ ⟶ Xo.XF c'' := basePt y
  have hp : p ≫ s = spMap σ := pullback.lift_snd _ _ _
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := (pullback.lift_fst _ _ _).trans hy
    rw [this]
    exact ht i' P hP
  let v : ℂ := evR Xo c'' χ (S := CAt σ) y
  have h6 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔ p (IsLocalRing.closedPoint ℂ) ∈ U :=
    h5 (IsLocalRing.closedPoint ℂ)
  have h7 : v ≠ 0 ↔ i' = i := by
    have h8 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔ v ≠ 0 := by
      show v ∉ IsLocalRing.maximalIdeal ℂ ↔ _
      rw [IsLocalRing.notMem_maximalIdeal, isUnit_iff_ne_zero]
    rw [← h8, h6]
    constructor
    · rintro ⟨q, hq, hqp, hqi⟩
      exact Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi))
    · rintro rfl
      exact ⟨p, hp, mem_connectedComponent, hp'⟩
  have h9 : IsIdempotentElem v := h4
  split_ifs with h
  · exact (IsIdempotentElem.iff_eq_zero_or_one.1 h9).resolve_left (h7.2 h)
  · exact not_not.1 (mt h7.1 h)

end GlobalTheory.CompIdem
