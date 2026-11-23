import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HomDescent

section Complex

theorem pol_countable_and_tangent_ext (hT : ThetaUnifAV) (Q Q' : Out.PolAV (Sp ℂ)) :
    {f : Q.A ⟶ Q'.A | IsMonHom f}.Countable ∧
      ∀ f f' : Q.A ⟶ Q'.A, IsMonHom f → IsMonHom f' → (∀ v, IsTangent v → v ≫ f = v ≫ f') → f = f' := by
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨rig', hrig'⟩ := Q'.rigid
  obtain ⟨u, -, -, -, -, -, -, h2, -⟩ := hT Q rig hrig
  obtain ⟨u', -, -, -, -, -, h1', h2', -⟩ := hT Q' rig' hrig'
  have key := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' h1' h2'
  constructor
  · choose F hF hΛ hd hu using key
    have := u.discrete
    have := u'.discrete
    have : Countable u'.Λ := Finsupp.Countable.of_moduleFinite (R := ℤ)
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := u.Λ)
    rw [← Set.countable_coe_iff]
    refine Function.Injective.countable
      (f := fun (f : {f : Q.A ⟶ Q'.A | IsMonHom f}) (i : Fin n) =>
        (⟨F f.1 f.2 (s i), hΛ f.1 f.2 _ (s i).2⟩ : u'.Λ)) ?_
    intro f f' h
    have e1 : ∀ l : u.Λ, F f.1 f.2 l = F f'.1 f'.2 l := by
      intro l
      have hl : l ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
      induction hl using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact congrArg Subtype.val (congrFun h i)
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => rw [Submodule.coe_smul, map_zsmul, map_zsmul, hx]
    have e2 : ∀ z, F f.1 f.2 z = F f'.1 f'.2 z := by
      intro z
      have hz : z ∈ Submodule.span ℝ (u.Λ : Set (Fin Q.g → ℂ)) := u.full ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem x hx => exact e1 ⟨x, hx⟩
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    exact Subtype.ext (hu f'.1 f'.2 f.1 fun z => by rw [← e2, hF])
  · intro f f' hf hf' h
    obtain ⟨F, hF, -, hd, -⟩ := key f hf
    obtain ⟨F', -, -, hd', hu'⟩ := key f' hf'
    refine hu' f fun z => ?_
    obtain ⟨v, ⟨hv, hvz⟩, -⟩ := h2 z
    have a := hd z v hv hvz
    have b := hd' z v hv hvz
    rw [← h v hv] at b
    rw [← hF, (h1' _ a.1).unique a.2 b.2]

theorem isTangent_comp {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    [IsMonHom f] {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem exists_pol_iso (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (t : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (Q : Out.PolAV S') (e : Q.A ≅ (Over.pullback t).obj P.A), IsMonHom e.hom := by
  obtain ⟨Q, g, hg, -, hm, -⟩ := hB S S' t P
  have h : IsGrpPullback Q.A P.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hm]; rfl⟩
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback P.A t)
  exact ⟨Q, e, he⟩

theorem countable_and_tangent_ext (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) {S : Scheme.{0}}
    (t : Sp ℂ ⟶ S) (P P' : Out.PolAV S) :
    {f : (Over.pullback t).obj P.A ⟶ (Over.pullback t).obj P'.A | IsMonHom f}.Countable ∧
      ∀ f f' : (Over.pullback t).obj P.A ⟶ (Over.pullback t).obj P'.A, IsMonHom f → IsMonHom f' →
        (∀ v, IsTangent v → v ≫ f = v ≫ f') → f = f' := by
  obtain ⟨Q, e, he⟩ := exists_pol_iso hB t P
  obtain ⟨Q', e', he'⟩ := exists_pol_iso hB t P'
  obtain ⟨h1, h2⟩ := pol_countable_and_tangent_ext hT Q Q'
  constructor
  · refine (h1.image fun g => e.inv ≫ g ≫ e'.hom).mono fun f hf => ?_
    have : IsMonHom f := hf
    exact ⟨e.hom ≫ f ≫ e'.inv, show IsMonHom _ from inferInstance, by simp⟩
  · intro f f' hf hf' h
    have := h2 (e.hom ≫ f ≫ e'.inv) (e.hom ≫ f' ≫ e'.inv) inferInstance inferInstance fun v hv => by
      have := h _ (isTangent_comp e.hom hv)
      simp only [← Category.assoc] at this ⊢
      rw [this]
    simpa using this

end Complex

section Algebra

variable {k : Type} [Field k] {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra k R] [Algebra k S]
  [Algebra k B]

theorem basis_repr_map {J : Type} (b : Module.Basis J k B) (ρ : R →ₐ[k] S) (x : R ⊗[k] B) (i : J) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map ρ (AlgHom.id k B) x) i =
      ρ ((Algebra.TensorProduct.basis R b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

end Algebra

theorem specialise_eq_of_countable (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ)
    (hR : R.FG) {B : Type} [CommRing B] [Algebra k B] {Z : Scheme.{0}} (Φ : Sp (R ⊗[k] B) ⟶ Z) (U : Z.Opens)
    (hU : IsAffineOpen U) (hΦ : ∀ x, Φ x ∈ U)
    (hc : (Set.range fun ρ : R →ₐ[k] ℂ =>
      spMap (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom ≫ Φ).Countable)
    (ρ₁ : R →ₐ[k] ℂ) (hρ₁ : ∀ c : R, IsAlgebraic k c → ρ₁ c = c) :
    spMap (Algebra.TensorProduct.map ρ₁ (AlgHom.id k B)).toRingHom ≫ Φ =
      spMap (Algebra.TensorProduct.map R.val (AlgHom.id k B)).toRingHom ≫ Φ := by
  let Φ' := IsOpenImmersion.lift hU.fromSpec Φ (by
    rw [hU.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact hΦ x)
  have hΦ' : Φ' ≫ hU.fromSpec = Φ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ := Spec.map_surjective Φ'
  let G : (Γ(Z, U) ⟶ CommRingCat.of (ℂ ⊗[k] B)) → (Sp (ℂ ⊗[k] B) ⟶ Z) := fun a => Spec.map a ≫ hU.fromSpec
  have hG : Function.Injective G := fun a a' h => Spec.map_injective ((cancel_mono _).1 h)
  have e : ∀ ρ : R →ₐ[k] ℂ, spMap (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom ≫ Φ =
      G (φ ≫ CommRingCat.ofHom (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom) := fun ρ => by
    rw [← hΦ', ← hφ]
    simp only [G, Spec.map_comp, Category.assoc]
  rw [e, e]
  congr 1
  let b := Module.Basis.ofVectorSpace k B
  ext y
  apply (Algebra.TensorProduct.basis ℂ b).repr.injective
  ext i
  change (Algebra.TensorProduct.basis ℂ b).repr (Algebra.TensorProduct.map ρ₁ (AlgHom.id k B) (φ.hom y)) i =
    (Algebra.TensorProduct.basis ℂ b).repr (Algebra.TensorProduct.map R.val (AlgHom.id k B) (φ.hom y)) i
  rw [basis_repr_map, basis_repr_map]
  apply hρ₁
  refine (specialisation_numberField_and_countable_values k R hR _ 1 one_ne_zero).2 _
    ((hc.preimage_of_injOn hG.injOn).image fun a => (Algebra.TensorProduct.basis ℂ b).repr (a.hom y) i)
    fun ρ => ⟨_, ⟨ρ, e ρ⟩, ?_⟩
  exact basis_repr_map b ρ _ i

section Geometry

open GlobalTheory.Spread

theorem exists_isMonHom_pull {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G j φ) (hH : IsGrpPullback H' H j ψ) (f : G ⟶ H) [IsMonHom f] :
    ∃ f' : G' ⟶ H', IsMonHom f' ∧ f'.left ≫ ψ = φ ≫ f.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hG (isGrpPullback_pullback G j)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H j) hH
  refine ⟨a.hom ≫ (Over.pullback j).map f ≫ b.hom, inferInstance, ?_⟩
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ExtUnique.pullback_map_left_fst,
    ← Category.assoc, ha']

variable {k : Type} [CommRing k] {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

theorem isGrpPullback_bcMap (A : Over (Sp k)) [GrpObj A] (ρ : R →ₐ[k] S) :
    IsGrpPullback ((Over.pullback (spMap (algebraMap k S))).obj A) ((Over.pullback (spMap (algebraMap k R))).obj A)
      (spMap ρ.toRingHom) (bcMap A.hom ρ) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (spMap_algHom_comp ρ).symm (bcMap_fst A.hom ρ).symm) (bcMap_snd A.hom ρ)

theorem exists_specialise {A A' : Over (Sp k)} [GrpObj A] [GrpObj A']
    (f : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A')
    [IsMonHom f] (ρ : R →ₐ[k] S) :
    ∃ g : (Over.pullback (spMap (algebraMap k S))).obj A ⟶ (Over.pullback (spMap (algebraMap k S))).obj A',
      IsMonHom g ∧ g.left ≫ pullback.fst _ _ = bcMap A.hom ρ ≫ f.left ≫ pullback.fst _ _ := by
  obtain ⟨g, hg, e⟩ := exists_isMonHom_pull (isGrpPullback_bcMap A ρ) (isGrpPullback_bcMap A' ρ) f
  refine ⟨g, hg, ?_⟩
  rw [← Category.assoc, ← e, Category.assoc]
  exact congrArg (g.left ≫ ·) (bcMap_fst A'.hom ρ).symm

variable {B : Type} [CommRing B] [Algebra k B] {X : Scheme.{0}} (p : X ⟶ Sp k)

def ptBC (t : Sp B ⟶ X) (ht : t ≫ p = spMap (algebraMap k B)) (R : Type) [CommRing R] [Algebra k R] :
    Sp (R ⊗[k] B) ⟶ pullback p (spMap (algebraMap k R)) :=
  pullback.lift (spMap (Algebra.TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B).toRingHom ≫ t)
    (spMap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] B).toRingHom)
    (by rw [Category.assoc, ht, spMap_algHom_comp, spMap_algHom_comp])

theorem spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_ptBC_eq {t : Sp B ⟶ X} (ht : t ≫ p = spMap (algebraMap k B)) {C : Type} [CommRing C]
    (m : R ⊗[k] B →+* C) (x : Sp C ⟶ pullback p (spMap (algebraMap k R)))
    (h₁ : x ≫ pullback.fst _ _ =
      spMap (m.comp (Algebra.TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B).toRingHom) ≫ t)
    (h₂ : x ≫ pullback.snd _ _ =
      spMap (m.comp (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] B).toRingHom)) :
    spMap m ≫ ptBC p t ht R = x := by
  apply pullback.hom_ext
  · rw [h₁, ptBC, Category.assoc, pullback.lift_fst, ← Category.assoc, spMap_comp]
  · rw [h₂, ptBC, Category.assoc, pullback.lift_snd, spMap_comp]

theorem spMap_map_ptBC {t : Sp B ⟶ X} (ht : t ≫ p = spMap (algebraMap k B)) (ρ : R →ₐ[k] S) :
    spMap (Algebra.TensorProduct.map ρ (AlgHom.id k B)).toRingHom ≫ ptBC p t ht R =
      ptBC p t ht S ≫ bcMap p ρ := by
  apply spMap_ptBC_eq
  · rw [Category.assoc, bcMap_fst, ptBC, pullback.lift_fst]
    congr 2
    ext b; simp
  · rw [Category.assoc, bcMap_snd, ptBC, pullback.lift_snd_assoc, spMap_comp]
    congr 1

theorem surjective_spMap_map_fst {C : Type} [CommRing C] [Algebra k C] :
    Function.Surjective (spMap (Algebra.TensorProduct.map (AlgHom.id k R)
      ((TrivSqZeroExt.fstHom C C C).restrictScalars k)).toRingHom) := by
  have hs : Function.Surjective ((TrivSqZeroExt.fstHom C C C).restrictScalars k) :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  intro (x : PrimeSpectrum _)
  have hx : x ∈ Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.map (AlgHom.id k R)
      ((TrivSqZeroExt.fstHom C C C).restrictScalars k)).toRingHom) := by
    rw [range_comap_of_surjective _ _ (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hs),
      PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    refine (Algebra.TensorProduct.lTensor_ker _ hs).le.trans (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
    have h0 : a.fst = 0 := ha
    have h2 : a * a = 0 := by ext <;> simp [h0]
    have : (PrimeSpectrum.asIdeal x).IsPrime := PrimeSpectrum.isPrime x
    refine (Ideal.IsPrime.mem_or_mem inferInstance (x := a) (y := a) ?_).elim id id
    rw [h2]; exact zero_mem _
  exact hx

end Geometry

section Tangent

open GlobalTheory.Spread

variable {k : Type} [CommRing k] {C : Type} [CommRing C] [Algebra k C] {A A' : Over (Sp k)} [GrpObj A] [GrpObj A']

theorem tangent_over (v : epsR C ⟶ (Over.pullback (spMap (algebraMap k C))).obj A) :
    (v.left ≫ pullback.fst _ _) ≫ A.hom = spMap (algebraMap k (DualNumber C)) := by
  have h : v.left ≫ pullback.snd _ _ = spMap (algebraMap C (DualNumber C)) := Over.w v
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  erw [h]
  rw [spMap_comp, ← IsScalarTower.algebraMap_eq]

theorem tangent_factor (v : epsR C ⟶ (Over.pullback (spMap (algebraMap k C))).obj A) :
    ∃ m : Sp (DualNumber C) ⟶ Sp (C ⊗[k] DualNumber C), m ≫ ptBC A.hom _ (tangent_over v) C = v.left := by
  have h : v.left ≫ pullback.snd _ _ = spMap (algebraMap C (DualNumber C)) := Over.w v
  refine ⟨spMap (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k C (DualNumber C)) (AlgHom.id k _)
    fun _ _ => Commute.all _ _).toRingHom, spMap_ptBC_eq _ _ _ _ ?_ ?_⟩
  · have e : ((Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k C (DualNumber C)) (AlgHom.id k _)
        fun _ _ => Commute.all _ _).toRingHom.comp
        (Algebra.TensorProduct.includeRight : _ →ₐ[k] C ⊗[k] DualNumber C).toRingHom) = RingHom.id _ := by
      refine RingHom.ext fun b => ?_
      simp
    rw [e]
    exact ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm
  · refine h.trans ?_
    congr 1
    refine RingHom.ext fun b => ?_
    simp

theorem tangent_range {R : Type} [CommRing R] [Algebra k R]
    (f : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A')
    [IsMonHom f] (v : epsR C ⟶ (Over.pullback (spMap (algebraMap k C))).obj A) (hv : IsTangent v)
    (x : Sp (R ⊗[k] DualNumber C)) :
    (ptBC A.hom _ (tangent_over v) R ≫ f.left ≫ pullback.fst _ _) x ∈ Set.range (eSec A') := by
  obtain ⟨y, rfl⟩ := surjective_spMap_map_fst x
  have z : ∀ (G : Over (Sp k)) [GrpObj G] (T : Type) [CommRing T] [Algebra k T],
      eSec ((Over.pullback (spMap (algebraMap k T))).obj G) ≫ pullback.fst _ _ =
        spMap (algebraMap k T) ≫ eSec G := fun G _ T _ _ =>
    PolBaseChange.eSec_comm (isGrpPullback_pullback G _)
  have e₁ : spMap (Algebra.TensorProduct.map (AlgHom.id k R)
      ((TrivSqZeroExt.fstHom C C C).restrictScalars k)).toRingHom ≫ ptBC A.hom _ (tangent_over v) R =
      spMap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] C).toRingHom ≫
        eSec ((Over.pullback (spMap (algebraMap k R))).obj A) := by
    apply spMap_ptBC_eq
    · have e : ((Algebra.TensorProduct.map (AlgHom.id k R)
          ((TrivSqZeroExt.fstHom C C C).restrictScalars k)).toRingHom.comp
          (Algebra.TensorProduct.includeRight : _ →ₐ[k] R ⊗[k] DualNumber C).toRingHom) =
          (Algebra.TensorProduct.includeRight : C →ₐ[k] R ⊗[k] C).toRingHom.comp
            (TrivSqZeroExt.fstHom C C C).toRingHom := by
        refine RingHom.ext fun b => ?_
        simp
      have hv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left ≫ pullback.fst _ _ =
          spMap (algebraMap k C) ≫ eSec A := by
        rw [← Category.assoc]
        exact (congrArg (· ≫ _) hv).trans (z A C)
      rw [e, ← spMap_comp, Category.assoc, Category.assoc]
      erw [hv', z A R]
      rw [← Category.assoc, ← Category.assoc, spMap_algHom_comp, spMap_algHom_comp]
    · have h : eSec ((Over.pullback (spMap (algebraMap k R))).obj A) ≫ pullback.snd _ _ = 𝟙 _ :=
        Over.w η[(Over.pullback (spMap (algebraMap k R))).obj A]
      rw [Category.assoc]
      erw [h, Category.comp_id]
      congr 1
  have e₂ : eSec ((Over.pullback (spMap (algebraMap k R))).obj A) ≫ f.left =
      eSec ((Over.pullback (spMap (algebraMap k R))).obj A') :=
    congrArg (fun a => a.left) (IsMonHom.one_hom f)
  have e₃ : spMap (Algebra.TensorProduct.map (AlgHom.id k R)
      ((TrivSqZeroExt.fstHom C C C).restrictScalars k)).toRingHom ≫ ptBC A.hom _ (tangent_over v) R ≫
        f.left ≫ pullback.fst _ _ = (spMap (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] C).toRingHom ≫
          spMap (algebraMap k R)) ≫ eSec A' := by
    rw [← Category.assoc, e₁, Category.assoc, Category.assoc, ← z A' R, ← e₂]
    exact congrArg (_ ≫ ·) (Category.assoc _ _ _).symm
  exact ⟨_, (congrArg (fun a => a y) e₃).symm⟩

theorem exists_fg_isMonHom [QuasiCompact A.hom] [QuasiSeparated A.hom] [Flat A.hom]
    [LocallyOfFinitePresentation A'.hom] [IsSeparated A'.hom]
    (f : (Over.pullback (spMap (algebraMap k C))).obj A ⟶ (Over.pullback (spMap (algebraMap k C))).obj A')
    [IsMonHom f] :
    ∃ (R : Subalgebra k C)
      (g : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A'),
      R.FG ∧ IsMonHom g ∧ bcMap A.hom R.val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ := by
  have hfw : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  obtain ⟨R, ψ, hR, hψ, hψf⟩ := exists_fg_comp_eq A.hom A'.hom (f.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) hfw)
  let fR : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A' :=
    Over.homMk (pullback.lift ψ (pullback.snd _ _) (hψ.trans pullback.condition)) (pullback.lift_snd _ _ _)
  have hfR : fR.left ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hfR' : fR.left ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hm : IsMonHom fR := by
    have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom R.val.toRingHom)
      Subtype.val_injective
    have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
      inferInstanceAs (Flat (pullback.snd _ _))
    have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
      inferInstanceAs (IsSeparated (pullback.snd _ _))
    refine ExtUnique.isMonHom_of_isGrpPullback (isGrpPullback_bcMap A R.val) (isGrpPullback_bcMap A' R.val)
      f fR ?_
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      erw [bcMap_fst, hfR, hψf]
    · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      have a₁ := congrArg (f.left ≫ ·) (bcMap_snd A'.hom R.val)
      have a₂ := congrArg (bcMap A.hom R.val ≫ ·) hfR'
      have a₃ := congrArg (· ≫ spMap R.val.toRingHom) hfw
      exact a₁.trans ((Category.assoc _ _ _).symm.trans
        (a₃.trans ((bcMap_snd A.hom R.val).symm.trans a₂.symm)))
  exact ⟨R, fR, hR, hm, (congrArg (_ ≫ ·) hfR).trans hψf⟩

end Tangent

end GlobalTheory.HomDescent

namespace GlobalTheory

open HomDescent Spread

theorem hom_descends_to_numberField : ThetaUnifAV → Out.PolBaseChangeSt →
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (P P' : Out.PolAV (Sp k))
    (f : (Over.pullback (spMap (algebraMap k ℂ))).obj P.A ⟶ (Over.pullback (spMap (algebraMap k ℂ))).obj P'.A),
    IsMonHom f →
  ∃ (K₁ : IntermediateField k ℂ)
    (f₁ : (Over.pullback (spMap (algebraMap k K₁))).obj P.A ⟶ (Over.pullback (spMap (algebraMap k K₁))).obj P'.A)
    (j : pullback P.A.hom (spMap (algebraMap k ℂ)) ⟶ pullback P.A.hom (spMap (algebraMap k K₁))),
    FiniteDimensional k K₁ ∧ IsMonHom f₁ ∧ j ≫ pullback.fst _ _ = pullback.fst _ _ ∧
    j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap K₁.val.toRingHom ∧
    j ≫ f₁.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ := by
  intro hT hB k _ P P' f hf
  have := P.isAb.proper
  have := P'.isAb.proper
  have := P.isAb.smooth
  have := P'.isAb.smooth
  obtain ⟨R, fR, hR, hm, hfR⟩ := exists_fg_isMonHom f
  obtain ⟨K₁, ρ, hK, -, hρ⟩ := exists_specialisation_finite R hR 1 one_ne_zero
  obtain ⟨f₁, hf₁, e₁⟩ := exists_specialise fR ρ
  refine ⟨K₁, f₁, bcMap P.A.hom K₁.val, hK, hf₁, bcMap_fst _ _, bcMap_snd _ _, ?_⟩
  choose g hg eg using fun σ : R →ₐ[k] ℂ => exists_specialise fR σ
  obtain ⟨hc, hext⟩ := countable_and_tangent_ext hT hB (spMap (algebraMap k ℂ)) P P'
  have main : g (K₁.val.comp ρ) = f := by
    refine hext _ _ (hg _) hf fun v hv => ?_
    obtain ⟨U, hU, h0, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := P'.A.left) (x := eSec P'.A (default : Sp k)) (U := ⊤) trivial
    have e : ∀ σ : R →ₐ[k] ℂ, spMap (Algebra.TensorProduct.map σ (AlgHom.id k (DualNumber ℂ))).toRingHom ≫
        ptBC P.A.hom _ (tangent_over v) R ≫ fR.left ≫ pullback.fst _ _ =
        ptBC P.A.hom _ (tangent_over v) ℂ ≫ (g σ).left ≫ pullback.fst _ _ := fun σ =>
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (spMap_map_ptBC P.A.hom (tangent_over v) σ)).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (eg σ).symm)))
    have h := specialise_eq_of_countable k R hR
      (ptBC P.A.hom _ (tangent_over v) R ≫ fR.left ≫ pullback.fst _ _) U hU
      (fun x => by
        obtain ⟨y, hy⟩ := tangent_range fR v hv x
        rw [← hy, Subsingleton.elim (α := Sp k) y default]
        exact h0)
      ((hc.image fun a => ptBC P.A.hom _ (tangent_over v) ℂ ≫ a.left ≫ pullback.fst _ _).mono (by
        rintro _ ⟨σ, rfl⟩
        exact ⟨g σ, hg σ, (e σ).symm⟩))
      (K₁.val.comp ρ) hρ
    have a : (g R.val).left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ :=
      (eg R.val).trans hfR
    replace h := (e _).symm.trans (h.trans ((e _).trans (congrArg (_ ≫ ·) a)))
    obtain ⟨m, hm⟩ := tangent_factor v
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have b : ∀ c : pullback P.A.hom (spMap (algebraMap k ℂ)) ⟶ P'.A.left,
          m ≫ ptBC P.A.hom _ (tangent_over v) ℂ ≫ c = v.left ≫ c := fun c =>
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) hm)
      exact (Category.assoc _ _ _).trans ((b _).symm.trans ((congrArg (m ≫ ·) h).trans
        ((b _).trans (Category.assoc _ _ _).symm)))
    · exact (Over.w _).trans (Over.w _).symm
  rw [← main]
  exact (congrArg (_ ≫ ·) e₁).trans ((bcMap_comp_assoc P.A.hom ρ K₁.val _).trans (eg _).symm)

end GlobalTheory
