import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianTorusLieSubStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExactStatement

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ToricQuot

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem exists_denominator {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (δ : X →+ K) :
    ∃ (a : O) (δ' : X →+ O), a ≠ 0 ∧ (algebraMap O K).toAddMonoidHom.comp δ' = algebraMap O K a • δ := by
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) (fun i => δ (b i))
  choose g hg using ha
  refine ⟨a, (b.constr ℤ g).toAddMonoidHom, nonZeroDivisors.coe_ne_zero a, ?_⟩
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun i => ?_
  have := hg i
  simp only [Algebra.smul_def] at this
  simp [this, Algebra.smul_def]

theorem lattice_step {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {E E' T T' : Type} [AddCommGroup E] [Module O E] [AddCommGroup E'] [Module O E'] [Module.Projective O E']
    [AddCommGroup T] [Module K T] [Module O T] [IsScalarTower O K T]
    [AddCommGroup T'] [Module K T'] [Module O T'] [IsScalarTower O K T']
    (j : E →ₗ[O] T) (j' : E' →ₗ[O] T') (hj : IsBaseChange K j) (hj' : IsBaseChange K j')
    (I : (X →+ K) →ₗ[K] T) (A : T →ₗ[K] T') (hex : ∀ t, A t = 0 ↔ ∃ δ, I δ = t) (hA : Function.Surjective A)
    (io : (X →+ O) →ₗ[O] E) (f : E →ₗ[O] E')
    (hio : ∀ δ, j (io δ) = I ((algebraMap O K).toAddMonoidHom.comp δ)) (hf : ∀ e, j' (f e) = A (j e))
    (hsat : ∀ (a : O) (y : E), a ≠ 0 → a • y ∈ LinearMap.range io → y ∈ LinearMap.range io) :
    LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  have : IsLocalizedModule (nonZeroDivisors O) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K j).2 hj
  have : IsLocalizedModule (nonZeroDivisors O) j' :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K j').2 hj'
  have hinj : Function.Injective j' := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := j') hxy
    exact smul_right_injective E' (nonZeroDivisors.coe_ne_zero c) hc
  refine ⟨le_antisymm ?_ ?_, fun e' => ?_⟩
  · intro e he
    have h0 : A (j e) = 0 := by rw [← hf, show f e = 0 from he, map_zero]
    obtain ⟨δ, hδ⟩ := (hex _).1 h0
    obtain ⟨a, δ', ha, hδ'⟩ := exists_denominator (O := O) δ
    have h1 : j (a • e) = j (io δ') := by
      rw [hio, hδ', map_smul, map_smul, hδ, algebraMap_smul]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := j) h1
    refine hsat a e ha (hsat c _ (nonZeroDivisors.coe_ne_zero c) ⟨(c : O) • δ', ?_⟩)
    rw [map_smul]
    exact hc.symm
  · rintro _ ⟨δ, rfl⟩
    apply hinj
    rw [hf, hio, map_zero]
    exact (hex _).2 ⟨_, rfl⟩
  · obtain ⟨t, ht⟩ := hA (j' e')
    obtain ⟨⟨e, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors O) j t
    refine ⟨s, e, nonZeroDivisors.coe_ne_zero s, hinj ?_⟩
    have hs' : (s : O) • t = j e := hs
    rw [hf, ← hs', map_smul j', ← ht, ← algebraMap_smul K (s : O) t, map_smul, algebraMap_smul]

theorem exists_model_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S}
    (h : x = y) {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∃ M' : LieModel G y E, ∀ e, (M'.pt e).left = (M.pt e).left := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_fibre_model {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (G₁ : Over (Sp R')) [GrpObj G₁] (φ : G₁.left ⟶ G.left)
    (h : IsGrpPullback G₁ G (spMap (algebraMap R R')) φ) {V : Type} [AddCommGroup V] [Module R V]
    (M : LieModel G (𝟙 _) V) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T)
      (M₁ : LieModel G₁ (𝟙 _) T) (j : V →ₗ[R] T),
      (∀ e, M.Lifts (algebraMap R R') φ e (M₁.pt (j e))) ∧ IsBaseChange R' j := by
  obtain ⟨T, iT, mT, ⟨M'⟩⟩ := lieModel_exists _ G R' (spMap (algebraMap R R') ≫ 𝟙 _)
  letI mR : Module R T := Module.compHom T (algebraMap R R')
  have hsm : ∀ (a : R) (t : T), a • t = algebraMap R R' a • t := fun _ _ => rfl
  have tower : IsScalarTower R R' T :=
    ⟨fun a b t => by rw [Algebra.smul_def, hsm, mul_smul]⟩
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ 𝟙 (Sp R) = spMap (algebraMap R R') ≫ 𝟙 _ := rfl
  have ex : ∀ e, ∃ t, M'.pt t = LieTangent.epsBase (algebraMap R R') hφ ≫ M.pt e :=
    fun e => M'.onto _ (LieTangent.isTanAt_base _ hφ (M.tan e))
  choose f hf using ex
  let j : V →ₗ[R] T :=
    { toFun := f
      map_add' := fun a b => M'.inj (by rw [M'.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M'.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          LieTangent.base_scale, Category.assoc]) }
  have hl : ∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (j e)) := fun e => by
    change (M'.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf]
    exact Category.comp_id _
  obtain ⟨M'', h''⟩ := exists_model_of_eq (y := 𝟙 (Sp R') ≫ spMap (algebraMap R R'))
    (by rw [Category.comp_id, Category.id_comp]) M'
  obtain ⟨M₁, h₁⟩ := (LiePull.lieModel_pullback _ _ G G₁ _ φ h R' (𝟙 _) T).1 M''
  refine ⟨T, iT, mT, mR, tower, M₁, j, fun e => ?_, GlobalTheory.T.lie_model_isBaseChange _ G R R' _ V T M M' j hl⟩
  have := hl e
  unfold LieModel.Lifts at this ⊢
  rw [h₁, h'', ← this]
  exact (Category.comp_id _).symm

theorem lifts_unique {R R' : Type} [CommRing R] [CommRing R'] {c : R →+* R'} {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] {φ : G₁.left ⟶ G.left} (h : IsGrpPullback G₁ G (spMap c) φ)
    {V : Type} [AddCommGroup V] [Module R V] {M : LieModel G (𝟙 _) V} {e : V} {v w : epsAt (𝟙 (Sp R')) ⟶ G₁}
    (hv : M.Lifts c φ e v) (hw : M.Lifts c φ e w) : v = w := by
  apply Over.OverMorphism.ext
  refine h.1.hom_ext (hv.trans hw.symm) ?_
  rw [Over.w v, Over.w w]

theorem lie_quot_full : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (τ : TorusExtension GK) (φ : GK.left ⟶ G.left) (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback τ.B G' (spMap (algebraMap O K)) φ' → ∀ (MT : LieModel (splitTorus (Sp K) τ.X) (𝟙 _) (τ.X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ (io : (τ.X →+ O) →ₗ[O] E) (f : E →ₗ[O] E'), (∀ δ, M.Lifts (algebraMap O K) φ (io δ) (MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ τ.i)) ∧ (∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), M.Lifts (algebraMap O K) φ e v → M'.Lifts (algebraMap O K) φ' (f e) (v ≫ τ.q)) ∧ Function.Injective io ∧ LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  intro O K _ _ _ _ _ G G' _ _ GK _ τ φ φ'
  letI := τ.addCommGroup
  letI := τ.grpB
  intro hG hG' hφ hφ' MT hMT E _ _ E' _ _ M M'
  have := τ.free
  have := τ.finite
  have := τ.q_hom
  have := τ.i_hom
  have := hG.comm
  have := hG.smooth
  have := hG'.comm
  have := hG'.smooth
  have : Mono τ.i := ⟨fun a b hab => τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  obtain ⟨io, hio, hinj, hsat⟩ := GlobalTheory.T.semiabelian_torus_lie_sub O K G GK φ hG hφ τ.X τ.i MT hMT E M
  obtain ⟨f, hf⟩ := GlobalTheory.T.semiabelian_hom_lie_extends O K G G' GK τ.B φ φ' hG hG' hφ hφ' τ.q E E' M M'
  have := (GlobalTheory.T.lie_model_finite_projective _ G' O _ E' M').2
  obtain ⟨T, _, _, _, _, MK, j, hj, hbc⟩ := exists_fibre_model G GK φ hφ M
  obtain ⟨T', _, _, _, _, MK', j', hj', hbc'⟩ := exists_fibre_model G' τ.B φ' hφ' M'
  obtain ⟨I, hI, -⟩ := lieModel_exists_unique_diff _ _ GK K _ _ T MT MK τ.i
  obtain ⟨A, hA, -⟩ := lieModel_exists_unique_diff _ GK τ.B K _ T T' MK MK' τ.q
  have hex := GlobalTheory.T.torus_extension_tangent_exact K GK τ K (RingHom.id K)
  have hid : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  rw [hid] at hex
  refine ⟨io, f, hio, hf, hinj, lattice_step j j' hbc hbc' I A (fun t => ?_) (fun t' => ?_) io f
    (fun δ => ?_) (fun e => ?_) hsat⟩
  · have h1 : A t = 0 ↔ MK.pt t ≫ τ.q = 1 := by
      rw [← hA, ← MK'.pt_zero]
      exact MK'.inj.eq_iff.symm
    rw [h1, hex.1 _ (MK.tan t)]
    constructor
    · rintro ⟨w, hw, e⟩
      obtain ⟨δ, rfl⟩ := MT.onto w hw
      exact ⟨δ, MK.inj (by rw [hI, e])⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨_, MT.tan δ, (hI δ).symm⟩
  · obtain ⟨v, hv, e⟩ := hex.2 _ (MK'.tan t')
    obtain ⟨t, rfl⟩ := MK.onto v hv
    exact ⟨t, MK'.inj (by rw [hA, e])⟩
  · apply MK.inj
    rw [hI]
    exact lifts_unique hφ (hj _) (hio δ)
  · apply MK'.inj
    rw [hA]
    exact lifts_unique hφ' (hj' _) (hf e _ (hj e))

end GlobalTheory.CompanionTheory.Ar.ToricQuot
