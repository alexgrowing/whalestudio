import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfEquivariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GenTorsMap

theorem exists_factor {K : Type} [Field K] (X : Over (Sp K)) (hX : IsFinite X.hom) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra K F] (x : Sp F ⟶ X.left) (hx : x ≫ X.hom = spMap (algebraMap K F)) :
    ∃ (σ : AlgebraicClosure K →ₐ[K] F) (x' : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X),
      x = spMap σ.toRingHom ≫ x'.left := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ X.left.isoSpec.hom)
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have hfin : c.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hc]; infer_instance
  have e : c ≫ φ = CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hc, Category.assoc, Iso.hom_inv_id_assoc, hx]
  let σ : AlgebraicClosure K →ₐ[K] F := IsAlgClosed.lift
  have hr : ∀ b, φ.hom b ∈ σ.range := fun b => by
    have hi : IsIntegral K (φ.hom b) := by
      obtain ⟨p, hp, h0⟩ := hfin.to_isIntegral b
      refine ⟨p, hp, ?_⟩
      have := congrArg φ.hom h0
      rw [Polynomial.hom_eval₂, map_zero] at this
      have e' : φ.hom.comp c.hom = algebraMap K F := congrArg CommRingCat.Hom.hom e
      rwa [e'] at this
    exact hi.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) σ
  have hσ : Function.Injective σ := σ.toRingHom.injective
  let φ' : Γ(X.left, ⊤) →+* AlgebraicClosure K :=
    (AlgEquiv.ofInjective σ hσ).symm.toRingEquiv.toRingHom.comp (φ.hom.codRestrict σ.range hr)
  have h1 : ∀ b, σ (φ' b) = φ.hom b := fun b =>
    congrArg Subtype.val ((AlgEquiv.ofInjective σ hσ).apply_symm_apply ⟨φ.hom b, hr b⟩)
  refine ⟨σ, Over.homMk (Spec.map (CommRingCat.ofHom φ') ≫ X.left.isoSpec.inv) ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    erw [← hc]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    apply hσ
    refine (h1 _).trans ?_
    refine Eq.trans ?_ (σ.commutes a).symm
    exact congrArg (fun g => CommRingCat.Hom.hom g a) e
  · show x = _ ≫ _ ≫ _
    rw [← Category.assoc, Iso.eq_comp_inv, ← hφ, ← Spec.map_comp]
    congr 1
    ext b
    exact (h1 b).symm

theorem hom_ext_points {K : Type} [Field K] {X Y : Over (Sp K)} (hX : IsFinite X.hom) (hE : Etale X.hom)
    (hY : IsSeparated Y.hom) (u v : X ⟶ Y)
    (h : ∀ x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X, x ≫ u = x ≫ v) : u = v := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  haveI : IsReduced X.left := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
    have he : c.hom.Etale := by
      rw [← HasRingHomProperty.Spec_iff (P := @Etale), hc]; infer_instance
    letI := c.hom.toAlgebra
    haveI : Algebra.Etale K Γ(X.left, ⊤) := he
    haveI : _root_.IsReduced Γ(X.left, ⊤) := Algebra.FormallyUnramified.isReduced_of_field K _
    exact isReduced_of_isAffine_isReduced _
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq _ _ Y.hom Set.univ dense_univ (fun z _ => ?_) (by simp)
  let F := AlgebraicClosure (X.left.residueField z)
  let i := spMap (algebraMap (X.left.residueField z) F)
  obtain ⟨c, hc⟩ := Spec.map_surjective ((i ≫ X.left.fromSpecResidueField z) ≫ X.hom)
  letI : Algebra K F := c.hom.toAlgebra
  obtain ⟨σ, x', e⟩ := exists_factor X hX F _ hc.symm
  have : Epi i := by
    have : Flat i := inferInstance
    have : Surjective i :=
      ⟨fun _ => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (X.left.residueField z)) _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi i, ← Category.assoc, ← Category.assoc]
  erw [e]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun g => _ ≫ g.left) (h x')

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (j : S' ⟶ S) (G : Over S) [GrpObj G] {X : Over S'} {Z : Over S}
    (a : X ⟶ (Over.pullback j).obj G) (b : Z ⟶ G) (i : Z.left ⟶ X.left) (hi : i ≫ X.hom ≫ j = Z.hom)
    (hb : b.left = i ≫ a.left ≫ pullback.fst G.hom j) (k : ℕ) (ha : a ^ k = 1) : b ^ k = 1 := by
  let adj := Over.mapPullbackAdj j
  let c : (Over.map j).obj X ⟶ G := (adj.homEquiv _ _).symm a
  have hc : c ^ k = 1 := by
    apply (adj.homEquiv _ _).injective
    have h1 : a = adj.unit.app X ≫ (Over.pullback j).map c := by
      exact (Equiv.apply_symm_apply _ _).symm.trans (adj.homEquiv_unit _ _ c)
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have h2 := map_pow ((Over.pullback j).homMonoidHom (X := (Over.map j).obj X) (M := G)) c k
    have h3 := map_one ((Over.pullback j).homMonoidHom (X := (Over.map j).obj X) (M := G))
    refine (congrArg (_ ≫ ·) h2).trans (Eq.trans ?_ (congrArg (_ ≫ ·) h3).symm)
    rw [MonObj.comp_one, MonObj.comp_pow]
    exact (congrArg (· ^ k) h1).symm.trans ha
  have : b = (Over.homMk i hi : Z ⟶ (Over.map j).obj X) ≫ c := by
    apply Over.OverMorphism.ext
    rw [hb]
    simp [c, adj, Adjunction.homEquiv_counit]
  rw [this, ← MonObj.comp_pow, hc, MonObj.comp_one]

variable {R : Type} [CommRing R] [IsDomain R]

theorem isFinite_snd {W : (Sp R).Opens} (hW : (W : Set (Sp R)).Nonempty) (N : Over W.toScheme)
    (hN : IsFinite N.hom) : IsFinite (pullback.snd (overW W N).hom (jK R)) := by
  have hr : Set.range (jK R) ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨w, hw⟩ := hW
    refine W.isOpen.stableUnderGeneralization ?_ hw
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro r hr
    have h0 : algebraMap R (FractionRing R) r ∈ (z : PrimeSpectrum (FractionRing R)).asIdeal := hr
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z ⊥] at h0
    have : r = 0 := (IsFractionRing.to_map_eq_zero_iff).1 h0
    rw [this]; exact zero_mem _
  let l := IsOpenImmersion.lift W.ι (jK R) hr
  have hl : l ≫ W.ι = jK R := IsOpenImmersion.lift_fac _ _ _
  have P : IsPullback (pullback.fst (overW W N).hom (jK R)) (pullback.snd (overW W N).hom (jK R)) N.hom l := by
    have Q := IsPullback.of_hasPullback (overW W N).hom (jK R)
    refine ⟨⟨(cancel_mono W.ι).1 ?_⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => Q.lift s.fst s.snd ?_) (fun s => Q.lift_fst _ _ _) (fun s => Q.lift_snd _ _ _)
      (fun s m h1 h2 => Q.hom_ext (h1.trans (Q.lift_fst _ _ _).symm) (h2.trans (Q.lift_snd _ _ _).symm))⟩⟩
    · rw [Category.assoc, Category.assoc, hl]; exact Q.w
    · rw [← hl, ← Category.assoc, ← s.condition, Category.assoc]; rfl
  exact MorphismProperty.of_isPullback P hN

theorem qkExt_of_isPullF {D : DegPre R} {W : (Sp R).Opens} {ψW : PsiOn D W} {k : ℕ} {N : Over W.toScheme}
    {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    {x : Sp F ⟶ N.left} {x' : Sp F' ⟶ N.left} (e : x' = spMap f ≫ x) {p : QkPtW D W ψW k N}
    {q : QkPt D F k} {q' : QkPt D F' k} (h : QkPtW.IsPullF F x p q) (h' : QkPtW.IsPullF F' x' p q') :
    QkExt f q q' := by
  subst e
  refine ⟨h'.1.trans h.1.symm, h'.2.1.trans ((Category.assoc _ _ _).trans (congrArg _ h.2.1.symm)), fun χ =>
    corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans (Eq.symm ?_))
  refine (val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_))
  rw [Category.assoc]

theorem exists_genericMap : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ u : genPart (overW W N) ⟶ t.G, u ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ (genPart (overW W N)).left), OverGen F (genPart (overW W N)) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F (x ≫ (genι (overW W N)).left) p₀ q → IsImage P F k q (x ≫ u.left) := by
  intro E _ _ _ H R _ _ _ _ hR t P W hW _ ψW k hk y N p₀ hN
  let K := FractionRing R
  let C := AlgebraicClosure K
  let X : Over (Sp K) := Over.mk (pullback.snd (overW W N).hom (jK R))
  have hX : IsFinite X.hom := isFinite_snd hW N hN.1.1
  have hE : Etale X.hom := hN.1.2.2
  obtain ⟨f, hf, -⟩ := torsionIso_holds E H R _ hR t P C k hk
  have hq : ∀ x : TFK (R := R) C ⟶ X, ∃ q : QkPt P.D.toPre C k,
      QkPtW.IsPullF C (x.left ≫ pullback.fst (overW W N).hom (jK R)) p₀ q := fun x => by
    refine ((FieldRestrictionTest.existsUnique_pair_iff _ p₀).2 ?_).exists
    refine (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) pullback.condition).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (Over.w x))
  choose q hq using hq
  have hext := TorsionExt.qkToAkU_iff_of_qkExt firstFiveLaws R _ hR P.D P.A t.G t.semi P.U C
  obtain ⟨u, hu⟩ := GaloisPoints.exists_hom_of_equivariant K X P.A.A hX hE (fun x => f (q x)) (fun σ x x' e => by
    let a : TFK (R := R) C ⟶ P.A.A := Over.homMk (spMap σ.toAlgHom.toRingHom ≫ (f (q x)).left) (by
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w (f (q x)))).trans ?_)
      refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
      ext c
      exact σ.commutes c)
    have h := (hext C σ.toAlgHom k hk (q x) (q x') (f (q x)) a
      (qkExt_of_isPullF _ ((congrArg (· ≫ _) e).trans (Category.assoc _ _ _)) (hq x) (hq x')) rfl).1
      ((hf _ _).2 rfl)
    exact (congrArg (·.left) ((hf _ _).1 h)).symm)
  have hk1 : u ^ k = 1 := by
    have : IsSeparated P.A.A.hom := by
      have := P.U.separated
      rw [← Over.w P.U.gen.inv]
      have : IsSeparated ((Over.pullback (jK R)).obj t.G).hom :=
        inferInstanceAs (IsSeparated (pullback.snd t.G.hom (jK R)))
      infer_instance
    refine hom_ext_points hX hE this _ _ fun x => ?_
    obtain ⟨w, hw⟩ := P.U.ext
    rw [MonObj.comp_one, MonObj.comp_pow, hu]
    exact ((hf (q x) _).2 rfl w hw).1
  let v : genPart (overW W N) ⟶ t.G :=
    Over.homMk (u.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) (by
      refine Eq.trans ?_ (pullback.condition (f := (overW W N).hom) (g := jK R)).symm
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ jK R) ((Category.assoc _ _ _).symm.trans (Over.w (u ≫ P.U.gen.inv))))
  refine ⟨v, ?_, fun F _ _ _ x hx q' hq' => ?_⟩
  · refine pow_eq_one_of_pullback (jK R) t.G (u ≫ P.U.gen.inv) v (𝟙 _)
      ((Category.id_comp _).trans pullback.condition.symm)
      ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm) k ?_
    haveI := P.U.gen_hom
    haveI : IsMonHom P.U.gen.inv := inferInstance
    rw [← MonObj.pow_comp, hk1, MonObj.one_comp]
  · have hx' : x ≫ X.hom = spMap (algebraMap K F) := by
      have : Mono (jK R) := by
        have : Epi (CommRingCat.ofHom (algebraMap R K)) := IsLocalization.epi (nonZeroDivisors R) K
        exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))
      rw [← cancel_mono (jK R), Category.assoc]
      exact (congrArg (x ≫ ·) pullback.condition.symm).trans hx
    obtain ⟨σ, x', e⟩ := exists_factor X hX F x hx'
    let a : TFK (R := R) F ⟶ P.A.A := (Over.homMk x hx' : TFK (R := R) F ⟶ X) ≫ u
    refine ⟨a, Category.assoc _ _ _, ?_⟩
    refine (hext F σ k hk (q x') q' (f (q x')) a
      (qkExt_of_isPullF _ ((congrArg (· ≫ _) e).trans (Category.assoc _ _ _)) (hq x') hq') ?_).1 ((hf _ _).2 rfl)
    rw [← hu x']
    exact (congrArg (· ≫ u.left) e).trans (Category.assoc _ _ _)

end GlobalTheory.GenTorsMap
