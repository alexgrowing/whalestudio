import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinEtSubgroup

variable {K : Type} [Field K]

theorem discreteTopology_of_isFinite (X : Over (Sp K)) [IsFinite X.hom] : DiscreteTopology X.left := by
  have : IsLocallyArtinian (Sp K) := inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of K)))
  have : IsLocallyArtinian X.left := IsLocallyArtinian.of_locallyQuasiFinite X.hom
  infer_instance

theorem exists_pt_of_finiteEtale (X : Over (Sp K)) [IsFinite X.hom] [Etale X.hom] (x : X.left) :
    ∃ y : ptOver K (AlgebraicClosure K) ⟶ X, x ∈ Set.range y.left := by
  let Ω := AlgebraicClosure K
  let t : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := t) x
    (IsLocalRing.closedPoint Ω) (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  obtain ⟨s, hs, -, hx⟩ := (FinEt.isSplitOfRank_iff _ _).mp
    (FinEt.isSplitOfRank_of_isSepClosed (pullback.snd X.hom t) (pullback.snd X.hom t z))
  obtain ⟨i, w, hw⟩ := (hx z).exists
  refine ⟨Over.homMk (s i ≫ pullback.fst X.hom t) ?_, w, ?_⟩
  · change (s i ≫ pullback.fst X.hom t) ≫ X.hom = t
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · change (s i ≫ pullback.fst X.hom t) w = x
    rw [Scheme.Hom.comp_apply, hw, hz]

theorem exists_gal_of_apply_eq (X : Over (Sp K)) (a b : ptOver K (AlgebraicClosure K) ⟶ X)
    (p : Sp (AlgebraicClosure K)) (h : a.left p = b.left p) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, a = specAut σ ≫ b := by
  let Ω := AlgebraicClosure K
  obtain ⟨⟨q, φ⟩, ha⟩ := (Scheme.SpecToEquivOfField Ω X.left).symm.surjective a.left
  obtain ⟨⟨q', ψ⟩, hb⟩ := (Scheme.SpecToEquivOfField Ω X.left).symm.surjective b.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb
  have hq : q = q' := by
    have h1 : (Spec.map φ ≫ X.left.fromSpecResidueField q) p =
        (Spec.map ψ ≫ X.left.fromSpecResidueField q') p := by rw [ha, hb]; exact h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using h1
  subst hq
  let c : CommRingCat.of K ⟶ X.left.residueField q := Spec.preimage (X.left.fromSpecResidueField q ≫ X.hom)
  have hc : Spec.map c = X.left.fromSpecResidueField q ≫ X.hom := Spec.map_preimage _
  have key : ∀ (χ : X.left.residueField q ⟶ CommRingCat.of Ω)
      (u : ptOver K Ω ⟶ X), Spec.map χ ≫ X.left.fromSpecResidueField q = u.left →
      c ≫ χ = CommRingCat.ofHom (algebraMap K Ω) := by
    intro χ u hu
    apply Spec.map_injective
    rw [Spec.map_comp, hc, ← Category.assoc, hu]
    exact Over.w u
  have hφ := key φ a ha
  have hψ := key ψ b hb
  letI : Algebra K (X.left.residueField q) := c.hom.toAlgebra
  letI : Algebra (X.left.residueField q) Ω := ψ.hom.toAlgebra
  haveI : IsScalarTower K (X.left.residueField q) Ω := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (fun f => f.hom x) hψ).symm
  let φ' : X.left.residueField q →ₐ[K] Ω :=
    { φ.hom with commutes' := fun x => congrArg (fun f => f.hom x) hφ }
  let σ₀ : Ω →ₐ[K] Ω := φ'.liftNormal Ω
  have hσ₀ : ∀ x, σ₀ (ψ.hom x) = φ.hom x := fun x => φ'.liftNormal_commutes Ω x
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  refine ⟨σ, Over.OverMorphism.ext ?_⟩
  change a.left = spMap (σ : Ω →+* Ω) ≫ b.left
  rw [← ha, ← hb, ← Category.assoc]
  congr 1
  rw [spMap, ← Spec.map_comp]
  congr 1
  ext x
  exact (hσ₀ x).symm

theorem exists_finiteEtale_subgroup_of_points : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (H : Over (Sp K)) (_ : GrpObj H) (i : H ⟶ A.X), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ x : A.Pt, x ∈ G ↔ ∃ y, y ≫ i = x := by
  intro K _ A G _ hn hgal
  classical
  let Ω := AlgebraicClosure K
  let n := Nat.card G
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, hTf, hTe⟩ := GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu
  let T := torsion A.X n
  let ι₀ : T ⟶ A.X := torsion.ι A.X n
  have hι₀ : ι₀ ^ n = 1 := by
    rw [← GrpTangent.comp_mulN]
    refine pullback.condition.trans ?_
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  haveI : IsSplitMono η[A.X] := IsSplitMono.mk' ⟨toUnit _, toUnit_unique _ _⟩
  haveI : Mono ι₀ := inferInstanceAs (Mono (pullback.fst _ _))
  have hpow : ∀ x ∈ G, x ^ n = 1 := fun x hx =>
    congrArg Subtype.val (pow_card_eq_one' (G := G) (x := ⟨x, hx⟩))
  let lt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X), x ^ n = 1 → (S ⟶ T) := fun x hx =>
    pullback.lift x (toUnit _) (by rw [GrpTangent.comp_mulN, hx, Hom.one_def])
  have hlt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X) (hx : x ^ n = 1), lt x hx ≫ ι₀ = x :=
    fun x hx => pullback.lift_fst _ _ _
  let U : Set T.left := {t | ∃ (x : A.Pt) (hx : x ∈ G) (p : Sp Ω), (lt x (hpow x hx)).left p = t}
  haveI := discreteTopology_of_isFinite T
  let V : T.left.Opens := ⟨U, isOpen_discrete U⟩
  let H : Over (Sp K) := Over.mk (V.ι ≫ T.hom)
  let j : H ⟶ T := Over.homMk V.ι rfl
  obtain ⟨ν, hνj⟩ : ∃ ν : H ⟶ A.X, ν = j ≫ ι₀ := ⟨_, rfl⟩
  haveI : IsClosedImmersion V.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_discrete _)
  haveI hHf : IsFinite H.hom := by change IsFinite (V.ι ≫ T.hom); infer_instance
  haveI hHe : Etale H.hom := by change Etale (V.ι ≫ T.hom); infer_instance
  haveI : Mono j := (Over.forget _).mono_of_mono_map (by change Mono V.ι; infer_instance)
  haveI : Mono ν := hνj ▸ mono_comp _ _
  have hν : ν ^ n = 1 := by
    rw [hνj, ← MonObj.comp_pow, hι₀, MonObj.comp_one]
  have lift : ∀ {S : Over (Sp K)} (f : S ⟶ A.X) (hf : f ^ n = 1),
      (∀ s : S.left, ∃ y : ptOver K Ω ⟶ S, s ∈ Set.range y.left) →
      (∀ y : ptOver K Ω ⟶ S, y ≫ f ∈ G) → ∃ g : S ⟶ H, g ≫ ν = f := by
    intro S f hf hS hG
    have hr : Set.range (lt f hf).left ⊆ Set.range V.ι := by
      rintro _ ⟨s, rfl⟩
      obtain ⟨y, p, rfl⟩ := hS s
      rw [Scheme.Opens.range_ι]
      have e : y ≫ lt f hf = lt (y ≫ f) (hpow _ (hG y)) := by
        rw [← cancel_mono ι₀, hlt (y ≫ f) (hpow _ (hG y)), Category.assoc, hlt f hf]
      refine ⟨y ≫ f, hG y, p, ?_⟩
      rw [← e]
      rfl
    let g : S ⟶ H := Over.homMk (IsOpenImmersion.lift V.ι (lt f hf).left hr) (by
      change IsOpenImmersion.lift V.ι (lt f hf).left hr ≫ V.ι ≫ T.hom = S.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w _)
    have hg : g ≫ j = lt f hf := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    exact ⟨g, by rw [hνj, ← Category.assoc, hg, hlt f hf]⟩
  have hP : ∀ y : ptOver K Ω ⟶ H, y ≫ ν ∈ G := by
    intro y
    obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
    have hmem : (y ≫ j).left p ∈ U := by
      have h1 : V.ι (y.left p) ∈ Set.range V.ι := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at h1
      exact h1
    obtain ⟨x, hx, p', hp'⟩ := hmem
    rw [Subsingleton.elim p' p] at hp'
    obtain ⟨σ, hσ⟩ := exists_gal_of_apply_eq T (y ≫ j) (lt x (hpow x hx)) p hp'.symm
    have e : y ≫ ν = galPts A.X σ x := by
      show y ≫ ν = specAut σ ≫ x
      rw [hνj, ← Category.assoc, hσ, Category.assoc, hlt x (hpow x hx)]
    rw [e]
    exact hgal σ x hx

  have hone : η[A.X] = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨e, he⟩ := lift η[A.X] (by rw [hone, one_pow])
    (fun s => ⟨toUnit _, by
      obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
      exact ⟨p, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩)
    (fun y => by
      have : y ≫ η[A.X] = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) y]
      rw [this]; exact one_mem G)
  have hmul : (ν ⊗ₘ ν) ≫ μ[A.X] = (fst H H ≫ ν) * (snd H H ≫ ν) := by
    rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
  haveI : IsFinite (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : Etale (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hν' : ∀ {S : Over (Sp K)} (g : S ⟶ H), (g ≫ ν) ^ n = 1 := fun g => by
    rw [← MonObj.comp_pow ν n g, hν, MonObj.comp_one]
  obtain ⟨m, hm⟩ := lift ((ν ⊗ₘ ν) ≫ μ[A.X])
    (by rw [hmul, mul_pow, hν' (fst H H), hν' (snd H H), _root_.one_mul])
    (exists_pt_of_finiteEtale _)
    (fun y => by
      rw [hmul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
      exact mul_mem (hP (y ≫ fst H H)) (hP (y ≫ snd H H)))
  obtain ⟨i, hi⟩ := lift (ν ≫ ι[A.X]) (by rw [← Hom.inv_def, inv_pow, hν, inv_one])
    (exists_pt_of_finiteEtale _)
    (fun y => by
      rw [← Hom.inv_def, GrpObj.comp_inv]
      exact inv_mem (hP y))
  obtain ⟨gH, hνH⟩ := ReducedSubgroup.exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨H, gH, ν, hνH, inferInstance, hHf, hHe, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨g, hg⟩ := lift x (hpow x hx) (fun s => ⟨𝟙 _, s, rfl⟩) (fun y => by
      obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
      obtain ⟨σ, hσ⟩ := exists_gal_of_apply_eq (ptOver K Ω) y (𝟙 _) p
        (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
      rw [hσ, Category.comp_id]
      exact hgal σ x hx)
    exact ⟨g, hg⟩
  · rintro ⟨y, rfl⟩
    exact hP y

end GlobalTheory.FinEtSubgroup
