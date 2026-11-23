import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LieEigen

section Module

open EigenSplit

theorem exists_eigenvectors {O R k I κ : Type} [CommRing O] [Module.Finite ℤ O] [CommRing R] [Field k]
    [Finite I] [Fintype κ] {σ : I → O →+* R} (hσ : IsSplitting σ) {n : ℕ}
    (ρ : O →+* Module.End R (Fin n → R)) (f : R →+* k) (ρk : O →+* Module.End k (Fin n → k))
    (hf : ∀ a x, f ∘ ρ a x = ρk a (f ∘ x)) (ty : κ → I)
    (hm : ∀ τ, Module.finrank k (eigenSub ρk (f.comp (σ τ))) = Nat.card {i // ty i = τ}) :
    ∃ x : κ → Fin n → R, (∀ i, x i ∈ eigenSub ρ (σ (ty i))) ∧
      ∃ b : Module.Basis κ k (Fin n → k), ∀ i, b i = f ∘ x i := by
  classical
  let _ := f.toAlgebra
  let F : (Fin n → R) →ₗ[R] (Fin n → k) := (Algebra.linearMap R k).compLeft (Fin n)
  have hb : IsBaseChange k F := IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R k)
  have hs : ∀ τ, eigenSub ρk (f.comp (σ τ)) = Submodule.span k (F '' eigenSub ρ (σ τ)) := fun τ =>
    eigenSub_eq_span_of_factor (σ := σ) (ρ := ρ) (ρ' := ρk) (f := F) R hσ hf hb τ
  have key : ∀ τ, ∃ c : Module.Basis {i // ty i = τ} k (eigenSub ρk (f.comp (σ τ))),
      ∀ i, (c i : Fin n → k) ∈ F '' eigenSub ρ (σ τ) := fun τ => by
    obtain ⟨s, hs1, hs2, hs3⟩ := exists_linearIndependent k (F '' eigenSub ρ (σ τ))
    let c := (Module.Basis.span hs3).map
      (LinearEquiv.ofEq _ _ (by rw [Subtype.range_coe, hs2, hs]) : _ ≃ₗ[k] eigenSub ρk (f.comp (σ τ)))
    have : Finite s := Module.Finite.finite_basis c
    have hc : Nat.card s = Nat.card {i // ty i = τ} := by
      rw [← hm, Module.finrank_eq_nat_card_basis c]
    obtain ⟨e⟩ := Finite.card_eq.1 hc
    refine ⟨c.reindex e, fun i => hs1 ?_⟩
    simp [c, Module.Basis.span_apply]
  choose c hc using key
  choose x hx hx' using hc
  refine ⟨fun i => x (ty i) ⟨i, rfl⟩, fun i => hx _ _,
    ((isInternal_eigenSub (hσ.map f) ρk).collectedBasis c).reindex (Equiv.sigmaFiberEquiv ty),
    fun i => ?_⟩
  rw [Module.Basis.reindex_apply, DirectSum.IsInternal.collectedBasis_coe]
  exact (hx' _ _).symm

theorem exists_basis_of_isUnit {R k : Type} [CommRing R] [Field k] {n g : ℕ} (f : R →+* k)
    (x : Fin g → Fin n → R) (b : Module.Basis (Fin g) k (Fin n → k)) (hb : ∀ i, b i = f ∘ x i) :
    ∃ r, f r ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (f' : R →+* R'), IsUnit (f' r) →
      ∃ b' : Module.Basis (Fin g) R' (Fin n → R'), ∀ i, b' i = f' ∘ x i := by
  obtain rfl : n = g := by simpa using Module.finrank_eq_card_basis b
  have h : ∀ (R' : Type) [CommRing R'] (f' : R →+* R'),
      (Pi.basisFun R' (Fin n)).det (fun i => f' ∘ x i) = f' (Matrix.of x).det := fun R' _ f' => by
    rw [Pi.basisFun_det_apply, RingHom.map_det]
    rfl
  refine ⟨(Matrix.of x).det, ?_, fun R' _ f' hu => ?_⟩
  · rw [← h, ← funext hb]
    exact ((Pi.basisFun k (Fin n)).isUnit_det b).ne_zero
  · rw [← h] at hu
    obtain ⟨h1, h2⟩ := (Module.Basis.is_basis_iff_det _).2 hu
    exact ⟨Module.Basis.mk h1 h2.ge, fun i => by simp⟩

end Module

section Coordinates

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)
open GlobalTheory.SqZero (prodPts_eq_lieExp lieExp_add comp_lieExp lieExp_congr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}

theorem prodPts_add (hv : ∀ i, IsTangent (v i)) (c c' : Fin n → R) :
    prodPts (c + c') v = prodPts c v * prodPts c' v := by
  rw [prodPts_eq_lieExp, prodPts_eq_lieExp, prodPts_eq_lieExp,
    ← lieExp_add hv _ _ _ _ (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
      (fun _ => by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
  exact lieExp_congr _ (fun _ => TrivSqZeroExt.inr_add _ _ _) _ _

theorem prodPts_smul (a : R) (c : Fin n → R) :
    prodPts (a • c) v = Chart.spMap (scaleD a) ≫ prodPts c v := by
  rw [prodPts_eq_lieExp, prodPts_eq_lieExp, comp_lieExp]
  exact lieExp_congr _ (fun _ => by rw [TrivSqZeroExt.map_inr]; rfl) _ _

theorem isTangent_prodPts (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) : IsTangent (prodPts c v) := by
  rw [prodPts_eq_lieExp, ← Chart.isTan_iff]
  exact SqZero.comp_eq_one_of_mem_redKer (J := RingHom.ker (Chart.fstD R))
    (SqZero.lieExp_mem_redKer hv _ (fun _ => rfl) _) _ fun a ha => ha

omit [IsCommMonObj G] in
theorem exists_prodPts (hv : IsLieBasis v) {w : epsR R ⟶ G} (hw : IsTangent w) :
    ∃ c, prodPts c v = w :=
  (hv.2 w hw).exists.imp fun _ h => ((Chart.isLieComb_iff _ _ _).1 h).symm

theorem prodPts_injective (hv : IsLieBasis v) : Function.Injective fun c => prodPts c v :=
  fun c _ h => (hv.2 _ (isTangent_prodPts hv.1 c)).unique ((Chart.isLieComb_iff _ _ _).2 rfl)
    ((Chart.isLieComb_iff _ _ _).2 h)

def tanHom (hv : ∀ i, IsTangent (v i)) : Multiplicative (Fin n → R) →* (epsR R ⟶ G) :=
  MonoidHom.mk' (fun c => prodPts c.toAdd v) fun c c' => prodPts_add hv _ _

theorem prodPts_prodPts (hv : ∀ i, IsTangent (v i)) {m : ℕ} (d : Fin m → R) (b : Fin m → Fin n → R) :
    prodPts d (fun i => prodPts (b i) v) = prodPts (∑ i, d i • b i) v := by
  have h := map_prod (tanHom hv) (fun i => Multiplicative.ofAdd (d i • b i)) Finset.univ
  rw [← ofAdd_sum] at h
  refine Eq.trans ?_ h.symm
  rw [prodPts, List.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => (prodPts_smul _ _).symm

theorem isLieBasis_prodPts (hv : IsLieBasis v) {m : ℕ} (b : Module.Basis (Fin m) R (Fin n → R)) :
    IsLieBasis fun i => prodPts (b i) v := by
  refine ⟨fun i => isTangent_prodPts hv.1 _, fun w hw => ?_⟩
  obtain ⟨c, rfl⟩ := exists_prodPts hv hw
  refine ⟨b.equivFun c, (Chart.isLieComb_iff _ _ _).2 ?_, fun d hd => ?_⟩
  · rw [prodPts_prodPts hv.1, b.sum_equivFun]
  · replace hd := (Chart.isLieComb_iff _ _ _).1 hd
    rw [prodPts_prodPts hv.1] at hd
    rw [prodPts_injective hv hd, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem exists_action (hv : IsLieBasis v) {O : Type} [CommRing O] (act : OAct O G) :
    ∃ ρ : O →+* Module.End R (Fin n → R), ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ act.act a := by
  have := act.hom
  choose T hT using fun a c =>
    exists_prodPts hv (SqZero.isTangent_comp (act.act a) (isTangent_prodPts hv.1 c))
  have inj : ∀ {c c'}, prodPts c v = prodPts c' v → c = c' := fun h => prodPts_injective hv h
  let L : O → Module.End R (Fin n → R) := fun a =>
    { toFun := T a
      map_add' := fun c c' => inj (by
        rw [prodPts_add hv.1, hT, hT, hT, prodPts_add hv.1]
        exact map_mul (IsMonHom.monoidHom (act.act a) _) _ _)
      map_smul' := fun r c => inj (by
        rw [RingHom.id_apply, prodPts_smul, hT, hT, prodPts_smul, Category.assoc]) }
  have hL : ∀ a c, prodPts (L a c) v = prodPts c v ≫ act.act a := hT
  refine ⟨RingHom.mk'
    { toFun := L
      map_one' := LinearMap.ext fun c => inj (by rw [hL, act.one, Category.comp_id]; rfl)
      map_mul' := fun a b => LinearMap.ext fun c => inj (by
        rw [Module.End.mul_apply, hL, hL, hL, mul_comm, act.mul, Category.assoc]) }
    fun a b => LinearMap.ext fun c => inj ?_, hL⟩
  change prodPts (L (a + b) c) v = prodPts (L a c + L b c) v
  rw [prodPts_add hv.1, hL, hL, hL, act.add, MonObj.comp_mul]

variable {R' : Type} [CommRing R'] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
  {v' : Fin n → (epsR R' ⟶ G')} {f : R →+* R'} {φ : G'.left ⟶ G.left}

omit [IsCommMonObj G] [IsCommMonObj G'] in

theorem prodPts_left (h : IsGrpPullback G' G (spMap f) φ)
    (hv' : ∀ i, (v' i).left ≫ φ = spMap (dualMapR f) ≫ (v i).left) (c : Fin n → R) :
    (prodPts (f ∘ c) v').left ≫ φ = spMap (dualMapR f) ≫ (prodPts c v).left := by
  let U : Over.mk ((epsR R').hom ≫ spMap f) ⟶ epsR R := Over.homMk (spMap (dualMapR f)) (by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    ext a <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
  have e : pushHom h (epsR R') (prodPts (f ∘ c) v') = preHom U (prodPts c v) := by
    rw [prodPts, prodPts, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext i
    refine Over.OverMorphism.ext ?_
    change (spMap (epsScaleR (f (c i))) ≫ (v' i).left) ≫ φ =
      spMap (dualMapR f) ≫ spMap (epsScaleR (c i)) ≫ (v i).left
    rw [Category.assoc, hv', ← Category.assoc, ← Category.assoc]
    congr 1
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    ext a <;> simp [dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  exact congrArg (fun z => z.left) e

theorem action_baseChange (h : IsGrpPullback G' G (spMap f) φ) (hb : IsLieBasis v')
    (hv' : ∀ i, (v' i).left ≫ φ = spMap (dualMapR f) ≫ (v i).left)
    {O : Type} [CommRing O] {act : OAct O G} {act' : OAct O G'}
    (ha : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left)
    {ρ : O →+* Module.End R (Fin n → R)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ act.act a)
    {ρ' : O →+* Module.End R' (Fin n → R')}
    (hρ' : ∀ a c, prodPts (ρ' a c) v' = prodPts c v' ≫ act'.act a) (a : O) (c : Fin n → R) :
    f ∘ ρ a c = ρ' a (f ∘ c) := by
  refine prodPts_injective hb (Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  dsimp only
  rw [hρ', prodPts_left h hv', hρ, Over.comp_left, Over.comp_left, Category.assoc, ha,
    ← Category.assoc, ← Category.assoc, prodPts_left h hv']

end Coordinates

section Field

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD)

theorem finrank_of_lieMult {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [Field k]
    {G' : Over (Sp k)} [GrpObj G'] [IsCommMonObj G'] {x : Sp k ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x φ) {n : ℕ} {v : Fin n → (epsR k ⟶ G')} (hv : IsLieBasis v)
    {O : Type} [CommRing O] {act : OAct O G} {act' : OAct O G'}
    (ha : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left)
    {ρ : O →+* Module.End k (Fin n → k)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ act'.act a)
    {τ : O →+* k} {N : ℕ} (hN : LieMult act x τ N) :
    Module.finrank k (EigenSplit.eigenSub ρ τ) = N := by
  have hN' : LieMult act' (𝟙 _) τ N :=
    (LiePull.lieMult_pull O _ _ G G' x φ act act' h ha k (𝟙 _) τ N).2 (by rwa [Category.id_comp])
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ G') ≃* (epsR k ⟶ G') :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl G')).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ G').left = η[G'].left := Category.id_comp _
  obtain ⟨w, hw, H⟩ := LiePull.basis_transport e (P := IsLieEigen act' (𝟙 _) τ)
    (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (Q := fun w => IsTangent w ∧ ∀ a, w ≫ act'.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl))
    (fun c u v => by rw [he, he]; rfl) N hN'
  have mem : ∀ c, c ∈ EigenSplit.eigenSub ρ τ ↔
      ∀ a, prodPts c v ≫ act'.act a = Chart.spMap (scaleD (τ a)) ≫ prodPts c v := fun c => by
    rw [EigenSplit.mem_eigenSub]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← prodPts_smul]
    exact (prodPts_injective hv).eq_iff.symm
  choose b hb using fun i => exists_prodPts hv (hw i).1
  obtain rfl : w = fun i => prodPts (b i) v := (funext hb).symm
  let b' : Fin N → EigenSplit.eigenSub ρ τ := fun i => ⟨b i, (mem _).2 (hw i).2⟩
  have key : ∀ c : EigenSplit.eigenSub ρ τ, ∃! d, Fintype.linearCombination k b' d = c := fun c => by
    refine (existsUnique_congr fun d => ?_).1 (H _ ⟨isTangent_prodPts hv.1 c, (mem _).1 c.2⟩)
    refine (Chart.isLieComb_iff d _ _).trans ?_
    rw [prodPts_prodPts hv.1, Subtype.ext_iff, Fintype.linearCombination_apply, eq_comm]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    exact (prodPts_injective hv).eq_iff
  rw [← (LinearEquiv.ofBijective _ ((Function.bijective_iff_existsUnique _).2 key)).finrank_eq,
    Module.finrank_fin_fun]

end Field

end GlobalTheory.LieEigen

namespace GlobalTheory

open LieEigen in

theorem exists_isLieBasis_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ (R : Type) [CommRing R] (j : c.F →+* R) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (n : ℕ) (v₀ : Fin n → (epsR R ⟶ o.t.G)), IsLieBasis v₀ → ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal, ∀ (t' : SAB H (Sp (Localization.Away r))), Nonempty (SABMap t' o.t (spMap (algebraMap R (Localization.Away r)))) → ∃ v : Fin g → (epsR (Localization.Away r) ⟶ t'.G), (IsLieBasis v ∧ ∀ i a, (v i ≫ t'.act.act a).left = spMap (epsScaleR (algebraMap R (Localization.Away r) (j ⟨ty i (a : E), c.conj (ty i) a⟩))) ≫ (v i).left) := by
  intro E _ _ _ H D l c g ty hty R _ j o n v₀ hv₀ p
  let σ₀ : (E →+* ℂ) → 𝓞 E →+* c.F := fun τ =>
    (τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E)
  have hσ₀ : Function.Injective σ₀ := fun τ τ' h =>
    (EigenSplit.isSplitting_complex E).injective
      (RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a))
  have hσ : EigenSplit.IsSplitting fun τ => j.comp (σ₀ τ) :=
    EigenSplit.isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) j (by
      simpa using (EigenSplit.isUnit_discr_of_charZero (E := E) c.F).map j)
  obtain ⟨ρ, hρ⟩ := exists_action hv₀ o.t.act
  let k := AlgebraicClosure p.asIdeal.ResidueField
  let f : R →+* k := (algebraMap p.asIdeal.ResidueField k).comp (algebraMap R _)
  have := (IsSemiAbelian.pullback (spMap f) o.t.G o.t.semi).comm
  have hk := isGrpPullback_pullback o.t.G (spMap f)
  obtain ⟨vk, hvk, hvk'⟩ := exists_isLieBasis_baseChange R k f _ _ _ hk o.t.semi.smooth n v₀ hv₀
  let actk := OAct.pullback (spMap f) o.t.G o.t.act
  have hak : ∀ a, (actk.act a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (o.t.act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  obtain ⟨ρk, hρk⟩ := exists_action hvk actk
  obtain ⟨hdet, -⟩ := o.geom k (spMap f)
    ((f.comp j).comp (IntermediateField.inclusion c.le).toRingHom)
    (((congrArg (spMap f ≫ ·) (Spec.map_comp _ _).symm).trans (Spec.map_comp _ _).symm))
  have hrt : ∀ τ : E →+* ℂ, f.comp (j.comp (σ₀ τ)) H.rt =
      (f.comp j).comp (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ ↔
        τ (H.rt : E) = H.rt0 := fun τ =>
    (f.comp j).injective.eq_iff.trans Subtype.ext_iff
  obtain ⟨x, hx, b, hb⟩ := exists_eigenvectors hσ ρ f ρk
    (action_baseChange hk hvk hvk' hak hρ hρk) ty fun τ => by
      by_cases h : τ (H.rt : E) = H.rt0
      · rw [(hty τ).1 h]
        exact finrank_of_lieMult hk hvk hak hρk ((hdet _).1 ((hrt τ).2 h))
      · rw [(hty τ).2 h]
        exact finrank_of_lieMult hk hvk hak hρk ((hdet _).2 (mt (hrt τ).1 h))
  obtain ⟨r, hr, H⟩ := exists_basis_of_isUnit f x b hb
  refine ⟨r, fun h => hr ?_, fun t' ⟨m⟩ => ?_⟩
  · rw [RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
  obtain ⟨b', hb'⟩ := H _ (algebraMap R (Localization.Away r))
    (IsLocalization.Away.algebraMap_isUnit r)
  obtain ⟨v', hv', e'⟩ := exists_isLieBasis_baseChange R _ _ _ _ _ m.cart o.t.semi.smooth n v₀ hv₀
  obtain ⟨ρ', hρ'⟩ := exists_action hv' t'.act
  refine ⟨_, isLieBasis_prodPts hv' b', fun i a => ?_⟩
  rw [← hρ', hb', ← action_baseChange m.cart hv' e' m.act hρ hρ',
    EigenSplit.mem_eigenSub.1 (hx i) a]
  refine Eq.trans ?_ (congrArg (fun z => z.left) (prodPts_smul (v := v') _ _))
  congr 2
  funext s
  exact map_mul _ _ _

end GlobalTheory
