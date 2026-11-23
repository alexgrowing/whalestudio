import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldOfTangentVectorOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFields

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem dualMapR_eq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : Chart.dualMapR f = dualMap f :=
  RingHom.ext fun z => by ext <;> simp [dualMap, Chart.dualMapR]

theorem one_left {S : Scheme.{0}} (X G : Over S) [GrpObj G] : (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  rw [Hom.one_def]; rfl

theorem red_of_isTr {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]
    {φ : R →+* S} {g : Sp S ⟶ G.left} {v : TanM (𝟙 (Sp R)) G} {w : Sp (DualNumber S) ⟶ G.left}
    (hg : g ≫ G.hom = spMap φ) (h : IsTr G φ g v w) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := h
  have e0 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [sp_comp]
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact Spec.map_id _
  let red : Over.mk (g ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom = g ≫ G.hom
      rw [← Category.assoc, e0, Category.id_comp])
  have ef : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    exact RingHom.ext fun z => by simp [dualMap]
  have hv : red ≫ v' = 1 := by
    apply Over.OverMorphism.ext
    have hr := congrArg (fun q => q.left) (GlobalTheory.InvFieldBase.redPt_tv G v)
    simp only [Over.comp_left] at hr
    rw [Over.comp_left, one_left, h₂, ← Category.assoc]
    change (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ _ = _
    rw [sp_comp, ef, ← sp_comp, Category.assoc]
    change spMap φ ≫ ((GlobalTheory.InvFieldBase.redPt R).left ≫ (tv v).left) = _
    rw [hr, one_left]
    change spMap φ ≫ 𝟙 _ ≫ _ = (g ≫ G.hom) ≫ _
    rw [Category.id_comp, hg]
  have k := congrArg (fun q => q.left) (MonObj.comp_mul red g' v')
  simp only [hv, _root_.mul_one, Over.comp_left] at k
  change red.left ≫ _ = g
  rw [k, h₁, ← Category.assoc]
  change (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S))) ≫ g = g
  rw [e0, Category.id_comp]

theorem isTr_push {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left)
    (hm : IsGrpPullback A G (spMap x₀) m) (w₀ : TanM (𝟙 (Sp R)) G) (v : TanM (𝟙 (Sp K)) A)
    (hv : (tv v).left ≫ m = spMap (dualMap x₀) ≫ (tv w₀).left) {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (y : Sp (DualNumber B) ⟶ A.left) (hy : IsTr A φ x v y) :
    IsTr G (φ.comp x₀) (x ≫ m) w₀ (y ≫ m) := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := hy
  obtain ⟨p, q, hp, hq, hpq⟩ := GlobalTheory.CechKS.exists_mul_of_isGrpPullback hm (tEpsG (x ≫ A.hom)) g' v'
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ G.hom) (by
      change _ = (spMap (algebraMap B (DualNumber B)) ≫ x ≫ A.hom) ≫ spMap x₀
      rw [Category.assoc x m, hm.1.w]
      simp only [Category.assoc])
  refine ⟨p, q, ?_, ?_, hpq⟩
  · simp only [hp, h₁, Category.assoc]
  · rw [hq, h₂, Category.assoc (spMap (dualMap φ)), hv, ← Category.assoc, sp_comp, dualMap_comp]

def epsOf {L : Type} [CommRing L] (D : L → L) (h1 : D 1 = 0) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = x * D y + y * D x) : L →+* DualNumber L where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (D s)
  map_one' := by ext <;> simp [h1]
  map_zero' := by
    have h0 : D 0 = 0 := by have := ha 0 0; simp at this; exact this
    ext <;> simp [h0]
  map_add' a b := by ext <;> simp [ha]
  map_mul' a b := by ext <;> simp [hm]; ring

theorem eq_of_isTr {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {v : TanM (𝟙 (Sp R)) G} {dd : Fld G.left} (hd : IsInv G v dd) {L : Type} [CommRing L] (φ : R →+* L)
    (y : Sp L ⟶ G.left) (hy : y ≫ G.hom = spMap φ) (D : L → L) (h1 : D 1 = 0) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = x * D y + y * D x) (U : G.left.Opens) (hU : IsAffineOpen U)
    (hyU : ⊤ ≤ y ⁻¹ᵁ U) (hD : ∀ f, valR y U (dd U f) = D (valR y U f)) {w : Sp (DualNumber L) ⟶ G.left}
    (hw : IsTr G φ y v w) : w = spMap (epsOf D h1 ha hm) ≫ y := by
  have r1 := red_of_isTr hy hw
  have e1 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ spMap (epsOf D h1 ha hm) = 𝟙 _ := by
    rw [sp_comp]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (epsOf D h1 ha hm) = RingHom.id L := by
      ext r; simp [epsOf]
    rw [this]; exact Spec.map_id _
  have r2 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ (spMap (epsOf D h1 ha hm) ≫ y) = y := by
    rw [← Category.assoc, e1, Category.id_comp]
  have hwU := GlobalTheory.CechKS.le_preimage_of_red r1 hyU
  refine GlobalTheory.Points.ext_of_valR hU hwU (GlobalTheory.CechKS.le_preimage_of_red r2 hyU) fun f => ?_
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hyU]
  have h0 := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom L L L).toRingHom w U hwU f
  rw [r1] at h0
  ext
  · rw [h0]; simp [epsOf]
  · rw [hd.2 L φ y w U f hy hyU hw, hD]; simp [epsOf]

theorem exists_affine {Ω : Type} [CommRing Ω] [IsLocalRing Ω] {X : Scheme.{0}} (x : Sp Ω ⟶ X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show x.base (IsLocalRing.closedPoint Ω) ∈ (⊤ : X.Opens) from trivial)
  refine ⟨U, hU, fun p _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint (R := Ω) p).map x.base.hom.continuous).mem_open U.isOpen hx

theorem exists_basis_bc {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left)
    (hm : IsGrpPullback A G (spMap x₀) m) (hs : Smooth G.hom) {n : ℕ}
    (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) :
    ∃ v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) A),
      ∀ a, (tv (v a)).left ≫ m = spMap (dualMap x₀) ≫ (tv (v' a)).left := by
  obtain ⟨u', hu', hu'l⟩ := GlobalTheory.Heat.CoeffWt.exists_isLieBasis v'
  obtain ⟨u, hu, hul⟩ := GlobalTheory.exists_isLieBasis_baseChange R K x₀ G A m hm hs n u' hu'
  have h := GlobalTheory.Heat.CoeffWt.isGrpPullback_self A
  let b : Fin n → TanM (𝟙 (Sp K)) A := fun j =>
    PullbackSections.mkT (pushHom h (epsR K) (u j)) ((PullbackSections.isTangent_iff h _).1 (hu.1 j))
  have ts : ∀ f : Fin n → TanM (𝟙 (Sp K)) A, tv (∑ i, f i) = ∏ i, tv (f i) := fun f => by
    simp only [tv, toMul_sum, Subgroup.val_finset_prod]
  have hcomb : ∀ (c : Fin n → K) (w : epsR K ⟶ A), IsLieComb c u w ↔
      pushHom h (epsR K) w = tv (∑ i, c i • b i) := fun c w => by
    rw [PullbackSections.isLieComb_iff h, ts]
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination K b) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact PullbackSections.tv_mem W)
    refine (existsUnique_congr fun c => ?_).1 (hu.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (PullbackSections.tanM_ext e).symm, fun e => by rw [e]⟩
  refine ⟨(Pi.basisFun K (Fin n)).map (LinearEquiv.ofBijective _ hbij), fun a => ?_⟩
  have e : (Pi.basisFun K (Fin n)).map (LinearEquiv.ofBijective _ hbij) a = b a := by
    simp [Module.Basis.map_apply, Fintype.linearCombination_apply_single]
  rw [e]
  change ((u a).left ≫ 𝟙 _) ≫ m = _
  rw [Category.comp_id, hul a, hu'l a, dualMapR_eq]

theorem der_frac {R : Type} [CommRing R] [IsDomain R] {L : Type} [Field L] (ψ : FractionRing R →+* L)
    (D : L → L) (hl : ∀ x y, D (x * y) = x * D y + y * D x) (h : ∀ r, D (ψ (algebraMap R (FractionRing R) r)) = 0)
    (k : FractionRing R) :
    D (ψ k) = 0 := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hy0 : algebraMap R (FractionRing R) y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hψ0 : ψ (algebraMap R (FractionRing R) y) ≠ 0 := (map_ne_zero ψ).2 hy0
  have e : ψ (algebraMap R (FractionRing R) x / algebraMap R (FractionRing R) y) * ψ (algebraMap R (FractionRing R) y) =
      ψ (algebraMap R (FractionRing R) x) := by rw [← map_mul, div_mul_cancel₀ _ hy0]
  have k2 := congrArg D e
  rw [hl, h, h, mul_zero, zero_add] at k2
  exact (mul_eq_zero.1 k2).resolve_left hψ0

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (v : Module.Basis (Fin n) (FractionRing R) (TanM (𝟙 (Sp (FractionRing R))) P.A.A)) (dd : Fin n → Fld P.A.A.left), (∀ a, IsInv P.A.A (v a) (dd a)) ∧ ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL a (valR ξ O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx' hinv hδ hval _ g _ δL hδL ψ ξ
    hψ hξA hξ _
  have hm : IsGrpPullback P.A.A t.G (spMap (algebraMap R (FractionRing R)))
      (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  obtain ⟨v, hv⟩ := exists_basis_bc (algebraMap R (FractionRing R)) t.G P.A.A _ hm t.semi.smooth v'
  choose dd hdd using fun a => GlobalTheory.InvFieldBase.exists_isInv (FractionRing R) P.A.A (v a)
  refine ⟨v, dd, hdd, fun a O f hO => ?_⟩
  obtain ⟨U, hU, hxU⟩ := exists_affine x'
  have hyU : ⊤ ≤ (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ⁻¹ᵁ U := by
    rw [hξ]
    exact fun p _ => hxU (Set.mem_univ ((spMap (algebraMap Ω (FractionRing Ω))).base p))
  have hyG : (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ≫ t.G.hom =
      spMap (ψ.comp (algebraMap R (FractionRing R))) := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hξA, sp_comp]
  have hl : ∀ x y, δL a (x * y) = x * δL a y + y * δL a x := fun x y => by
    rw [(δL a).leibniz, smul_eq_mul, smul_eq_mul]
  have hDy : ∀ f, valR (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) U (dd' a U f) =
      δL a (valR (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) U f) := by
    intro f
    rw [hξ, GlobalTheory.Points.valR_spMap_comp _ _ _ hxU, GlobalTheory.Points.valR_spMap_comp _ _ _ hxU, hval a U _ hxU, hδL]
  have hc : ∀ k, δL a (ψ k) = 0 := der_frac ψ (δL a) hl fun r => by rw [hψ, hδL, hδ, map_zero]
  have hdual : (dualMap ψ).comp (algebraMap (FractionRing R) (DualNumber (FractionRing R))) =
      (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))).comp ψ := by
    ext k <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let g' : tEpsG (ξ ≫ P.A.A.hom) ⟶ P.A.A :=
    Over.homMk (spMap (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))) ≫ ξ) (Category.assoc _ _ _)
  let w' : tEpsG (ξ ≫ P.A.A.hom) ⟶ P.A.A :=
    Over.homMk (spMap (dualMap ψ) ≫ (tv (v a)).left) (by
      rw [Category.assoc, Over.w (tv (v a)), hξA]
      change spMap (dualMap ψ) ≫ spMap (algebraMap _ _) ≫ 𝟙 _ = spMap _ ≫ spMap ψ
      rw [Category.comp_id, sp_comp, sp_comp, hdual])
  have htr : IsTr P.A.A ψ ξ (v a) (g' * w').left := ⟨g', w', rfl, rfl, rfl⟩
  have key : (g' * w').left = spMap (epsOf (δL a) (δL a).map_one_eq_zero (map_add _) hl) ≫ ξ := by
    refine hm.1.hom_ext ?_ ?_
    · rw [eq_of_isTr (hinv a) _ _ hyG (δL a) (δL a).map_one_eq_zero (map_add _) hl U hU hyU hDy
        (isTr_push _ _ hm (v' a) (v a) (hv a) ψ ξ _ htr), Category.assoc]
    · rw [Over.w (g' * w')]
      change spMap (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))) ≫ ξ ≫ P.A.A.hom =
        (spMap _ ≫ ξ) ≫ P.A.A.hom
      rw [Category.assoc, hξA, sp_comp, sp_comp]
      congr 1
      ext k
      · simp [epsOf, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [epsOf, TrivSqZeroExt.algebraMap_eq_inl, hc]
  rw [← (hdd a).2 (FractionRing Ω) ψ ξ _ O f hξA hO htr, key, GlobalTheory.Points.valR_spMap_comp _ _ _ hO]
  simp [epsOf]

end GlobalTheory.GenFields
