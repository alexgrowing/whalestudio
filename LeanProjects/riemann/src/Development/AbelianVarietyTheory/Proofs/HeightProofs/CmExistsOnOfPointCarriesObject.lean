import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.PhiNeOne
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TensorObjectExistence
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmDatumFormSqrtNegDPurePeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsTenBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.T2SpacePtsOverOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM GlobalTheory.IndefiniteRowSideFullHecke.TensorObjectExistence

noncomputable section
namespace GlobalTheory.CMExistsCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

section Triples

variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem sab_comp {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g)
    (h : g ≫ f = k) : ∃ n : SABMap t'' t k, n.φ = m'.φ ≫ m.φ := by
  subst h
  exact ObjMaps.exists_sab_comp m m'

theorem sab_cancel {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t k)
    (h : g ≫ f = k) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst h
  exact ObjMaps.exists_sab_cancel m n

theorem sab_lbIso {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem exists_ptEquiv {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {x' : T ⟶ S'} {x : T ⟶ S} (h : x' ≫ f = x) :
    ∃ p : (Over.mk x' ⟶ t'.G) ≃* (Over.mk x ⟶ t.G), ∀ u, (p u).left = u.left ≫ m.φ :=
  LiePull.exists_pushEquiv m.cart (Over.mk x') x h.symm

theorem pt_ext {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {u v : T ⟶ t'.G.left} (h₁ : u ≫ m.φ = v ≫ m.φ)
    (h₂ : u ≫ t'.G.hom = v ≫ t'.G.hom) : u = v :=
  m.cart.1.hom_ext h₁ h₂

theorem isExpAt_iff {f : S' ⟶ S} (m : SABMap t' t f) {x' : Sp ℂ ⟶ S'} {x : Sp ℂ ⟶ S} (h : x' ≫ f = x)
    {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    {e' : (Fin g → ℂ) → (Over.mk x' ⟶ t'.G)} {e : (Fin g → ℂ) → (Over.mk x ⟶ t.G)}
    (he : ∀ z, (e z).left = (e' z).left ≫ m.φ) : IsExpAt t' x' D ty Pe e' ↔ IsExpAt t x D ty Pe e := by
  subst h
  obtain ⟨p, hp⟩ := exists_ptEquiv m (x' := x') rfl
  obtain rfl : e = fun z => p (e' z) := funext fun z => Over.OverMorphism.ext ((he z).trans (hp _).symm)
  have hact : ∀ (u : Over.mk x' ⟶ t'.G) a, p (u ≫ t'.act.act a) = p u ≫ t.act.act a := fun u a => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hp, hp, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  refine and_congr_right fun _ => and_congr ⟨fun hh => ?_, fun hh => ?_⟩ (and_congr ?_ (and_congr ?_ (and_congr ?_
    (and_congr ?_ ?_))))
  · simp only [hp]
    exact HolFibre.isHolTo_comp hh m.φ
  · simp only [hp] at hh
    refine HolFibre.isHolTo_of_isPullback m.cart.1 hh ?_
    have : (fun w => (e' w).left ≫ t'.G.hom) = fun _ => x' := funext fun w => Over.w (e' w)
    rw [this]
    exact HolFibre.isHolTo_const isOpen_univ x'
  · simp only [← map_mul, EmbeddingLike.apply_eq_iff_eq]
  · exact (EquivLike.comp_surjective e' p).symm
  · simp only [EmbeddingLike.map_eq_one_iff]
  · simp only [← hact, EmbeddingLike.apply_eq_iff_eq]
  · refine forall_congr' fun k => forall_congr' fun a => forall_congr' fun b => forall_congr' fun c =>
      forall_congr' fun _ => forall_congr' fun _ => ?_
    exact weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ t.PP.isLB t'.PP.isLB m.cart (sab_lbIso m) (Over.mk x') k _ _ _ _ _
      (hp _) (hp _)

theorem exists_lift {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {x' : T ⟶ S'} {x : T ⟶ S} (h : x' ≫ f = x)
    {V : Type} (e : V → (Over.mk x ⟶ t.G)) :
    ∃ e' : V → (Over.mk x' ⟶ t'.G), ∀ z, (e z).left = (e' z).left ≫ m.φ := by
  obtain ⟨p, hp⟩ := exists_ptEquiv m h
  exact ⟨fun z => p.symm (e z), fun z => by rw [← hp, p.apply_symm_apply]⟩

theorem exists_push {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {x' : T ⟶ S'} {x : T ⟶ S} (h : x' ≫ f = x)
    {V : Type} (e' : V → (Over.mk x' ⟶ t'.G)) :
    ∃ e : V → (Over.mk x ⟶ t.G), ∀ z, (e z).left = (e' z).left ≫ m.φ := by
  obtain ⟨p, hp⟩ := exists_ptEquiv m h
  exact ⟨fun z => p (e' z), fun z => hp _⟩

end Triples

section Extend

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem spMap_int (j : K →+* K') {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : σ'.comp j = σ) :
    spMap (σ'.comp (algebraMap (𝓞 K') K')) ≫ spMap (RingOfIntegers.mapRingHom j) =
      spMap (σ.comp (algebraMap (𝓞 K) K)) := by
  rw [spMap_comp', ← h]
  rfl

theorem exists_cmObj_extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ p q) (j : K →+* K') (σ' : K' →+* ℂ)
    (h : σ'.comp j = σ) :
    ∃ (X' : CMObj H K' (RingOfIntegers.mapRingHom j ρ) σ' p q)
      (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
      (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
      X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := by
  set f := RingOfIntegers.mapRingHom j with hf
  have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
  choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
  obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
  have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
  choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
  have hpt := spMap_int j h
  refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K' j X.split |>.1
            ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
            A := A', B := B'
            typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
            typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
            typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
            hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
  · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
    have e := congrArg Over.Hom.left ((X.lin i).2 c)
    simp only [Over.comp_left] at e
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
      (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
  · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
    choose pA hA using fun b => exists_ptEquiv (a b) hpt
    obtain ⟨x, hx⟩ := X.onto (pB y)
    refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
    rw [hx, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    apply Over.OverMorphism.ext
    simp only [Function.comp_apply]
    rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
    erw [hφ]
    rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
  · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
      (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
      ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
    rw [hpt]
    exact X.weil i

end Extend

section Conclusions

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Pe : D'.La →+ (Fin g → ℂ)} {hP : IsPeriod D' ty Pe}

def SubfieldConcl (Z : CMLat hP D.p D.q) (x : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G))
    (k : IntermediateField ℚ ℂ) : Prop :=
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ρ : 𝓞 K₁)
    (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁))
    (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (gA : Bool → ℕ) (tyA : ∀ b, Fin (gA b) → (E →+* ℂ)) (PA : ∀ b, (Z.D₁ b).La →+ (Fin (gA b) → ℂ))
    (eA : ∀ b, (Fin (gA b) → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ (X.A b).t.G))
    (F : ∀ j : Fin D.p ⊕ Fin D.q, (Fin (gA j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    k ≤ K₁ ∧ ((ρ : K₁) : ℂ) = H.rt0 ∧ X.hh = Z.hh ∧
    y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = x ∧
    (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (tyA b) ∧ IsExp (X.A b) _ (Z.D₁ b) (tyA b) (PA b) (eA b)) ∧
    (∀ j a, F j (PA _ a) = Pe (Z.f j a)) ∧
    ∀ (j : Fin D.p ⊕ Fin D.q) (z : Fin (gA j.isLeft) → ℂ) (w : Sp ℂ ⟶ t₀.G.left), w ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) →
      w ≫ m'.φ = (eA _ z ≫ X.φ j).left → w ≫ m.φ = (e (F j z)).left

def EmbeddedConcl (Z : CMLat hP D.p D.q) (x : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G))
    {K' : Type} [Field K'] [NumberField K'] (κ : KA l →+* K') (σ' : K' →+* ℂ) : Prop :=
  ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (j : K' →+* K₁) (σ₁ : K₁ →+* ℂ) (ρ : 𝓞 K₁)
    (X : CMObj H K₁ ρ σ₁ D.p D.q) (y : Sp K₁ ⟶ Xo.X) (o : Obj D l (baseKA l) (spMap (j.comp κ)))
    (mU : ObjMap o Xo.univ y) (mB : SABMap o.t X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (eB : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K₁) K₁))) ⟶ X.B.t.G)),
    σ₁.comp j = σ' ∧ (ρ : K₁) = j (κ (baseKA l).ρ) ∧ y ≫ Xo.s = spMap (j.comp κ) ∧ spMap σ₁ ≫ y = x ∧
    (∀ z, ∃ w : Over.mk (spMap σ₁) ⟶ o.t.G,
      w.left ≫ mU.toSABMap.φ = (e z).left ∧ w.left ≫ mB.φ = (eB z).left) ∧
    TiedToLattices Z X eB

theorem exists_image {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) :
    ∃ (K₂ : IntermediateField ℚ ℂ) (_ : NumberField K₂) (j : K →+* K₂),
      (algebraMap K₂ ℂ).comp j = σ ∧ ∀ z : ℂ, z ∈ K₂ ↔ z ∈ Set.range σ := by
  let e := σ.toRatAlgHom.equivFieldRange
  haveI : FiniteDimensional ℚ σ.toRatAlgHom.fieldRange := e.toLinearEquiv.finiteDimensional
  exact ⟨σ.toRatAlgHom.fieldRange, ⟨⟩, e.toRingEquiv.toRingHom, RingHom.ext fun _ => rfl, fun z => Iff.rfl⟩

variable {Xo} {Z : CMLat hP D.p D.q} {x : Sp ℂ ⟶ Xo.X} {e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)}
  {K' : Type} [Field K'] [NumberField K'] {κ : KA l →+* K'} {σ' : K' →+* ℂ} {k : IntermediateField ℚ ℂ}

theorem subfieldConcl_of_embeddedConcl (hκ : σ'.comp κ = algebraMap (KA l) ℂ) (hk : ∀ z ∈ k, z ∈ Set.range σ')
    (h : EmbeddedConcl Xo Z x e κ σ') : SubfieldConcl Xo Z x e k := by
  obtain ⟨K₁, _, _, j, σ₁, ρ, X, y, o, mU, mB, eB, hj, hρ, hy, hx, hw, -, hhh, gA, tyA, PA, eA, hA, hF⟩ := h
  choose F hF hφ using hF
  obtain ⟨K₂, _, i, hi, hK₂⟩ := exists_image σ₁
  have hle : ∀ a, σ' a ∈ K₂ := fun a => (hK₂ _).2 ⟨j a, by rw [← hj]; rfl⟩
  have hKA : KA l ≤ K₂ := fun z hz => by
    have := hle (κ ⟨z, hz⟩)
    rwa [← RingHom.comp_apply, hκ] at this
  obtain ⟨X', a, mb, hh', hφ'⟩ := exists_cmObj_extend X i (algebraMap K₂ ℂ) hi
  obtain ⟨T₀, m', -⟩ := PAT.exists_pullback E H _ _ (spMap (algebraMap (𝓞 K₂) K₂)) X'.B
  obtain ⟨n₁, hn₁⟩ := sab_comp mb m' rfl
  obtain ⟨n, hn⟩ := sab_cancel (g := spMap i) mB n₁ (by rw [spMap_comp', spMap_comp']; rfl)
  obtain ⟨m, hm⟩ := sab_comp mU.toSABMap n rfl
  have hpt := spMap_int i hi
  choose eA' heA' using fun b => exists_lift (a b) hpt (eA b)
  have hσ : spMap (algebraMap K₂ ℂ) ≫ spMap i = spMap σ₁ := by rw [spMap_comp', hi]
  refine ⟨K₂, inferInstance, hKA, _, X', spMap i ≫ y, T₀.t, m, m', gA, tyA, PA, eA', F, fun z hz => ?_, ?_,
    hh'.trans hhh, ?_, ?_, fun b => ⟨(hA b).1, (isExpAt_iff (a b) hpt (heA' b)).2 (hA b).2⟩, hF, fun s z w hw₁ hw₂ => ?_⟩
  · obtain ⟨b, rfl⟩ := hk z hz
    exact hle b
  · show (algebraMap K₂ ℂ).comp i (ρ : K₁) = _
    rw [hi, hρ, ← RingHom.comp_apply, hj, ← RingHom.comp_apply, hκ]
    rfl
  · rw [Category.assoc, hy, spMap_comp']
    congr 1
    ext b
    show (algebraMap K₂ ℂ).comp i (j (κ b)) = _
    rw [hi, ← RingHom.comp_apply, hj, ← RingHom.comp_apply, hκ]
    rfl
  · rw [← Category.assoc, hσ, hx]
  · obtain ⟨v, hv₁, hv₂⟩ := hw (F s z)
    have : w ≫ n.φ = v.left := by
      refine pt_ext mB ?_ ?_
      · rw [Category.assoc, ← hn, hn₁, ← Category.assoc, hw₂, hv₂, ← hφ, Over.comp_left, Over.comp_left,
          Category.assoc, hφ', heA', Category.assoc]
      · rw [Category.assoc, n.cart.1.w, ← Category.assoc, hw₁, hσ]
        exact (Over.w v).symm
    rw [hm, ← Category.assoc, this, hv₁]

theorem embeddedConcl_of_subfieldConcl (hκ : σ'.comp κ = algebraMap (KA l) ℂ) (hk : ∀ a, σ' a ∈ k)
    (he : IsExpAt Xo.univ.t x D' ty Pe e) (h : SubfieldConcl Xo Z x e k) : EmbeddedConcl Xo Z x e κ σ' := by
  obtain ⟨K₁, _, hKA, ρ, X, y, t₀, m, m', gA, tyA, PA, eA, F, hle, hρ, hhh, hy, hx, hA, hF, hφ⟩ := h
  let j : K' →+* K₁ := σ'.codRestrict K₁.toSubfield fun a => hle (hk a)
  have hj : (algebraMap K₁ ℂ).comp j = σ' := RingHom.ext fun _ => rfl
  have hjκ : (IntermediateField.inclusion hKA).toRingHom = j.comp κ :=
    RingHom.ext fun b => Subtype.ext (RingHom.congr_fun hκ b).symm
  rw [hjκ] at hy
  obtain ⟨o, ⟨mU⟩⟩ := ObjPull.objPull_of_pol pol_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s
    (spMap (j.comp κ)) y rfl rfl (by rw [hy, spMap_comp', RingHom.comp_id]) Xo.univ
  obtain ⟨n, hn⟩ := sab_cancel m mU.toSABMap (Category.id_comp y)
  obtain ⟨mB, hmB⟩ := sab_comp m' n (Category.id_comp _)
  obtain ⟨e₀, he₀⟩ := exists_lift mU.toSABMap hx e
  have hpt := spMap_comp' (algebraMap (𝓞 K₁) K₁) (algebraMap K₁ ℂ)
  obtain ⟨eB, heB⟩ := exists_push mB hpt e₀
  refine ⟨K₁, inferInstance, inferInstance, j, algebraMap K₁ ℂ, ρ, X, y, o, mU, mB, eB, hj, ?_, hy, hx,
    fun z => ⟨e₀ z, (he₀ z).symm, (heB z).symm⟩,
    (isExpAt_iff mB hpt heB).1 ((isExpAt_iff mU.toSABMap hx he₀).2 he), hhh, gA, tyA, PA, eA, hA,
    fun s => ⟨F s, hF s, fun z => ?_⟩⟩
  · exact Subtype.ext (hρ.trans (RingHom.congr_fun hκ (baseKA l).ρ).symm)
  · obtain ⟨w, ⟨hw₁, hw₂⟩, -⟩ := ExSt.existsUnique_point (algebraMap K₁ ℂ) m' (eA _ z ≫ X.φ s)
    have : w = (e₀ (F s z)).left ≫ n.φ := by
      refine pt_ext m ?_ ?_
      · rw [hφ s z w hw₁ hw₂, he₀, hn, Category.assoc]
      · rw [hw₁, Category.assoc, n.cart.1.w, Category.comp_id]
        exact (Over.w (e₀ (F s z))).symm
    apply Over.OverMorphism.ext
    rw [← hw₂, this, heB, hmB, Category.assoc]

end Conclusions

section ChangeOfExp

variable {D₁ D₂ : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)}

theorem int_eq_of_exp {a b : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (a : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (b : ℂ) / k)) :
    a = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((a - b).natAbs + 1) (Nat.succ_pos _))
  set k : ℕ := (a - b).natAbs + 1 with hk
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e : ((b - a : ℤ) : ℂ) = ((n * k : ℤ) : ℂ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    field_simp at hn
    push_cast
    linear_combination (2 * Real.pi * Complex.I) * hn
  have e' : b - a = n * k := by exact_mod_cast e
  have : (b - a).natAbs = n.natAbs * k := by rw [e', Int.natAbs_mul, Int.natAbs_natCast]
  rcases Nat.eq_zero_or_pos n.natAbs with h0 | h0
  · rw [h0, zero_mul] at this
    omega
  · have := Nat.mul_le_mul_right k h0
    omega

theorem linear_eq_zero_of_countable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (L : V →ₗ[ℂ] W) {s : Set W} (hs : s.Countable) (h : ∀ v, L v ∈ s) (v : V) : L v = 0 := by
  by_contra hv
  have : (Set.univ : Set ℂ).Countable :=
    Set.countable_of_injective_of_countable_image (f := fun c : ℂ => c • L v) (fun a _ b _ e => smul_left_injective ℂ hv e)
      (hs.mono (by rintro _ ⟨c, -, rfl⟩; simpa using h (c • v)))
  exact not_countable_complex this

theorem countable_la (D : Datum H) : Countable D.La := by
  have := D.fin
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  exact Finsupp.Countable.of_moduleFinite (R := 𝓞 E)

theorem exists_isometry {S : Scheme.{0}} {t : SAB H S} {x : Sp ℂ ⟶ S} {e₁ e₂ : (Fin g → ℂ) → (Over.mk x ⟶ t.G)}
    (h₁ : IsExpAt t x D₁ ty P₁ e₁) (h₂ : IsExpAt t x D₂ ty P₂ e₂) (hd : UnifPoint.IsExp e₂) :
    ∃ (ψ : D₁.La →ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), Function.Surjective ψ ∧
      (∀ a b, D₂.EF (ψ a) (ψ b) = D₁.EF a b) ∧ (∀ a, P₂ (ψ a) = h (P₁ a)) ∧ (∀ z, e₂ (h z) = e₁ z) ∧
      ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := by
  obtain ⟨hP₁, hol₁, add₁, on₁, ker₁, lin₁, w₁⟩ := h₁
  obtain ⟨hP₂, hol₂, add₂, on₂, ker₂, lin₂, w₂⟩ := h₂
  have := t.semi.separated
  have c₁ := countable_la D₁
  have c₂ := countable_la D₂
  let Λ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule P₂.range
  have : DiscreteTopology Λ := hP₂.2.2.1
  have : IsZLattice ℝ Λ := ⟨hP₂.2.2.2.1⟩
  obtain ⟨h, hh⟩ := hd.exists_linearEquiv Λ ker₂ add₁ on₁ hol₁
    ((Set.countable_range P₁).mono fun z hz => (ker₁ z).1 hz)
  have hc : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    let d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := LinearMap.pi fun k => ty k (a : E) • LinearMap.proj k
    refine sub_eq_zero.1 (linear_eq_zero_of_countable (h.toLinearMap ∘ₗ d - d ∘ₗ h.toLinearMap)
      (Set.countable_range P₂) (fun v => (ker₂ _).1 ((UnifPoint.eq_iff_sub_of_add add₂ _ _).1 ?_)) z)
    exact (hh _).trans ((lin₁ a v).trans (((lin₂ a (h v)).trans (by rw [hh])).symm))
  have hz₁ := UnifPoint.map_zero_of_add add₁
  choose ψ hψ using fun a => (ker₂ (h (P₁ a))).1 ((hh _).trans ((ker₁ _).2 ⟨a, rfl⟩))
  refine ⟨⟨⟨ψ, fun a b => hP₂.2.1 (by rw [map_add, hψ, hψ, hψ, map_add, map_add])⟩, fun s a => hP₂.2.1 ?_⟩, h,
    fun b => ?_, fun a b => ?_, hψ, hh, hc⟩
  · rw [hψ, show P₁ (s • a) = _ from funext (hP₁.1 s a), hc]
    funext k
    rw [RingHom.id_apply, hP₂.1, hψ]
  · obtain ⟨a, ha⟩ := (ker₁ (h.symm (P₂ b))).1 (by rw [← hh, h.apply_symm_apply]; exact (ker₂ _).2 ⟨b, rfl⟩)
    exact ⟨a, hP₂.2.1 ((hψ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  · refine int_eq_of_exp fun k hk => ?_
    have u₁ := w₁ k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have u₂ := w₂ k (ψ a) (ψ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hψ, hψ, ← map_smul h, ← map_smul h, hh, hh] at u₂
    exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ x k _ _ _ _ u₂ u₁)

def moveLat {hP₁ : IsPeriod D₁ ty P₁} (hP₂ : IsPeriod D₂ ty P₂) {p q : ℕ} (Z : CMLat hP₁ p q)
    (ψ : D₁.La →ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hs : Function.Surjective ψ)
    (hE : ∀ a b, D₂.EF (ψ a) (ψ b) = D₁.EF a b) (hψ : ∀ a, P₂ (ψ a) = h (P₁ a))
    (hc : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k) : CMLat hP₂ p q where
  D₁ := Z.D₁
  sigP := Z.sigP
  sigM := Z.sigM
  f j := ψ ∘ₗ Z.f j
  pure j a := fun k hk => by
    set ρ : ℂ := if j.isLeft then H.rt0 else -H.rt0
    have e : (fun k => ty k (H.rt : E) * P₁ (Z.f j a) k) = ρ • P₁ (Z.f j a) := funext fun k => by
      by_cases h' : ty k (H.rt : E) = ρ
      · rw [h']; rfl
      · simp [Z.pure j a k h']
    have e' := congrFun (hc H.rt (P₁ (Z.f j a))) k
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul] at e'
    rw [LinearMap.comp_apply, hψ]
    exact (mul_eq_mul_right_iff.1 e').resolve_left (Ne.symm hk)
  hh := Z.hh
  form j a b := (hE _ _).trans (Z.form j a b)
  span := by
    obtain ⟨n, hn, hs'⟩ := Z.span
    refine ⟨n, hn, fun b => ?_⟩
    obtain ⟨a, rfl⟩ := hs b
    obtain ⟨x, hx⟩ := hs' a
    exact ⟨x, by rw [← map_nsmul, hx, map_sum]; rfl⟩

theorem subfieldConcl_of_exp {D : Datum H} {l : Level H} {Xo : Moduli D l} {x : Sp ℂ ⟶ Xo.X}
    {e₁ e₂ : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)} (h₁ : IsExpAt Xo.univ.t x D₁ ty P₁ e₁)
    (h₂ : IsExpAt Xo.univ.t x D₂ ty P₂ e₂) (hd : UnifPoint.IsExp e₂) {k : IntermediateField ℚ ℂ}
    (hc : ∀ Z : CMLat h₂.1 D.p D.q, SubfieldConcl Xo Z x e₂ k) {hP₁ : IsPeriod D₁ ty P₁} (Z : CMLat hP₁ D.p D.q) :
    SubfieldConcl Xo Z x e₁ k := by
  obtain ⟨ψ, h, hs, hE, hψ, he, hl⟩ := exists_isometry h₁ h₂ hd
  obtain ⟨K₁, _, hKA, ρ, X, y, t₀, m, m', gA, tyA, PA, eA, F, hle, hρ, hhh, hy, hx, hA, hF, hφ⟩ :=
    hc (moveLat h₂.1 Z ψ h hs hE hψ hl)
  refine ⟨K₁, inferInstance, hKA, ρ, X, y, t₀, m, m', gA, tyA, PA, eA, fun j => h.symm.toLinearMap ∘ₗ F j, hle, hρ, hhh,
    hy, hx, hA, fun j a => ?_, fun j z w hw₁ hw₂ => ?_⟩
  · exact h.symm_apply_eq.2 ((hF j a).trans (hψ _))
  · rw [hφ j z w hw₁ hw₂, ← he]
    exact congrArg (fun v => (e₂ v).left) (h.apply_symm_apply _).symm

end ChangeOfExp

section Point

theorem embeddedConcl_of_inclusion {D : Datum H} {l : Level H} {Xo : Moduli D l} (hpq : 1 ≤ D.p + D.q) {D' : Datum H}
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D'.La →+ (Fin g → ℂ)} {hP : IsPeriod D' ty Pe} (Z : CMLat hP D.p D.q)
    {K' : Type} [Field K'] [NumberField K'] {σ' : K' →+* ℂ}
    (h : ∀ (κ : KA l →+* K') (x : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)),
      σ'.comp κ = algebraMap (KA l) ℂ → x ≫ Xo.s = spMap (algebraMap (KA l) ℂ) → IsExpAt Xo.univ.t x D' ty Pe e →
      EmbeddedConcl Xo Z x e κ σ')
    {κ : KA l →+* K'} {x : Sp ℂ ⟶ Xo.X} {e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)}
    (hρ : σ' (κ (baseKA l).ρ) = H.rt0) (hx : x ≫ Xo.s = spMap (σ'.comp κ)) (he : IsExpAt Xo.univ.t x D' ty Pe e) :
    EmbeddedConcl Xo Z x e κ σ' := by
  obtain ⟨τ, hτ, hτ'⟩ := LevQuot.exists_fieldAut l (σ'.comp κ) (algebraMap (KA l) ℂ) hρ
  obtain ⟨r, m, -, hr, -⟩ := LevQuot.exists_semiTwist_iso (l := l) hpq { l with A := 1, A_pos := one_pos } rfl rfl rfl Xo τ hτ
  obtain ⟨e', he'⟩ := exists_push m (x' := x) rfl e
  obtain ⟨K₁, _, _, j, σ₁, ρ, X, y', o', mU', mB', eB, hj, hρ₁, hy, hx', hw, hT⟩ :=
    h (κ.comp τ.toRingHom) (x ≫ r.hom) e' hτ' (by rw [Category.assoc, hr, ← Category.assoc, hx, spMap_comp', hτ'])
      ((isExpAt_iff m rfl he').1 he)
  have hid : spMap τ.toRingHom ≫ spMap τ.symm.toRingHom = 𝟙 _ := by
    rw [spMap_comp', RingEquiv.toRingHom_comp_symm_toRingHom]
    exact Spec.map_id _
  have hyr : (y' ≫ r.inv) ≫ r.hom = y' := by simp
  have hs : (y' ≫ r.inv) ≫ Xo.s = spMap (j.comp κ) := by
    rw [← Category.comp_id Xo.s, ← hid, ← Category.assoc Xo.s, ← hr, Category.assoc r.hom, ← Category.assoc, hyr,
      ← Category.assoc, hy, spMap_comp', RingHom.comp_assoc, RingHom.comp_assoc,
      RingEquiv.toRingHom_comp_symm_toRingHom, RingHom.comp_id]
  have hxy : spMap σ₁ ≫ y' ≫ r.inv = x := by rw [← Category.assoc, hx']; simp
  obtain ⟨o, ⟨mU⟩⟩ := ObjPull.objPull_of_pol pol_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s
    (spMap (j.comp κ)) (y' ≫ r.inv) rfl rfl (by rw [hs, spMap_comp', RingHom.comp_id]) Xo.univ
  obtain ⟨n₁, hn₁⟩ := sab_comp m mU.toSABMap hyr
  obtain ⟨n, hn⟩ := sab_cancel mU'.toSABMap n₁ (Category.id_comp y')
  obtain ⟨mB, hmB⟩ := sab_comp mB' n (Category.id_comp _)
  obtain ⟨e₀, he₀⟩ := exists_lift mU.toSABMap hxy e
  refine ⟨K₁, inferInstance, inferInstance, j, σ₁, ρ, X, y' ≫ r.inv, o, mU, mB, eB, hj,
    hρ₁.trans (congrArg (fun a => j (κ a)) hτ), hs, hxy, fun z => ⟨e₀ z, (he₀ z).symm, ?_⟩, hT⟩
  obtain ⟨w, hw₁, hw₂⟩ := hw z
  have : (e₀ z).left ≫ n.φ = w.left := by
    refine pt_ext mU'.toSABMap ?_ ?_
    · rw [Category.assoc, ← hn, hn₁, ← Category.assoc, ← he₀, ← he', hw₁]
    · rw [Category.assoc, n.cart.1.w, Category.comp_id]
      exact (Over.w (e₀ z)).trans (Over.w w).symm
  rw [hmB, ← Category.assoc, this, hw₂]

def CMExistsOn (P : ℕ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → P (D.p + D.q) →
    SubfieldConcl Xo Z (FU.u i Pe) (FU.ex i Pe) k

theorem cmExistsSt_iff : CMExistsSt ↔ CMExistsOn (1 ≤ ·) ∧ CMExistsOn (· = 0) :=
  ⟨fun h => ⟨fun E _ _ _ H D l Xo g ty FU i Pe hP Z k hk _ => h E H D l Xo g ty FU i Pe hP Z k hk,
      fun E _ _ _ H D l Xo g ty FU i Pe hP Z k hk _ => h E H D l Xo g ty FU i Pe hP Z k hk⟩,
    fun h E _ _ _ H D l Xo g ty FU i Pe hP Z k hk => (Nat.eq_zero_or_pos (D.p + D.q)).elim
      (h.2 E H D l Xo g ty FU i Pe hP Z k hk) (h.1 E H D l Xo g ty FU i Pe hP Z k hk)⟩

theorem cmExistsOn_of_pointCarriesObject (h : PointCarriesObject) : CMExistsOn (1 ≤ ·) := by
  intro E _ _ _ H D l Xo g ty FU i Pe hP Z k hk hpq
  have := LevQuot.finiteDimensional_field l
  have : NumberField (k ⊔ KA l : IntermediateField ℚ ℂ) := ⟨⟩
  have hty := PeriodCompare.isTypeFn_of_isPeriod hP
  rw [(FU.sig i).1, (FU.sig i).2] at hty
  exact subfieldConcl_of_embeddedConcl (σ' := algebraMap (k ⊔ KA l : IntermediateField ℚ ℂ) ℂ)
    (κ := (IntermediateField.inclusion le_sup_right).toRingHom) rfl
    (fun z hz => ⟨⟨z, (le_sup_left : k ≤ k ⊔ KA l) hz⟩, rfl⟩)
    (h E H D l Xo _ _ _ _ _ g ty Pe hP _ Z hpq rfl (FU.over_σ i Pe hP) (FU.sig i).1 (FU.sig i).2 hty
      (isExpAt_of_familyUnif FU i Pe hP))

theorem pointCarriesObject_of_cmExistsOn (hU : N1c) (h : CMExistsOn (1 ≤ ·)) : PointCarriesObject := by
  intro E _ _ _ H D l Xo K' _ _ κ σ' x D' g ty Pe hP e Z hpq hρ hx _ _ hty he
  refine embeddedConcl_of_inclusion hpq Z (fun κ x e hκ hx he => ?_) hρ hx he
  obtain ⟨FU⟩ := hU E H D l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty
  obtain ⟨i, P, hP', rfl⟩ := FU.onto x hx
  obtain ⟨k, _, -, -, hk⟩ := exists_image σ'
  have he' := isExpAt_of_familyUnif FU i P hP'
  exact embeddedConcl_of_subfieldConcl hκ (fun a => (hk _).2 ⟨a, rfl⟩) he
    (subfieldConcl_of_exp he he' ⟨he'.2.2.1, he'.2.2.2.1, he'.2.1, FU.ex_diff i P hP'⟩
      (fun Z' => h E H D l Xo g ty FU i P hP' Z' k inferInstance hpq) Z)

theorem cmExistsOn_iff (hU : N1c) : CMExistsOn (1 ≤ ·) ↔ PointCarriesObject :=
  ⟨pointCarriesObject_of_cmExistsOn hU, cmExistsOn_of_pointCarriesObject⟩

end Point

section Tensor

def PrincipalCurve : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (σ : M →+* ℂ) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω),
      C.IsPrincipalAt (σ.comp (algebraMap (𝓞 M) M))

def TensorForSomeCurve : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → D.p = 0 ∨ D.q = 0 →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (ε : ℤˣ) (h : D.La → D.La → OK H)
      (T : PAT H (Sp (𝓞 M))) (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (β : 𝓞 M →+* K₁) (κ : KA l →+* K₁)
      (σ₁ : K₁ →+* ℂ) (o : Obj D l (baseKA l) (spMap κ)),
      σ₁.comp κ = algebraMap (KA l) ℂ ∧ (∀ z ∈ k, z ∈ Set.range σ₁) ∧ C.IsPrincipalAt (σ₁.comp β) ∧
      IsKForm D ε h ∧ Nonempty (IsTen C D h T) ∧ Nonempty (SABMap o.t T.t (spMap β))

theorem tensorObjSt_iff_some : TensorObjSt ↔ TensorForSomeCurve := by
  refine ⟨fun hA E _ _ _ H D l k hk hD => ?_, fun hB E _ _ _ H D l k hk hD => ?_⟩
  · obtain ⟨K₁, _, hKA, ω, C, ε, h, T, o, hle, hC, hh, hT, hm⟩ := hA E H D l k hk hD
    exact ⟨K₁, inferInstance, inferInstance, ω, C, ε, h, T, K₁, inferInstance, inferInstance, _, _, algebraMap K₁ ℂ, o,
      rfl, fun z hz => ⟨⟨z, hle hz⟩, rfl⟩, hC, hh, hT, hm⟩
  · obtain ⟨M, _, _, ω, C, ε, h, T, K₁, _, _, β, κ, σ₁, o, hκ, hle, hC, hh, ⟨tt⟩, ⟨m⟩⟩ := hB E H D l k hk hD
    obtain ⟨K₂, _, i, hi, hK₂⟩ := exists_image σ₁
    have hKA : KA l ≤ K₂ := fun z hz => (hK₂ z).2 ⟨κ ⟨z, hz⟩, RingHom.congr_fun hκ _⟩
    have hiκ : (IntermediateField.inclusion hKA).toRingHom = i.comp κ := RingHom.ext fun b =>
      Subtype.ext ((RingHom.congr_fun hκ b).symm.trans (RingHom.congr_fun hi (κ b)).symm)
    let f : 𝓞 M →+* 𝓞 K₂ := (i.comp β).codRestrict (integralClosure ℤ K₂).toSubring fun a =>
      (RingOfIntegers.isIntegral a).map (i.comp β).toIntAlgHom
    have hf : (algebraMap (𝓞 K₂) K₂).comp f = i.comp β := RingHom.ext fun _ => rfl
    obtain ⟨C', φ, hφ⟩ := exists_ellMap polBaseChange_holds E H _ ω C _ f
    obtain ⟨T', mT, -⟩ := PAT.exists_pullback E H _ _ (spMap f) T
    obtain ⟨tt', -⟩ := isTen_baseChange E H _ ω C D h T tt _ _ C' f φ T' mT hφ
    obtain ⟨o', ⟨mo⟩⟩ := ObjPull.objPull_of_pol pol_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (spMap κ)
      (spMap (IntermediateField.inclusion hKA).toRingHom) (spMap i) rfl rfl
      (by rw [hiκ, spMap_comp', spMap_comp', RingHom.comp_id]) o
    obtain ⟨n₁, -⟩ := sab_comp m mo.toSABMap rfl
    obtain ⟨n, -⟩ := sab_cancel (g := spMap (algebraMap (𝓞 K₂) K₂)) mT n₁ (by rw [spMap_comp', spMap_comp', hf])
    refine ⟨K₂, inferInstance, hKA, _, C', ε, h, T', o', fun z hz => (hK₂ z).2 (hle z hz), ?_, hh, ⟨tt'⟩, ⟨n⟩⟩
    refine (EllComp.ellMap_comp E H _ ω C _ _ C' f φ hφ).2.1 _ ?_
    rwa [RingHom.comp_assoc, hf, ← RingHom.comp_assoc, hi]

theorem principalCurve_of_tensorObjSt (h : TensorObjSt) : PrincipalCurve := by
  intro E _ _ _ H
  obtain ⟨l⟩ : Nonempty (Level H) := inferInstance
  obtain ⟨K₁, hK, -, ω, C, -, -, -, -, -, hC, -⟩ := h E H (ExStModel.zeroDatum H) l ⊥ inferInstance (Or.inl rfl)
  exact ⟨K₁, inferInstance, hK, algebraMap K₁ ℂ, ω, C, hC⟩

theorem ell_sq {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) : (2 * ω - 1) ^ 2 = -(H.d : R) := by
  obtain ⟨τ, hτ, -⟩ := LieChar.ell_char E H R ω C
  have : (2 * wK H - 1) ^ 2 = -(H.d : OK H) := Subtype.ext (by
    push_cast
    show (2 * H.w0 - 1) ^ 2 = _
    rw [H.two_weight_eq_one_add_root, add_sub_cancel_left, H.rt_sq])
  simpa [hτ, map_ofNat] using congrArg τ this

theorem exists_curve_sign (hC : PrincipalCurve) (H : Host E) {r : ℂ} (hr : r ^ 2 = -(H.d : ℂ)) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (σ : M →+* ℂ) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω),
      C.IsPrincipalAt (σ.comp (algebraMap (𝓞 M) M)) ∧ σ.comp (algebraMap (𝓞 M) M) (2 * ω - 1) = r := by
  obtain ⟨M, _, _, σ, ω, C, hp⟩ := hC E H
  have h₁ : σ.comp (algebraMap (𝓞 M) M) (2 * ω - 1) ^ 2 = r ^ 2 := by
    rw [← map_pow, ell_sq C, map_neg, map_natCast, hr]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h₁ with h₂ | h₂
  · exact ⟨M, inferInstance, inferInstance, σ, ω, C, hp, h₂⟩
  · obtain ⟨a, -, h₃, h₄, h₅⟩ := EllConj.exists_conj_action E H _ ω C
    refine ⟨M, inferInstance, inferInstance, σ, 1 - ω, ⟨C.P, C.dim, a, C.v, C.basis, h₃, h₄, h₅⟩, hp, ?_⟩
    rw [show 2 * (1 - ω) - 1 = -(2 * ω - 1) by ring, map_neg, h₂, neg_neg]

theorem some_of_tensor (h₁ : TensorExists) (h₂ : TensorIsObject) (hC : PrincipalCurve) : TensorForSomeCurve := by
  intro E _ _ _ H D l k hk hD
  have him : H.rt0.im ≠ 0 := fun h0 => by
    have h := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp [sq, h0] at h
    nlinarith [mul_self_nonneg H.rt0.re]
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℤˣ, 0 < ((ε₀ : ℤ) : ℝ) * H.rt0.im := by
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨-1, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨ε, r, hr, hε, hs⟩ : ∃ (ε : ℤˣ) (r : ℂ), r ^ 2 = -(H.d : ℂ) ∧
      (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ ((D.q = 0 ∧ H.rt0 = r) ∨ (D.p = 0 ∧ H.rt0 = -r)) := by
    rcases hD with h | h
    · exact ⟨-ε₀, -H.rt0, by rw [neg_sq, H.sqrt_neg_disc_sq], definite_datum_form_pos E H D _ (Or.inr ⟨h, by simpa using hε₀⟩),
        Or.inr ⟨h, (neg_neg _).symm⟩⟩
    · exact ⟨ε₀, H.rt0, H.sqrt_neg_disc_sq, definite_datum_form_pos E H D _ (Or.inl ⟨h, hε₀⟩), Or.inl ⟨h, rfl⟩⟩
  obtain ⟨M, _, _, σ, ω, C, hp, hω⟩ := exists_curve_sign hC H hr
  obtain ⟨h, hh⟩ : ∃ h : D.La → D.La → OK H, IsKForm D ε h :=
    ⟨fun x y => (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H,
      fun x y => by simp [wK]⟩
  obtain ⟨T, hT⟩ := h₁ E H M ω C D ε h hh hε
  obtain ⟨M', _, i, hi, -⟩ := exists_image σ
  have := LevQuot.finiteDimensional_field l
  let K' : IntermediateField ℚ ℂ := (k ⊔ KA l) ⊔ M'
  have : NumberField K' := ⟨⟩
  let β : 𝓞 M →+* K' := ((IntermediateField.inclusion le_sup_right).toRingHom.comp i).comp (algebraMap (𝓞 M) M)
  let κ : KA l →+* K' := (IntermediateField.inclusion (le_sup_right.trans le_sup_left)).toRingHom
  have hβ : (algebraMap K' ℂ).comp β = σ.comp (algebraMap (𝓞 M) M) := by rw [← hi]; rfl
  have hω' : ((β (2 * ω - 1) : K') : ℂ) = r := (RingHom.congr_fun hβ _).trans hω
  obtain ⟨K₁, _, _, j, o, hm⟩ := h₂ E H M ω C D ε h T hh hT l K' β κ
    (hs.imp (fun a => ⟨a.1, Subtype.ext (a.2.trans hω'.symm)⟩)
      fun a => ⟨a.1, Subtype.ext (a.2.trans (congrArg Neg.neg hω'.symm))⟩)
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : K₁ →+* ℂ, σ₁.comp j = algebraMap K' ℂ := by
    letI := j.toAlgebra
    haveI : IsScalarTower ℚ K' K₁ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast j q).symm
    haveI : Algebra.IsAlgebraic K' K₁ := Algebra.IsAlgebraic.tower_top (K := ℚ) K'
    exact ⟨(IsAlgClosed.lift (R := K') (S := K₁) (M := ℂ)).toRingHom,
      RingHom.ext fun a => (IsAlgClosed.lift (R := K') (S := K₁) (M := ℂ)).commutes a⟩
  refine ⟨M, inferInstance, inferInstance, ω, C, ε, h, T, K₁, inferInstance, inferInstance, j.comp β, j.comp κ, σ₁, o,
    ?_, fun z hz => ⟨j ⟨z, (le_sup_left.trans le_sup_left : k ≤ K') hz⟩, RingHom.congr_fun hσ₁ _⟩, ?_, hh, hT, hm⟩
  · rw [← RingHom.comp_assoc, hσ₁]; rfl
  · rwa [← RingHom.comp_assoc, hσ₁, hβ]

theorem tensorObjSt_iff_curve (h₁ : TensorExists) (h₂ : TensorIsObject) : TensorObjSt ↔ PrincipalCurve :=
  ⟨principalCurve_of_tensorObjSt, fun hC => tensorObjSt_iff_some.2 (some_of_tensor h₁ h₂ hC)⟩

end Tensor

theorem compare :
    (CMExistsSt ↔ CMExistsOn (1 ≤ ·) ∧ CMExistsOn (· = 0)) ∧ (PointCarriesObject → CMExistsOn (1 ≤ ·)) ∧
    (N1c → (CMExistsOn (1 ≤ ·) ↔ PointCarriesObject)) ∧ (TensorObjSt ↔ TensorForSomeCurve) ∧
    (TensorExists ∧ TensorIsObject → (TensorObjSt ↔ PrincipalCurve)) ∧
    (CMExists → PrincipalCurve → TensorObjSt ∧ CMExistsOn (1 ≤ ·)) :=
  ⟨cmExistsSt_iff, cmExistsOn_of_pointCarriesObject, cmExistsOn_iff, tensorObjSt_iff_some,
    fun h => tensorObjSt_iff_curve h.1 h.2,
    fun h hC => ⟨(tensorObjSt_iff_curve h.1.1 h.1.2).2 hC, cmExistsOn_of_pointCarriesObject h.2⟩⟩

end GlobalTheory.CMExistsCompare
end
