import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConvTermFe
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecRelationDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelationOfFiniteLevels
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenT
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ConvFE
open ReciprocityTheory.ChartRestriction.G.DVR

def cst {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = cst (r ≫ p) z c :=
  (gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _)

theorem cst_specMap {A R : Type} [CommRing A] [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
    (f : A →+* R) (c : A) : cst (q ≫ Spec.map (CommRingCat.ofHom f)) z c = cst q z (f c) := by
  have e := congrArg (fun t => t.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [e]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem pullB_val {T : Over (Spec (CommRingCat.of R))} {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α}
    {s : Raw D F k} (h : PullB D F φ k f s) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J := by
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) r z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left r z J hJ).2.1 (f α)
  have hJ' : Good D.P.L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ _
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)

theorem whisker_trT {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst T D.P.A ≫ cP D T mu)).trans ?_
    rw [whiskerRight_snd, comp_cP, comp_cP]
    rfl

theorem cst_unit {r : R} (hr : r ≠ 0) (z : (DegPre.BF D F).left) : IsUnit (cst (DegPre.BF D F).hom z r) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A)).symm.trans (Category.assoc _ _ _).symm
  rw [e]
  refine (congrArg IsUnit ((cst_specMap _ z (algebraMap R (FractionRing R)) r).trans (cst_specMap _ z _ _))).mpr
    (IsUnit.map _ (IsUnit.map _ (Ne.isUnit ?_)))
  exact fun h => hr (IsFractionRing.injective R (FractionRing R) (h.trans (map_zero _).symm))

theorem form_delta {T : Over (Spec (CommRingCat.of R))} (k : ℕ) (α' α : D.X) (b : T ⟶ D.P.A) :
    FormEq (famφT D T α') (DegPre.famε k) (Sum.elim (fun i => (trT D b).left ≫ famφT D T α i) (deltaφT D α' α b))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) := fun U _ h => by
  refine Eq.symm (Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (c := ∏ i, h ((trT D b).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
    (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
      (c := ∏ i, h (famφT D T α' i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_)
  exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)

theorem noeth (V W : Type) [CommRing V] [IsNoetherianRing V] [CommRing W] [Algebra V W] [Module.Finite V W] :
    IsNoetherianRing Γ((TA V W).left, ⊤) := by
  haveI : IsNoetherianRing W := isNoetherian_of_tower V inferInstance
  exact isNoetherianRing_of_ringEquiv W (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm

theorem jac (V W : Type) [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]
    [IsLocalHom (algebraMap V W)] (r : V) (hr : r ∈ IsLocalRing.maximalIdeal V) :
    scal (TA V W).hom r ∈ Ideal.jacobson (⊥ : Ideal Γ((TA V W).left, ⊤)) := by
  let E : W ≃+* Γ((TA V W).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm
  have e : scal (TA V W).hom r = E (algebraMap V W r) :=
    (congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V W)))).symm
  have hw : algebraMap V W r ∈ Ideal.jacobson (⊥ : Ideal W) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact map_nonunit (algebraMap V W) r hr
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  have := (Ideal.mem_jacobson_bot.1 hw (E.symm y)).map E
  simpa using this

theorem sval_twist {W : Type} [CommRing W] [Algebra R W] {k : ℕ} (a : Multiplicative D.X →* Wˣ)
    (f : ∀ α, SecBT D (TA R W) k α) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TA R W ⊗ D.P.A).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (twist a f α) r z J =
      cst (R := W) (r ≫ (fst (TA R W) D.P.A).left) z (a (Multiplicative.ofAdd α)).val * sval (f α) r z J :=
  (sval_secScale _ _ r z hJ).trans (congrArg (· * _) (gs_scal (R := W) _ r z _))

theorem term_val {W : Type} [CommRing W] [Algebra R W] {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (a a' : Multiplicative D.X →* Wˣ) {β ga α : D.X}
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (twist a f β) (twist a' g ga) p)
    {Z : Over (Spec (CommRingCat.of R))} (r : Z ⟶ DegPre.BF D F) (z : Z.left) {J} (hJ : Good D.P.L z J) :
    sval p (r ≫ φ ▷ D.P.A).left z J =
      cst (R := W) (r ≫ fst _ _ ≫ φ).left z (a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd ga)).val *
        (sval (s β) r.left z J * sval (s' ga) r.left z J *
          (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) (r ≫ snd _ _)).val) := by
  have e : (r ≫ φ ▷ D.P.A).left ≫ (fst (TA R W) D.P.A).left = (r ≫ fst _ _ ≫ φ).left := by
    rw [← Over.comp_left, Category.assoc, whiskerRight_fst]
  rw [hp Z _ z J hJ, sval_twist a f β _ z hJ, sval_twist a' g ga _ z hJ, e, pullB_val hf β _ z hJ,
    pullB_val hg ga _ z hJ, Category.assoc, whiskerRight_snd, Units.val_mul, map_mul, Over.comp_left _ _ _ r (φ ▷ D.P.A)]
  ring

theorem term_rel (hG : GlobalFnsSt) (hB : D.TauBimult) {W : Type} [CommRing W] [Algebra R W]
    {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (hs : DegPre.FamFE D F k s) (hs' : DegPre.FamFE D F l s')
    (a a' : Multiplicative D.X →* Wˣ) (mu α β : D.X)
    (ha : a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1)
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (twist a f β) (twist a' g (α - β)) p)
    {p' : SecBT D (TA R W) (k + l) (α + (k + l) • mu)}
    (hp' : IsProdB (twist a f (β + k • mu)) (twist a' g (α + (k + l) • mu - (β + k • mu))) p')
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l)))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α))
    (z : (DegPre.BF D F).left) {J} (hJ : Good D.P.L z J) :
    sval p' (φ ▷ D.P.A).left z J =
      sval p ((φ ▷ D.P.A).left ≫ (trT D (toUnit _ ≫ D.c mu)).left) z J * (val u (𝟙 _) z J).val := by
  have hγ : α + (k + l) • mu - (β + k • mu) = α - β + l • mu := by rw [add_nsmul]; abel
  have e₁ := term_val hf hg a a' hp' (𝟙 (DegPre.BF D F)) z hJ
  have e₂ := term_val hf hg a a' hp (𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) z hJ
  have e₃ := ConvTermFE.conv_term_fe hG R D hB F k l s s' hs hs' mu α β (α - β) _ _ (add_sub_cancel _ _) rfl hγ u hu hc
    _ (𝟙 (DegPre.BF D F)) z J hJ
  have e₄ : (𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) ≫ fst _ _ ≫ φ = 𝟙 (DegPre.BF D F) ≫ fst _ _ ≫ φ := by
    rw [Category.id_comp, Category.id_comp, DegPre.trF, lift_fst_assoc]
  have e₅ : a (Multiplicative.ofAdd (β + k • mu)) * a' (Multiplicative.ofAdd (α + (k + l) • mu - (β + k • mu))) =
      a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd (α - β)) := by
    rw [hγ, ofAdd_add, ofAdd_add, map_mul, map_mul, _root_.mul_mul_mul_comm, ha, _root_.mul_one]
  have e₆ : (φ ▷ D.P.A).left ≫ (trT D (toUnit _ ≫ D.c mu)).left =
      ((𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) ≫ φ ▷ D.P.A).left := by
    rw [Category.id_comp, ← whisker_trT, Over.comp_left]
  rw [e₅, e₃, Category.id_comp (φ ▷ D.P.A)] at e₁
  rw [e₄] at e₂
  rw [e₆, e₁, e₂]
  exact (_root_.mul_assoc _ _ _).symm

theorem conv_famFE : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W), Function.Injective φ.left.appTop.hom → ∀ (k l : ℕ) (f : ∀ α, SecBT D (TA V W) k α) (g : ∀ α, SecBT D (TA V W) l α) (h : ∀ α, SecBT D (TA V W) (k + l) α) (s : Raw D F k) (s' : Raw D F l) (s'' : Raw D F (k + l)) (a a' : Multiplicative D.X →* Wˣ), (∀ mu : D.X, a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1) → PullB D F φ k f s → PullB D F φ l g s' → PullB D F φ (k + l) h s'' → DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ConvT (IsLocalRing.maximalIdeal V) (twist a f) (twist a' g) h → DegPre.FamFE D F (k + l) s'' := by
  intro hG V _ _ _ hV D hB W _ _ _ hW F _ _ φ hφ k l f g h s s' s'' a a' ha hf hg hh hs hs' hconv mu α u hu hc
  obtain ⟨u₀, r₁, r₂, hu₀, -, hr₂, hrel⟩ := GlobalTheory.UU.IntGen.main hG V D (TA V W) (k + l) α mu
  obtain ⟨p, hp, hS⟩ := hconv α
  obtain ⟨p', hp', hS'⟩ := hconv (α + (k + l) • mu)
  haveI := hV.1
  haveI := hW.1
  haveI := hW.2.2.2.1
  haveI := noeth V W
  haveI := D.P.isAb.smooth
  haveI := D.P.isAb.geomConnected
  haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TF (R := V) F).left := inferInstanceAs (IsAffine (Spec _))
  have hcs : ∀ (z : (DegPre.BF D F).left) (c : V),
      gs (φ ▷ D.P.A).left z ⊤ (scal (TA V W ⊗ D.P.A).hom c) = cst (DegPre.BF D F).hom z c := fun z c => by
    rw [gs_scal, Over.w]
  have hu' : ∀ (z : (DegPre.BF D F).left) (J), Good D.P.L z J →
      cst (DegPre.BF D F).hom z r₂ * (val u (𝟙 _) z J).val =
        cst (DegPre.BF D F).hom z r₁ * (val u₀ (φ ▷ D.P.A).left z J).val := fun z J hJ => by
    have := hrel F φ u hu hc _ (𝟙 _) z J hJ
    rwa [gs_scal, gs_scal, Category.id_comp, Category.id_comp] at this
  have H := relation_of_finite_levels V (IsLocalRing.maximalIdeal V) (TA V W) D.P.A (jac V W) _ _ D.P.L D.P.isLB _ _ _
    _ _ _ _ _ _ (trT D (toUnit _ ≫ D.c mu)).left (h α) (h (α + (k + l) • mu)) u₀ (scal (TA V W ⊗ D.P.A).hom r₁)
    (scal (TA V W ⊗ D.P.A).hom r₂) hu₀ (form_delta _ _ _ _)
    (adicSum_rel V (IsLocalRing.maximalIdeal V) _ _ (trT D (toUnit _ ≫ D.c mu)) _ D.P.L _ _ _ _ _ _ _ _ _ u₀ _ _ _ _
      (Equiv.addRight (k • mu)) p p' _ _ hS hS' fun β =>
      sec_relation_descends _ D.P.A (TA V W) (TF (R := V) F) φ hφ _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ _ (p β)
        (p' (β + k • mu)) u₀ _ _ hu₀ (form_delta _ _ _ _) fun z J hJ => by
          rw [hcs, hcs, term_rel hG hB hf hg hs hs' a a' mu α β (ha mu) (hp β) (hp' _) u hu hc z hJ, mul_left_comm,
            hu' z J hJ, mul_left_comm])
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun z J hJ => ?_
  have e := H _ (φ ▷ D.P.A).left z J hJ
  rw [hcs, hcs, mul_left_comm, ← hu' z J hJ, mul_left_comm, ← Over.comp_left, whisker_trT, Over.comp_left] at e
  rw [pullB_val hh _ _ z hJ, pullB_val hh _ _ z hJ, Category.id_comp, Category.id_comp]
  exact (cst_unit hr₂ z).mul_left_cancel e

end GlobalTheory.ConvFE
