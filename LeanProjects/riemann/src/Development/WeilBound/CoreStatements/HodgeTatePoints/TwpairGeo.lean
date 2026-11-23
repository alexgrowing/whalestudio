import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairAlg
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFinite
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.SubOrder

noncomputable section

namespace PositivityTheory.HtPt.Twpair

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

omit [IsDomain R] in
theorem mem_of_finite [IsLocalRing R] {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  have : IsFinite (h.left ≫ X.hom) := by rw [Over.w h]; exact hY
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) X.hom W hW h.left).ge (Set.mem_univ z)

theorem isFinOpenSub [IsLocalRing R] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hfin : IsFinite (U.ι ≫ Γ.G.hom))
    (hU : ∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) : Γ.IsFinOpenSub U := by
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

theorem regularAt_generic [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left)
    (hg : (Γ.G.hom g).asIdeal = ⊥) : Γ.RegularAt f g := by
  obtain ⟨d, hd, V, hgV, s, hs⟩ := RegDenom.exists_denom_regularAt R T Γ f g
  let σ : Γ(Γ.G.left, V) := RegDenom.structHom Γ.G.hom V d
  let W := Γ.G.left.basicOpen σ
  have hW : W ≤ V := Γ.G.left.basicOpen_le σ
  have hgW : g ∈ W := by
    have e : W = V ⊓ Γ.G.hom ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv d) :=
      Scheme.basicOpen_appLE _ _ _ _ _
    rw [e, basicOpen_eq_of_affine]
    refine ⟨hgV, ?_⟩
    change d ∉ (Γ.G.hom g).asIdeal
    rw [hg]
    exact hd
  let ρ : Γ(Γ.G.left, V) →+* Γ(Γ.G.left, W) := (Γ.G.left.presheaf.map (homOfLE hW).op).hom
  have hu : IsUnit (ρ σ) := Γ.G.left.toRingedSpace.isUnit_res_basicOpen σ
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  refine ⟨W, hgW, u * ρ s, fun t ht => ?_⟩
  have htV : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V := fun z hz => hW (ht hz)
  have hρ : ∀ a, RegDenom.valHom (Γ.pt t).left W ht (ρ a) = RegDenom.valHom (Γ.pt t).left V htV a := by
    intro a
    have := Scheme.Hom.map_appLE (Γ.pt t).left ht (homOfLE hW).op
    simp only [RegDenom.valHom, RingHom.comp_apply]
    rw [← this]
    rfl
  have h1 := congrArg (RegDenom.valHom (Γ.pt t).left W ht) hu
  rw [map_mul, map_one, hρ, RegDenom.valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t)) V htV d] at h1
  rw [← RegDenom.valHom_apply, map_mul, hρ, RegDenom.valHom_apply _ _ _ s, hs t htV]
  change _ * (_ * f t) = f t
  rw [← _root_.mul_assoc, h1, _root_.one_mul]

theorem valHom_top_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (φ : B →+* C) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ x) ⊤ le_top s = φ (valAt x ⊤ le_top s) := by
  have e : (x.appLE ⊤ ⊤ le_top).hom s =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (valAt x ⊤ le_top s) := by
    simp [valAt]
  have e1 := valHom_appLE (Spec.map (CommRingCat.ofHom φ)) x (V := ⊤) (W := ⊤) le_top le_top le_top s
  have e2 := valHom_spec_top φ le_top (valAt x ⊤ le_top s)
  exact e1.symm.trans ((congrArg _ e).trans e2)

section sec

variable {Γ : QFGroup R T} {U : Γ.G.left.Opens} {hU : IsAffineOpen U}
variable [Algebra R Γ(Γ.G.left, U)]
  (hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))))

include hρ

theorem exists_tensor_of_prod (s : Γ((Γ.G ⊗ Γ.G).left, ⊤)) :
    ∃ c : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∀ (a b : T) (ha : ⊤ ≤ (Γ.pt a).left ⁻¹ᵁ U)
      (hb : ⊤ ≤ (Γ.pt b).left ⁻¹ᵁ U),
      valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s =
        Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb) c := by
  let B := Γ(Γ.G.left, U)
  let Q : Over (Spec (CommRingCat.of R)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B))))
  let iL : B →+* B ⊗[R] B := (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom
  let iR : B →+* B ⊗[R] B := (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom
  let x : Q ⟶ Γ.G := Over.homMk (Spec.map (CommRingCat.ofHom iL) ≫ hU.fromSpec) (by
    simp only [Category.assoc, Q, Over.mk_hom]
    rw [hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2)
  let y : Q ⟶ Γ.G := Over.homMk (Spec.map (CommRingCat.ofHom iR) ≫ hU.fromSpec) (by
    simp only [Category.assoc, Q, Over.mk_hom]
    rw [hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [iR, Algebra.TensorProduct.algebraMap_apply'])
  refine ⟨valAt (lift x y).left ⊤ le_top s, ?_⟩
  intro a b ha hb
  let φ : B ⊗[R] B →+* FractionRing R :=
    (Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb)).toRingHom
  let w : genPt R ⟶ Q := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    simp only [Q, Over.mk_hom, genPt]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [φ])
  have hwx : w ≫ x = Γ.pt a := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, w, x, Over.homMk_left]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.comp iL = valHom (Γ.pt a).left U ha := by
      ext r
      simp [φ, iL]
      try rfl
    rw [this]
    exact spec_valHom_fromSpec _ hU ha
  have hwy : w ≫ y = Γ.pt b := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, w, y, Over.homMk_left]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.comp iR = valHom (Γ.pt b).left U hb := by
      ext r
      simp [φ, iR]
      try rfl
    rw [this]
    exact spec_valHom_fromSpec _ hU hb
  have hw : w ≫ lift x y = lift (Γ.pt a) (Γ.pt b) := by
    rw [comp_lift, hwx, hwy]
  have e : (lift (Γ.pt a) (Γ.pt b)).left = Spec.map (CommRingCat.ofHom φ) ≫ (lift x y).left := by
    rw [← hw]; rfl
  have e2 := valHom_congr e ⊤ le_top le_top
  exact (DFunLike.congr_fun e2 s).trans (valHom_top_comp (lift x y).left φ s)

end sec

theorem exists_order [ValuationRing R] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hF : Γ.IsFinOpenSub U) :
    ∃ A : Subalgebra R (subH Γ hF → R), IsHopfOrder A ∧
      (∀ f ∈ A, ∃ s : Γ(Γ.G.left, U), ∀ (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
        valAt (Γ.pt t).left U h s = algebraMap R _ (f t)) ∧
      ∀ (s : Γ((Γ.G ⊗ Γ.G).left, ⊤)) (g : subH Γ hF × subH Γ hF → R),
        (∀ z : subH Γ hF × subH Γ hF, valAt (lift (Γ.pt z.1) (Γ.pt z.2)).left ⊤ le_top s = algebraMap R _ (g z)) →
        g ∈ prodSpan A := by
  have hU := isAffineOpen_of_fin Γ hF
  letI : Algebra R Γ(Γ.G.left, U) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) :=
    fromSpec_hom Γ hU
  have hfin := sec_finite hρ hF
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hval : ∀ (t : subH Γ hF) (s : Γ(Γ.G.left, U)),
      ∃ r : R, algebraMap R (FractionRing R) r = valAlg hρ t t.2 s := by
    intro t s
    have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t t.2))
  choose Φf hΦf using hval
  let Φ : Γ(Γ.G.left, U) →ₐ[R] (subH Γ hF → R) :=
    { toFun := fun s t => Φf t s
      map_one' := funext fun t => inj (by simp [hΦf])
      map_mul' := fun a b => funext fun t => inj (by simp [hΦf])
      map_zero' := funext fun t => inj (by simp [hΦf])
      map_add' := fun a b => funext fun t => inj (by simp [hΦf])
      commutes' := fun r => funext fun t => inj (by
        rw [hΦf, AlgHom.commutes]; rfl) }
  have hΦ : ∀ (s : Γ(Γ.G.left, U)) (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
      valAt (Γ.pt t).left U h s = algebraMap R _ (Φ s t) := fun s t h => (hΦf t s).symm
  have key : ∀ c' : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∃ g ∈ prodSpan Φ.range, ∀ z : subH Γ hF × subH Γ hF,
      algebraMap R (FractionRing R) (g z) =
        Algebra.TensorProduct.productMap (valAlg hρ z.1 z.1.2) (valAlg hρ z.2 z.2.2) c' := by
    intro c'
    induction c' with
    | zero => exact ⟨0, Submodule.zero_mem _, fun z => by simp⟩
    | tmul a b =>
      refine ⟨fun z => Φ a z.1 * Φ b z.2, Submodule.subset_span ⟨Φ a, ⟨a, rfl⟩, Φ b, ⟨b, rfl⟩, rfl⟩, fun z => ?_⟩
      simp only [map_mul, Algebra.TensorProduct.productMap_apply_tmul]
      exact congrArg₂ (· * ·) (hΦ a z.1 z.1.2).symm (hΦ b z.2 z.2.2).symm
    | add a b ha hb =>
      obtain ⟨g, hg, hg'⟩ := ha
      obtain ⟨g₂, hg₂, hg₂'⟩ := hb
      exact ⟨g + g₂, Submodule.add_mem _ hg hg₂, fun z => by simp [hg', hg₂']⟩
  have hfinA : Module.Finite R Φ.range :=
    Module.Finite.of_surjective Φ.rangeRestrict.toLinearMap Φ.rangeRestrict_surjective
  refine ⟨Φ.range, ⟨hfinA, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have htf : Module.IsTorsionFree R Φ.range :=
      Function.Injective.moduleIsTorsionFree Φ.range.val.toLinearMap Subtype.val_injective (fun _ _ => rfl)
    have : Module.Flat R Φ.range := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
      exact htf
    have : Module.Free R Φ.range := Module.free_of_flat_of_isLocalRing
    infer_instance
  · classical
    have := Fintype.ofFinite (subH Γ hF)
    let v : subH Γ hF → Γ(Γ.G.left, U) →+* FractionRing R := fun t => RegDenom.valHom (Γ.pt t.1).left U t.2
    have hv : Function.Injective v := by
      intro s t e
      have hst := RegDenom.eq_of_valHom_eq hU s.2 t.2 e
      obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := inferInstance
      exact Subtype.ext (Γ.pt_inj s.1 t.1 x x (by rw [hst]))
    have h1 : ∀ h : subH Γ hF, ∃ d : R, d ≠ 0 ∧ d • (Pi.single h 1 : subH Γ hF → R) ∈ Φ.range := by
      intro h
      obtain ⟨d, hd, b, hb⟩ := RegDenom.exists_denom_of_injective (algebraMap R Γ(Γ.G.left, U)) v hv
        (fun t r => val_algebraMap hρ t.1 t.2 r) (fun t => algebraMap R _ ((Pi.single h 1 : subH Γ hF → R) t))
      refine ⟨d, hd, b, funext fun t => inj ?_⟩
      refine (hΦ b t t.2).symm.trans ((hb t).trans ?_)
      rw [← map_mul]
      rfl
    choose d hd hdA using h1
    refine ⟨∏ h, d h, Finset.prod_ne_zero_iff.2 fun h _ => hd h, fun f => ?_⟩
    have e : (∏ h, d h) • f =
        ∑ h, (f h * ∏ h' ∈ Finset.univ.erase h, d h') • (d h • (Pi.single h 1 : subH Γ hF → R)) := by
      funext t
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_eq_single t]
      · rw [Pi.single_eq_same, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ t)]
        ring
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [e]
    exact Subalgebra.sum_mem _ fun h _ => Subalgebra.smul_mem _ (hdA h) _
  · rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := exists_tensor hρ hF s
    obtain ⟨g, hg, hg'⟩ := key c
    have : (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) = g := by
      funext z
      apply inj
      rw [hg' z, ← hc z.1 z.2 z.1.2 z.2.2 (z.1 * z.2).2]
      exact (hΦ s (z.1 * z.2) (z.1 * z.2).2).symm
    change (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) ∈ prodSpan Φ.range
    rw [this]
    exact hg
  · rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := exists_inv hρ hF s
    refine ⟨c, funext fun x => inj ?_⟩
    have e1 := hc x x.2 (x⁻¹).2
    have e2 := hΦ s x⁻¹ (x⁻¹).2
    have e3 := hΦ c x x.2
    exact e3.symm.trans (Eq.trans (valAlg_apply hρ _ _ _).symm (e1.symm.trans e2))
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, fun t h => hΦ s t h⟩
  · intro s g hg
    obtain ⟨c, hc⟩ := exists_tensor_of_prod hρ s
    obtain ⟨g', hg1, hg2⟩ := key c
    have : g = g' := funext fun z => inj (by rw [hg2 z, ← hc z.1 z.2 z.1.2 z.2.2, hg z])
    rw [this]
    exact hg1

theorem bichar_mem_prodSpan [ValuationRing R] (hH : HenselianLocalRing R)
    (hdim : ∀ P : PrimeSpectrum R, P.asIdeal = ⊥ ∨ P = IsLocalRing.closedPoint R) [Finite T] (Γ : QFGroup R T)
    (β : T →* T →* Rˣ) (s : Γ((Γ.G ⊗ Γ.G).left, ⊤))
    (hs : ∀ a b, valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s = algebraMap R _ ((β a b : Rˣ) : R)) :
    (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan (Γ.btOrder ⊤) := by
  have := Γ.quasiFinite
  have := Γ.separated
  have := Γ.quasiCompact
  have := Γ.finPres
  let U := GlobalTheory.finitePart Γ.G.hom
  have hU : ∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U :=
    GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R) Γ.G.hom
  have hF := isFinOpenSub Γ U (GlobalTheory.isFinite_finitePart (R := CommRingCat.of R) Γ.G.hom) hU
  obtain ⟨A, hA, hsec, hprod⟩ := exists_order Γ U hF
  have h1 := pair_ind R T (subH Γ hF) A β hA (hprod s _ fun z => hs z.1 z.2)
  have hle : indOrder (subH Γ hF).subtype A ≤ Γ.btOrder ⊤ := by
    intro f hf
    refine Algebra.subset_adjoin fun t g _ => ?_
    rcases hdim (Γ.G.hom g) with hg | hg
    · exact regularAt_generic Γ _ g hg
    · obtain ⟨σ, hσ⟩ := hsec _ (hf t)
      exact ⟨U, hU g hg, σ, fun h hh => hσ ⟨h, hh⟩ hh⟩
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hle ha, b, hle hb, rfl⟩

end PositivityTheory.HtPt.Twpair
