import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KTrivAndPolAtTensAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.ValExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_generic {Dw : Datum H} {B K : Type} [CommRing B] [IsDomain B] [Field K] {Z : Scheme.{0}} {tZ : SAB H Z}
    (c : B →+* K) (hinj : Function.Injective c) {b : Sp B ⟶ Z} {t₀ : SAB H (Sp K)} (m₀ : SABMap t₀ tZ (spMap c ≫ b))
    (h₀ : IsOfType Dw t₀) {tB : SAB H (Sp B)} (mB : SABMap tB tZ b) : GlobalTheory.LN.PolAt tB (Out.jK B) := by
  let i : FractionRing B →+* K := IsFractionRing.lift hinj
  have hi : i.comp (algebraMap B (FractionRing B)) = c := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  clear_value i
  have e : spMap c ≫ b = spMap i ≫ Out.jK B ≫ b := by
    rw [← hi, Cris.spMap_comp, Category.assoc]
  obtain ⟨tF, ⟨mF⟩⟩ := exists_sab (Out.jK B) tB
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mB mF
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ n (e ▸ m₀)
  have := tF.semi.quasiCompact
  have := tF.semi.separated
  have := tF.semi.smooth
  obtain ⟨hp, hA, hK⟩ := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension _ _ i tF.G t₀.G k.φ k.cart
    tF.PP.L t₀.PP.L tF.PP.isLB t₀.PP.isLB (k.lin.imp fun _ h => h.1) h₀.1 h₀.2.1 h₀.2.2.1
  refine GlobalTheory.LocM.PolFibre.polAt_of_map mF ?_ hA hK
  rw [← mF.cart.1.isoPullback_inv_snd]
  infer_instance

theorem exists_isProper_near {Dw : Datum H} {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {g : X ⟶ Z}
    {tZ : SAB H Z} {t₀ : SAB H (Sp (Kbar X))} (m₀ : SABMap t₀ tZ (genPt X ≫ g)) (h₀ : IsOfType Dw t₀) (x : X)
    (hx : g x ∈ abLocus tZ.G) : ∃ (U : AffOp X) (tB : SAB H (Sp Γ(X, U.1))) (_ : SABMap tB tZ (U.2.1.fromSpec ≫ g)),
      x ∈ U.1 ∧ IsProper tB.G.hom := by
  obtain ⟨tX, ⟨mX⟩⟩ := exists_sab g tZ
  have key : ∀ y, g y ∈ abLocus tZ.G ↔ y ∈ abLocus tX.G := fun y => abLocus_pullback abLocusOne tZ.semi mX.cart.1 y
  have ho := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian tX.G tX.semi
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⟨_, ho⟩) (x := x) ((key x).1 hx)
  obtain ⟨U, rfl⟩ : ∃ U : AffOp X, U.1 = W := ⟨⟨W, hW, ⟨⟨x, hxW⟩⟩⟩, rfl⟩
  obtain ⟨tB, ⟨mB⟩⟩ := exists_sab (S' := Sp Γ(X, U.1)) (U.2.1.fromSpec ≫ g) tZ
  refine ⟨U, tB, mB, hxW, ?_⟩
  have e : genPt X ≫ g = spMap (algebraMap Γ(X, U.1) (Kbar X)) ≫ U.2.1.fromSpec ≫ g := by
    rw [← U.val_toX, AffOp.toX, IsScalarTower.algebraMap_eq Γ(X, U.1) U.Bp (Kbar X), Cris.spMap_comp]
    simp only [Category.assoc]
  have := h₀.charZero
  have : CharZero Γ(X, U.1) := RingHom.charZero (algebraMap Γ(X, U.1) (Kbar X))
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, hW⟩
  refine GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H _ tB
    (polAt_generic _ (FaithfulSMul.algebraMap_injective _ _) (e ▸ m₀) h₀ mB)
    (Set.eq_univ_of_forall fun y => (abLocus_pullback abLocusOne tZ.semi mB.cart.1 y).1 ?_)
  rw [Scheme.Hom.comp_apply]
  refine (key _).2 (hle ?_)
  have : hW.fromSpec y ∈ Set.range hW.fromSpec := ⟨y, rfl⟩
  rwa [hW.range_fromSpec] at this

theorem exists_torsMap_eq : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (X Z : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z) (tZ : SAB H Z), GlobalTheory.IsNormalScheme X → ∀ (t₀ : SAB H (Sp (Kbar X))), Nonempty (SABMap t₀ tZ (genPt X ≫ g)) → IsOfType Dw t₀ → ∀ (U : AffOp X) (t : SAB H (Sp U.Bp)), Nonempty (SABMap t tZ (U.toX ≫ g)) → ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra U.Bp V] [Algebra V (Kbar X)] [IsScalarTower U.Bp V (Kbar X)] [IsFractionRing V (Kbar X)], spMap (algebraMap U.Bp V) (IsLocalRing.closedPoint V) ∈ abLocus t.G → ∀ (n : ℕ) (z : Tors t.G (p ^ n) (Kbar X)), ∃ z' : Tors t.G (p ^ n) V, torsMap (IsScalarTower.toAlgHom U.Bp V (Kbar X)) z' = z := by
  intro _ _ _ E _ _ _ H Dw p _ X Z _ _ g tZ _ t₀ ⟨m₀⟩ h₀ U t ⟨m⟩ V _ _ _ _ _ _ _ hV n z
  let s : Sp V ⟶ Sp U.Bp := spMap (algebraMap U.Bp V)
  let j : Sp (Kbar X) ⟶ Sp V := spMap (algebraMap V (Kbar X))
  have hx : g ((s ≫ U.toX) (IsLocalRing.closedPoint V)) ∈ abLocus tZ.G := by
    have := (abLocus_pullback abLocusOne tZ.semi m.cart.1 _).2 hV
    rw [Scheme.Hom.comp_apply] at this
    exact (congrArg (fun q => g q ∈ abLocus tZ.G) (Scheme.Hom.comp_apply s U.toX _)).mpr this
  obtain ⟨W, tB, mB, hxW, hp⟩ := exists_isProper_near m₀ h₀ _ hx
  have hr : Set.range (s ≫ U.toX) ⊆ Set.range W.2.1.fromSpec := by
    rintro _ ⟨y, rfl⟩
    rw [W.2.1.range_fromSpec]
    exact ((IsLocalRing.specializes_closedPoint y).map (s ≫ U.toX).continuous).mem_open W.1.isOpen hxW
  let y : Sp V ⟶ Sp Γ(X, W.1) := IsOpenImmersion.lift W.2.1.fromSpec _ hr
  have hy : y ≫ W.2.1.fromSpec = s ≫ U.toX := IsOpenImmersion.lift_fac _ _ hr
  have hz : z.1.left ≫ t.G.hom = j ≫ s := by
    rw [Over.w z.1, ← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq]
    rfl
  have mw : m.φ ≫ tZ.G.hom = t.G.hom ≫ U.toX ≫ g := m.cart.1.w
  have mBw : mB.φ ≫ tZ.G.hom = tB.G.hom ≫ W.2.1.fromSpec ≫ g := mB.cart.1.w
  have w₁ : (z.1.left ≫ m.φ) ≫ tZ.G.hom = (j ≫ y) ≫ W.2.1.fromSpec ≫ g := by
    rw [Category.assoc, mw, ← Category.assoc, hz, Category.assoc, Category.assoc, reassoc_of% hy]
  have hE : ValuativeCriterion.Existence tB.G.hom := by
    have h : UniversallyClosed tB.G.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq tB.G.hom :=
    { R := V, K := Kbar X, i₁ := mB.cart.1.lift _ _ w₁, i₂ := y, commSq := ⟨mB.cart.1.lift_snd _ _ w₁⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  have l₁ : j ≫ l.l = mB.cart.1.lift _ _ w₁ := l.fac_left
  have l₂ : l.l ≫ tB.G.hom = y := l.fac_right
  have w₂ : (l.l ≫ mB.φ) ≫ tZ.G.hom = s ≫ U.toX ≫ g := by
    rw [Category.assoc, mBw, ← Category.assoc, l₂, reassoc_of% hy]
  let z₁ : SpAlg U.Bp V ⟶ t.G := Over.homMk (m.cart.1.lift _ _ w₂) (m.cart.1.lift_snd _ _ w₂)
  have hz₁ : spOver (IsScalarTower.toAlgHom U.Bp V (Kbar X)) ≫ z₁ = z.1 := by
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_)
    · change (j ≫ m.cart.1.lift _ _ w₂) ≫ m.φ = _
      rw [Category.assoc]
      refine (congrArg (j ≫ ·) (m.cart.1.lift_fst _ _ w₂)).trans ?_
      rw [← Category.assoc, l₁]
      exact mB.cart.1.lift_fst _ _ w₁
    · exact (Over.w _).trans (Over.w _).symm
  refine ⟨⟨z₁, ?_⟩, Subtype.ext hz₁⟩
  have hinj : Function.Injective (algebraMap V (Kbar X)) := IsFractionRing.injective V _
  have : IsDominant j :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)⟩
  have := t.semi.separated
  have h₃ : spOver (IsScalarTower.toAlgHom U.Bp V (Kbar X)) ≫ (z₁ ^ p ^ n) =
      spOver (IsScalarTower.toAlgHom U.Bp V (Kbar X)) ≫ (1 : SpAlg U.Bp V ⟶ t.G) := by
    rw [MonObj.comp_pow, hz₁, z.2, MonObj.comp_one]
  have : IsReduced (SpAlg U.Bp V).left := inferInstanceAs (IsReduced (Sp V))
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated t.G.hom ((Over.w _).trans (Over.w _).symm) j
    (congrArg (fun q => q.left) h₃))

end GlobalTheory.GroupBplus.ValExt
