import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Twhopf

theorem valAt_restrict {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem top_le_of_le {Y X : Scheme.{0}} (x : Y ⟶ X) {U V : X.Opens} (i : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ U := fun _ hz => i (hV hz)

theorem top_le_of_mem {K : Type} [Field K] {X : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens}
    (z : Spec (CommRingCat.of K)) (hz : x z ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := fun w _ => by
  have e : w = z := Subsingleton.elim (α := PrimeSpectrum K) w z
  subst e
  exact hz

theorem sec_inj : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 := by
  intro R _ _ T _ _ Γ U s hs
  have := Γ.flat
  have := Γ.gen_reduced
  have hdom : IsDominant (genPt R).hom :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R (FractionRing R)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  have : IsSchemeTheoreticallyDominant (genPt R).hom := .of_isDominant _
  have : QuasiCompact (genPt R).hom :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  let j := pullback.fst Γ.G.hom (genPt R).hom
  apply j.app_injective U
  rw [map_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro z hz
  exfalso
  have hz' : j z ∈ Γ.G.left.basicOpen s := hz
  have hgen : (Γ.G.hom (j z)).asIdeal = ⊥ := by
    have e : Γ.G.hom (j z) = (genPt R).hom (pullback.snd Γ.G.hom (genPt R).hom z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [e]
    generalize pullback.snd Γ.G.hom (genPt R).hom z = w
    have hw : PrimeSpectrum.asIdeal (R := FractionRing R) w = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (PrimeSpectrum.isPrime (R := FractionRing R) w).ne_top
    change Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal (R := FractionRing R) w) = ⊥
    rw [hw]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hgen
  rw [← hx] at hz'
  have h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_mem _ x (Γ.G.left.basicOpen_le s hz')
  have h0 : (Γ.pt t).left.appLE U ⊤ h s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).1
    rw [map_zero]
    exact hs t h
  have h1 := Scheme.basicOpen_appLE (Γ.pt t).left ⊤ U h s
  rw [h0, Scheme.basicOpen_zero] at h1
  have h2 : x ∈ (⊤ : (genPt R).left.Opens) ⊓ (Γ.pt t).left ⁻¹ᵁ Γ.G.left.basicOpen s := ⟨trivial, hz'⟩
  rw [← h1] at h2
  exact h2

theorem reg_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t := by
  intro R _ _ T _ _ Γ U f
  refine ⟨fun h => ?_, fun ⟨s, hs⟩ g hg => ⟨U, hg, s, hs⟩⟩
  choose W hW s hs using fun g : U => h g.1 g.2
  let V : U → Γ.G.left.Opens := fun g => W g ⊓ U
  let sf : ∀ g : U, Γ(Γ.G.left, V g) := fun g =>
    (Γ.G.left.presheaf.map (homOfLE (inf_le_left : V g ≤ W g)).op).hom (s g)
  have hsf : ∀ (g : U) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V g), valAt (Γ.pt t).left (V g) h (sf g) = f t :=
    fun g t h => (valAt_restrict _ _ h (top_le_of_le _ inf_le_left h) _).trans (hs g t _)
  have hcomp : TopCat.Presheaf.IsCompatible Γ.G.left.sheaf.1 V sf := by
    intro a b
    have := sec_inj R T Γ (V a ⊓ V b)
      ((Γ.G.left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op).hom (sf a) -
        (Γ.G.left.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op).hom (sf b)) (fun t h => by
          rw [← SubOrder.valHom_apply, map_sub, SubOrder.valHom_apply, SubOrder.valHom_apply,
            valAt_restrict _ _ h (top_le_of_le _ inf_le_left h),
            valAt_restrict _ _ h (top_le_of_le _ inf_le_right h), hsf, hsf, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨σ, hσ, -⟩ := Γ.G.left.sheaf.existsUnique_gluing' V U (fun g => homOfLE inf_le_right)
    (fun g hg => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, hg⟩, hW ⟨g, hg⟩, hg⟩) sf hcomp
  refine ⟨σ, fun t ht => ?_⟩
  let x : Spec (CommRingCat.of (FractionRing R)) := default
  let g : U := ⟨(Γ.pt t).left x, ht (Set.mem_univ x)⟩
  have hg : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V g := top_le_of_mem (Γ.pt t).left x ⟨hW g, g.2⟩
  exact (valAt_restrict _ (homOfLE (inf_le_right : V g ≤ U)) hg ht σ).symm.trans
    ((congrArg (valAt (Γ.pt t).left (V g) hg) (hσ g)).trans (hsf g t hg))

section ops

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)

theorem regularAt_const (r : R) (g : Γ.G.left) : Γ.RegularAt (fun _ => algebraMap R _ r) g :=
  ⟨⊤, trivial, RegDenom.structHom Γ.G.hom ⊤ r, fun t h =>
    RegDenom.valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t)) ⊤ h r⟩

theorem regularAt_add_mul {f f' : T → FractionRing R} {g : Γ.G.left} (h : Γ.RegularAt f g)
    (h' : Γ.RegularAt f' g) :
    Γ.RegularAt (fun t => f t + f' t) g ∧ Γ.RegularAt (fun t => f t * f' t) g := by
  obtain ⟨U, hU, s, hs⟩ := h
  obtain ⟨V, hV, s', hs'⟩ := h'
  let a := (Γ.G.left.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom s
  let b := (Γ.G.left.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom s'
  have ha : ∀ t h, valAt (Γ.pt t).left (U ⊓ V) h a = f t := fun t h =>
    (valAt_restrict _ _ h (top_le_of_le _ inf_le_left h) _).trans (hs t _)
  have hb : ∀ t h, valAt (Γ.pt t).left (U ⊓ V) h b = f' t := fun t h =>
    (valAt_restrict _ _ h (top_le_of_le _ inf_le_right h) _).trans (hs' t _)
  refine ⟨⟨U ⊓ V, ⟨hU, hV⟩, a + b, fun t h => ?_⟩, ⟨U ⊓ V, ⟨hU, hV⟩, a * b, fun t h => ?_⟩⟩
  · rw [← SubOrder.valHom_apply, map_add, SubOrder.valHom_apply, SubOrder.valHom_apply, ha, hb]
  · rw [← SubOrder.valHom_apply, map_mul, SubOrder.valHom_apply, SubOrder.valHom_apply, ha, hb]

def btSub (U : Γ.G.left.Opens) : Subalgebra R (T → R) where
  carrier := Γ.btSet U
  mul_mem' hf hf' t g hg := by
    simpa only [Pi.mul_apply, map_mul] using (regularAt_add_mul Γ (hf t g hg) (hf' t g hg)).2
  add_mem' hf hf' t g hg := by
    simpa only [Pi.add_apply, map_add] using (regularAt_add_mul Γ (hf t g hg) (hf' t g hg)).1
  algebraMap_mem' r _ g _ := regularAt_const Γ r g

end ops

theorem mem_order : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U := by
  intro R _ _ T _ _ Γ U f
  exact ⟨fun h => Algebra.adjoin_le (S := btSub Γ U) (fun _ hx => hx) h, fun h => Algebra.subset_adjoin h⟩

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder in

theorem sub_order : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∃ (H : Subgroup T) (A : Subalgebra R (H → R)), (∀ t, t ∈ H ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsHopfOrder A ∧ ∀ f : H → R, f ∈ A ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : H) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  intro R _ _ _ T _ _ Γ U hF
  have hU := isAffineOpen_of_fin Γ hF
  letI : Algebra R Γ(Γ.G.left, U) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) :=
    fromSpec_hom Γ hU
  have hfin := sec_finite hρ hF
  have hproj := sec_projective hρ hF
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
  have hA : ∀ f : subH Γ hF → R, f ∈ Φ.range ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : subH Γ hF)
      (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
    intro f
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, fun t h => hΦ s t h⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, funext fun t => inj ((hΦ s t t.2).symm.trans (hs t t.2))⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    refine sec_inj R T Γ U s fun t h => ?_
    have := hΦ s ⟨t, h⟩ h
    rw [hs] at this
    simpa using this
  refine ⟨subH Γ hF, Φ.range, fun t => Iff.rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, hA⟩
  · exact Module.Finite.of_surjective Φ.rangeRestrict.toLinearMap Φ.rangeRestrict_surjective
  · exact Module.Projective.of_equiv (AlgEquiv.ofInjective Φ hinj).toLinearEquiv
  · classical
    have := Fintype.ofFinite (subH Γ hF)
    have hc : IsCompact (U : Set Γ.G.left) := hU.isCompact
    have h1 : ∀ h : subH Γ hF, ∃ d : R, d ≠ 0 ∧ d • (Pi.single h 1 : subH Γ hF → R) ∈ Φ.range := by
      intro h
      obtain ⟨d, hd, hreg⟩ := exists_den Γ hc (fun t => if t = (h : T) then 1 else 0)
      obtain ⟨s, hs⟩ := (reg_iff R T Γ U _).1 hreg
      refine ⟨d, hd, (hA _).2 ⟨s, fun t ht => ?_⟩⟩
      rw [hs t ht]
      by_cases e : t = h
      · subst e; simp
      · have : (t : T) ≠ h := fun e' => e (Subtype.ext e')
        simp [e, this]
    choose d hd hdA using h1
    refine ⟨∏ h, d h, Finset.prod_ne_zero_iff.2 fun h _ => hd h, fun f => ?_⟩
    have e : (∏ h, d h) • f = ∑ h, (f h * ∏ h' ∈ Finset.univ.erase h, d h') • (d h • (Pi.single h 1 : subH Γ hF → R)) := by
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

theorem regularAt_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left), (Γ.G.hom g).asIdeal = ⊥ → Γ.RegularAt f g := by
  intro R _ _ T _ _ Γ f g hg
  obtain ⟨d, hd, U, hU, s, hs⟩ := RegDenom.exists_denom_regularAt R T Γ f g
  let c : Γ(Γ.G.left, U) := RegDenom.structHom Γ.G.hom U d
  have hgW : g ∈ Γ.G.left.basicOpen c := by
    have e := Scheme.basicOpen_appLE Γ.G.hom U ⊤ (RegDenom.le_preimage_top Γ.G.hom U)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv d)
    rw [basicOpen_eq_of_affine] at e
    have e' : Γ.G.left.basicOpen c = _ := e
    rw [e']
    refine ⟨hU, ?_⟩
    change d ∉ (Γ.G.hom g).asIdeal
    rw [hg]
    exact hd
  let ρ := (Γ.G.left.presheaf.map (homOfLE (Γ.G.left.basicOpen_le c)).op).hom
  have hu : IsUnit (ρ c) := Γ.G.left.toRingedSpace.isUnit_res_basicOpen c
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  refine ⟨_, hgW, w * ρ s, fun t h => ?_⟩
  have hU' := top_le_of_le _ (Γ.G.left.basicOpen_le c) h
  have e1 : valAt (Γ.pt t).left _ h (ρ s) = algebraMap R _ d * f t :=
    (valAt_restrict _ _ h hU' _).trans (hs t hU')
  have e2 : valAt (Γ.pt t).left _ h (ρ c) = algebraMap R _ d :=
    (valAt_restrict _ _ h hU' _).trans (RegDenom.valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t)) U hU' d)
  have e3 := congrArg (SubOrder.valHom (Γ.pt t).left _ h) hw
  rw [map_mul, map_one, SubOrder.valHom_apply _ _ _ (ρ c), e2] at e3
  rw [← SubOrder.valHom_apply, map_mul, SubOrder.valHom_apply _ _ _ (ρ s), e1, ← _root_.mul_assoc, e3, _root_.one_mul]

end PositivityTheory.HtPt.Twhopf
