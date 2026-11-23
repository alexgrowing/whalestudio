import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldPullbackBaseChangeDerivationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerOfCohomologousCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductAffineOpenClosureLegsEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecAppLETopEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfIsTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeformationChartPointSpecMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDerivationsEqZeroKillingBothFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoOntoPullbackIntertwinesTransitionsStatement
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

namespace GlobalTheory.KSBaseChange

theorem isTranslate_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R S S' : Type) [CommRing R] [CommRing S] [CommRing S'] (φ : R →+* S) (ψ : S →+* S') (g₀ : Sp S ⟶ t.G.left) (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), IsTranslate t φ g₀ v w → IsTranslate t (ψ.comp φ) (spMap ψ ≫ g₀) v (spMap (dualMap ψ) ≫ w) := by
  intro E _ _ _ H X t R S S' _ _ _ φ ψ g₀ v w ⟨g', v', h₁, h₂, h₃⟩
  have e1 : spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp']
    congr 1
    refine RingHom.ext fun a => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let h : tEpsG ((spMap ψ ≫ g₀) ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) := Over.homMk (spMap (dualMap ψ)) (by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom =
      spMap (algebraMap S' (DualNumber S')) ≫ (spMap ψ ≫ g₀) ≫ t.G.hom
    rw [← Category.assoc, e1]; simp only [Category.assoc])
  refine ⟨h ≫ g', h ≫ v', ?_, ?_, ?_⟩
  · rw [Over.comp_left, h₁]
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ = _
    rw [← Category.assoc, e1, Category.assoc]
  · rw [Over.comp_left, h₂]
    show spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ v = _
    rw [← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.dualMap_comp']
  · rw [← MonObj.comp_mul, Over.comp_left, h₃]
    rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isTranslate_push {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {g : X' ⟶ X} (mu : SABMap t' t g)
    (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) {vb : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left}
    {vb' : Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left} (hvb : IsTanAtG t (chart U) vb) (hvb' : IsTanAtG t' (chart U') vb')
    (hvv : vb' ≫ mu.φ = spMap (dualMap (g.appLE U.1 U'.1 hU).hom) ≫ vb) {S : Type} [CommRing S]
    (φS : Γ(X', U'.1) →+* S) (g₀ : Sp S ⟶ t'.G.left) (hg₀ : g₀ ≫ t'.G.hom = spMap φS ≫ chart U')
    (w' : Sp (DualNumber S) ⟶ t'.G.left) (hw' : IsTranslate t' φS g₀ vb' w') :
    IsTranslate t (φS.comp (g.appLE U.1 U'.1 hU).hom) (g₀ ≫ mu.φ) vb (w' ≫ mu.φ) := by
  have hx : chart U' ≫ g = spMap (g.appLE U.1 U'.1 hU).hom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 U'.2 hU).symm
  have hg : (g₀ ≫ mu.φ) ≫ t.G.hom = spMap (φS.comp (g.appLE U.1 U'.1 hU).hom) ≫ chart U := by
    rw [Category.assoc, mu.cart.1.w, ← Category.assoc, hg₀, Category.assoc, hx, ← Category.assoc,
      GlobalTheory.LogKSLoc.spMap_comp']
  obtain ⟨w, hw, -⟩ := existsUnique_isTranslate t (φS.comp (g.appLE U.1 U'.1 hU).hom) hg hvb
  obtain ⟨w'', h1, h2⟩ := GlobalTheory.T.tangentTranslate_lifts_semiAbelianTripleMap E H X X' t t' g mu _ _ (g.appLE U.1 U'.1 hU).hom (chart U) (chart U') hx vb vb'
    hvb hvb' hvv S φS g₀ hg₀ w hw
  obtain ⟨_, _, huniq⟩ := existsUnique_isTranslate t' φS hg₀ hvb'
  have e : w'' = w' := (huniq _ h2).trans (huniq _ hw').symm
  rw [← e, h1]
  exact hw

end GlobalTheory.KSBaseChange

namespace GlobalTheory.KSBaseChange

theorem valR_add_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a + b) = valR x O a + valR x O b := by
  simp only [valR, dif_pos h, map_add]

theorem valR_zero' {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens) :
    valR x O 0 = 0 := by
  unfold valR; split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem red_translate {X : Scheme.{0}} (t : SAB H X) {R S : Type} [CommRing R] [CommRing S] {φ : R →+* S}
    {x : Sp R ⟶ X} {g₀ : Sp S ⟶ t.G.left} {v : Sp (DualNumber R) ⟶ t.G.left} {w : Sp (DualNumber S) ⟶ t.G.left}
    (hg : g₀ ≫ t.G.hom = spMap φ ≫ x) (hv : IsTanAtG t x v) (hw : IsTranslate t φ g₀ v w) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ :=
  GlobalTheory.LogKS.IsTranslate.fst_comp E H X t R S φ x g₀ v w hg hv hw

theorem fst_valR_of_red {Y : Scheme.{0}} {S : Type} [CommRing S] {g₀ : Sp S ⟶ Y} {w : Sp (DualNumber S) ⟶ Y}
    (hr : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀) {O : Y.Opens} (h : ⊤ ≤ g₀ ⁻¹ᵁ O) (x : Γ(Y, O)) :
    (valR w O x).fst = valR g₀ O x := by
  conv_rhs => rw [← hr]
  rw [GlobalTheory.CechKS.valR_spMap_comp _ _ _ (GlobalTheory.CechKS.le_preimage_of_red hr h)]
  rfl

theorem snd_dualMap {S S' : Type} [CommRing S] [CommRing S'] (σ : S →+* S') (y : DualNumber S) :
    (dualMap σ y).snd = σ y.snd := by
  simp [dualMap]

theorem rel_pair {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {g : X' ⟶ X} (mu : SABMap t' t g)
    (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) {n : ℕ}
    {v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)} {v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left)}
    (hv : ∀ i, IsTanAtG t (chart U) (v i)) (hv' : ∀ i, IsTanAtG t' (chart U') (v' i))
    (hvv : ∀ i, v' i ≫ mu.φ = spMap (dualMap (g.appLE U.1 U'.1 hU).hom) ≫ v i) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1))
    {j₁ j₂ : t.PP.L.ι} {W₁ W₂ : t.G.left.Opens} (hW₁ : W₁ ≤ t.G.hom ⁻¹ᵁ U.1)
    (d₁ d₂ : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O))
    (hrel : ∀ (O : t.G.left.Opens), O ≤ W₁ ⊓ W₂ → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S]
      (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)),
      g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) →
      valR g₀ O (d₁ O f - d₂ O f) =
        ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g j₁ j₂).val).snd * valR g₀ _ (t.PP.L.g j₁ j₂)⁻¹.val) *
          (valR (w a) O f).snd)
    (D' : Γ(X', U'.1) → Γ(X', U'.1)) (e₁ e₂ : ∀ O : t'.G.left.Opens, Γ(t'.G.left, O) → Γ(t'.G.left, O))
    (he₁ : IsField (mu.φ ⁻¹ᵁ W₁ ⊓ t'.G.hom ⁻¹ᵁ U'.1) e₁) (he₂ : IsField (mu.φ ⁻¹ᵁ W₂ ⊓ t'.G.hom ⁻¹ᵁ U'.1) e₂)
    (hl₁ : ∀ (O' : t'.G.left.Opens) (h' : O' ≤ t'.G.hom ⁻¹ᵁ U'.1), O' ≤ mu.φ ⁻¹ᵁ W₁ → ∀ r,
      e₁ O' ((t'.G.hom.appLE U'.1 O' h').hom r) = (t'.G.hom.appLE U'.1 O' h').hom (D' r))
    (hl₂ : ∀ (O' : t'.G.left.Opens) (h' : O' ≤ t'.G.hom ⁻¹ᵁ U'.1), O' ≤ mu.φ ⁻¹ᵁ W₂ → ∀ r,
      e₂ O' ((t'.G.hom.appLE U'.1 O' h').hom r) = (t'.G.hom.appLE U'.1 O' h').hom (D' r))
    (hc₁ : ∀ (O : t.G.left.Opens) (O' : t'.G.left.Opens) (h : O' ≤ mu.φ ⁻¹ᵁ O), O ≤ W₁ → O' ≤ t'.G.hom ⁻¹ᵁ U'.1 →
      ∀ f, e₁ O' ((mu.φ.appLE O O' h).hom f) = (mu.φ.appLE O O' h).hom (d₁ O f))
    (hc₂ : ∀ (O : t.G.left.Opens) (O' : t'.G.left.Opens) (h : O' ≤ mu.φ ⁻¹ᵁ O), O ≤ W₂ → O' ≤ t'.G.hom ⁻¹ᵁ U'.1 →
      ∀ f, e₂ O' ((mu.φ.appLE O O' h).hom f) = (mu.φ.appLE O O' h).hom (d₂ O f))
    (Ω : t'.G.left.Opens) (hΩ : Ω ≤ mu.φ ⁻¹ᵁ (t.PP.L.U j₁ ⊓ t.PP.L.U j₂))
    (O : t'.G.left.Opens) (hO : O ≤ mu.φ ⁻¹ᵁ (W₁ ⊓ W₂) ⊓ t'.G.hom ⁻¹ᵁ U'.1) (hOΩ : O ≤ Ω) (f : Γ(t'.G.left, O))
    (S : Type) [CommRing S] (φS : Γ(X', U'.1) →+* S) (g₀ : Sp S ⟶ t'.G.left)
    (w : Fin n → (Sp (DualNumber S) ⟶ t'.G.left))
    (hg₀ : g₀ ≫ t'.G.hom = spMap φS ≫ chart U') (hO₀ : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (hw : ∀ b, IsTranslate t' φS g₀ (v' b) (w b)) :
    valR g₀ O (e₁ O f - e₂ O f) =
      ∑ b, ∑ b', φS (((g.appLE U.1 U'.1 hU).hom.mapMatrix Θ) b b') *
        ((valR (w b') Ω (res hΩ (pullU mu.φ _ (t.PP.L.g j₁ j₂))).val).snd *
          valR g₀ Ω (res hΩ (pullU mu.φ _ (t.PP.L.g j₁ j₂)))⁻¹.val) * (valR (w b) O f).snd := by
  have hreg₁ : ∀ {O'' : t'.G.left.Opens}, O'' ≤ O → O'' ≤ mu.φ ⁻¹ᵁ W₁ ⊓ t'.G.hom ⁻¹ᵁ U'.1 := fun h =>
    h.trans (hO.trans (inf_le_inf_right _ (mu.φ.preimage_mono inf_le_left)))
  have hreg₂ : ∀ {O'' : t'.G.left.Opens}, O'' ≤ O → O'' ≤ mu.φ ⁻¹ᵁ W₂ ⊓ t'.G.hom ⁻¹ᵁ U'.1 := fun h =>
    h.trans (hO.trans (inf_le_inf_right _ (mu.φ.preimage_mono inf_le_right)))
  suffices key : ∀ (S : Type) [CommRing S] [IsLocalRing S] (φS : Γ(X', U'.1) →+* S) (g₀ : Sp S ⟶ t'.G.left)
      (w : Fin n → (Sp (DualNumber S) ⟶ t'.G.left)), g₀ ≫ t'.G.hom = spMap φS ≫ chart U' → ⊤ ≤ g₀ ⁻¹ᵁ O →
      (∀ b, IsTranslate t' φS g₀ (v' b) (w b)) → valR g₀ O (e₁ O f - e₂ O f) =
      ∑ b, ∑ b', φS (((g.appLE U.1 U'.1 hU).hom.mapMatrix Θ) b b') *
        ((valR (w b') Ω (res hΩ (pullU mu.φ _ (t.PP.L.g j₁ j₂))).val).snd *
          valR g₀ Ω (res hΩ (pullU mu.φ _ (t.PP.L.g j₁ j₂)))⁻¹.val) * (valR (w b) O f).snd by
    have hred : ∀ b, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w b = g₀ := fun b =>
      red_translate t' hg₀ (hv' b) (hw b)
    have hΩ₀ : ⊤ ≤ g₀ ⁻¹ᵁ Ω := fun p hp => hOΩ (hO₀ hp)
    refine Module.eq_of_localization_maximal (R := S) (fun P _ => Localization.AtPrime P)
      (fun P _ => Algebra.linearMap S _) _ _ fun P _ => ?_
    simp only [Algebra.linearMap_apply]
    set σ := algebraMap S (Localization.AtPrime P) with hσ
    have k := key (Localization.AtPrime P) (σ.comp φS) (spMap σ ≫ g₀) (fun b => spMap (dualMap σ) ≫ w b)
      (by rw [Category.assoc, hg₀, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp'])
      (fun p _ => hO₀ (Set.mem_univ ((spMap σ).base p)))
      (fun b => isTranslate_baseChange E H X' t' _ _ _ φS σ g₀ (v' b) (w b) (hw b))
    rw [← GlobalTheory.CechKS.valR_spMap_comp σ g₀ O hO₀, k, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [GlobalTheory.CechKS.valR_spMap_comp _ _ _ (GlobalTheory.CechKS.le_preimage_of_red (hred b') hΩ₀),
      GlobalTheory.CechKS.valR_spMap_comp _ _ _ (GlobalTheory.CechKS.le_preimage_of_red (hred b) hO₀),
      GlobalTheory.CechKS.valR_spMap_comp σ g₀ Ω hΩ₀, snd_dualMap, snd_dualMap, map_mul, map_mul, map_mul]
    rfl
  intro S _ _ φS g₀ w hg₀ hO₀ hw
  set ψ := (g.appLE U.1 U'.1 hU).hom with hψ
  have hred : ∀ b, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w b = g₀ := fun b =>
    red_translate t' hg₀ (hv' b) (hw b)
  have hwO : ∀ b {O'' : t'.G.left.Opens}, ⊤ ≤ g₀ ⁻¹ᵁ O'' → ⊤ ≤ w b ⁻¹ᵁ O'' := fun b _ h =>
    GlobalTheory.CechKS.le_preimage_of_red (hred b) h
  have hΩ₀ : ⊤ ≤ g₀ ⁻¹ᵁ Ω := fun p hp => hOΩ (hO₀ hp)
  set c : Fin n → Fin n → S := fun b b' => φS ((ψ.mapMatrix Θ) b b') *
    ((valR (w b') Ω (res hΩ (pullU mu.φ _ (t.PP.L.g j₁ j₂))).val).snd *
      valR g₀ Ω (res hΩ (pullU mu.φ _ (t.PP.L.g j₁ j₂)))⁻¹.val) with hc
  let Δ : ∀ O'' : t'.G.left.Opens, Γ(t'.G.left, O'') → S := fun O'' x =>
    valR g₀ O'' (e₁ O'' x - e₂ O'' x) - ∑ b, ∑ b', c b b' * (valR (w b) O'' x).snd
  have hpb : IsPullback mu.φ t'.G.hom t.G.hom g := mu.cart.1
  have hsq : (g₀ ≫ mu.φ) ≫ t.G.hom = spMap (φS.comp ψ) ≫ chart U := by
    have hx : chart U' ≫ g = spMap ψ ≫ chart U := (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 U'.2 hU).symm
    rw [Category.assoc, hpb.w, ← Category.assoc, hg₀, Category.assoc, hx, ← Category.assoc,
      GlobalTheory.LogKSLoc.spMap_comp']
  have key := GlobalTheory.T.pointDerivations_eq_zero_killing_both_factors _ _ _ _ t.G.hom t'.G.hom mu.φ g hpb U U' hU (W₁ ⊓ W₂) (inf_le_left.trans hW₁) O hO S g₀ hO₀ Δ
    ?add ?mul ?res ?gen₁ ?gen₂ f
  · exact sub_eq_zero.1 key
  case add =>
    intro O' hO' h x y
    have hA : ∀ b, valR (w b) O' (x + y) = valR (w b) O' x + valR (w b) O' y := fun b =>
      valR_add_of_le _ _ (hwO b h) x y
    simp only [Δ, (he₁.1 O' (hreg₁ hO')), (he₂.1 O' (hreg₂ hO')), hA, TrivSqZeroExt.snd_add, mul_add,
      Finset.sum_add_distrib]
    rw [add_sub_add_comm, valR_add_of_le _ _ h]
    ring
  case mul =>
    intro O' hO' h x y
    have hM : ∀ b, (valR (w b) O' (x * y)).snd = valR g₀ O' x * (valR (w b) O' y).snd +
        valR g₀ O' y * (valR (w b) O' x).snd := fun b => by
      rw [GlobalTheory.CechKSSmul.valR_mul_of_le _ _ (hwO b h), TrivSqZeroExt.snd_mul, fst_valR_of_red (hred b) h,
        fst_valR_of_red (hred b) h]
      simp [smul_eq_mul, MulOpposite.smul_eq_mul_unop]
      ring
    have hS : ∀ (a : S) (F : Fin n → S), ∑ b, ∑ b', c b b' * (a * F b) = a * ∑ b, ∑ b', c b b' * F b := by
      intro a F
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [Δ, (he₁.2.1 O' (hreg₁ hO')), (he₂.2.1 O' (hreg₂ hO')), hM, mul_add, Finset.sum_add_distrib, hS]
    rw [GlobalTheory.CechKSSmul.valR_sub_of_le _ _ h, GlobalTheory.CechKSSmul.valR_sub_of_le _ _ h,
      GlobalTheory.CechKSSmul.valR_sub_of_le _ _ h]
    simp only [valR_add_of_le _ _ h, GlobalTheory.CechKSSmul.valR_mul_of_le _ _ h]
    ring
  case res =>
    intro O₁ O₂ h hO₁ hO₂ x
    simp only [Δ]
    rw [(he₁.2.2 O₁ O₂ h (hreg₁ hO₁)), (he₂.2.2 O₁ O₂ h (hreg₂ hO₁)), ← map_sub,
      GlobalTheory.CechKS.valR_resG g₀ h hO₂]
    congr 1
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [GlobalTheory.CechKS.valR_resG (w b) h (hwO b hO₂)]
  case gen₁ =>
    intro O₀ O' h hO₀W hO' hO'₀ f₀
    have hU' : O' ≤ t'.G.hom ⁻¹ᵁ U'.1 := hO'.trans (hO.trans inf_le_right)
    have hpt : ⊤ ≤ (g₀ ≫ mu.φ) ⁻¹ᵁ O₀ := fun p hp => h (hO'₀ hp)
    simp only [Δ]
    rw [hc₁ O₀ O' h (hO₀W.trans inf_le_left) hU', hc₂ O₀ O' h (hO₀W.trans inf_le_right) hU', ← map_sub,
      GlobalTheory.CechKSSmul.valR_appLE_comp g₀ mu.φ O₀ O' h hO'₀,
      hrel O₀ hO₀W f₀ S (φS.comp ψ) (g₀ ≫ mu.φ) (fun b => w b ≫ mu.φ) hsq hpt
        (fun b => isTranslate_push mu U U' hU (hv b) (hv' b) (hvv b) φS g₀ hg₀ (w b) (hw b)), sub_eq_zero]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    have hu2 : (res hΩ (pullU mu.φ _ (t.PP.L.g j₁ j₂)))⁻¹.val =
        (mu.φ.appLE _ Ω hΩ).hom (t.PP.L.g j₁ j₂)⁻¹.val := by
      rw [← map_inv, ← map_inv]; rfl
    have hu1 : (res hΩ (pullU mu.φ _ (t.PP.L.g j₁ j₂))).val = (mu.φ.appLE _ Ω hΩ).hom (t.PP.L.g j₁ j₂).val := rfl
    simp only [hc]
    rw [hu1, hu2, GlobalTheory.CechKSSmul.valR_appLE_comp (w b') mu.φ _ Ω hΩ (hwO b' hΩ₀),
      GlobalTheory.CechKSSmul.valR_appLE_comp g₀ mu.φ _ Ω hΩ hΩ₀,
      GlobalTheory.CechKSSmul.valR_appLE_comp (w b) mu.φ O₀ O' h (hwO b hO'₀)]
    rfl
  case gen₂ =>
    intro O' h hO' hO'₀ r
    have hW : ∀ b, w b ≫ t'.G.hom = spMap ((algebraMap S (DualNumber S)).comp φS) ≫ chart U' := fun b => by
      obtain ⟨g', v'', -, -, h3⟩ := hw b
      rw [← h3, Over.w]
      show spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t'.G.hom = _
      rw [hg₀, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
    have hz : ∀ b, (valR (w b) O' ((t'.G.hom.appLE U'.1 O' h).hom r)).snd = 0 := fun b => by
      rw [GlobalTheory.KSRechart.valR_appLE t'.G.hom U' _ (w b) (hW b) h (hwO b hO'₀) r]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    simp only [Δ, hz, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [hl₁ O' h (hO'.trans (hreg₁ le_rfl) |>.trans inf_le_left), hl₂ O' h (hO'.trans (hreg₂ le_rfl) |>.trans inf_le_left),
      sub_self, valR_zero']

end GlobalTheory.KSBaseChange

namespace GlobalTheory.KSBaseChange

theorem isKS_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (g : X' ⟶ X) (mu : SABMap t' t g) (V : X.Opens) (V' : X'.Opens) (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1), U'.1 ⊓ V' ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ i, IsTanAtG t' (chart U') (v' i)) → (∀ i, v' i ≫ mu.φ = spMap (dualMap (g.appLE U.1 U'.1 hU).hom) ≫ v i) → ∀ (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ Θ : Matrix (Fin n) (Fin n) Γ(X, U.1), IsKS t V U v D Θ → IsKS t' V' U' v' D' ((g.appLE U.1 U'.1 hU).hom.mapMatrix Θ) := by
  intro E _ _ _ H X X' t t' g mu V V' U U' hU hUV n v v' hv hv' hvv D D' hD Θ hKS
  obtain ⟨J, W, j, d, hcov, hWj, hfld, hlift, hrel⟩ := hKS
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup W i).trans (hcov.le.trans (t.G.hom.preimage_mono inf_le_left))
  have hpb : IsPullback mu.φ t'.G.hom t.G.hom g := mu.cart.1
  choose e he hel hec using fun i => GlobalTheory.T.exists_vectorField_pullback_baseChange_derivation _ _ _ _ t.G.hom t'.G.hom mu.φ g hpb U U' hU D D' hD (W i) (hWU i)
    (d i) (hfld i) (hlift i (hWU i))
  obtain ⟨w, hwg, -⟩ := mu.lin
  let W' : J × t'.PP.L.ι → t'.G.left.Opens := fun q =>
    mu.φ ⁻¹ᵁ W q.1 ⊓ t'.G.hom ⁻¹ᵁ (U'.1 ⊓ V') ⊓ t'.PP.L.U q.2
  have hW'1 : ∀ q, W' q ≤ mu.φ ⁻¹ᵁ W q.1 := fun q => inf_le_left.trans inf_le_left
  have hW'2 : ∀ q, W' q ≤ t'.G.hom ⁻¹ᵁ U'.1 := fun q =>
    inf_le_left.trans (inf_le_right.trans (t'.G.hom.preimage_mono inf_le_left))
  have hW'L : ∀ q, W' q ≤ (t.PP.L.pull mu.φ).U (fun _ => j q.1) ⊓ t'.PP.L.U q.2 := fun q =>
    le_inf (fun y hy => Set.mem_iInter.2 fun _ => hWj q.1 (hW'1 q hy)) inf_le_right
  have hΩ : ∀ q q', W' q ⊓ W' q' ≤ mu.φ ⁻¹ᵁ (t.PP.L.U (j q.1) ⊓ t.PP.L.U (j q'.1)) := fun q q' y hy =>
    ⟨hWj _ (hW'1 q hy.1), hWj _ (hW'1 q' hy.2)⟩
  refine GlobalTheory.T.isKodairaSpencer_of_cohomologous_cocycle E H X' t' V' U' n v' hv' D' _ (J × t'.PP.L.ι) W' Prod.snd (fun q => e q.1)
    (fun q => inf_le_right) (fun q => res (hW'L q) (w.s (fun _ => j q.1, q.2)))
    (fun q q' => res (hΩ q q') (pullU mu.φ _ (t.PP.L.g (j q.1) (j q'.1)))) ?_ ?_ ?_ ?_ ?_
  · refine le_antisymm (iSup_le fun q => inf_le_left.trans inf_le_right) fun y hy => ?_
    have h1 : mu.φ y ∈ ⨆ i, W i := by
      rw [hcov]
      have : (mu.φ ≫ t.G.hom) y ∈ U.1 ⊓ V := by
        rw [hpb.w, Scheme.Hom.comp_apply]
        exact ⟨hU hy.1, hUV hy⟩
      exact this
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
    have h2 : y ∈ ⨆ k, t'.PP.L.U k := by rw [t'.PP.isLB.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, k), ⟨⟨hi, hy⟩, hk⟩⟩
  · intro q
    have hle : W' q ≤ mu.φ ⁻¹ᵁ W q.1 ⊓ t'.G.hom ⁻¹ᵁ U'.1 := le_inf (hW'1 q) (hW'2 q)
    exact ⟨fun O hO => (he q.1).1 O (hO.trans hle), fun O hO => (he q.1).2.1 O (hO.trans hle),
      fun O O' h' hO => (he q.1).2.2 O O' h' (hO.trans hle)⟩
  · intro q h r
    exact hel q.1 (W' q) h (hW'1 q) r
  · intro q q'
    exact GlobalTheory.T.bundleIsoOntoPullback_intertwines_transitions _ _ mu.φ t.PP.L t'.PP.L w hwg (j q.1) (j q'.1) q.2 q'.2 (W' q) (W' q') (hW'L q) (hW'L q')
      inf_le_right inf_le_right (hΩ q q')
  · intro q q' O hO f S _ φS g₀ w' hg₀ hO₀ hw'
    have hO' : O ≤ mu.φ ⁻¹ᵁ (W q.1 ⊓ W q'.1) ⊓ t'.G.hom ⁻¹ᵁ U'.1 := fun y hy =>
      ⟨⟨hW'1 q (hO hy).1, hW'1 q' (hO hy).2⟩, hW'2 q (hO hy).1⟩
    exact rel_pair mu U U' hU hv hv' hvv Θ (hWU q.1) (d q.1) (d q'.1) (hrel q.1 q'.1) D' (e q.1) (e q'.1) (he q.1)
      (he q'.1) (hel q.1) (hel q'.1) (hec q.1) (hec q'.1) (W' q ⊓ W' q') (hΩ q q') O hO' hO f S φS g₀ w' hg₀ hO₀ hw'

end GlobalTheory.KSBaseChange
