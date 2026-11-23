import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGermStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

section TanDer

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (s : S)
  (β : S.presheaf.stalk s →+* R) {n : ℕ} {V : S.Opens} (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R)

def tanVal {U : G.left.Opens} {V' : S.Opens} (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V')
    (f : Γ(G.left, U)) : R :=
  ∑ i, w i * β (S.presheaf.germ V' s hs' (dualApp (τ i) hV (dUnit G he f)))

theorem tanVal_mono {U : G.left.Opens} {V' V'' : S.Opens} (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U)
    (hs' : s ∈ V') (k : V'' ≤ V') (hs'' : s ∈ V'') (f : Γ(G.left, U)) :
    tanVal G s β τ w (k.trans hV) (k.trans he) hs'' f = tanVal G s β τ w hV he hs' f := by
  unfold tanVal
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← resM_dUnit G he k f, dualApp_resM]
  congr 2
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem tanVal_indep {U : G.left.Opens} {V₁ V₂ : S.Opens} (hV₁ : V₁ ≤ V) (he₁ : V₁ ≤ unitSec G ⁻¹ᵁ U)
    (hs₁ : s ∈ V₁) (hV₂ : V₂ ≤ V) (he₂ : V₂ ≤ unitSec G ⁻¹ᵁ U) (hs₂ : s ∈ V₂) (f : Γ(G.left, U)) :
    tanVal G s β τ w hV₁ he₁ hs₁ f = tanVal G s β τ w hV₂ he₂ hs₂ f :=
  (tanVal_mono G s β τ w hV₁ he₁ hs₁ (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ⟨hs₁, hs₂⟩ f).symm.trans
    (tanVal_mono G s β τ w hV₂ he₂ hs₂ (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ⟨hs₁, hs₂⟩ f)

theorem tanVal_resG {U U' : G.left.Opens} (k : U' ≤ U) {V' : S.Opens} (hV : V' ≤ V)
    (he : V' ≤ unitSec G ⁻¹ᵁ U') (hs' : s ∈ V') (f : Γ(G.left, U)) :
    tanVal G s β τ w hV he hs' (resG _ k f) =
      tanVal G s β τ w hV (he.trans ((unitSec G).preimage_mono k)) hs' f := by
  unfold tanVal
  simp only [dUnit_resG]

variable {s}

theorem mem_inf_unitSec (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) : s ∈ V ⊓ unitSec G ⁻¹ᵁ U :=
  Opens.mem_inf.2 ⟨hs, hU⟩

def tanCan (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (f : Γ(G.left, U)) : R :=
  tanVal G s β τ w (V' := V ⊓ unitSec G ⁻¹ᵁ U) inf_le_left inf_le_right (mem_inf_unitSec G hs hU) f

theorem tanCan_eq (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) {V' : S.Opens} (hV : V' ≤ V)
    (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V') (f : Γ(G.left, U)) :
    tanCan G β τ w hs hU f = tanVal G s β τ w hV he hs' f :=
  tanVal_indep G s β τ w _ _ _ _ _ _ f

theorem tanCan_res (hs : s ∈ V) {U U' : G.left.Opens} (k : U' ≤ U) (hU' : unitSec G s ∈ U') (f : Γ(G.left, U)) :
    tanCan G β τ w hs hU' (resG _ k f) = tanCan G β τ w hs (k hU') f := by
  rw [tanCan, tanVal_resG]
  exact (tanCan_eq G β τ w hs (k hU') _ _ _ f).symm

theorem tanCan_germ_eq (hs : s ∈ V) {U U' : G.left.Opens} (hU : unitSec G s ∈ U) (hU' : unitSec G s ∈ U')
    (f : Γ(G.left, U)) (f' : Γ(G.left, U'))
    (h : G.left.presheaf.germ U _ hU f = G.left.presheaf.germ U' _ hU' f') :
    tanCan G β τ w hs hU f = tanCan G β τ w hs hU' f' := by
  obtain ⟨W, hW, iU, iU', e⟩ := TopCat.Presheaf.germ_eq _ _ hU hU' f f' h
  have h1 := tanCan_res G β τ w hs iU.le hW f
  have h2 := tanCan_res G β τ w hs iU'.le hW f'
  have e' : resG _ iU.le f = resG _ iU'.le f' := e
  rw [← h1, ← h2, e']

theorem tanCan_add (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (a b : Γ(G.left, U)) :
    tanCan G β τ w hs hU (a + b) = tanCan G β τ w hs hU a + tanCan G β τ w hs hU b := by
  unfold tanCan tanVal
  simp only [map_add, mul_add, Finset.sum_add_distrib]

theorem tanCan_mul (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (a b : Γ(G.left, U))
    (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s)
    (hε : ∀ f : Γ(G.left, U), ε (G.left.presheaf.germ U _ hU f) =
      S.presheaf.germ (V ⊓ unitSec G ⁻¹ᵁ U) s (mem_inf_unitSec G hs hU) ((unitSec G).appLE U _ inf_le_right f)) :
    tanCan G β τ w hs hU (a * b) = β (ε (G.left.presheaf.germ U _ hU a)) * tanCan G β τ w hs hU b +
      β (ε (G.left.presheaf.germ U _ hU b)) * tanCan G β τ w hs hU a := by
  rw [hε, hε]
  unfold tanCan tanVal
  simp only [dUnit_mul, map_add, map_smul, smul_eq_mul, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

def tanStalk (hs : s ∈ V) (x : G.left.presheaf.stalk (unitSec G s)) : R :=
  tanCan G β τ w hs (TopCat.Presheaf.germ_exist _ x).choose_spec.choose
    (TopCat.Presheaf.germ_exist _ x).choose_spec.choose_spec.choose

theorem tanStalk_germ (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (f : Γ(G.left, U)) :
    tanStalk G β τ w hs (G.left.presheaf.germ U _ hU f) = tanCan G β τ w hs hU f := by
  unfold tanStalk
  apply tanCan_germ_eq
  exact (TopCat.Presheaf.germ_exist _ _).choose_spec.choose_spec.choose_spec

end TanDer

theorem germ_exist_two {X : Scheme.{0}} (p : X) (x y : X.presheaf.stalk p) :
    ∃ (U : X.Opens) (hU : p ∈ U) (a b : Γ(X, U)), X.presheaf.germ U p hU a = x ∧ X.presheaf.germ U p hU b = y := by
  obtain ⟨U₁, h₁, a, rfl⟩ := TopCat.Presheaf.germ_exist _ x
  obtain ⟨U₂, h₂, b, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  exact ⟨U₁ ⊓ U₂, Opens.mem_inf.2 ⟨h₁, h₂⟩, resG _ inf_le_left a, resG _ inf_le_right b,
    TopCat.Presheaf.germ_res_apply _ _ _ _ _, TopCat.Presheaf.germ_res_apply _ _ _ _ _⟩

theorem exists_stalkDer_of_lie : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) (β : S.presheaf.stalk s →+* R) (n : ℕ) (V : S.Opens) (hs : s ∈ V) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), StalkData G s π ε m → ∃ δ : G.left.presheaf.stalk (unitSec G s) →+ R, (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) ∧ (∀ a, δ (π a) = 0) ∧ ∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V') (f : Γ(G.left, U)), δ (G.left.presheaf.germ U _ hU f) = ∑ i, w i * β (S.presheaf.germ V' s hs' (dualApp (τ i) hV (dUnit G he f))) := by
  intro S G _ R _ s π ε m β n V hs τ w hD
  have hI := GlobalTheory.T.groupSchemeUnitStalkData_germ S G s π ε m hD
  refine ⟨AddMonoidHom.mk' (tanStalk G β τ w hs) ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨U, hU, a, b, rfl, rfl⟩ := germ_exist_two (unitSec G s) x y
    rw [← map_add, tanStalk_germ, tanStalk_germ, tanStalk_germ, tanCan_add]
  · intro x y
    obtain ⟨U, hU, a, b, rfl, rfl⟩ := germ_exist_two (unitSec G s) x y
    simp only [AddMonoidHom.mk'_apply]
    rw [← map_mul, tanStalk_germ, tanStalk_germ, tanStalk_germ,
      tanCan_mul G β τ w hs hU a b ε (fun f => hI.2.1 U hU _ _ inf_le_right f)]
  · intro a
    obtain ⟨V₀, h₀, a₀, rfl⟩ := TopCat.Presheaf.germ_exist _ a
    have hU : unitSec G s ∈ G.hom ⁻¹ᵁ V₀ := by
      show (unitSec G ≫ G.hom) s ∈ V₀
      rw [sec_hom]
      exact h₀
    rw [hI.1 V₀ h₀ _ hU le_rfl a₀]
    simp only [AddMonoidHom.mk'_apply, tanStalk_germ, tanCan, tanVal, dUnit_base, map_zero, mul_zero,
      Finset.sum_const_zero]
  · intro U hU V' hV he hs' f
    simp only [AddMonoidHom.mk'_apply]
    rw [tanStalk_germ]
    exact tanCan_eq G β τ w hs hU hV he hs' f

end GlobalTheory.Nef
