import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivationsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationLiftSmoothOverFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Cocycle

theorem rsT_of_le {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    rsT s O = (Y.presheaf.map (homOfLE h).op).hom s := by
  unfold rsT; rw [dif_pos h]

theorem rsT_rsT {Y : Scheme.{0}} {O₀ O₁ O₂ : Y.Opens} (h : O₁ ≤ O₀) (h' : O₂ ≤ O₁) (s : Γ(Y, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le h', rsT_of_le h, rsT_of_le (h'.trans h), ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_add {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s t : Γ(Y, O₀)) :
    rsT (s + t) O = rsT s O + rsT t O := by
  simp only [rsT_of_le h, map_add]

theorem rsT_sub {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s t : Γ(Y, O₀)) :
    rsT (s - t) O = rsT s O - rsT t O := by
  simp only [rsT_of_le h, map_sub]

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  unfold pbT
  rw [dif_pos (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]
  have : (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _ := by
    change 𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _
    simp
  rw [this]; rfl

theorem constFn_zero' {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) :
    constFn q O (0 : K) = 0 := by
  simp [constFn]

theorem locDerK_sub {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D : R → K} {W₁ W₂ W₀ : X.Opens} {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂) (l₁ : W₀ ≤ W₁) (l₂ : W₀ ≤ W₂) :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d₂ W f - d₁ W f) where
  add W hW f f' := by
    rw [h₁.add W (hW.trans l₁), h₂.add W (hW.trans l₂)]; ring
  mul W hW f f' := by
    rw [h₁.mul W (hW.trans l₁), h₂.mul W (hW.trans l₂)]; ring
  res W W' h hW f := by
    rw [h₁.res W W' h (hW.trans l₁), h₂.res W W' h (hW.trans l₂), rsT_sub (m.preimage_mono h)]
  base W hW r := by
    rw [h₁.base W (hW.trans l₁), h₂.base W (hW.trans l₂), sub_self, constFn_zero']

theorem basis_id (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀))
    (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R)
    (m : A₀.left ⟶ X) (hp : IsPullback m A₀.hom p (spMap x₀)) (W₀ : X.Opens)
    (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (h : LocDerK A₀.hom p m (fun _ => 0) W₀ d) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' q' e₁ e₂ d h
    subst e₁ e₂
    exact GlobalTheory.T.invariantVectorFields_basis_verticalDerivations K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h
  have := key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h
  simpa only [pbT_id] using this

theorem exists_ksCoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a) := by
  intro K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp hsp D I W hD hW
  choose d hder using fun i => GlobalTheory.T.exists_local_derivation_lift_smooth_over_field K R x₀ A₀.left X A₀.hom p m D (W i) hsp hp.w hD (hW i)
  have hb := basis_id K A₀ g v dd hs hv hd R x₀ X p m hp
  choose c hc using fun i j => (hb (W i ⊓ W j) _ (locDerK_sub (hder i) (hder j) inf_le_left inf_le_right)).exists
  have e : ∀ i j, m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j) := fun i j => rfl
  have e3 : ∀ i j k, m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j ⊓ m ⁻¹ᵁ W k = m ⁻¹ᵁ (W i ⊓ W j ⊓ W k) := fun i j k => rfl
  refine ⟨d, fun a i j => rsT (c i j a) _, ⟨hder, ?_⟩, ?_⟩
  · intro i j O hO f
    rw [hc i j O hO f]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [rsT_rsT (e i j).le ((m.preimage_mono hO).trans (e i j).ge)]
  · intro a i j k
    have lij : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j := inf_le_left
    have ljk : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k := inf_le_inf_right _ inf_le_right
    have lik : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k := inf_le_inf_right _ inf_le_left
    have hu := (hb (W i ⊓ W j ⊓ W k) _
      (locDerK_sub (hder i) (hder k) (lik.trans inf_le_left) inf_le_right)).unique
      (y₁ := fun a => rsT (c i j a) _ + rsT (c j k a) _) (y₂ := fun a => rsT (c i k a) _)
      (by
        intro O hO f
        have h1 := hc i j O (hO.trans lij) f
        have h2 := hc j k O (hO.trans ljk) f
        have : d k O f - d i O f = (d j O f - d i O f) + (d k O f - d j O f) := by ring
        rw [this, h1, h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [rsT_add (m.preimage_mono hO), rsT_rsT (m.preimage_mono lij) (m.preimage_mono hO),
          rsT_rsT (m.preimage_mono ljk) (m.preimage_mono hO), add_mul])
      (by
        intro O hO f
        rw [hc i k O (hO.trans lik) f]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [rsT_rsT (m.preimage_mono lik) (m.preimage_mono hO)])
    rw [rsT_rsT (e i j).le inf_le_left, rsT_rsT (e j k).le (inf_le_inf_right _ inf_le_right),
      rsT_rsT (e i k).le (inf_le_inf_right _ inf_le_left)]
    exact congrFun hu a

end GlobalTheory.KS.Cocycle
end
