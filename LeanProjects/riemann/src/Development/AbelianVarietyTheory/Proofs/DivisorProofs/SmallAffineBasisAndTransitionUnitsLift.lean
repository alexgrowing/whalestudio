import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

theorem app_presheaf_map {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem presheaf_map_map {Y : Scheme.{0}} {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₂).op).hom ((Y.presheaf.map (homOfLE h₁).op).hom y) =
      (Y.presheaf.map (homOfLE (h₂.trans h₁)).op).hom y := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isBasis_smallG (hi : IsThick I s i) (hL : L.IsLB) : IsBasis (smallG i L) := by
  haveI := hi.closed
  have hind : Topology.IsInducing i.base := i.isClosedEmbedding.isInducing
  have cov : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : (Small i L)ᵒᵖ,
      x ∈ ((smallG i L).obj t).unop.1 ∧ ((smallG i L).obj t).unop.1 ≤ U := by
    intro x U hx
    obtain ⟨x₀, rfl⟩ := hi.surj.surj x
    have hx₀ : x₀ ∈ ⨆ j, L.U j := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₀
    obtain ⟨V, hV, hVe⟩ := hind.isOpen_iff.1 (L.U j).isOpen
    have hxV : i.base x₀ ∈ (⟨V, hV⟩ : X.Opens) ⊓ U := ⟨show x₀ ∈ i.base ⁻¹' V from hVe ▸ hj, hx⟩
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxV
    have hsm : i ⁻¹ᵁ W ≤ L.U j := fun y hy ↦ by
      show y ∈ (L.U j : Set X₀)
      rw [← hVe]
      exact (hWle hy).1
    exact ⟨Opposite.op ⟨(⟨W, hW⟩, j), hsm⟩, hxW, fun y hy ↦ (hWle hy).2⟩
  refine ⟨cov, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t₃, hx₃, hle⟩ := cov x (U ⊓ ((smallG i L).obj t₁).unop.1 ⊓ ((smallG i L).obj t₂).unop.1)
    ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨t₃, ⟨(homOfLE (show t₃.unop ≤ t₁.unop from fun y hy ↦ (hle hy).1.2)).op⟩,
    ⟨(homOfLE (show t₃.unop ≤ t₂.unop from fun y hy ↦ (hle hy).2)).op⟩, hx₃, fun y hy ↦ (hle hy).1.1⟩

theorem exists_isLift (hi : IsThick I s i) : ∃ u, IsLift s i L u :=
  ⟨fun p q a ↦ (hi.app_surj q.unop.1.1 (res (Small.le_inf a) (L.g p.unop.1.2 q.unop.1.2)).val).choose,
    fun p q a ↦ (hi.app_surj q.unop.1.1 _).choose_spec⟩

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift
variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isUnit_of_sqZero {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = ⊥) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp v
  have hn : x * y - 1 ∈ K := hker _ (by simp [hv])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this

theorem lift_isUnit (hI : I ^ 2 = ⊥) (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (p q : (Small i L)ᵒᵖ) (a : p ⟶ q) : IsUnit (u p q a) := by
  have hK : ∀ (A : Type) [CommRing A] [Algebra R A], (I.map (algebraMap R A)) ^ 2 = ⊥ := fun A _ _ ↦ by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  exact isUnit_of_sqZero (A := Γ(X, q.unop.1.1.1)) (i.app q.unop.1.1.1).hom (hi.app_surj q.unop.1.1)
    (I.map (algebraMap R (Sec s q.unop.1.1.1))) (hK (Sec s q.unop.1.1.1)) (fun b hb ↦ (hi.ker q.unop.1.1 b).1 hb) (u p q a)
    ((hu p q a).symm ▸ Units.isUnit _)

theorem lift_mdef (hi : IsThick I s i) (hL : L.IsLB) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u) :
    In2 I _ (mdef _ u) := by
  intro t t' t'' a b
  refine (hi.ker t''.unop.1.1 _).1 ?_
  have hb : t''.unop.1.1.1 ≤ t'.unop.1.1.1 := leOfHom b.unop
  have h2 : i ⁻¹ᵁ t''.unop.1.1.1 ≤ L.U t.unop.1.2 ⊓ L.U t'.unop.1.2 ⊓ L.U t''.unop.1.2 :=
    le_inf ((i.preimage_mono hb).trans (Small.le_inf a)) t''.unop.2
  have hc := congrArg (fun w ↦ (X₀.presheaf.map (homOfLE h2).op).hom w.val)
    (hL.cocycle t.unop.1.2 t'.unop.1.2 t''.unop.1.2)
  simp only [Units.val_mul, map_mul, res, Units.coe_map, MonoidHom.coe_coe,
    presheaf_map_map] at hc
  have k : ∀ (x : Γ(X, t'.unop.1.1.1)) (y z : Γ(X, t''.unop.1.1.1)),
      (i.app t'.unop.1.1.1).hom x = (res (Small.le_inf a) (L.g t.unop.1.2 t'.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom y = (res (Small.le_inf b) (L.g t'.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom z = (res (Small.le_inf (a ≫ b)) (L.g t.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom ((X.presheaf.map (homOfLE hb).op).hom x * y - z) = 0 := by
    intro x y z hx hy hz
    rw [map_sub, map_mul, app_presheaf_map, hx, hy, hz, sub_eq_zero]
    simp only [res, Units.coe_map, MonoidHom.coe_coe, presheaf_map_map]
    exact hc
  exact k _ _ _ (hu t t' a) (hu t' t'' b) (hu t t'' (a ≫ b))

theorem isLiftOfTransitionUnits_of_ideal_cochain_change (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (u' : C1 (smallG i L ⋙ OAff s)) (h : In1 I _ (u' - u)) : IsLift s i L u' := by
  intro p q a
  have h0 := (hi.ker q.unop.1.1 _).2 (h p q a)
  have e : u' p q a = u p q a + (u' - u) p q a := by simp
  rw [e]
  exact (map_add (i.app q.unop.1.1.1).hom (u p q a) ((u' - u) p q a)).trans
    ((congrArg₂ (· + ·) (hu p q a) h0).trans (add_zero _))

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift

theorem small_basis_lift : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀), IsThick I s i → L.IsLB → IsBasis (smallG i L) ∧ (∃ u, IsLift s i L u) ∧ ∀ u, IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) ∧ In2 I _ (mdef _ u) ∧ ∀ u', In1 I _ (u' - u) → IsLift s i L u' := by
  intro R _ I hI X X₀ s i L hi hL
  exact ⟨isBasis_smallG hi hL, exists_isLift hi, fun u hu ↦
    ⟨lift_isUnit hI hi hu, lift_mdef hi hL hu, fun u' h ↦ isLiftOfTransitionUnits_of_ideal_cochain_change hi hu u' h⟩⟩

end GlobalTheory.LBLift
