import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AlgGroupAdic

open GlobalTheory.AlgGroup (exists_point word_compat word_points)

variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {B : Over (Spec (CommRingCat.of R))}
  {b : ∀ e, (Y e).left ⟶ B.left}

theorem exists_hom [IsNoetherianRing R] (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (hc₀ : IsAdicComplete I R)
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} (hB : IsProper B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (Z : Over (Spec (CommRingCat.of R))) (hZ : IsProper Z.hom)
    (φ : ∀ e, thickObj R I e Z ⟶ Y e) (hφ : ∀ e, thickMap R I e Z ≫ (φ (e + 1)).left = (φ e).left ≫ β e) :
    ∃ g : Z ⟶ B, ∀ e, pullback.fst Z.hom (thick R I e) ≫ g.left = (φ e).left ≫ b e := by
  obtain ⟨g, hg, -⟩ := hM.existsUnique_thick hc₀ Z B (fun e => (φ e).left ≫ b e)
    (fun e => by
      rw [Category.assoc, (hb e).w, Over.w_assoc]
      exact pullback.condition.symm)
    (fun e => by rw [← Category.assoc, hφ, Category.assoc, hβb])
  exact ⟨g, hg⟩

theorem exists_word [IsNoetherianRing R] (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (hc₀ : IsAdicComplete I R) [∀ e, GrpObj (Y e)]
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left}
    (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) (hB : IsProper B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    {κ : Type} (w : FreeGroup κ) (Z : Over (Spec (CommRingCat.of R))) (hZ : IsProper Z.hom)
    (p : κ → (Z ⟶ B)) :
    ∃ g : Z ⟶ B, ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (k : Over.mk (T.hom ≫ thick R I e) ⟶ Z) (x : κ → (T ⟶ Y e)),
      (∀ i, (k ≫ p i).left = (x i).left ≫ b e) → (k ≫ g).left = (FreeGroup.lift x w).left ≫ b e := by
  have ex : ∀ e i, ∃ x : thickObj R I e Z ⟶ Y e,
      pullback.fst Z.hom (thick R I e) ≫ (p i).left = x.left ≫ b e := fun e i =>
    ⟨Over.homMk ((hb e).lift (pullback.fst Z.hom (thick R I e) ≫ (p i).left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w, pullback.condition])) ((hb e).lift_snd _ _ _),
      ((hb e).lift_fst _ _ _).symm⟩
  choose X hX using ex
  obtain ⟨g, hg⟩ := exists_hom hM hc₀ hB hb hβb Z hZ (fun e => FreeGroup.lift (X e) w) fun e =>
    word_compat (hβ e) (hb (e + 1)) (hβb e) ((pullback.lift_fst _ _ _).trans (Category.comp_id _))
      (pullback.lift_snd _ _ _) p (X e) (X (e + 1)) (hX e) (hX (e + 1)) w
  exact ⟨g, fun e T k x hx =>
    word_points (hb e) (IsPullback.of_hasPullback _ _) p (X e) (hX e) w g (hg e) T k x hx⟩

theorem hom_eq_of_points [IsNoetherianRing R] (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (hc₀ : IsAdicComplete I R)
    {Z : Over (Spec (CommRingCat.of R))} (hZ : IsProper Z.hom) [IsProper B.hom] {f g : Z ⟶ B}
    (h : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (k : Over.mk (T.hom ≫ thick R I e) ⟶ Z), (k ≫ f).left = (k ≫ g).left) : f = g := by
  refine hM.hom_ext hc₀ fun e ↦ ?_
  exact h e (thickObj R _ e Z) (Over.homMk (pullback.fst Z.hom (thick R _ e)) pullback.condition)

theorem exists_grpObj [IsNoetherianRing R] (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (hc₀ : IsAdicComplete I R) [∀ e, GrpObj (Y e)]
    (hc : ∀ e, IsCommMonObj (Y e)) (hB : IsProper B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e))
    (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B)
    (hm : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ Y e)
      (x₀ y₀ : Over.mk (T.hom ≫ thick R I e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e →
      (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e)
    (hi : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : T ⟶ Y e)
      (x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ B), x₀.left = x.left ≫ b e →
      (x₀ ≫ io).left = (x⁻¹).left ≫ b e)
    (hu : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))),
      (toUnit (Over.mk (T.hom ≫ thick R I e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) :
    ∃ _ : GrpObj B, IsCommMonObj B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  have ex := exists_point hb
  have h2 := isProper_tensorObj_over hB hB
  have h3 := isProper_tensorObj_over h2 hB
  have one_mul' : lift (toUnit B ≫ un) (𝟙 B) ≫ mu = 𝟙 B := by
    refine hom_eq_of_points hM hc₀ hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T 1 x _ _ (hu e T) hx, _root_.one_mul, hx]
  have mul_one' : lift (𝟙 B) (toUnit B ≫ un) ≫ mu = 𝟙 B := by
    refine hom_eq_of_points hM hc₀ hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T x 1 _ _ hx (hu e T), _root_.mul_one, hx]
  have linv : lift io (𝟙 B) ≫ mu = toUnit B ≫ un := by
    refine hom_eq_of_points hM hc₀ hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T _ x _ _ (hi e T x k hx) hx, inv_mul_cancel, hu e T]
  have rinv : lift (𝟙 B) io ≫ mu = toUnit B ≫ un := by
    refine hom_eq_of_points hM hc₀ hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T x _ _ _ hx (hi e T x k hx), mul_inv_cancel, hu e T]
  have assoc' : (mu ▷ B) ≫ mu = (α_ B B B).hom ≫ (B ◁ mu) ≫ mu := by
    refine hom_eq_of_points hM hc₀ h3 fun e T k ↦ ?_
    obtain ⟨p, q, r, rfl⟩ : ∃ p q r, k = lift (lift p q) r :=
      ⟨k ≫ fst _ _ ≫ fst _ _, k ≫ fst _ _ ≫ snd _ _, k ≫ snd _ _, by ext1 <;> [ext1; skip] <;> simp⟩
    obtain ⟨x, hx⟩ := ex e T p
    obtain ⟨y, hy⟩ := ex e T q
    obtain ⟨z, hz⟩ := ex e T r
    rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
      hm e T _ z _ _ (hm e T x y _ _ hx hy) hz, hm e T x _ _ _ hx (hm e T y z _ _ hy hz),
      _root_.mul_assoc]
  let G : GrpObj B :=
    { one := un
      mul := mu
      inv := io
      one_mul := by
        rw [← cancel_epi (λ_ B).inv, Iso.inv_hom_id, ← one_mul', ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_one := by
        rw [← cancel_epi (ρ_ B).inv, Iso.inv_hom_id, ← mul_one', ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_assoc := assoc'
      left_inv := linv
      right_inv := rinv }
  refine ⟨G, ⟨?_⟩, fun e ↦ ⟨hb e, fun T x y x₀ y₀ hx hy ↦ hm e T x y x₀ y₀ hx hy⟩⟩
  change (β_ B B).hom ≫ mu = mu
  refine hom_eq_of_points hM hc₀ h2 fun e T k ↦ ?_
  obtain ⟨p, q, rfl⟩ : ∃ p q, k = lift p q := ⟨k ≫ fst _ _, k ≫ snd _ _, by ext1 <;> simp⟩
  obtain ⟨x, hx⟩ := ex e T p
  obtain ⟨y, hy⟩ := ex e T q
  have := hc e
  rw [lift_braiding_hom_assoc, hm e T x y _ _ hx hy, hm e T y x _ _ hy hx, _root_.mul_comm]

theorem exists_grpObj_of_thickenings : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsCommMonObj (Y e)) → (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProper B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ _ : GrpObj B, IsCommMonObj B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  intro hM R _ _ I hc Y _ β hY hβ B b hB hb hβb
  obtain ⟨mu, hm⟩ := exists_word hM hc hβ hB hb hβb
    (FreeGroup.of true * FreeGroup.of false) (B ⊗ B) (isProper_tensorObj_over hB hB)
    (fun i => bif i then fst B B else snd B B)
  obtain ⟨io, hi⟩ := exists_word hM hc hβ hB hb hβb
    (FreeGroup.of ())⁻¹ B hB (fun _ => 𝟙 B)
  obtain ⟨un, hu⟩ := exists_word hM hc hβ hB hb hβb
    (1 : FreeGroup Empty) (𝟙_ _) (inferInstanceAs (IsProper (𝟙 _))) Empty.elim
  exact exists_grpObj hM hc hY hB hb mu io un
    (fun e T x y x₀ y₀ hx hy => by
      have := hm e T (lift x₀ y₀) (fun i => bif i then x else y) (fun i => by
        cases i
        · simpa using hy
        · simpa using hx)
      rwa [map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at this)
    (fun e T x x₀ hx => by
      have := hi e T x₀ (fun _ => x) (fun _ => by rwa [Category.comp_id])
      rwa [map_inv, FreeGroup.lift_apply_of] at this)
    (fun e T => by
      have := hu e T (toUnit _) Empty.elim (fun i => i.elim)
      rwa [map_one] at this)

end GlobalTheory.AlgGroupAdic
end
