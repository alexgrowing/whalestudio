import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TorIso

variable {R : Type} [CommRing R] [IsDomain R] {T₁ T₂ : Type} [CommGroup T₁] [CommGroup T₂]
  {Γ₁ : BT.QFGroup R T₁} {Γ₂ : BT.QFGroup R T₂} {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {N : ℕ}
  {i₁ : Γ₁.G.left ⟶ G.left} {i₂ : Γ₂.G.left ⟶ G.left}

theorem exists_hom (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂) :
    ∃ ψ : Γ₁.G ⟶ Γ₂.G, ψ.left ≫ i₂ = i₁ := by
  let g : Over.mk (Γ₁.G.hom ≫ x) ⟶ G := Over.homMk i₁ h₁.isOver
  have hg : g ^ N = 1 := (h₁.kernel Γ₁.G g).2 ⟨𝟙 _, by simp [g]⟩
  obtain ⟨y, hy⟩ := (h₂.kernel Γ₁.G g).1 hg
  exact ⟨y, hy⟩

theorem hom_mul (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂) (ψ : Γ₁.G ⟶ Γ₂.G)
    (hψ : ψ.left ≫ i₂ = i₁) {Y : Over (Spec (CommRingCat.of R))} (y z : Y ⟶ Γ₁.G) :
    (y * z) ≫ ψ = (y ≫ ψ) * (z ≫ ψ) := by
  have w : ∀ u : Y ⟶ Γ₁.G, (u.left ≫ i₁) ≫ G.hom = (Over.mk (Y.hom ≫ x)).hom := fun u => by
    have := Over.w u
    simp only [Category.assoc, h₁.isOver, Over.mk_hom]
    rw [← Category.assoc, this]
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk (y.left ≫ i₁) (w y)
  let z₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk (z.left ≫ i₁) (w z)
  have e₁ := h₁.mul Y y z y₀ z₀ rfl rfl
  have e₂ := h₂.mul Y (y ≫ ψ) (z ≫ ψ) y₀ z₀ (by simp [y₀, hψ]) (by simp [z₀, hψ])
  apply h₂.inj
  rw [Over.comp_left, Category.assoc, hψ, ← e₁, e₂]

theorem exists_pt (ψ : Γ₁.G ⟶ Γ₂.G) (t : T₁) : ∃ t', Γ₁.pt t ≫ ψ = Γ₂.pt t' := by
  obtain ⟨t', ht⟩ := BT.QFGroup.exists_eq_comp_pt R T₂ Γ₂ (FractionRing R) (RingHom.id _)
    ((Γ₁.pt t).left ≫ ψ.left) (by
      rw [Category.assoc, Over.w ψ, Over.w (Γ₁.pt t), RingHom.id_comp]
      rfl)
  refine ⟨t', Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, ht]
  have : CommRingCat.ofHom (RingHom.id (FractionRing R)) = 𝟙 _ := rfl
  rw [this, Spec.map_id, Category.id_comp]

theorem pt_injective (Γ : BT.QFGroup R T₁) : Function.Injective Γ.pt := fun a b h => by
  let o : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  exact Γ.pt_inj a b o o (by rw [h])

theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ Y) (g : Y ⟶ X)
    (s : Γ(X, ⊤)) : BT.valAt (y ≫ g) ⊤ le_top s = BT.valAt y ⊤ le_top (g.appTop s) := by
  unfold BT.valAt
  congr 1

theorem exists_mulEquiv_isHT : ∀ (R : Type) [CommRing R] [IsDomain R] (T₁ T₂ : Type) [CommGroup T₁] [CommGroup T₂] (Γ₁ : BT.QFGroup R T₁) (Γ₂ : BT.QFGroup R T₂) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i₁ : Γ₁.G.left ⟶ G.left) (i₂ : Γ₂.G.left ⟶ G.left), Γ₁.IsTorsionAlong G x N i₁ → Γ₂.IsTorsionAlong G x N i₂ → ∃ b : T₁ ≃* T₂, ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T₁ →* Rˣ) (w : Module.Dual R L), Γ₁.IsHT i₁ M N χ w → Γ₂.IsHT i₂ M N (χ.comp b.symm.toMonoidHom) w := by
  intro R _ _ T₁ T₂ _ _ Γ₁ Γ₂ S G _ x N i₁ i₂ h₁ h₂
  obtain ⟨ψ, hψ⟩ := exists_hom h₁ h₂
  obtain ⟨ψ', hψ'⟩ := exists_hom h₂ h₁
  have c₁ : ψ ≫ ψ' = 𝟙 _ := h₁.inj _ _ _ (by simp [hψ, hψ'])
  have c₂ : ψ' ≫ ψ = 𝟙 _ := h₂.inj _ _ _ (by simp [hψ, hψ'])
  choose f hf using exists_pt (Γ₁ := Γ₁) (Γ₂ := Γ₂) ψ
  choose f' hf' using exists_pt (Γ₁ := Γ₂) (Γ₂ := Γ₁) ψ'
  have fmul : ∀ a c, f (a * c) = f a * f c := fun a c => pt_injective Γ₂ (by
    rw [← hf, map_mul, map_mul, hom_mul h₁ h₂ ψ hψ, hf, hf])
  let b : T₁ ≃* T₂ :=
    { toFun := f
      invFun := f'
      left_inv := fun t => pt_injective Γ₁ (by rw [← hf', ← hf, Category.assoc, c₁, Category.comp_id])
      right_inv := fun t => pt_injective Γ₂ (by rw [← hf, ← hf', Category.assoc, c₂, Category.comp_id])
      map_mul' := fmul }
  refine ⟨b, ?_⟩
  rintro L _ _ M χ w ⟨s, hs, hv⟩
  refine ⟨ψ'.left.appTop s, fun t => ?_, fun e => ?_⟩
  · have e₁ : (Γ₂.pt t).left ≫ ψ'.left = (Γ₁.pt (f' t)).left := congrArg (fun z => z.left) (hf' t)
    refine (valAt_comp _ _ s).symm.trans ?_
    rw [e₁]
    exact hs (f' t)
  · obtain ⟨v, v₁, v₂, v₃⟩ := hv e
    have e₁ : ψ.left ≫ ψ'.left = 𝟙 _ := congrArg (fun z => z.left) c₁
    refine ⟨v ≫ ψ.left, ?_, ?_, ?_⟩
    · rw [Category.assoc, Over.w ψ, v₁]
    · rw [Category.assoc, hψ, v₂]
    · refine (valAt_comp _ _ s).symm.trans ?_
      rw [Category.assoc, e₁, Category.comp_id]
      exact v₃

end GlobalTheory.CompanionTheory.Ar.BT.TorIso
