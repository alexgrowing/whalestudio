import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleHeckeKernelListsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndEtaleOfCompOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPerm

theorem lists_perm {S : Scheme.{0}} {G : Over S} [GrpObj G] {N n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ G)}
    {K : Set G.left} (h : Lists N σ K) (g : Equiv.Perm (Fin n)) : Lists N (fun j => σ (g j)) K := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun j => h₁ _, ?_, fun k _ _ x => (h₃ k x).comp g.injective⟩
  rw [h₂]
  exact (g.surjective.iUnion_comp (fun j => Set.range (σ j).left)).symm

theorem exists_perm {α : Type} {n : ℕ} {u v : Fin n → α} (hu : Function.Injective u) (hv : Function.Injective v)
    (h : Set.range u = Set.range v) : ∃ g : Equiv.Perm (Fin n), ∀ j, u (g j) = v j := by
  have : ∀ j, ∃ i, u i = v j := fun j => by
    have : v j ∈ Set.range u := h ▸ Set.mem_range_self j
    exact this
  choose g hg using this
  have gi : Function.Injective g := fun a b e => hv (by rw [← hg, ← hg, e])
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 gi), hg⟩

theorem exists_lists_mod_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ), admitted l 𝔓 p → ∃ (Y Hk : Scheme.{0}) (q : Y ⟶ Hk) (π₁ : Hk ⟶ Xo.X) (oY : Ob D l ((q ≫ π₁) ≫ Xo.s)) (m : ObjMap oY Xo.univ (q ≫ π₁)) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite q ∧ Etale q ∧ Surjective q ∧ IsFinite π₁ ∧ Etale π₁ ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q ↔ Set.range (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ) = Set.range (fun j => y' ≫ (σ j).left ≫ m.toSABMap.φ) ∧ y ≫ q ≫ π₁ = y' ≫ q ≫ π₁) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ Xo.X) (t : SAB H T) (mu : SABMap t Xo.univ.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃ h : T ⟶ Y, h ≫ q ≫ π₁ = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l Xo P p i n hA
  obtain ⟨Y, a, oY, m, σ, K, fa, ea, hL, hK, hu⟩ := GlobalTheory.T.exists_finiteEtale_heckeKernel_lists E H D l P p i n Xo.X Xo.s Xo.univ hA
  have hρ := fun g : Equiv.Perm (Fin n) => hu Y a oY.t m.toSABMap (fun j => σ (g j)) K (lists_perm hL g) hK
  choose ρ hρ₁ hρ₂ using hρ
  have r₁ : ∀ g, ρ g ≫ a = a := fun g => (hρ₁ g).1
  have r₂ : ∀ g j, ρ g ≫ (σ j).left ≫ m.toSABMap.φ = (σ (g j)).left ≫ m.toSABMap.φ := fun g => (hρ₁ g).2
  have one : ρ 1 = 𝟙 Y := (hρ₂ 1 _ ⟨by simp, fun j => by simp⟩).symm
  have mul : ∀ g c, ρ (g * c) = ρ g ≫ ρ c := fun g c =>
    (hρ₂ (g * c) _ ⟨by rw [Category.assoc, r₁, r₁], fun j => by
      rw [Category.assoc, r₂, r₂]; rfl⟩).symm
  have inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y),
      Function.Injective fun j => y ≫ (σ j).left ≫ m.toSABMap.φ := by
    intro k _ _ y b c e
    apply hL.2.2 k y
    have w : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w _
    refine m.toSABMap.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using e
    · simp only [Category.assoc, w]
  have free : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (g : Equiv.Perm (Fin n)), y ≫ ρ g = y → g = 1 := by
    intro k _ _ y g e
    ext1 j
    apply inj k y
    change y ≫ (σ (g j)).left ≫ m.toSABMap.φ = y ≫ (σ j).left ≫ m.toSABMap.φ
    rw [← r₂, ← Category.assoc, e]
  have uq : ∀ (T : Scheme.{0}) (y y' : T ⟶ Y), y ≫ a = y' ≫ a →
      (∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = y' ≫ (σ j).left ≫ m.toSABMap.φ) → y = y' := by
    intro T y y' e₁ e₂
    obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull y oY.t
    obtain ⟨mu, hmu⟩ := GlobalTheory.ObjMaps.exists_sab_comp m.toSABMap m'
    obtain ⟨τ, hτ, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m'.cart K _ n σ hL
    have hτ' : ∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := fun j => by
      rw [hmu, ← Category.assoc, ← hτ, Category.assoc]
    exact (hu T (y ≫ a) _ mu τ _ hL' (GlobalTheory.HkSetPull.heckeSet_pull D P p i m' K hK)).unique ⟨rfl, hτ'⟩
      ⟨e₁.symm, fun j => (e₂ j).symm.trans (hτ' j)⟩
  have hq := GlobalTheory.isQProjOver_comp_of_isFinite_noetherian (KA l) Y Xo.X a Xo.s fa Xo.qproj
  obtain ⟨Hk, q, sH, hs, hG, sep, lft, -⟩ := GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver (KA l) Y (a ≫ Xo.s)
    (Equiv.Perm (Fin n)) ρ hq one mul (fun g => by rw [← Category.assoc, r₁]) free
  have hd := (GlobalTheory.ZM.galoisCover_descent Y Hk q _ ρ hG).1
  obtain ⟨π₁, rfl, -⟩ := hd Xo.X a r₁
  have hs' : π₁ ≫ Xo.s = sH := (hd _ ((q ≫ π₁) ≫ Xo.s) (fun g => by rw [← Category.assoc, r₁])).unique
    (Category.assoc _ _ _).symm hs
  subst hs'
  have : IsSeparated π₁ := IsSeparated.of_comp π₁ Xo.s
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : LocallyOfFiniteType π₁ := locallyOfFiniteType_of_comp π₁ Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨f₁, e₁⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover Y Hk Xo.X q π₁ hG.fin hG.etale hG.onto fa ea
    inferInstance inferInstance
  refine ⟨Y, Hk, q, π₁, oY, m, σ, K, hG.fin, hG.etale, hG.onto, f₁, e₁, hL, hK, fun k _ _ y y' => ⟨fun e => ?_, fun e => ?_⟩,
    fun T f t mu τ K' h₁ h₂ => (hu T f t mu τ K' h₁ h₂).exists⟩
  · obtain ⟨g, rfl, -⟩ := hG.fibre k y y' e
    refine ⟨?_, by rw [← Category.assoc, e, Category.assoc]⟩
    simp only [Category.assoc, r₂]
    exact (g.surjective.range_comp (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ)).symm
  · obtain ⟨g, hg⟩ := exists_perm (inj k y) (inj k y') e.1
    have : y ≫ ρ g = y' := uq _ _ _ (by rw [Category.assoc, r₁]; exact e.2) fun j => by
      rw [Category.assoc, r₂]; exact hg j
    rw [← this, Category.assoc, hG.inv]

end GlobalTheory.HkPerm
