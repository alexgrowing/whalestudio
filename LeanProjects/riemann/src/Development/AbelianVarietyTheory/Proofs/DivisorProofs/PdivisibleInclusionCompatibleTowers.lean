import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BadPt.FinTower

variable {p : ℕ} {R : Type} [CommRing R] {Γ Δ : PDivGroup p R} {G G₁ : Over (Sp R)} [GrpObj G] [GrpObj G₁]

def ptsHom (s : FinTower Γ G) (n : ℕ) (B : Type) [CommRing B] [Algebra R B] :
    WithConv (Γ.A n →ₐ[R] B) →* (SpAlg R B ⟶ G) :=
  MonoidHom.mk' (fun φ => spOver φ.ofConv ≫ s.y n) (s.mul n B)

theorem y_pow_eq_one (s : FinTower Γ G) (n : ℕ) : s.y n ^ p ^ n = 1 := by
  have h := map_pow (s.ptsHom n (Γ.A n)) (WithConv.toConv (AlgHom.id R _)) (p ^ n)
  rw [Γ.pts_pow_self, map_one] at h
  refine Eq.trans ?_ h.symm
  congr 1
  exact ((congrArg (· ≫ s.y n) (spOver_id _)).trans (Category.id_comp _)).symm

theorem exists_hom_y (s : FinTower Γ G) (s₁ : FinTower Δ G₁) (f : G ⟶ G₁) [IsMonHom f] :
    ∃ g : Γ ⟶ Δ, ∀ n, spOver (g.app n : Δ.A n →ₐ[R] Γ.A n) ≫ s₁.y n = s.y n ≫ f := by
  choose g hg using fun n => s₁.surj n (Γ.A n) (s.y n ≫ f)
    (by rw [← MonObj.pow_comp, s.y_pow_eq_one, MonObj.one_comp])
  have key : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (x : WithConv (Γ.A n →ₐ[R] B)),
      s₁.ptsHom n B (WithConv.toConv (x.ofConv.comp (g n))) = s.ptsHom n B x ≫ f := fun n B _ _ x => by
    change spOver (x.ofConv.comp (g n)) ≫ s₁.y n = (spOver x.ofConv ≫ s.y n) ≫ f
    rw [← spOver_comp, Category.assoc, hg, Category.assoc]
  let b : ∀ n, SemiBialgHom (RingHom.id R) (Δ.A n) (Γ.A n) := fun n =>
    .ofPts (g n : Δ.A n →+* Γ.A n) (g n).commutes
      (fun a => by
        have h := key n R 1
        rw [map_one, MonObj.one_comp, ← map_one (s₁.ptsHom n R)] at h
        exact DFunLike.congr_fun (s₁.inj n R _ _ h) a)
      fun B _ i j hB x y x₀ y₀ hx hy => by
        obtain rfl : i = j := Algebra.algebra_ext _ _ hB
        obtain rfl : x₀ = WithConv.toConv (x.ofConv.comp (g n)) := WithConv.ofConv_injective (AlgHom.ext hx)
        obtain rfl : y₀ = WithConv.toConv (y.ofConv.comp (g n)) := WithConv.ofConv_injective (AlgHom.ext hy)
        have h := key n B (x * y)
        rw [map_mul, MonObj.mul_comp, ← key, ← key, ← map_mul] at h
        exact fun a => (DFunLike.congr_fun (s₁.inj n B _ _ h) a).symm
  refine ⟨⟨fun n => (b n).toBialgHom, fun n => BialgHom.coe_toAlgHom_injective ?_⟩, hg⟩
  refine s₁.inj (n + 1) (Γ.A n) ((Γ.res n : Γ.A (n + 1) →ₐ[R] Γ.A n).comp (g (n + 1)))
    ((g n).comp (Δ.res n : Δ.A (n + 1) →ₐ[R] Δ.A n)) ?_
  rw [← spOver_comp, ← spOver_comp, Category.assoc, Category.assoc, hg, s₁.res, hg, ← Category.assoc, s.res]

end GlobalTheory.BadPt.FinTower

namespace GlobalTheory.BadPt

theorem exists_finTower_endo : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (Γ' : PDivGroup p R) (s : FinTower Γ' G) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (κ : Γ'.baseChange K ⟶ 𝒜), s.IsIncl t φ κ → ∀ (f : G ⟶ G) (f' : A ⟶ A) [IsMonHom f] [IsMonHom f'], f'.left ≫ φ = φ ≫ f.left → ∃ g : Γ' ⟶ Γ', PDivGroup.baseChangeMap K g ≫ κ = κ ≫ t.map t f' := by
  intro p _ R _ _ _ K _ _ _ G _ A _ φ _ hφ Γ' s 𝒜 t κ hκ f f' _ _ hf
  obtain ⟨g, hg⟩ := s.exists_hom_y s f
  refine ⟨g, t.hom_ext_y fun n => Over.OverMorphism.ext
    (hφ.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩
  have h1 : spMap (g.app n : Γ'.A n →+* Γ'.A n) ≫ (s.y n).left = (s.y n).left ≫ f.left :=
    congrArg Over.Hom.left (hg n)
  have h2 : spMap ((t.map t f').app n : 𝒜.A n →+* 𝒜.A n) ≫ (t.y n).left = (t.y n).left ≫ f'.left :=
    congrArg Over.Hom.left (t.map_y t f' n)
  have h3 : (bcMap K (g.app n) : K ⊗[R] Γ'.A n →+* K ⊗[R] Γ'.A n).comp ((Γ'.toBase K).app n).toRingHom =
      ((Γ'.toBase K).app n).toRingHom.comp (g.app n : Γ'.A n →+* Γ'.A n) := RingHom.ext fun _ => rfl
  change (spMap ((bcMap K (g.app n) : K ⊗[R] Γ'.A n →+* K ⊗[R] Γ'.A n).comp
      (κ.app n : 𝒜.A n →+* (Γ'.baseChange K).A n)) ≫ (t.y n).left) ≫ φ =
    (spMap ((κ.app n : 𝒜.A n →+* (Γ'.baseChange K).A n).comp ((t.map t f').app n : 𝒜.A n →+* 𝒜.A n)) ≫
      (t.y n).left) ≫ φ
  rw [Cris.spMap_comp, Cris.spMap_comp]
  simp only [Category.assoc]
  rw [hκ n, reassoc_of% h2, hf, reassoc_of% (hκ n), ← h1, ← Category.assoc, ← Category.assoc,
    ← Cris.spMap_comp, ← Cris.spMap_comp, h3]

end GlobalTheory.BadPt
