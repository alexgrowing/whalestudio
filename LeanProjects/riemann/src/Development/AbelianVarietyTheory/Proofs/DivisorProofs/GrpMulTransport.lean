import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolAVPull

theorem grp_mul_transport {Y X : Scheme.{0}} (G : Over X) [GrpObj G] {a b : Y ⟶ X} (h : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u'.left = u.left) (hv : v'.left = v.left) :
    (u' * v').left = (u * v).left := by
  subst h
  have e1 : u' = u := Over.OverMorphism.ext hu
  have e2 : v' = v := Over.OverMorphism.ext hv
  rw [e1, e2]

theorem polAV_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (K : Type) [Field K] (z : Sp K ⟶ X') (P₀ : PolAV (Sp K)) (θ : P₀.A.left ⟶ T.G.left), IsGrpPullback P₀.A T.G (z ≫ g) θ → LBIso P₀.L (T.PP.L.pull θ) → ∃ m : P₀.A.left ⟶ t.G.left, IsGrpPullback P₀.A t.G z m ∧ LBIso P₀.L (t.PP.L.pull m) := by
  intro E _ _ _ H X X' T t g φ K _ z P₀ θ hθ hL
  have hw : θ ≫ T.G.hom = (P₀.A.hom ≫ z) ≫ g := by rw [Category.assoc]; exact hθ.1.w
  let m : P₀.A.left ⟶ t.G.left := φ.cart.1.lift θ (P₀.A.hom ≫ z) hw
  have hm1 : m ≫ φ.φ = θ := φ.cart.1.lift_fst _ _ _
  have hm2 : m ≫ t.G.hom = P₀.A.hom ≫ z := φ.cart.1.lift_snd _ _ _
  refine ⟨m, ⟨?_, ?_⟩, ?_⟩
  · have s : IsPullback (m ≫ φ.φ) P₀.A.hom T.G.hom (z ≫ g) := by rw [hm1]; exact hθ.1
    exact IsPullback.of_right s hm2 φ.cart.1
  · intro T' x y x₀ y₀ hx hy
    apply φ.cart.1.hom_ext
    · let x₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (x₀.left ≫ φ.φ) (by
          show x₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w x₀]; rfl)
      let y₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (y₀.left ≫ φ.φ) (by
          show y₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w y₀]; rfl)
      have e1 := φ.cart.2 (Over.mk (T'.hom ≫ z)) x₀ y₀ x₁ y₁ rfl rfl
      let x₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (x.left ≫ θ) (by
        show x.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w x]; rfl)
      let y₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (y.left ≫ θ) (by
        show y.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w y]; rfl)
      have e2 := hθ.2 T' x y x₂ y₂ rfl rfl
      have e3 : (x₁ * y₁).left = (x₂ * y₂).left :=
        grp_mul_transport T.G (by simp [Category.assoc]) x₂ y₂ x₁ y₁
          (by simp [x₁, x₂, hx, Category.assoc, hm1]) (by simp [y₁, y₂, hy, Category.assoc, hm1])
      rw [← e1, e3, e2, Category.assoc, hm1]
    · rw [Category.assoc, hm2, Over.w]
      simp only [Over.mk_hom, ← Category.assoc, Over.w]
  · have h1 : LBIso (t.PP.L.pull m) (T.PP.L.pull θ) :=
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L m m rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame T.PP.L (fun _ : PUnit => θ) (fun _ => φ.φ) (fun _ => 1) m (fun _ => hm1.symm))
        (by obtain ⟨w, hw, -⟩ := φ.lin; exact ⟨w, hw⟩)
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.trans P₀.isLB (pull_isLB T.PP.isLB θ) (pull_isLB t.PP.isLB m) hL (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm h1)

end GlobalTheory.PolAVPull
