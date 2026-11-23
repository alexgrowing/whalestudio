import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNRatioTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

set_option maxHeartbeats 800000 in

theorem transfer_of_unif : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegData W I) (Av : Out.PolAV (Spec (CommRingCat.of (FractionRing W)))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D Av G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∀ τ : PtHom (spMap β) (spMap β) G D.toPre.P.A, (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ (U.gt 0).pG.left) → ∀ n : ℕ, Transfer n U.cubG D.toPre.cub τ := by
  intro W _ _ I D Av G _ _ U Ω _ β hβ τ hτ n A _ _ x y h
  let β₀ : W ⧸ I ^ (0 + 1) →+* A := Ideal.Quotient.lift _ ((algebraMap Ω A).comp β) fun a ha => by
    rw [zero_add, pow_one] at ha
    rw [RingHom.comp_apply, hβ a ha, map_zero]
  let T₀ : Over (Spec (CommRingCat.of (W ⧸ I ^ (0 + 1)))) := Over.mk (spMap β₀)
  have hT : T₀.hom ≫ Out.thick W I 0 = (overAt (spMap β) A).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  let ρ : overAt (spMap β) A ⟶ Over.mk (T₀.hom ≫ Out.thick W I 0) :=
    Over.homMk (𝟙 (Sp A)) ((Category.id_comp _).trans hT)
  let φ : (T₀ ⟶ Out.thickObj W I 0 G) →* (overAt (spMap β) A ⟶ G) :=
    (preHom ρ).comp (UU.toBaseHom (UU.toBase_mul_pullback G (Out.thick W I 0)) T₀)
  have hφ : ∀ r, (φ r).left = r.left ≫ (Out.fstG I 0 G).left := fun r => Category.id_comp _
  have hψ : ∀ r, (τ A (φ r)).left = r.left ≫ (U.gt 0).pG.left := fun r => hτ A _ _ (hφ r).symm
  have inj : Function.Injective φ := fun r s e => Over.OverMorphism.ext (pullback.hom_ext
    ((hφ r).symm.trans ((congrArg (·.left) e).trans (hφ s))) ((Over.w r).trans (Over.w s).symm))
  have surj : Function.Surjective φ := fun v =>
    ⟨Over.homMk (pullback.lift v.left T₀.hom ((Over.w v).trans hT.symm)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  obtain ⟨x, rfl⟩ := surj x
  obtain ⟨y, rfl⟩ := surj y
  have hx : x ^ n = 1 := inj ((map_pow φ x n).trans (h.1.trans (map_one φ).symm))
  have hy : y ^ n = 1 := inj ((map_pow φ y n).trans (h.2.1.trans (map_one φ).symm))
  refine ⟨by rw [← map_pow, h.1, map_one], by rw [← map_pow, h.2.1, map_one], fun z J hJ => ?_⟩
  obtain ⟨N, hN⟩ := UU.exists_good_pt U.LG.isLB (Z := Sp A) z
  have key : ∀ a b d : T₀ ⟶ Out.thickObj W I 0 G,
      cubV D.toPre.cub z J (τ A (φ a)) (τ A (φ b)) (τ A (φ d)) *
        TorusInvariance.wVal U 0 z J N (a * b).left * TorusInvariance.wVal U 0 z J N (a * d).left *
        TorusInvariance.wVal U 0 z J N (b * d).left * TorusInvariance.wVal U 0 z J N (1 : T₀ ⟶ _).left =
      TorusInvariance.wVal U 0 z J N (a * b * d).left * TorusInvariance.wVal U 0 z J N a.left *
        TorusInvariance.wVal U 0 z J N b.left * TorusInvariance.wVal U 0 z J N d.left *
        cubV U.cubG z N (φ a) (φ b) (φ d) := by
    intro a b d
    have e := TorusInvariance.cube_val U (T := T₀) ![a, b, d] hJ hN
    have t₁ : WCub.tri (Out.thick W I 0) (U.gt 0).pG ![a, b, d] =
        (lift (τ A (φ a)) (lift (τ A (φ b)) (τ A (φ d)))).left := hom_ext_triple _ fun i => by
      rw [← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, lift_fst,
        lift_snd_assoc, lift_snd, hψ] <;> rfl
    have t₂ : WCub.tri (Out.thick W I 0) (Out.fstG I 0 G) ![a, b, d] =
        (lift (φ a) (lift (φ b) (φ d))).left := hom_ext_triple _ fun i => by
      rw [← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, lift_fst,
        lift_snd_assoc, lift_snd, hφ] <;> rfl
    have p : ∀ k : thK.{0}, (psum (Out.thickObj W I 0 G) ![a, b, d] k.down).left =
        (lift a (lift b d)).left ≫ thφ _ (x3 (Out.thickObj W I 0 G)) k := fun k =>
      congrArg (·.left) ((congrArg (fun q => psum _ q k.down) (funext fun i => by
        fin_cases i <;> simp [x3, preHom])).trans
        (psum_hom (preHom (lift a (lift b d))) (x3 (Out.thickObj W I 0 G)) k.down).symm)
    rw [t₁, t₂] at e
    simp only [p] at e
    exact UU.cub_alg (e.trans (congrArg₂ (· * ·) (prod_cub a b d (TorusInvariance.wVal U 0 z J N)) rfl))
  refine UU.cubN_ratio_twist ((τ A).comp φ) (fun r => TorusInvariance.wVal U 0 z J N r.left)
    (θ := cubV D.toPre.cub z J) (θ' := fun a b d => cubV U.cubG z N (φ a) (φ b) (φ d)) key hx hy ?_
  simpa only [cubN, map_mul, map_pow, map_one] using h.2.2 z N hN

end GlobalTheory.AlphaPair
