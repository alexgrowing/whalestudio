import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {K : Type} [CommRing K]

theorem conj_pullback_map (x : Sp K ⟶ Xo.X) (g : Xo.univ.t.G ⟶ Xo.univ.t.G) :
    conj x x ((Over.pullback x).map g).left =
      (lift (fst (Over.mk x) Xo.univ.t.G) (snd (Over.mk x) Xo.univ.t.G ≫ g)).left := by
  refine gx_ext ?_ ?_
  · rw [lift_l_fst]
    exact (over_iff _).2 (pullback.lift_snd _ _ _)
  · rw [lift_l_snd, conj_apply, Category.assoc, Category.assoc, swap_inv_snd, Over.comp_left, ← swap_hom_fst,
      Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem conj_comp_left {x x' x'' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo x' ⟶ Fib Xo x'') :
    conj x x'' (f ≫ g).left = conj x x' f.left ≫ conj x' x'' g.left := by
  simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Over.comp_left]
  simp only [Category.assoc]

theorem conj_id_pow (x : Sp K ⟶ Xo.X) (n : ℕ) :
    conj x x (𝟙 (Fib Xo x) ^ n).left = (mulT Xo.univ.t.G (Over.mk x) n).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G ^ n) = 𝟙 (Fib Xo x) ^ n := by
    have := map_pow (Over.pullback x).homMonoidHom (𝟙 Xo.univ.t.G) n
    rw [← (Over.pullback x).map_id]
    exact this
  rw [← e, conj_pullback_map, MonObj.comp_pow, Category.comp_id, mulT]

theorem conj_id_inv (x : Sp K ⟶ Xo.X) :
    conj x x (𝟙 (Fib Xo x))⁻¹.left = (negT Xo.univ.t.G (Over.mk x)).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G)⁻¹ = (𝟙 (Fib Xo x))⁻¹ := by
    rw [Functor.map_inv', CategoryTheory.Functor.map_id]
  rw [← e, conj_pullback_map, GrpObj.comp_inv, Category.comp_id, negT]
  rfl

theorem negT_comm_conj {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] :
    (negT Xo.univ.t.G (Over.mk x)).left ≫ conj x x' f.left =
      conj x x' f.left ≫ (negT Xo.univ.t.G (Over.mk x')).left := by
  rw [← conj_id_inv, ← conj_id_inv, ← conj_comp_left, ← conj_comp_left, GrpObj.inv_comp, GrpObj.comp_inv,
    Category.id_comp, Category.comp_id]

theorem pow_eq_one_of_mem_transKer_conj {x x' : Sp K ⟶ Xo.X} {f : Fib Xo x ⟶ Fib Xo x'} {f' : Fib Xo x' ⟶ Fib Xo x}
    {n : ℕ} (h : f ≫ f' = 𝟙 _ ^ n) {c : Over.mk x ⟶ Xo.univ.t.G} (hc : c ∈ transKer Xo.univ.t.G (conj x x' f.left)) :
    c ^ n = 1 := by
  rw [← mem_transKer_mulT, mem_transKer, ← conj_id_pow, ← h, conj_comp_left, ← Category.assoc, mem_transKer.1 hc]

theorem thetaTrace_isTranslSum (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K)
    (hf : IsPair (p ^ 2) f f') (hs' : ∀ i, s'.f i = scal x' a i * s₀.f i)
    (h : IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s') :
    ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  obtain ⟨β, s₁, t, n, U, F, hβ, hs, ht, hr, hU, hF, hsum⟩ := h
  have := hf.1
  refine ⟨t, ⟨β, s', hβ, hs', ht⟩, n, F, fun i => ?_, hsum⟩
  have hk : (U i).pt ^ (p ^ 2) = 1 := pow_eq_one_of_mem_transKer_conj hf.2.2.1 (hU i).1
  obtain ⟨α₀, α, h₁, h₂, h₃, h₄⟩ := hs
  exact ⟨_, (U i).pt, α₀, α, s₁, U i, rfl, hk, h₁, h₂, h₃, h₄,
    (hU i).symLift hβ.2.1 Xo.univ.t.sym (negT_comm_conj f) hk, hF i⟩

end GlobalTheory.HkIntegral
