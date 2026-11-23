import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cup_natural_in_pairing : ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b) := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ]
  simp only [cpush, cpost_mk]
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 _ _ _ ?_).symm
  intro N w h U x
  have hm := fun {L L' : Cx R} (φ : L ⟶ L') {d : ℤ} (c : Cochain ((chains R).obj E) L d) p s hs U x =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := d)).2.2.2.2 φ c p s hs U x
  change ev (γ.1.comp (Cochain.ofHom u) (add_zero k)) N w h U x = _
  rw [hm, hγ N w h U x]
  refine (map_sum ((u.f w).hom.app (op U)).hom _ _).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  change Sec.map (u.f w) _ = _ • ν.mul U _ _ w _ (ev (α.1.comp (Cochain.ofHom f) (add_zero n)) _ _ _ U _) (ev (β.1.comp (Cochain.ofHom g) (add_zero m)) _ _ _ U _)
  rw [hm, hm, Units.smul_def, Units.smul_def, ← hc]
  exact map_zsmul ((u.f w).hom.app (op U)).hom _ _

end GlobalTheory
