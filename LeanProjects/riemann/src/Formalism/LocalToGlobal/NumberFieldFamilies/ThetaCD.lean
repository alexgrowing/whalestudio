import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCN

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RapidInt (D : D7) : Prop := ∀ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure →
  IsFundamentalDomain (GQ V) 𝓕 μ → ∀ f F : GA D V → ℂ, IsAutFun V f →
    (∃ N : ℕ, ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * (1 + normInf (th0 D) V g) ^ N) →
    IsAutFunSm (th0 D) V F → IsCuspFun V F → IntegrableOn (fun h => f h * F h) 𝓕 μ

def CuspBdd (D : D7) : Prop := ∀ (V : HSp D) (F : GA D V → ℂ), IsAutFunSm (th0 D) V F → IsCuspFun V F → ∃ C, ∀ g, ‖F g‖ ≤ C

variable {D : D7}

section Gen

theorem map_aff {E R S : Type} [CommRing E] [CommRing R] [CommRing S] (i : E →+* R) (f : R →+* S) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) E) (P : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin m) E) (x : Matrix (Fin n) (Fin n) R) :
    (M.map i * x * P.map i + Q.map i).map f = M.map (f.comp i) * x.map f * P.map (f.comp i) + Q.map (f.comp i) := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map,
    Matrix.map_map]
  rfl

theorem map_aff_one {E R S : Type} [CommRing E] [CommRing R] [CommRing S] (i : E →+* R) (f : R →+* S) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) E) (P : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin m) E) (h : M * P + Q = 1)
    (x : Matrix (Fin n) (Fin n) R) (hx : x.map f = 1) : (M.map i * x * P.map i + Q.map i).map f = 1 := by
  rw [map_aff, hx, Matrix.mul_one]
  have e : (M * P + Q).map (f.comp i) = 1 := by
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← e, Matrix.map_add _ (map_add _), Matrix.map_mul]

end Gen

section Emb

variable {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (hι : HSpace.IsIsomEmb B A ι) {s : GA D B → GA D A}
  (hs : ∀ h, EmbRel A B ι (s h) h)

include hι hs

theorem emb_mat (h : GA D B) : mt A (s h) =
    HMul.hMul (HMul.hMul ((frameMat A B ι).map (incA D)) (mt B h)) ((prM A B ι).map (incA D)) + (coM A B ι).map (incA D) :=
  emb_gen (incA D) _ _ _ (add_sub_cancel _ _) (mt A (s h)) (mt B h) (hs h).1 fun j =>
    (hs h).2 (fun k => coM A B ι k j) (funext fun i => congrFun (congrFun (perp_rel hι) i) j)

theorem emb_fin {k : GA D B} (hk : k ∈ GfC B) : s k ∈ GfC A := by
  have a : infHom B k = 1 := hk
  refine Units.ext (?_ : (mt A (s k)).map (infPart D) = 1)
  rw [emb_mat hι hs]
  exact map_aff_one _ _ _ _ _ (add_sub_cancel _ _) _ (congrArg Units.val a)

end Emb

end Formalism.L2.Fam.ThC

end
