import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem push_inj {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {a b : T ⟶ G'}
    (e : pushHom h T a = pushHom h T b) : a = b := by
  have e1 : a.left ≫ φ = b.left ≫ φ := congrArg (fun z => z.left) e
  have e2 : a.left ≫ G'.hom = b.left ≫ G'.hom := by
    rw [Over.w a, Over.w b]
  exact Over.OverMorphism.ext (h.1.hom_ext e1 e2)

theorem jetCoef_copy {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) (d m n : ℕ) (i : Fin n) :
    (jetCoef f (Fin n × Fin d) m).comp ((jetCopy (S := V) d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) :
      Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m) =
    ((jetCopy (S := K) d m i : Jet K (Fin 1 × Fin d) m →ₐ[K] Jet K (Fin n × Fin d) m) :
      Jet K (Fin 1 × Fin d) m →+* Jet K (Fin n × Fin d) m).comp (jetCoef f (Fin 1 × Fin d) m) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.C r))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.C r)))
    simp
  · intro q
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.X q))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.X q)))
    simp

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

def U2 (m : ℕ) : Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ jOG (𝟙 (Sp T.V)) d m 2 :=
  Over.homMk (spMap (jc (d := d) 2 m)) (by
    show spMap (jc (d := d) 2 m) ≫ spMap (algebraMap T.V (Jet T.V (Fin 2 × Fin d) m)) ≫ 𝟙 _ =
      (spMap (algebraMap T.Fr (Jet T.Fr (Fin 2 × Fin d) m)) ≫ 𝟙 _) ≫ spMap (algebraMap T.V T.Fr)
    rw [Category.comp_id, Category.comp_id, spMap_comp', spMap_comp', jetCoef_alg])

theorem push_jpt (m : ℕ) (i : Fin 2) :
    pushHom I.m2.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) = U2 (d := d) m ≫ jptG I.G (𝟙 (Sp T.V)) d xT m i := by
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_copy]

theorem xP_law (FT : Fin d → MvPowerSeries (Fin 2 × Fin d) T.V) (m : ℕ)
    (hl : Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (FT p.2)) ≫ xT m =
      jptG I.G (𝟙 (Sp T.V)) d xT m (0 : Fin 2) * jptG I.G (𝟙 (Sp T.V)) d xT m (1 : Fin 2)) :
    Formalism.L2.Pj.homAt (𝟙 (Sp T.Fr)) (jetSubstP m fun p : Fin 1 × Fin d =>
              MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (FT p.2))) ≫ xP I xT m =
      jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (0 : Fin 2) * jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (1 : Fin 2) := by
  apply push_inj I.m2.cart
  rw [map_mul, push_jpt, push_jpt, ← MonObj.comp_mul, ← hl]
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_substP]

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
