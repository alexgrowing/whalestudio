import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrA

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

theorem one_left {S : Scheme.{0}} {X : Over S} {G : Over S} [MonObj G] :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := rfl

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

abbrev fV : Sp T.Fr ⟶ Sp T.V := spMap (algebraMap T.V T.Fr)

abbrev jc (n m : ℕ) : Jet T.V (Fin n × Fin d) m →+* Jet T.Fr (Fin n × Fin d) m :=
  jetCoef (algebraMap T.V T.Fr) (Fin n × Fin d) m

theorem xL_w (m : ℕ) : (spMap (jc (d := d) 1 m) ≫ (xT m).left) ≫ I.G.G.hom =
    spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) ≫ spMap (algebraMap T.V T.Fr) := by
  rw [Category.assoc, Over.w]
  simp only [spMap_comp']
  simp only [jOG, Over.mk_hom, Category.comp_id, spMap_comp']
  congr 1
  ext r
  simp only [jc, jetCoef, RingHom.comp_apply]
  erw [Ideal.Quotient.lift_mk]
  simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  rfl

def xL (m : ℕ) : Sp (Jet T.Fr (Fin 1 × Fin d) m) ⟶ I.t'.G.left :=
  I.m2.cart.1.lift (spMap (jc (d := d) 1 m) ≫ (xT m).left) (spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)))
    (xL_w I xT m)

theorem xL_fst (m : ℕ) : xL I xT m ≫ I.m2.φ = spMap (jc (d := d) 1 m) ≫ (xT m).left := I.m2.cart.1.lift_fst _ _ _

theorem xL_snd (m : ℕ) : xL I xT m ≫ I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) := I.m2.cart.1.lift_snd _ _ _

def xP (m : ℕ) : jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G :=
  Over.homMk (xL I xT m) (by
    show xL I xT m ≫ I.t'.G.hom = spMap _ ≫ 𝟙 _
    rw [xL_snd, Category.comp_id])

def xU (m : ℕ) : (letI := io.toAlgebra; jO y.1 d m 1) ⟶ Xo.univ.t.G :=
  letI := io.toAlgebra
  Over.homMk (xL I xT m ≫ I.m1.φ) (by
    show (xL I xT m ≫ I.m1.φ) ≫ Xo.univ.t.G.hom = spMap _ ≫ y.1.x
    rw [Category.assoc, I.m1.cart.1.w, ← Category.assoc, xL_snd])

theorem ext2 {Z : Scheme.{0}} {a b : Z ⟶ I.t'.G.left} (h1 : a ≫ I.m2.φ = b ≫ I.m2.φ)
    (h2 : a ≫ I.t'.G.hom = b ≫ I.t'.G.hom) : a = b := I.m2.cart.1.hom_ext h1 h2

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
