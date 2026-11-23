import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrB

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  first
  | exact spMap_id R
  | exact spMap_id
  | simp [spMap]
  | unfold spMap

theorem spMap_alg_self (R : Type) [CommRing R] : spMap (algebraMap R R) = 𝟙 (Sp R) := by
  first
  | exact spMap_id' R
  | (rw [Algebra.algebraMap_self]; exact spMap_id' R)

theorem spMap_algHom_alg {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) : spMap (φ : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  first
  | (rw [← spMap_comp]; congr 1; exact φ.comp_algebraMap)
  | (rw [spMap_comp]; congr 1; exact φ.comp_algebraMap)
  | (simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])
  | unfold spMap

theorem jetCoef_substP {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) {κ κ' : Type} (m : ℕ)
    (φ : κ → MvPolynomial κ' V) :
    (jetCoef f κ' m).comp ((jetSubstP m φ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetSubstP m (fun i => MvPolynomial.map f (φ i)) : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  have keyV : ∀ (ψ : κ → MvPolynomial κ' V) (j : κ),
      (jetSubstP m ψ : Jet V κ m →ₐ[V] Jet V κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        Ideal.Quotient.mk _ (ψ j - MvPolynomial.C (MvPolynomial.constantCoeff (ψ j))) := fun ψ j =>
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.bind₁_X_right _ j)
  have keyK : ∀ (ψ : κ → MvPolynomial κ' K) (j : κ),
      (jetSubstP m ψ : Jet K κ m →ₐ[K] Jet K κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        Ideal.Quotient.mk _ (ψ j - MvPolynomial.C (MvPolynomial.constantCoeff (ψ j))) := fun ψ j =>
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.bind₁_X_right _ j)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro v
    have e2 : ∀ (κ'' : Type), jetCoef f κ'' m (algebraMap V (Jet V κ'' m) v) =
        algebraMap K (Jet K κ'' m) (f v) := by
      intro κ''
      show jetCoef f κ'' m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
      simp [jetCoef]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (Ideal.Quotient.mk (orig V κ ^ (m + 1))) (MvPolynomial.C v) = algebraMap V (Jet V κ m) v from rfl]
    rw [AlgHom.commutes, e2, e2, AlgHom.commutes]
  · intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [keyV φ i]
    have eX : jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i)) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
      simp [jetCoef]
    rw [eX, keyK]
    simp [jetCoef, MvPolynomial.constantCoeff_map]

theorem unit_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  obtain ⟨hpb, hmul⟩ := h
  let x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) (by
    show (η[G'].left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w η[G']])
  have hη : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    show toUnit (𝟙_ (Over S')) ≫ η[G'] = η[G']
    first
    | rw [toUnit_unit, Category.id_comp]
    | rw [Subsingleton.elim (toUnit (𝟙_ (Over S'))) (𝟙 _), Category.id_comp]
  have h2 := hmul (𝟙_ (Over S')) η[G'] η[G'] x₀ x₀ rfl rfl
  have hidem : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, ← hη, _root_.one_mul]
    rfl
  have h1 : x₀ = 1 := by
    first
    | exact mul_eq_left.1 hidem
    | exact mul_right_eq_self.1 hidem
  have h3 : x₀.left = (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ η[G]).left :=
    congrArg (fun g => g.left) h1
  rw [Over.comp_left] at h3
  have h4 : (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f))).left = f := by
    first
    | simp
    | simpa using Over.w (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)))
  rw [h4] at h3
  exact h3

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

theorem xL_zero (hz : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetAug : Jet T.V (Fin 1 × Fin d) m →ₐ[T.V] T.V) ≫ xT m = 1)
    (m : ℕ) : spMap ((jetAug : Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] T.Fr) : Jet T.Fr (Fin 1 × Fin d) m →+* T.Fr) ≫
      xL I xT m = η[I.t'.G].left := by
  apply ext2 I
  · rw [Category.assoc, xL_fst, ← Category.assoc, spMap_comp', jetCoef_aug, ← spMap_comp', Category.assoc,
      unit_push I.m2.cart]
    have e := congrArg CommaMorphism.left (hz m)
    change spMap _ ≫ (xT m).left = (spMap (algebraMap T.V T.V) ≫ 𝟙 _) ≫ η[I.G.G].left at e
    rw [e, spMap_alg_self, Category.id_comp, Category.id_comp]
  · rw [Category.assoc, xL_snd, spMap_algHom_alg, spMap_alg_self, Over.w η[I.t'.G]]
    rfl

theorem xL_trunc (ht : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
      (jetTrunc : Jet T.V (Fin 1 × Fin d) (m + 1) →ₐ[T.V] Jet T.V (Fin 1 × Fin d) m) ≫ xT (m + 1) = xT m)
    (m : ℕ) : spMap ((jetTrunc : Jet T.Fr (Fin 1 × Fin d) (m + 1) →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
      Jet T.Fr (Fin 1 × Fin d) (m + 1) →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT (m + 1) = xL I xT m := by
  apply ext2 I
  · rw [Category.assoc, xL_fst, xL_fst, ← Category.assoc, spMap_comp', jetCoef_trunc, ← spMap_comp',
      Category.assoc]
    exact congrArg (spMap (jc (d := d) 1 m) ≫ ·) (congrArg CommaMorphism.left (ht m))
  · rw [Category.assoc, xL_snd, xL_snd, spMap_algHom_alg]

theorem xL_act (actT : Fin d → MvPowerSeries (Fin 1 × Fin d) T.V) (a : 𝓞 E) (m : ℕ) (ha : xT m ≫ I.G.act.act a =
      Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (actT p.2)) ≫ xT m) :
    xL I xT m ≫ (I.t'.act.act a).left =
      spMap ((jetSubstP m fun p : Fin 1 × Fin d => MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (actT p.2)) :
        Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
          Jet T.Fr (Fin 1 × Fin d) m →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT m := by
  apply ext2 I
  · rw [Category.assoc, I.m2.act a, ← Category.assoc, xL_fst, Category.assoc, Category.assoc, xL_fst,
      ← Category.assoc (spMap _) (spMap _), spMap_comp', ← jetCoef_substP, ← spMap_comp', Category.assoc]
    exact congrArg (spMap (jc (d := d) 1 m) ≫ ·) (congrArg CommaMorphism.left ha)
  · rw [Category.assoc, Over.w (I.t'.act.act a), Category.assoc, xL_snd, spMap_algHom_alg]

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
