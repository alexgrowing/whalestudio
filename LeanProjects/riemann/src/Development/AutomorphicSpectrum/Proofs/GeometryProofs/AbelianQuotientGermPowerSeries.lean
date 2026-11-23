import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUniqueStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap

open Formalism.MainNotions.ModuliIntegralCharts.H1

section Jets

variable {k : Type} [CommRing k]

theorem exists_jetMap {κ κ' : Type} {m : ℕ} (χ : Jet k κ m →ₐ[k] Jet k κ' m)
    (h : ∀ q, (jetAug : Jet k κ' m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) :
    ∃ (φ : κ → MvPolynomial κ' k) (hφ : ∀ i, φ i ∈ orig k κ'), χ = jetMap φ hφ := by
  choose P hP using fun q => Ideal.Quotient.mk_surjective (χ (Ideal.Quotient.mk (orig k κ ^ (m + 1)) (MvPolynomial.X q)))
  have hc : ∀ q, MvPolynomial.constantCoeff (P q) = 0 := fun q => by
    have e : (jetAug : Jet k κ' m →ₐ[k] k) (Ideal.Quotient.mk _ (P q)) = 0 := by rw [hP]; exact h q
    have e' : (MvPolynomial.aeval (fun _ : κ' => (0 : k))) (P q) = 0 := e
    rwa [MvPolynomial.aeval_zero'] at e'
  have hm : ∀ q, P q ∈ orig k κ' := fun q => by
    have := sub_const_mem_orig (P q)
    rwa [hc q, map_zero, sub_zero] at this
  refine ⟨P, hm, GermD.jet_hom_ext fun q => ?_⟩
  rw [GermD.jetMap_mk, MvPolynomial.aeval_X, hP]

end Jets

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

theorem fibPt_fst {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

theorem fibPt_snd {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.snd t.G.hom x = spMap (algebraMap k A) :=
  (pullback.lift_snd _ _ _).trans (by simp)

theorem homAt_fibPt {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (y : overAt x A ⟶ t.G) : homAt (𝟙 (Sp k)) f ≫ fibPt t x y = fibPt t x (homAt x f ≫ y) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc]
    erw [fibPt_fst, fibPt_fst]
    rfl
  · rw [Over.comp_left, Category.assoc]
    erw [fibPt_snd, fibPt_snd]
    exact spMap_comp_alg f

theorem one_left_fst {T : Over (Sp k)} :
    (1 : T ⟶ GF t x).left ≫ pullback.fst t.G.hom x = T.hom ≫ x ≫ η[t.G].left := by
  rw [Hom.one_def, Over.comp_left, Category.assoc]
  have e : η[(Over.pullback x).obj t.G].left ≫ pullback.fst t.G.hom x = x ≫ η[t.G].left := by
    rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
      ← pullback.condition_assoc]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  erw [e]
  rfl

theorem fibPt_one {A : Type} [CommRing A] [Algebra k A] : fibPt t x (1 : overAt x A ⟶ t.G) = 1 := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · erw [fibPt_fst, one_left_fst]
    rw [Hom.one_def, Over.comp_left]
    simp
  · erw [fibPt_snd]
    have := Over.w (1 : overAt (𝟙 (Sp k)) A ⟶ GF t x)
    simpa using this.symm

end Fibre

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {k : Type} [Field k] {x : Sp k ⟶ X}

theorem q_one (Q : AbQuot t x) {T : Over (Sp k)} : (1 : T ⟶ GF t x) ≫ Q.q = 1 := by
  have := Q.q_hom
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]

theorem chart_trunc {S : Type} [CommRing S] {Y : Scheme.{0}} {G : Over Y} (x₀ : Sp S ⟶ Y) {d e : ℕ}
    (gx : ∀ m, jOG x₀ e m 1 ⟶ G)
    (htr : ∀ m, homAt x₀ (jetTrunc : Jet S (Fin 1 × Fin e) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin e) m) ≫ gx (m + 1) = gx m)
    (y : ∀ m, overAt x₀ (Jet S (Fin 1 × Fin d) m) ⟶ G)
    (hy : ∀ m, homAt x₀ (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ y (m + 1) = y m)
    (χ : ∀ m, Jet S (Fin 1 × Fin e) m →ₐ[S] Jet S (Fin 1 × Fin d) m)
    (hz : ∀ m q, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (χ m (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0)
    (hχ : ∀ m, y m = homAt x₀ (χ m) ≫ gx m)
    (hu : ∀ m (ψ : Jet S (Fin 1 × Fin e) m →ₐ[S] Jet S (Fin 1 × Fin d) m),
      (∀ q, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (ψ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) →
        y m = homAt x₀ ψ ≫ gx m → ψ = χ m) (m : ℕ) (q : Fin 1 × Fin e) :
    (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m)
      (χ (m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X q))) = χ m (Ideal.Quotient.mk _ (MvPolynomial.X q)) := by
  obtain ⟨φ, hφ, e₁⟩ := exists_jetMap (χ (m + 1)) (hz (m + 1))
  have hcomm : (jetMap (m := m) φ hφ).comp
      (jetTrunc : Jet S (Fin 1 × Fin e) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin e) m) =
      (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m).comp (χ (m + 1)) := by
    rw [e₁]
    exact GermD.jet_hom_ext fun i => rfl
  have hψ : jetMap (m := m) φ hφ = χ m := by
    refine hu m _ (fun q => ?_) ?_
    · have h := hz (m + 1) q
      rw [e₁] at h
      exact h
    · rw [← hy m, hχ (m + 1), ← htr m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp, hcomm]
  rw [← hψ]
  exact (AlgHom.congr_fun hcomm _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) ∧ (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) := by
  intro E _ _ _ H _ hst X t k _ _ p _ _ x Q d d' g gB
  have hy₀ : ∀ m, homAt (𝟙 (Sp k)) (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫ (fibPt t x (g.x m) ≫ Q.q) = 1 := fun m => by
    rw [← Category.assoc, homAt_fibPt, g.chart.zero m, fibPt_one, q_one]
  have hy₁ : ∀ m, homAt (𝟙 (Sp k)) (jetTrunc : Jet k (Fin 1 × Fin d) (m + 1) →ₐ[k] Jet k (Fin 1 × Fin d) m) ≫
      (fibPt t x (g.x (m + 1)) ≫ Q.q) = fibPt t x (g.x m) ≫ Q.q := fun m => by
    rw [← Category.assoc, homAt_fibPt, g.chart.trunc m]
  choose χ hχ hu using fun m =>
    (GlobalTheory.T.formal_germ_dimension_unique E H hst (Sp k) Q.tB k (𝟙 (Sp k)) d' gB).2 (Fin 1 × Fin d) m _ (hy₀ m)
  have hc := chart_trunc (𝟙 (Sp k)) gB.x gB.chart.trunc (fun m => fibPt t x (g.x m) ≫ Q.q) hy₁ χ
    (fun m => (hχ m).1) (fun m => (hχ m).2) (fun m ψ h₁ h₂ => hu m ψ ⟨h₁, h₂⟩)
  choose Qs hQs using fun i : Fin d' => GaugeR.exists_ps_of_compat
    (fun m => χ m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))) (fun m => hc m _)
  have hconst : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0 := fun i => by
    rw [← GaugeR.jetAug_psJet 0 (Qs i), hQs i 0]
    exact (hχ 0).1 _
  refine ⟨Qs, hconst, fun m => ?_⟩
  have he : sub1 Qs m = χ m := by
    refine GermD.jet_hom_ext fun q => ?_
    obtain ⟨a, i⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have h0 : MvPolynomial.constantCoeff (psTrunc m (Qs i)) = 0 := by
      rw [MvPolynomial.constantCoeff_eq, GermFun.coeff_psTrunc _ _ _ (by simp)]
      exact hconst i
    rw [← hQs i m, sub1, jetSubstP, GermD.jetMap_mk, MvPolynomial.aeval_X, h0, map_zero, sub_zero]
    rfl
  rw [he]
  exact (hχ m).2

end Main

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap
