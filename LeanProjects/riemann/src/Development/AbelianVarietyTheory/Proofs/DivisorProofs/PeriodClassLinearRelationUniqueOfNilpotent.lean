import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationChartCoboundaryOnChartsFirstOrder
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
  {R : Type} [CommRing R] (et : Hol F.V →+* R) (M : Ideal R)

def perZDLin : (Λ →+ R) →ₗ[R] GlobalTheory.CatCoh.Z1 (K.OD et M) where
  toFun := K.perZD et M
  map_add' q q' := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦ map_add (algebraMap R S'.T.C) (q f.1.deg) (q' f.1.deg))
  map_smul' r q := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦
    (map_mul (algebraMap R S'.T.C) r (q f.1.deg)).trans (Algebra.smul_def (A := S'.T.C) r _).symm)

end GlobalTheory.AnPer.Charts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AnPer.perClD_relation_unique : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : _root_.GlobalTheory.AnPer.Fam Empty g Λ} (K₀ : _root_.GlobalTheory.AnPer.Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : _root_.GlobalTheory.AnPer.Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : _root_.GlobalTheory.AnPer.Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  intro g Λ _ F₀ K₀ R _ _ et M hrich hV hnil het io S d q q' hrel l
  let q'' : Λ →+ R := q' - ∑ i ∈ S, d i • q i
  have hq'' : ∀ m, q'' m = q' m - ∑ i ∈ S, d i * q i m := by
    intro m
    simp [q'', AddMonoidHom.finset_sum_apply, smul_eq_mul]
  have hcl : K₀.perClD et M q'' = 0 := by
    have hc : ∀ p : Λ →+ R, K₀.perClD et M p =
        _root_.GlobalTheory.CatCoh.H1.mk _
          (K₀.perZDLin et M p) := fun p => rfl
    simp only [hc] at hrel ⊢
    simp only [q'', map_sub, map_sum, map_smul, hrel, sub_self]
  obtain ⟨G, hG0, hGsh⟩ := _root_.GlobalTheory.ChartCobd.coboundary_on_charts K₀ et M hnil het q'' hcl
  have hzero : q'' l = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let Φ : ∀ k, R ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol (K₀.W k) →ₗ[ℂ]
        _root_.GlobalTheory.AnPer.Hol (K₀.W k) :=
      fun k => (TensorProduct.lid ℂ _).toLinearMap ∘ₗ LinearMap.rTensor _ φ
    have hΦ : ∀ k r h, Φ k (r ⊗ₜ h) = φ r • h := by
      intro k r h
      simp [Φ]
    have hΦd : ∀ k a y, _root_.GlobalTheory.AnPer.dw a (Φ k y) =
        Φ k (LinearMap.lTensor R (_root_.GlobalTheory.AnPer.dw a).toLinearMap y) := by
      intro k a y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r h => simp [hΦ]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hΦs : ∀ {m k k'} (h : K₀.le m k' k) y,
        Φ k' (Algebra.TensorProduct.map (AlgHom.id ℂ R)
          (_root_.GlobalTheory.AnPer.Charts.shA h) y) =
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k y) := by
      intro m k k' h y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b =>
        simp [hΦ, ← _root_.GlobalTheory.AnPer.Charts.shA_apply]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hfsh : ∀ m k k' (h : K₀.le m k' k),
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k (G k)) =
          Φ k' (G k') + K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) := by
      intro m k k' h
      have h1 := congrArg (Φ k') (hGsh m k k' h)
      rw [map_sub, hΦs, hΦ] at h1
      have h2 : K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) =
          -(φ (q'' m) • 1) := by
        unfold _root_.GlobalTheory.AnPer.Charts.cst
        simp [Algebra.algebraMap_eq_smul_one]
      rw [h2, ← h1]
      abel
    obtain ⟨Gf, -, -, hper, hconst⟩ := _root_.GlobalTheory.AnPer.Charts.glue K₀
      hrich (fun k => Φ k (G k)) (by
        intro k k' h
        simp [hfsh 0 k k' h])
    have hc := hconst (fun k a => by rw [hΦd, hG0, map_zero])
    let p : _root_.GlobalTheory.AnPer.Tot Empty g := ((0 : Empty → ℂ), (0 : Fin g → ℂ))
    have hp := hper l (algebraMap ℂ _ (-(φ (q'' l)))) (fun k k' h => hfsh l k k' h) p (hV _)
    have e : Gf (F₀.shift l p) = Gf p := by
      calc Gf (F₀.shift l p) =
          Gf ((F₀.shift l p).1, (F₀.shift l p).2) := rfl
        _ = Gf ((F₀.shift l p).1, 0) := hc _ (hV _) _
        _ = Gf (p.1, 0) := by rw [Subsingleton.elim (F₀.shift l p).1 p.1]
        _ = Gf p := rfl
    have hfn : (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol F₀.V)
        (-(φ (q'' l)))).fn p.1 = -(φ (q'' l)) := by
      unfold _root_.GlobalTheory.AnPer.Hol.fn
      simp [hV]
    rw [e, hfn] at hp
    linear_combination hp
  rw [← sub_eq_zero, ← hq'' l]
  exact hzero
