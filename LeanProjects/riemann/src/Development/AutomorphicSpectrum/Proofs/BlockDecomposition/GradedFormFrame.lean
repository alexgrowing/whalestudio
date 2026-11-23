import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.FrameEx

theorem dividedPowerFiltration_dividedPowersBot (O : Type) [CommRing O] {n : ℕ} (hn : n ≠ 0) :
    pdP (dividedPowersBot O) n = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have hpos : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra hne
    push_neg at hne
    have : (l.map Prod.fst).sum = 0 := by
      refine List.sum_eq_zero ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hne p hp
    omega
  obtain ⟨p, hp, hp0⟩ := hpos
  have h0 : p.2 = 0 := by simpa using hl p hp
  have : (dividedPowersBot O).dpow p.1 p.2 = 0 := by
    rw [h0]; exact (dividedPowersBot O).dpow_eval_zero hp0
  have hz : (l.map fun q => (dividedPowersBot O).dpow q.1 q.2).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨p, hp, this⟩)
  rw [hz]
  exact Ideal.zero_mem _

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem inU_of_SS {l s : ℕ} {W : X.Opens} (T : Thick (LL q)) (h : SS q l s W T) : InU W T := by
  obtain ⟨-, V, hV, hT⟩ := h
  rw [Set.mem_singleton_iff.1 hV] at hT
  exact hT

end GlobalTheory.CompanionTheory.GrForm.FrameEx

namespace GlobalTheory.CompanionTheory.GrForm

open FrameEx in

theorem stFrame : StFrame := by
  intro O _ l s hb X q W d c u hu
  letI := (strV q W).toAlgebra
  obtain ⟨c', e, hTF, he1, het, hev⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := O) (I := ⊥) (dividedPowersBot O) l s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  have good := GlobalTheory.T.chart_is_good c'
  have hQ : ∀ T, SS q l s W T → InU W T := inU_of_SS
  have hD : SS q l s W c'.D := ⟨hTF, W, rfl, c'.inV⟩
  obtain ⟨hpow, hgr⟩ := GlobalTheory.T.chart_divided_powers_graded_constant c' good (SS q l s W) hQ hD
  have hval : ∀ (T : Thick (LL q)) (h : InU W T) (σ : c'.D ⟶ T) (f : Γ(X, W)),
      Ideal.Quotient.mk T.J (σ.φ (e (1 ⊗ₜ f))) = ev T h f := by
    intro T h σ f
    rw [ev_nat σ c'.inV h f, hev f]
    rfl
  have hσ : ∀ T : (SS q l s W).FullSubcategory, ∃ σ : c'.D ⟶ T.obj, ∀ i, σ.φ (c'.t i) = u i T.obj := by
    intro T
    have hT := hQ _ T.property
    obtain ⟨σ₀⟩ := good.1 T.obj hT
    obtain ⟨σ, h1, -⟩ := good.2 T.obj σ₀ (fun i => u i T.obj - σ₀.φ (c'.t i)) (fun i => by
      refine Ideal.Quotient.eq.1 ?_
      rw [hu i T.obj hT, ← het i, hval T.obj hT σ₀])
    exact ⟨σ, fun i => by simpa using h1 i⟩
  choose σ hσ using hσ
  let θ : Γ(X, W) ≃+* (sP (SS q l s W)).A.obj (c'.frame good (SS q l s W) hQ hD).D :=
    ((Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv).trans e
  have hθ : ∀ f, θ f = e (1 ⊗ₜ f) := fun f => rfl
  refine ⟨c'.frame good (SS q l s W) hQ hD, fun T => ObjectProperty.homMk (σ T), θ, hgr, ?_, ?_, ?_, ?_⟩
  · intro n hn
    change c'.D.pdPow ((n : ℤ).toNat) = ⊥
    rw [Int.toNat_natCast, hpow, dividedPowerFiltration_dividedPowersBot O hn, Ideal.map_bot]
  · intro i T s s'
    change (s'.hom.φ (c'.t i) - s.hom.φ (c'.t i) : T.obj.B) = s'.hom.φ (θ (c.t i)) - s.hom.φ (θ (c.t i))
    rw [hθ, het]
  · intro i T
    change (σ T).φ (θ (c.t i)) = u i T.obj
    rw [hθ, het, hσ]
  · intro T h f
    exact hval T.obj h (σ T) f

end GlobalTheory.CompanionTheory.GrForm
