import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WLeOneOfIsIntegral

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem finite_log_ext_ne_zero (F : Type) [Field F] [NumberField F] (a : AlgebraicClosure F) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ e : TrueGeo.Ext v, Real.log (e.w a) ≠ 0}.Finite := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · refine (finite_ext_ne_one F a ha).subset ?_
    rintro v ⟨e, he⟩
    exact ⟨e, fun h => he (by rw [h, Real.log_one])⟩

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem lnStep_of_letterOf_none {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x : Sp C ⟶ X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool)
    (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (h : letterOf Dw st = none) : lnStep t x u p b st = 0 := by
  obtain ⟨τ, k⟩ | k := st
  · have hk : ¬ k < Dw.mult τ := fun hk => by simp [letterOf, hk] at h
    exact dif_neg hk
  · have hk : ¬ k < (letters Dw).length := by simpa [letterOf] using h
    exact dif_neg hk

theorem exists_lgOf_eq (y : AlgPt Y.Y) :
    ∃ (G : (Sym E →₀ ℤ) → AlgebraicClosure F) (κ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → ℝ)
      (S : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → (resP v).Prime → Sym E → ℝ),
      (∀ w v ε (hp : (resP v).Prime), lgOf Y w v ε y =
        Real.log (ε.w (G w)) + κ v ε * w.sum fun a n => (n : ℝ) * S v ε hp a) ∧
      ∀ v ε hp a, letterOf Dw a.2.2 = none → S v ε hp a = 0 :=
  ⟨_, _, _, fun _ _ _ hp => dif_pos hp, fun _ _ _ _ h => lnStep_of_letterOf_none _ _ _ _ _ _ h⟩

theorem exists_lgOf_single (a : Sym E) (y : AlgPt Y.Y) :
    ∃ (G : ℤ → AlgebraicClosure F) (L : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → ℝ),
      (letterOf Dw a.2.2 = none → ∀ v ε, L v ε = 0) ∧
      ∀ v ε, (∀ n, lgOf Y (Finsupp.single a n) v ε y = 0) ∨
        ∀ n : ℤ, lgOf Y (Finsupp.single a n) v ε y = Real.log (ε.w (G n)) + n * L v ε := by
  obtain ⟨G, κ, S, h₁, h₂⟩ := exists_lgOf_eq Y y
  refine ⟨fun n => G (Finsupp.single a n), fun v ε => if hp : (resP v).Prime then κ v ε * S v ε hp a else 0,
    fun h v ε => ?_, fun v ε => ?_⟩
  · dsimp only
    split_ifs with hp
    · rw [h₂ v ε hp a h, mul_zero]
    · rfl
  · by_cases hp : (resP v).Prime
    · refine Or.inr fun n => ?_
      rw [h₁ _ v ε hp, Finsupp.sum_single_index (by simp)]
      simp only [dif_pos hp]
      ring
    · exact Or.inl fun n => dif_neg hp

theorem finite_lgOf_single (a : Sym E) (y : AlgPt Y.Y)
    (h : (letterOf Dw a.2.2).isSome →
      {v : HeightOneSpectrum (𝓞 F) | ∃ ε : TrueGeo.Ext v, lgOf Y (Finsupp.single a 1) v ε y ≠ 0}.Finite) (n : ℤ) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ ε : TrueGeo.Ext v, lgOf Y (Finsupp.single a n) v ε y ≠ 0}.Finite := by
  obtain ⟨G, L, h₀, hL⟩ := exists_lgOf_single Y a y
  cases ha : letterOf Dw a.2.2 with
  | none =>
    refine (finite_log_ext_ne_zero F (G n)).subset ?_
    rintro v ⟨ε, hε⟩
    refine ⟨ε, fun h' => hε ?_⟩
    rcases hL v ε with h₁ | h₁
    · exact h₁ n
    · rw [h₁ n, h', h₀ ha, mul_zero, add_zero]
  | some x =>
    refine (((h (by simp [ha])).union (finite_log_ext_ne_zero F (G n))).union
      (finite_log_ext_ne_zero F (G 1))).subset ?_
    rintro v ⟨ε, hε⟩
    by_contra hv
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hv
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hv
    rcases hL v ε with h₄ | h₄
    · exact hε (h₄ n)
    · have h₅ := h₄ 1
      rw [h₁ ε, h₃ ε] at h₅
      have h₆ : L v ε = 0 := by simpa using h₅.symm
      exact hε (by rw [h₄ n, h₂ ε, h₆, mul_zero, add_zero])

end

theorem Setup.finite_root0_lg : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (P : Finset ℕ) (x : DV.Rt D.what₂.Tau O.N) (y : AlgPt (O.var c)), (∀ st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ, (letterOf O.S.Dw st).isSome → {v : HeightOneSpectrum (𝓞 D.what₂.LL) | ∃ e : TrueGeo.Ext v, (O.adl0 c (Finsupp.single (ArIn.ind P, none, st) 1)).lg v e y ≠ 0}.Finite) → {v : HeightOneSpectrum (𝓞 D.what₂.LL) | ∃ e : TrueGeo.Ext v, (O.root0 c P x).lg v e y ≠ 0}.Finite := by
  intro D O c P x y h
  have key (st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) (n : ℤ) := finite_lgOf_single (O.Φ.C c) (ArIn.ind P, none, st) y (h st) n
  unfold Setup.root0 rootSym
  split_ifs
  · exact key _ _
  · exact key _ _

end GlobalTheory.Mean4O
