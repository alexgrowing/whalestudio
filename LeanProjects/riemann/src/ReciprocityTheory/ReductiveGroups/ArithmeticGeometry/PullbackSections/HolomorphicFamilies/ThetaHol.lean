import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartX
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

namespace ThetaHol

theorem isHolTo_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) :
    IsHolTo (Set.univ : Set V) (fun _ => y) := by
  intro Uo f
  by_cases h : ⊤ ≤ y ⁻¹ᵁ Uo
  · simp only [Set.mem_univ, true_and, h, Set.ofPred_true]
    exact ⟨isOpen_univ, differentiableOn_const _⟩
  · simp only [Set.mem_univ, true_and, h, Set.ofPred_false]
    exact ⟨isOpen_empty, differentiableOn_empty⟩

theorem isHolTo_of_fam {n : ℕ} {Y : Scheme.{0}} {y : (Fin n → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolFam y) :
    IsHolTo Set.univ y := by
  intro Uo f
  obtain ⟨h1, h2⟩ := h Uo f
  simp only [Set.mem_univ, true_and]
  exact ⟨h1, h2⟩

end ThetaHol

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem thPt_w {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (z : Fin W.g → ℂ) :
    𝟙 (Sp ℂ) ≫ (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left ≫ Xo.univ.t.G.hom := by
  exact (Category.id_comp _).trans (W.pt.trans (Over.w (W.F.ex (W.ik k) W.Pm z)).symm)

def thPt {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (z : Fin W.g → ℂ) :
    Sp ℂ ⟶ Gx (U.un k x).x :=
  (pullback.lift (𝟙 (Sp ℂ)) (W.F.ex (W.ik k) W.Pm z).left (thPt_w W z) :
    Sp ℂ ⟶ pullback (U.un k x).x Xo.univ.t.G.hom)

theorem thPt_fst {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (z : Fin W.g → ℂ) :
    thPt W z ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left :=
  pullback.lift_snd _ _ _

theorem thPt_snd {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (z : Fin W.g → ℂ) :
    thPt W z ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) :=
  pullback.lift_fst _ _ _

theorem theta_hol_of_pair {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (Wu : UnitAt W)
    (hHP : ∀ (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (n : ℕ) (B : Set (Fin n → ℂ))
      (e₁ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₂)) (he : ∀ b, e₁ b ≫ p₁ = e₂ b ≫ p₂),
      IsOpen B → IsHolTo B e₁ → IsHolTo B e₂ → IsHolTo B (fun b => pullback.lift (e₁ b) (e₂ b) (he b))) :
    Differentiable ℂ Wu.θ := by
  intro z0
  have hE : IsHolTo Set.univ (fun z => (W.F.ex (W.ik k) W.Pm z).left) :=
    ThetaHol.isHolTo_of_fam (anHol W.F (W.ik k) W.Pm W.per)
  have hP : IsHolTo Set.univ (thPt W) :=
    hHP Xo.X (Sp ℂ) Xo.univ.t.G.left (U.un k x).x Xo.univ.t.G.hom W.g Set.univ (fun _ => 𝟙 (Sp ℂ))
      (fun z => (W.F.ex (W.ik k) W.Pm z).left) (fun z => thPt_w W z) isOpen_univ (ThetaHol.isHolTo_const _) hE
  obtain ⟨q⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((W.F.ex (W.ik k) W.Pm z0).left q)
  have hz0 : ⊤ ≤ (W.F.ex (W.ik k) W.Pm z0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := (top_le_iff_mem _ _ q).2 hj
  have hOo : IsOpen {z | ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
    have := (hE (Xo.univ.t.PP.L.U j) 0).1
    simpa only [Set.mem_univ, true_and] using this
  have hsub : ∀ z ∈ {z | ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j},
      ⊤ ≤ thPt W z ⁻¹ᵁ (PPx (U.un k x).x).U (fun _ => j) := by
    intro z hz
    rw [top_le_iff_mem _ _ q]
    have h1 : (thPt W z ≫ gxFst (U.un k x).x) q ∈ Xo.univ.t.PP.L.U j := by
      rw [thPt_fst]
      exact (top_le_iff_mem _ _ q).1 hz
    exact Set.mem_iInter.2 fun _ => h1
  have hN : DifferentiableOn ℂ (fun z => valAt' (thPt W z) ((PPx (U.un k x).x).U (fun _ => j))
      ((U.un k x).s.f (fun _ => j))) {z | ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} :=
    (hP ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j))).2.mono
      fun z hz => ⟨trivial, hsub z hz⟩
  have hF0 : ∀ z ∈ {z | ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}, Wu.fr j z ≠ 0 :=
    fun z hz => Wu.c3 j z hz
  have heq : ∀ z ∈ {z | ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}, Wu.θ z =
      valAt' (thPt W z) ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) * (Wu.fr j)⁻¹ z := by
    intro z hz
    rw [Wu.c7 j z (thPt W z) (thPt_fst W z) (thPt_snd W z) hz, Pi.inv_apply, mul_assoc, mul_inv_cancel₀ (hF0 z hz),
      mul_one]
  have hd := (hN.mul ((Wu.c2 j).inv hF0)).differentiableAt (hOo.mem_nhds hz0)
  exact hd.congr_of_eventuallyEq (Filter.eventually_of_mem (hOo.mem_nhds hz0) heq)

end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections
