import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

structure UnfAt (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) where
  g : ℕ
  e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  ik : U.Comp → Fin F.n
  φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ
  isom : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))
  Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)
  pm_eq : ∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  per : IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm
  pt : (U.un k x).x = F.u (ik k) Pm
  der : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
    ((U.un k x).u τ i)
  unit : ((∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
              pt ≫ gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
              pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)

theorem nonempty_unfAt {U : Unf Xo c σ r} (h : IsUnf U) (k : U.Comp) (x : (U.X k).dom) :
    Nonempty (UnfAt U k x) := by
  obtain ⟨_, _, _, _, _, g, e, F, ik, φ, hiso, hpt⟩ := h
  obtain ⟨Pm, h1, h2, h3, h4, h5⟩ := hpt k x
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, h3, h4, h5⟩⟩

structure UnitAt {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) where
  Hm : Matrix (Fin W.g) (Fin W.g) ℂ
  χl : (Fin W.g → ℂ) → ℂ
  fr : Xo.univ.t.PP.L.ι → (Fin W.g → ℂ) → ℂ
  θ : (Fin W.g → ℂ) → ℂ
  Fd : Set (Fin W.g → ℂ)
  herm : Hm.IsHermitian
  pos : ∀ z : Fin W.g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re
  c1 : (∀ a b, (hermForm Hm (W.Pm a) (W.Pm b)).im = (W.F.Di (W.ik k)).EF a b)
  c2 : (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
  c3 : (∀ j z, ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
  c4 : (∀ j j' z, ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (W.F.ex (W.ik k) W.Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' z)
  c5 : (∀ j, ⊤ ≤ (W.F.ex (W.ik k) W.Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val)
  c6 : (∀ a j z, ‖χl (W.Pm a)‖ = 1 ∧ (⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (W.Pm a) * Complex.exp (Real.pi * hermForm Hm z (W.Pm a) +
      Real.pi / 2 * hermForm Hm (W.Pm a) (W.Pm a)) * fr j (z + W.Pm a)))
  c7 : (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
      pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left →
      pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z)
  c8 : MeasureTheory.IsAddFundamentalDomain W.Pm.range Fd MeasureTheory.volume
  c9 : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
      (MeasureTheory.volume Fd).toReal = 1

theorem nonempty_unitAt {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)
    (hu : ∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) : Nonempty (UnitAt W) := by
  obtain ⟨Hm, χl, fr, θ, Fd, h0, h0', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := W.unit hu
  exact ⟨⟨Hm, χl, fr, θ, Fd, h0, h0', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
