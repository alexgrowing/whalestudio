import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.SmGL.SegModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_irrCl_zero : Subsingleton (IrrCl (GL (Fin 0) k)) := by
  have key : ∀ σ : IrrRep (GL (Fin 0) k),
      Nonempty ((ofChar (1 : GL (Fin 0) k →* ℂˣ)).Equiv σ.ρ) := by
    intro σ
    have := nontrivial_of_irreducible σ.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : σ.V)
    have h1 : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
    let f : (ofChar (1 : GL (Fin 0) k →* ℂˣ)).IntertwiningMap σ.ρ :=
      ⟨LinearMap.toSpanSingleton ℂ σ.V v, fun g => by rw [h1 g]; ext; simp⟩
    have hf : Function.Injective f := LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ hv)
    obtain ⟨φ⟩ := (IsSubquotient.of_injective f hf).nonempty_equiv (isIrreducible_ofChar _) σ.irr
    exact ⟨φ.symm⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨φ⟩ := key a.rep
  obtain ⟨ψ⟩ := key b.rep
  rw [← a.cl_rep, ← b.cl_rep]
  exact IrrRep.cl_eq_iff.2 ⟨φ.symm.trans ψ⟩

theorem segmentClass_unique {Z Z' : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
    (h : IsSegmentClass k Z) (h' : IsSegmentClass k Z') : Z = Z' := by
  funext Δ
  let e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d) := Fintype.equivOfCardEq (by simp)
  have a := (h Δ Δ.start.rep Δ.start.cl_rep e (Z Δ).rep).2.1 (Z Δ).cl_rep
  exact (Z Δ).cl_rep.symm.trans ((h' Δ Δ.start.rep Δ.start.cl_rep e (Z Δ).rep).2.2 a)

theorem prod_ne_det (h : Published.ZelevinskyPolynomialRing) {χ ψ ω : kˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (hψ : IsSmoothChar ψ) (hω : IsSmoothChar ω) :
    IsEmpty ((prod₂ (detRep (Fin 1) χ) (detRep (Fin 1) ψ)).Equiv
      (detRep (Fin 2) (ω * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨Z, Ψ, hZ, hΨ, hX⟩ := h k
  have one : ∀ {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ), Ψ (clsGL (IrrRep.det (Fin 1) χ hχ).ρ
      (IrrRep.hasFiniteLength _)) = MvPolynomial.X (Segment.ofChar χ hχ 1 one_pos) := by
    intro χ hχ
    rw [clsGL_irr, ← hX, hZ.ofChar hχ one_pos]
    congr 3
    simp
  obtain ⟨hf, e⟩ := hΨ.2 1 1 _ _ (IrrRep.det (Fin 1) χ hχ).ρ (IrrRep.det (Fin 1) ψ hψ).ρ
    (IrrRep.hasFiniteLength _) (IrrRep.hasFiniteLength _) (IrrRep.smooth _) (IrrRep.smooth _)
  rw [one, one] at e
  have two := hX (Segment.ofChar ω hω 2 two_pos)
  rw [hZ.ofChar hω two_pos] at two
  let τ := IrrRep.det (Fin (2 * 1)) (ω * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))
      (hω.mul (isSmoothChar_of_isUnram (isUnram_absPow k _)))
  have e2 : clsGL (prod₂ (IrrRep.det (Fin 1) χ hχ).ρ (IrrRep.det (Fin 1) ψ hψ).ρ) hf =
      clsGL τ.ρ τ.hasFiniteLength := clsGL_congr φ _ _
  rw [e2, clsGL_irr] at e
  have e3 := two.symm.trans e
  have := congrArg (MvPolynomial.eval fun _ => (2 : ℤ)) e3
  simp at this

theorem sizeMatrix_two (b : SizeMatrix (fun _ : Fin 2 => Fin 1) (fun _ : Fin 2 => Fin 1)) :
    b.1 = ![![1, 0], ![0, 1]] ∨ b.1 = ![![0, 1], ![1, 0]] := by
  obtain ⟨b, h1, h2⟩ := b
  have a0 := h1 0
  have a1 := h1 1
  have b0 := h2 0
  simp only [Fin.sum_univ_two, Fintype.card_fin] at a0 a1 b0
  rcases Nat.eq_zero_or_pos (b 0 0) with h | h
  · right
    funext i j
    fin_cases i <;> fin_cases j <;> simp <;> omega
  · left
    funext i j
    fin_cases i <;> fin_cases j <;> simp <;> omega

example : Unique (SizeMatrix (fun _ : Empty => Empty) (fun _ : Empty => Empty)) :=
  ⟨⟨⟨fun i => i.elim, fun i => i.elim, fun i => i.elim⟩⟩, fun _ => Subtype.ext (funext fun i => i.elim)⟩

end GlobalTheory.SmGL.SegModel
