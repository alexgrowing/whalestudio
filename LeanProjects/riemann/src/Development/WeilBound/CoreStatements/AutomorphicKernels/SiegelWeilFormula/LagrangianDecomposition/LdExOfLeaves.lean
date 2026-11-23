import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def YFrame : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ), n + 1 = d.n → 1 ≤ n →
  ∃ (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ), SignOK d Y ∧ IsFrame2 σ Y b ∧
    d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε

def JEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ j : G2 σ Y →* d.G, IsJ d h b j

def KStd : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), IsFrame2 σ Y b → IsJ d h b j → IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j)

def HgtPull : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b → IsJ d h b j → IsHgt (d.K.comap j) (d.a ∘ j)

def ModelEx : Prop := TAll → AuxiliaryPrimeFunction → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b →
  (∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) → IsJ d h b j →
  ∃ (κ : Type) (_ : Fintype κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), IsDbl (σ := σ) (A := d.A) (Y := Y) d.B.ψ dd d.χ om S l ∧ Res d h b j dd om l

theorem ldEx_of_leaves (h1 : YFrame) (h2 : JEx) (h3 : KStd) (h4 : HgtPull) (h5 : ModelEx) : TAll → AuxiliaryPrimeFunction → LDEx := by
  intro hT hA F E _ _ _ _ _ σ d hd
  have h : d.n - 1 + 1 = d.n := by omega
  obtain ⟨Y, b, ε, hsign, hframe, hdb, hb⟩ := h1 F E σ d (d.n - 1) h (by omega)
  obtain ⟨j, hj⟩ := h2 F E σ d (d.n - 1) h Y b ε hdb hb
  have hK := h3 F E σ d (d.n - 1) h Y b j hframe hj
  have hH := h4 F E σ d (d.n - 1) h Y b j (by omega) hsign hframe hj
  obtain ⟨κ, hκ, dd, om, S, l, hdbl, hres⟩ :=
    h5 hT hA F E σ d (d.n - 1) h Y b j (by omega) hsign hframe ⟨ε, hdb, hb⟩ hj
  exact ⟨{
      n := d.n - 1, Y := Y, κ := κ, fin := hκ, dd := dd, om := om, S := S, l := l, b := b
      K := d.K.comap j, a := d.a ∘ j
      ok := {
        good := d.ok.good, hm := d.ok.hm, hn := by omega, aniso := d.ok.aniso, sign := hsign
        hecke := d.ok.hecke, res := d.ok.res, dbl := hdbl, frame := hframe, stdK := hK, hgt := hH
        haar := d.ok.haar, dom := d.ok.dom }
      i₀ := i0 h, em := em0 h, inj := em0_injective h, rng := ne_last_iff_mem_range h, j := j, cont := hj.1
      j_in := hj.2.1, j_out := hj.2.2, res := hres }⟩

end PositivityTheory.SiegelWeilFormula.Ald

end
