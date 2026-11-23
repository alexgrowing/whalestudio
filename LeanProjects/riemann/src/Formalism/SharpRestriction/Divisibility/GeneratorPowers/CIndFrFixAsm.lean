import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IsUnitCoeffZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddFirstSecond
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

def FrRatioSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (m : ℕ),
    ∃ U : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
          (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
        (scaleGen (Xo := Xo) _ _ (unitΓ U) (C.e m)) ∧
      jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) =
        jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) *
        jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) ∧
      jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) = U ∧
      ∀ a : 𝓞 E, jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) =
        jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m)

def ccOf {S : Type} [CommRing S] {d : ℕ} (cm : ℕ → Fin d → Fin d → S) : ℕ → Fin d → Fin d → S
  | 0 => 0
  | m + 1 => ccOf cm m - cm m

theorem frTruncFix_of (hA : FrRatioSt) : FrTruncFixSt := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C
  choose U hCorr h1 hs hb using fun m => hA E H Dw l Xo c hstar S y C m
  have hact : ∀ (a : 𝓞 E) (i : Fin C.d), MvPowerSeries.constantCoeff (C.B.A.act a i) = 0 :=
    fun a i => C.B.A.const a i
  choose cm hcs hcb hcU using fun m =>
    CIndFrExp3.fixExp (G := C.B.G) (act := C.B.A.act) (hact := hact) (bar := H.bar) (m := m)
      (U := U m) (h1 := h1 m) (hs := hs m) (hb := hb m)
  have hsym : ∀ m i j, ccOf cm m i j = ccOf cm m j i := by
    intro m
    induction m with
    | zero => intro i j; rfl
    | succ m ih =>
      intro i j
      show ccOf cm m i j - cm m i j = ccOf cm m j i - cm m j i
      rw [ih i j, hcs m i j]
  have hbal : ∀ m (a : 𝓞 E), Matrix.transpose (dLin (C.B.A.act a)) * Matrix.of (ccOf cm m) =
      Matrix.of (ccOf cm m) * dLin (C.B.A.act (H.bar a)) := by
    intro m
    induction m with
    | zero => intro a; simp only [ccOf, Matrix.of_zero, mul_zero, zero_mul]
    | succ m ih =>
      intro a
      simp only [ccOf]
      rw [← Matrix.of_sub_of, mul_sub, sub_mul, ih a, hcb m a]
  have hdiff : ∀ m, ccOf cm m - ccOf cm (m + 1) = cm m := fun m =>
    show ccOf cm m - (ccOf cm m - cm m) = cm m from sub_sub_cancel _ _
  obtain ⟨e', hfr, hrig, htr, hu⟩ := CIndFrFix2c.fixTw (C := C) (cc := ccOf cm) (h0 := rfl)
    (hsym := hsym) (hbal := hbal)
    (hstep := fun m => ⟨U m, by rw [hdiff m]; exact hcU m, hCorr m⟩)
  exact ⟨e', hfr, hrig, ccOf cm, htr, rfl, hsym, hbal, hu⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
