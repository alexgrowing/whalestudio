import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.EvNatPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def WtRed : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

theorem wtRed_of (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : AllTest Xo c) (hW : WtField Xo c) (hB : FrBCFieldSt Xo c) : WtRed Xo c := by
  intro a n f hf S _ _ _ t y y' hb
  have hN := evNat_of Xo c hWD hA
  rw [← sub_eq_zero]
  set d := evR Xo c f y' - wchar (ex Dw a n) t * evR Xo c f y with hd
  have hP : ∀ P : Ideal S, P.IsPrime → d ∈ P := by
    intro P hPp
    have := hPp
    let ρ : S →+* FractionRing (S ⧸ P) := (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
    let _ : Algebra c.F (FractionRing (S ⧸ P)) := (ρ.comp (algebraMap c.F S)).toAlgebra
    let φ : S →ₐ[c.F] FractionRing (S ⧸ P) := { ρ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hB S y (FractionRing (S ⧸ P)) φ
    obtain ⟨z', hz'⟩ := hB S y' (FractionRing (S ⧸ P)) φ
    have hbz := frBorBC (Xo := Xo) (c := c) S (FractionRing (S ⧸ P)) φ t y y' z z' hb hz hz'
    have e1 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y z hz
    have e2 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y' z' hz'
    have e3 := hW a n f hf (FractionRing (S ⧸ P)) _ z z' (hA _ z) (hA _ z') hbz
    have hw : φ (wchar (ex Dw a n) t) = wchar (ex Dw a n) (fun i => Units.map (φ : S →* FractionRing (S ⧸ P)) (t i)) := by
      simp only [wchar, map_prod, map_pow, Units.coe_map, MonoidHom.coe_coe]
    have h0 : φ d = 0 := by
      rw [hd, map_sub, map_mul, ← e1, ← e2, e3, hw, sub_self]
    have h1 : algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P d) = 0 := h0
    have h2 : Ideal.Quotient.mk P d = 0 :=
      (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))) (by rw [h1, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hnil : d ∈ nilradical S := by
    rw [nilradical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun Q hQ => hP Q hQ
  exact IsReduced.eq_zero d (mem_nilradical.mp hnil)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
