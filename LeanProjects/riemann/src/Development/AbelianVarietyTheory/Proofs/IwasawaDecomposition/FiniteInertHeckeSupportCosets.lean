import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd.CosetFin

theorem finite_cosets {G H : Type} [Group G] [Group H] (φ : G →* H) (H' : Subgroup H) (K : Subgroup H')
    (U : Subgroup G) (p : G → Prop) (F : Set (H' ⧸ K)) (hF : F.Finite)
    (hp : ∀ x, p x → ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) ∈ F)
    (hU : ∀ x y, p x → p y → ∀ hz : φ (x⁻¹ * y) ∈ H', (⟨φ (x⁻¹ * y), hz⟩ : H') ∈ K → x⁻¹ * y ∈ U) :
    Set.Finite {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} := by
  have hsub : {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} ⊆
      ⋃ d ∈ F, {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x ∧
        ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) = d} := by
    rintro c ⟨x, hc, hx⟩
    obtain ⟨h1, h2⟩ := hp x hx
    exact Set.mem_biUnion h2 ⟨x, hc, hx, h1, rfl⟩
  refine (hF.biUnion fun d _ => Set.Subsingleton.finite ?_).subset hsub
  rintro c ⟨x, rfl, hx, hx1, hx2⟩ c' ⟨y, rfl, hy, hy1, hy2⟩
  have hk := QuotientGroup.eq.1 (hx2.trans hy2.symm)
  have hz : φ (x⁻¹ * y) ∈ H' := by
    rw [map_mul, map_inv]; exact H'.mul_mem (H'.inv_mem hx1) hy1
  refine QuotientGroup.eq.2 (hU x y hx hy hz ?_)
  convert hk using 1
  apply Subtype.ext
  simp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

variable {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def locHom (D : InertDatum L n v w) : GAf L n →* GL (Fin n) (w.adicCompletion L) :=
  MonoidHom.mk' D.loc fun x y => by
    simp only [InertDatum.loc, Subgroup.coe_mul, map_mul, mul_assoc, mul_inv_cancel_left]

theorem entries_int {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {σ : K →+* K}
    {g : GU σ n} (hg : g ∈ KU σ n) (i j : Fin n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ intL K := by
  obtain ⟨-, k, hk⟩ := hg
  have hk' : bc (n := Fin n) (intL K).subtype k = (g : GL (Fin n) K) := hk
  rw [← hk']
  exact ((k : Matrix (Fin n) (Fin n) (intL K)) i j).2

theorem finite_inert_support : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ s : GU Dv.σw n, Set.Finite {c : GU Dv.σw n ⧸ KU Dv.σw n | ∃ a ∈ KU Dv.σw n, ((a * s : GU Dv.σw n) : GU Dv.σw n ⧸ KU Dv.σw n) = c}) → (∀ z : GAf L n, TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n) → ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} := by
  intro L _ _ _ n v w Dv hfin hint U hU h hh
  obtain ⟨-, S, hS⟩ := hh
  refine finite_cosets (locHom Dv) (GU Dv.σw n) (KU Dv.σw n) U
    (fun x => TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0) _
    (S.finite_toSet.biUnion fun s _ => hfin s) ?_ ?_
  · rintro x ⟨-, hx⟩
    have hm : Dv.loc x ∈ GU Dv.σw n := by
      by_contra hm
      exact hx (dif_neg hm)
    have hne : h ⟨Dv.loc x, hm⟩ ≠ 0 := by
      intro h0
      exact hx ((dif_pos hm).trans h0)
    obtain ⟨s, hs, a, b, e⟩ := hS _ hne
    refine ⟨hm, Set.mem_biUnion hs ⟨a, a.2, ?_⟩⟩
    have e' : (⟨locHom Dv x, hm⟩ : GU Dv.σw n) = (a : GU Dv.σw n) * s * b := e
    rw [e']
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  · rintro x y ⟨hx, -⟩ ⟨hy, -⟩ hz hk
    have ht : TrivOutside {v} (x⁻¹ * y) := trivOutside_mul (trivOutside_inv hx) hy
    exact (hU _ ht).2 (hint _ ht fun i j => entries_int hk i j)

end GlobalTheory.SatInd.CosetFin
