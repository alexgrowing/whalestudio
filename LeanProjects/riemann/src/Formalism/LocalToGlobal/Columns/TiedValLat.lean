import Formalism.LocalToGlobal.Columns.TiedVal
import Formalism.LocalToGlobal.Columns.TiedValLatG

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ)

omit hc hX σ₀ hσ in
theorem vl_natW_lamTrue (τ : X.Tau) : (W.lamTrue u i τ).natW = (W.lamN u i τ).natW := by
  rw [lamTrue_eq_shW]
  exact natW_shW _ _

include hX in

theorem Val.lat (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K)) (hpw : Function.Surjective pw)
    (hval : ∀ w (x : X.K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (Q : ValCrd W Λ σ₀ u i) :
    Val.Lat W Λ hc σ₀ hσ u i Pl Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro x
  rw [(stepGSD W Λ u i).mem_intDel_iff (stepOk W Λ hX u i) (stepGSD W Λ u i).outSec x]
  have key := fun c : StCl W Λ u i => vl_mem_delAtr_iff Pl pw hval X.emb σ₀ hpw (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
    (W.lamTrue u i) (W.lamN u i) (vl_natW_lamTrue W u i) ((stepGSD W Λ u i).outSec.rep c).1.Lsh
    ((stepGSD W Λ u i).outSec.rep c).2.Lsh_lattice ((x : (stepGSD W Λ u i).D → (stepGSD W Λ u i).V) ((stepGSD W Λ u i).outSec.rep c))
  constructor
  · intro h w c B hB
    have hB' : IsLocBasis (Pl.resChar w) (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L) B := hB
    rw [rlc_dualSet hc (R.N i)] at hB'
    obtain ⟨P, hP, he⟩ := (key c).1 (h c) w B hB'
    exact ⟨P, hP, fun z => congrFun he z⟩
  · intro h c
    refine (key c).2 fun w B hB => ?_
    have hB' : IsLocBasis (Pl.resChar w) (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L) B := by
      rw [rlc_dualSet hc (R.N i)]
      exact hB
    obtain ⟨P, hP, he⟩ := h w c B hB'
    exact ⟨P, hP, funext he⟩

end Gen

end Formalism.L2.Col
