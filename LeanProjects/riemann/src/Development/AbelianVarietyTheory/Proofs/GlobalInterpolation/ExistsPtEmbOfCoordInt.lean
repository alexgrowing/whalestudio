import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.BrExistsOfRestS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.FormsRatOfInt

theorem intSpan_le_ratSpan (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam ≤ Formalism.L2.Forms.RatSpan D lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan Formalism.L2.Forms.RatSpan
  apply AddSubgroup.closure_mono
  rintro p ⟨r, f, -, hf, rfl⟩
  exact ⟨r, f, hf, rfl⟩

theorem exists_ptEmb_of_coord_int : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E) (w : D.what₂.places.Pl), ∀ z ∈ (D.fm u).ptC, (∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg) → ∃ y, (D.fm u).ptEmb y = z := by
  intro D u Ch chOf Tf B w z hz hint
  refine (Tf.valP.rat z).2 ⟨hz, fun c => ?_⟩
  have hB : IsUnit ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (B w c))
  obtain ⟨Q, hQ, hq⟩ := Formalism.L2.GlobalTheoryTheory.Br.eW_repS Tf _ hB z hz c
  have hco : Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) :
      Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w z c = Q := by
    simp only [Formalism.L2.GlobalTheoryTheory.Br.coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearEquiv.coe_coe]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ hB)]
  have hQr : Q ∈ Formalism.L2.Forms.RatSpan D (D.fm u).sg := intSpan_le_ratSpan D w _ (hco ▸ hint c)
  obtain ⟨Q', hQ', he⟩ := GlobalTheory.LevelHecke.exists_ratSpan_fnOf_atInf (D.fm u).sg _ (shiftOf (sgT u))
    (((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹) hQr
  exact ⟨Q', hQ', hq.trans he⟩

end GlobalTheory.FormsRatOfInt
