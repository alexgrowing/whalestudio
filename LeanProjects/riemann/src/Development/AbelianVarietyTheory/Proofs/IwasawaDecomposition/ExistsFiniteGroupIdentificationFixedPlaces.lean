import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Formalism.LocalToGlobal.Columns.ExistsUnitOfPowEqOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem exists_grpIdent : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), IsPlacewiseIdentity X (px := px) eG ∧ (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  intro X px I U L hI hG hL
  obtain ⟨plg0, hplg0⟩ := hG.pl
  have hPr := (base_fields_primes_ok X.B px).2.1
  have h1 : ∀ P, P ∈ L.Pg ↔ P ∈ (X.B.primes px).vGs := fun P => by rw [hL.Pg]; exact Iff.rfl
  let eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r :=
    { toFun := fun g PP => g ⟨PP.1, (h1 _).1 PP.2⟩
      invFun := fun h PP => h ⟨PP.1, (h1 _).2 PP.2⟩
      left_inv := fun g => rfl
      right_inv := fun h => rfl
      map_mul' := fun _ _ => rfl }
  let plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg := plg0.trans (Equiv.subtypeEquivRight fun P => (h1 P).symm)
  have hmem : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ((plg kv : L.Pg) : Pl X.toD7.host.E) ∈ (X.B.primes px).vG kv.1 :=
    fun kv => (hI.pibar kv.1 _).2 (hplg0 kv).2
  have hiso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), Nonempty (ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1) := by
    intro kv
    haveI : Fact (X.toD7.host.g kv.1).Prime := ⟨hPr.g_prime kv.1⟩
    obtain ⟨e⟩ := Formalism.L2.Col.residueField_equiv_zmod (X := X.B.fields) (plg kv).1 (X.toD7.host.g kv.1) (hPr.vG_norm kv.1 _ (hmem kv))
    exact ⟨e.symm⟩
  let iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1 := fun kv => Classical.choice (hiso kv)
  let cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd :=
    { toEquiv := (Equiv.piCongrLeft (fun PP : L.Pg => GL (Fin X.toD7.R.r) (kP PP.1)) plg).symm.trans
        (Equiv.piCongrRight fun kv => (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm).toEquiv)
      map_mul' := fun f f' => by
        funext kv
        exact map_mul (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm) (f (plg kv)) (f' (plg kv)) }
  refine ⟨eG, cG, plg, iso, fun g P h h' => rfl, fun kv => (hplg0 kv).1, fun kv => ?_, fun g kv => ?_⟩
  · rw [hL.C]
    exact (hplg0 kv).2
  · show _ = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1)
      (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm (eG g (plg kv)))
    ext i j
    simp [Formalism.UG.bc, Formalism.L2.Col.generalLinearEquivOfRingEquiv]
end GlobalTheory.Mem.R3

end
