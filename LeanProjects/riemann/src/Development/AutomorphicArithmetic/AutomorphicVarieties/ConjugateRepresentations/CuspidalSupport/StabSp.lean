import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.stabSp :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.LevelSplit → UpperTheory.V.Cj.S.HullBdd → UpperTheory.V.Cj.S.HullOps → UpperTheory.V.Cj.S.StabSp := by
  intro hC hL hB hO E _ _ _ a S hS
  obtain ⟨L, hLo, hl⟩ := hS.level
  obtain ⟨L', hL'o, hle, T, hT, hsp⟩ := hL E a L hLo
  obtain ⟨h1, h2, h3⟩ := hO E a S
  have hb := hB E a S hS L' hL'o
  have hK : ∀ w ∉ T, fixed (finRep E a) L' ≤ fixed (fL a w) (KGL w a) := fun w hw φ hφ =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ _ ((hsp w hw).1 k hk)
  refine ⟨T, hT, hull S ⊓ fixed (finRep E a) L', le_inf h1 fun φ hφ => ?_, ?_, fun φ hφ => ?_,
    fun w hw => inf_le_right.trans (hK w hw), ?_⟩
  · refine GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (funext fun g => ?_)
    have := hl _ ⟨φ, hφ, rfl⟩ u (hle hu) g
    rw [UpperTheory.V.Fb.finEmb_eq] at this
    exact this
  · haveI := UpperTheory.V.Af.Fin.formsFinite E a _ hb
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (UpperTheory.V.Cm.smEq E a).injective _).symm
  · exact (UpperTheory.V.Cm.isAutForm_iff φ).2 (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hb _ ⟨φ, hφ, rfl⟩)
  · rintro (⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩) φ ⟨hφ, hφ'⟩
    · refine ⟨h2 t u φ hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
      have e := LinearMap.congr_fun ((hC E a t u).1 (finGL E a k)).eq φ
      have e' : rt E a (finGL E a k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ' k hk
      rw [Module.End.mul_apply, Module.End.mul_apply, e'] at e
      exact e.symm
    · have hc := Final.GLintComm E w a
      refine ⟨?_, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
      · change heckeVec (fL a w) (KGL w a) h φ ∈ hull S
        rw [heckeVec, finsum_eq_sum (fun c : _ ⧸ KGL w a => h c.out • fL a w c.out φ) (finite_heckeVec hc hh (fL a w) φ)]
        exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (h3 _ φ hφ)
      · change finRep E a u (heckeVec (fL a w) (KGL w a) h φ) = heckeVec (fL a w) (KGL w a) h φ
        obtain ⟨k, hk, u', hu', e1, rfl⟩ := (hsp w hw).2 u hu
        have e2 := map_heckeVec hc hh (ρ := fL a w) (ρ' := fL a w) (finRep E a u') (fun g y => by
          change finRep E a u' (finRep E a (locGL E a w g) y) = finRep E a (locGL E a w g) (finRep E a u' y)
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
            LocUniq.comm_locGL w e1]) φ
        rw [map_mul, Module.End.mul_apply, e2, GlobalTheory.LGrp.mem_fixed.1 hφ' u' hu']
        exact GlobalTheory.LGrp.mem_fixed.1 (SatCompare.heckeVec_mem_fixed hc hh (hK w hw hφ')) k hk
