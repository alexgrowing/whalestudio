import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open UpperTheory.V.Cj.S Formalism.UG.P
open GroundTheory.Automorphic.AutomorphicForm (archCompact infEmb)

private theorem ty_comm {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Submodule ℂ (Kinf E a → ℂ))
    [FiniteDimensional ℂ W] (T : Module.End ℂ (Sm E a)) (hT : ∀ k, Commute T (cptRep E a k)) (φ : Sm E a)
    (h : ∀ g, (fun k : Kinf E a => φ.1 (g * infGL E a (Unitary.toUnits k))) ∈ W) (g) :
    (fun k : Kinf E a => (T φ).1 (g * infGL E a (Unitary.toUnits k))) ∈ W := by
  let e := LinearEquiv.funCongrLeft ℂ ℂ (UpperTheory.V.Cm.cptEq E a).symm.toEquiv
  have key : ∀ (ψ : Sm E a) g, e (fun k : Kinf E a => ψ.1 (g * infGL E a (Unitary.toUnits k))) =
      fun k : archCompact E a => ψ.1 (g * infEmb E a k.1) := fun ψ g => funext fun k => by
    obtain ⟨k, rfl⟩ := (UpperTheory.V.Cm.cptEq E a).surjective k
    rw [UpperTheory.V.Cm.infEmb_cptEq]
    simp [e, LinearMap.funLeft]
  have h1 := typesComm E a (W.map e.toLinearMap) inferInstance T hT φ (fun g => ⟨_, h g, key φ g⟩) g
  obtain ⟨f, hf, e1⟩ := h1
  rwa [← e.injective (e1.trans (key (T φ) g).symm)]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.stabT :
    StabT := by
  intro E _ _ _ a bad L W hL hW S hS hty
  obtain ⟨h1, h2, h3⟩ := hullOps capAct E a S
  have hb := hullBdd typesComm E a S hS L hL.isOpen
  have hK : ∀ w ∉ bad, fixed (finRep E a) L ≤ fixed (fL a w) (KGL w a) := fun w hw φ hφ =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ _ (hL.loc w hw k hk)
  refine ⟨hull S ⊓ fixed (finRep E a) L, le_inf h1 fun φ hφ => ?_, ?_, fun φ hφ => ⟨?_, fun u hu g => ?_, ?_⟩,
    fun w hw => inf_le_right.trans (hK w hw), ?_⟩
  · exact GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (funext fun g => (hty φ hφ).1 u hu g)
  · haveI := UpperTheory.V.Af.Fin.formsFinite E a _ hb
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (UpperTheory.V.Cm.smEq E a).injective _).symm
  · exact (UpperTheory.V.Cm.isAutForm_iff φ).2 (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hb _ ⟨φ, hφ, rfl⟩)
  · exact congrFun (congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hφ.2 u hu)) g
  · have h4 := hφ.1
    clear hφ
    induction h4 using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨T, hT, φ, hφ, rfl⟩ := hψ
      exact ty_comm W T hT.1 φ (hty φ hφ).2
    | zero => exact fun _ => W.zero_mem
    | add x y _ _ hx hy => exact fun g => W.add_mem (hx g) (hy g)
    | smul c x _ hx => exact fun g => W.smul_mem c (hx g)
  · rintro (⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩) φ ⟨hφ, hφ'⟩
    · refine ⟨h2 t u φ hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
      have e := LinearMap.congr_fun ((capAct E a t u).1 (finGL E a k)).eq φ
      have e' : rt E a (finGL E a k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ' k hk
      rw [Module.End.mul_apply, Module.End.mul_apply, e'] at e
      exact e.symm
    · have hc := Final.GLintComm E w a
      refine ⟨?_, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
      · change heckeVec (fL a w) (KGL w a) h φ ∈ hull S
        rw [heckeVec, finsum_eq_sum (fun c : _ ⧸ KGL w a => h c.out • fL a w c.out φ) (finite_heckeVec hc hh (fL a w) φ)]
        exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (h3 _ φ hφ)
      · change finRep E a u (heckeVec (fL a w) (KGL w a) h φ) = heckeVec (fL a w) (KGL w a) h φ
        have hk := hL.int u hu w
        obtain ⟨u', hu', e1, e3⟩ : ∃ u' ∈ L, GeneralLinearGroup.map (pLoc E w) u' = 1 ∧
            u = locGL E a w (GeneralLinearGroup.map (pLoc E w) u) * u' :=
          ⟨_, L.mul_mem (L.inv_mem (hL.loc w hw _ hk)) hu, by rw [map_mul, map_inv, pLoc_locGL, inv_mul_cancel],
            (mul_inv_cancel_left _ _).symm⟩
        have e2 := map_heckeVec hc hh (ρ := fL a w) (ρ' := fL a w) (finRep E a u') (fun g y => by
          change finRep E a u' (finRep E a (locGL E a w g) y) = finRep E a (locGL E a w g) (finRep E a u' y)
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
            LocUniq.comm_locGL w e1]) φ
        rw [e3, map_mul, Module.End.mul_apply, e2, GlobalTheory.LGrp.mem_fixed.1 hφ' u' hu']
        exact GlobalTheory.LGrp.mem_fixed.1 (SatCompare.heckeVec_mem_fixed hc hh (hK w hw hφ')) _ hk
