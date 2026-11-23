import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MemArchMaxCompactIffOrthogonalAtInfinitePlaces
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem kfinite_of_level {K : Type} [Field K] [NumberField K] {n : ℕ} (φ : AdelicGLn.AdelicGL K n → ℂ)
    (hS : IsOpen {k : AdelicGLn.FiniteAdelicGL K n | rightTranslate (finEmb K n k) φ = φ})
    (W : Submodule ℂ (AdelicGLn.AdelicGL K n → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ y ∈ archCompact K n, rightTranslate (infEmb K n y) φ ∈ W) : IsKFinite φ := by
  classical
  obtain ⟨T, hT⟩ := (AdelicGLn.isCompact_integralFiniteGL K n).elim_finite_subcover
    (fun x : AdelicGLn.FiniteAdelicGL K n =>
      (fun y => x⁻¹ * y) ⁻¹' {k : AdelicGLn.FiniteAdelicGL K n | rightTranslate (finEmb K n k) φ = φ})
    (fun x => hS.preimage (continuous_const.mul continuous_id))
    fun k _ => Set.mem_iUnion.2 ⟨k, funext fun g => by simp [rightTranslate]⟩
  unfold IsKFinite
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ x : T, W.map (rightTranslateL (finEmb K n x))) ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨x, hx, hu⟩ := Set.mem_iUnion₂.1 (hT (finPart_mem_integralFiniteGL k.2))
  refine Submodule.mem_iSup_of_mem ⟨x, hx⟩ ⟨_, hW _ (archPart_mem_archCompact k.2), funext fun g => ?_⟩
  have h := congrFun hu (g * finEmb K n x * infEmb K n (archPart (k : AdelicGLn.AdelicGL K n)))
  change φ (g * finEmb K n x * infEmb K n (archPart (k : AdelicGLn.AdelicGL K n))) = φ (g * k)
  rw [← h]
  change φ (_ * _) = _
  congr 1
  conv_rhs => rw [← infEmb_archPart_mul_finEmb_finPart (k : AdelicGLn.AdelicGL K n)]
  rw [mul_assoc g, ← infEmb_mul_finEmb_comm, mul_assoc g, mul_assoc, ← map_mul, mul_inv_cancel_left]

theorem UpperTheory.k_finite_vectors :
    UpperTheory.V.Fb.KFinTo := by
  intro E _ _ _ a φ hl hk
  refine kfinite_of_level φ.1 ?_
    ((Submodule.span ℂ (Set.range fun k => TR.cptRep E a k φ)).map (TR.Sm E a).subtype) fun y hy => ?_
  · rw [finEmb_eq]
    convert hl using 1
    exact Set.ext fun k => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · obtain ⟨z, rfl⟩ := (grpEq E a).surjective y
    refine ⟨_, Submodule.subset_span ⟨⟨z.val, (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces E a z).1 hy⟩, rfl⟩, ?_⟩
    have e : Unitary.toUnits (⟨z.val, (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces E a z).1 hy⟩ : TR.Kinf E a) = z := Units.ext rfl
    rw [infEmb_grpEq]
    funext g
    change φ.1 (g * TR.infGL E a (Unitary.toUnits _)) = φ.1 (g * _)
    rw [e]
