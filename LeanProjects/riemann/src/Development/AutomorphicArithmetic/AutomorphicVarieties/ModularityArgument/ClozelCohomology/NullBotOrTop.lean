import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ClozelConjCOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix GlobalTheory.PRep GlobalTheory.Published GlobalTheory.CuspRep.LocEx

namespace UpperTheory.V.Z.Coh.FiniteTypesComponentExistence

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private def types (π : CuspSub E a) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) :
    Submodule ℂ π.V where
  carrier := {ψ | ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy g => add_mem (hx g) (hy g)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun c _ hx g => Submodule.smul_mem _ c (hx g)

private theorem types_act (π : CuspSub E a) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (g : GL (Fin a) (Af E)) (x : π.V) (hx : x ∈ types π ρ) :
    π.finPart g x ∈ types π ρ := fun y => by
  convert hx (y * finGL E a g) using 2 with k
  change x.1.1 (y * infGL E a _ * finGL E a _) = x.1.1 (y * finGL E a _ * infGL E a _)
  rw [mul_assoc, mul_assoc, infGL_comm]

private theorem types_fin (h : AutomorphicFormsFiniteGL) (π : CuspSub E a)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {ρ : Representation ℂ (Kinf E a) W}
    (hρ : AutFin.IsContRep ρ) (K : Subgroup (GL (Fin a) (Af E))) (hK : IsOpen (K : Set (GL (Fin a) (Af E)))) :
    FiniteDimensional ℂ ↥(types π ρ ⊓ fixed π.finPart K) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ π.V, cap τ u φ = c • φ := fun τ u =>
    π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a K hK W ρ hρ c
  exact FiniteDimensional.of_injective ((π.V.subtype ∘ₗ (types π ρ ⊓ fixed π.finPart K).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms K ρ c))
    fun v => Submodule.subset_span ⟨(π.cusp _ v.1.2).1, fun k hk => congrArg Subtype.val (mem_fix.1 v.2.2 k hk),
      v.2.1, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))

private theorem null_bot_or_top (π : CuspSub E a) (K : Subgroup (GL (Fin a) (Af E))) :
    nullPart π.finPart K = ⊥ ∨ nullPart π.finPart K = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ nullPart π.finPart K, π.op o x ∈ nullPart π.finPart K := fun o x hx => by
    cases o with
    | fin k => exact nullPart_act _ K k hx
    | cpt k =>
      refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a g)) y.1 =
        (rt E a (finGL E a g) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X => exact nullPart_comm _ K _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X g) y.1)) hx
  refine (π.irred ((nullPart π.finPart K).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩)).imp (fun e => hi (e.trans (Submodule.map_bot _).symm))
    fun e => hi (e.trans (Submodule.map_subtype_top _).symm)

private theorem exists_comp (h : AutomorphicFormsFiniteGL) (π : CuspSub E a) : ∃ τ, UpperTheory.V.Af.IsFinComp π τ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have h0' : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hL : IsOpen (stab π.finPart ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) := π.isSmooth_finPart _
  obtain ⟨K₀, ho₀, hc₀⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  have ho : IsOpen ((K₀ ⊓ stab π.finPart ⟨φ, hφ⟩ : Subgroup _) : Set (GL (Fin a) (Af E))) := ho₀.inter hL
  have hc : IsCompact ((K₀ ⊓ stab π.finPart ⟨φ, hφ⟩ : Subgroup _) : Set (GL (Fin a) (Af E))) :=
    hc₀.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1
  have : FiniteDimensional ℂ (orbSpan φ) := (π.cusp φ hφ).1.kfin
  obtain ⟨σ, hσ, -⟩ := exists_irred π.isSmooth_finPart ho (fun W hW e => by
      rcases null_bot_or_top π (K₀ ⊓ stab π.finPart ⟨φ, hφ⟩) with h2 | h2
      · exact le_bot_iff.1 (h2 ▸ le_nullPart π.isSmooth_finPart hc W hW e)
      · exact absurd (eq_zero_of_mem_nullPart π.isSmooth_finPart hc (mem_fix.2 fun k hk => hk.2)
          (h2 ▸ Submodule.mem_top)) h0')
    (types π (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ))) (types_act π _)
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩,
      AutFinGL.type_of_map (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)) (orbSpan φ).subtype (fun _ _ => rfl)
        ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩, h0'⟩)
    (types_fin h π (isContRep_sub _ _))
  exact ⟨σ, hσ⟩

end UpperTheory.V.Z.Coh.FiniteTypesComponentExistence

theorem UpperTheory.V.Z.Coh.finExC :
    UpperTheory.V.Lit.FinExC := fun _ _ _ _ _ π =>
  UpperTheory.V.Z.Coh.FiniteTypesComponentExistence.exists_comp UpperTheory.V.Af.formsFiniteGL π
