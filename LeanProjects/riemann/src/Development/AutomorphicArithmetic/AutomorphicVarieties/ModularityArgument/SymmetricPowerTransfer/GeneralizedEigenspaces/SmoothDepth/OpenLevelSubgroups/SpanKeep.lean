import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem dc_conj {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (T : M ≃ₗ[A] M)
    (hT : ∀ h m, T (ρ h m) = ρ h (T m)) (m : M) :
    T (UpperTheory.V.Hi.dc ρ K K' x m) = UpperTheory.V.Hi.dc ρ K K' x (T m) := by
  have hc : ∀ h, T.conj (ρ h) = ρ h := fun h => by
    ext v
    simp [LinearEquiv.conj_apply, hT]
  have key : T.conj (UpperTheory.V.Hi.dc ρ K K' x) = UpperTheory.V.Hi.dc ρ K K' x := by
    unfold UpperTheory.V.Hi.dc
    have := AddEquiv.map_finsum (T.conj.toAddEquiv)
      (fun q : MulAction.orbit K (x : H ⧸ K') => ρ (q : H ⧸ K').out)
    simpa [hc] using this
  have := congrArg (fun E : Module.End A M => E (T m)) key
  simpa [LinearEquiv.conj_apply] using this

theorem UpperTheory.V.Z.Sym.Al.spanKeep :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (w : Plc L) (φ φ' : UA L n → V), InSpan w φ φ' →
        (∀ π, IsAutRepU π → CoefIn φ π → CoefIn φ' π) ∧
        (∀ (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (A : Subgroup (UA L n)), A ≤ away n w → IsAF R A φ → IsAF R A φ') ∧
        ∀ w' : Plc L, IsSplitAt w' → w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → ∀ W d c, EigAt φ w' W d c → EigAt φ' w' W d c := by
  intro L _ _ _ n V _ _ w φ φ' h
  obtain ⟨h1, -, h3, h4, -, -⟩ := UpperTheory.V.Z.Sym.Al.factor L n w
  refine ⟨fun π hπ hc => ?_, fun R A hA hf => ?_, fun w' hs hne W d c he => ?_⟩
  · refine Submodule.span_induction (p := fun ψ _ => CoefIn ψ π) ?_ ?_ ?_ ?_ h
    · rintro _ ⟨x, hx, rfl⟩ f
      exact hπ.stable x _ (hc f)
    · intro f
      have e : f ∘ (0 : UA L n → V) = 0 := by ext; simp
      rw [e]
      exact π.zero_mem
    · intro a b _ _ ha hb f
      have e : f ∘ (a + b) = f ∘ a + f ∘ b := by ext; simp
      rw [e]
      exact π.add_mem (ha f) (hb f)
    · intro t a _ ha f
      have e : f ∘ (t • a) = t • (f ∘ a) := by ext; simp
      rw [e]
      exact π.smul_mem t (ha f)
  · have hle : Submodule.span ℂ {ψ | ∃ x ∈ locU n w, ψ = fun g => φ (g * x)} ≤ AF R A := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨fun γ hγ g => ?_, fun y hy g => ?_, fun u hu g => ?_⟩
      · show φ (γ * g * x) = φ (g * x)
        rw [mul_assoc]
        exact hf.left γ hγ _
      · show φ (g * y * x) = R (infC L n y⁻¹) (φ (g * x))
        rw [mul_assoc, ← h1 x hx y (h4 hy), ← mul_assoc]
        exact hf.inf y hy _
      · show φ (g * u * x) = φ (g * x)
        rw [mul_assoc, ← h1 x hx u (hA hu), ← mul_assoc]
        exact hf.level u hu _
    exact hle h
  · have hsec := (UpperTheory.V.Z.Sym.Al.secSpec L n w' hs).1
    refine Submodule.span_induction (p := fun ψ _ => EigAt ψ w' W d c) ?_ ?_ ?_ ?_ h
    · rintro _ ⟨x, hx, rfl⟩
      let T : (UA L n → V) ≃ₗ[ℂ] (UA L n → V) :=
        { toFun := fun ψ g => ψ (g * x)
          invFun := fun ψ g => ψ (g * x⁻¹)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun ψ => by ext g; simp
          right_inv := fun ψ => by ext g; simp }
      have hT : ∀ (y : GL (Fin n) (Kw w')) (m : UA L n → V),
          T (((rightReg ℂ (UA L n) V).comp (secW n w')) y m) =
            ((rightReg ℂ (UA L n) V).comp (secW n w')) y (T m) := by
        intro y m
        funext g
        show m (g * x * secW n w' y) = m (g * secW n w' y * x)
        rw [mul_assoc, mul_assoc, h1 x hx _ (h3 w' hne (hsec y))]
      have e := dc_conj _ (W.J n) (W.J n) (Sig.dg d) T hT φ
      show UpperTheory.V.Hi.dc _ _ _ _ (T φ) = c • T φ
      rw [← e]
      unfold EigAt at he
      rw [he, map_smul]
    · unfold EigAt
      rw [map_zero, smul_zero]
    · intro a b _ _ ha hb
      unfold EigAt at ha hb ⊢
      rw [map_add, ha, hb, smul_add]
    · intro t a _ ha
      unfold EigAt at ha ⊢
      rw [map_smul, ha, smul_comm]
