import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LocF
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.JL

private theorem UpperTheory.V.Lit.JL.exists_intertwiner_iff {G A A' B B' : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup A'] [Module ℂ A'] [AddCommGroup B] [Module ℂ B] [AddCommGroup B'] [Module ℂ B']
    (α : G → Module.End ℂ A) (α' : G → Module.End ℂ A') (β : G → Module.End ℂ B) (β' : G → Module.End ℂ B')
    (c : G → ℂ) (hc : ∀ g, c g ≠ 0) (e : A ≃ₗ[ℂ] A') (t : B ≃ₗ[ℂ] B')
    (he : ∀ g x, α' g (e x) = c g • e (α g x)) (ht : ∀ g y, β' g (t y) = c g • t (β g y)) :
    (∃ f : A →ₗ[ℂ] B, f ≠ 0 ∧ ∀ g x, f (α g x) = β g (f x)) ↔
      ∃ f : A' →ₗ[ℂ] B', f ≠ 0 ∧ ∀ g x, f (α' g x) = β' g (f x) := by
  rw [(LinearEquiv.arrowCongr e t).surjective.exists]
  refine exists_congr fun f => and_congr (LinearEquiv.map_ne_zero_iff _).symm (forall_congr' fun g => ?_)
  rw [e.surjective.forall]
  refine forall_congr' fun x => ?_
  simp only [he, ht, map_smul, LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
  rw [(smul_right_injective _ (hc g)).eq_iff, t.injective.eq_iff]

theorem UpperTheory.V.Lit.JL.tw :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (s : ℂ), ∃ (π' : TR.CuspSub F 2) (T : π.V ≃ₗ[ℂ] π'.V), (∀ φ g, (T φ).1.1 g = φ.1.1 g * ((chiDet 2 (Model.absC F s) g : ℂˣ) : ℂ)) ∧ (∀ v m, π.HasInfChar v m → π'.HasInfChar v (m.map (· + s))) ∧ (∀ v i j φ, ∃ h : TR.Eop v i j φ.1 ∈ π.V, TR.Eop v i j (T φ).1 = (T ⟨_, h⟩).1 + (if i = j then s else 0) • (T φ).1) ∧ ∀ τ τ' : SmIrr (GL (Fin 2) (Af F)), IsTw s τ τ' → (π.IsFinComp τ ↔ π'.IsFinComp τ') := by
  intro F _ _ _ π s
  refine ⟨π.twist (Model.absC F s), π.toTwist (Model.absC F s), fun φ g => rfl, fun v m h => ?_,
    fun v i j φ => ⟨π.stable (.lie _) _ φ.2, ?_⟩, ?_⟩
  · have h1 := h.twist (Model.absC F s)
    rwa [TR.SS.expo_absC] at h1
  · have h1 := TR.Eop_mulChi (Model.absC F s) v i j φ.1
    rw [TR.SS.expo_absC, map_add, map_smul] at h1
    exact h1
  · rintro τ τ' ⟨e, he⟩
    exact exists_intertwiner_iff (fun g => τ.ρ g) (fun g => τ'.ρ g) (fun g => π.finPart g)
      (fun g => (π.twist (Model.absC F s)).finPart g) _ (fun g => Units.ne_zero _) e _ he
      (TR.CuspSub.finPart_toTwist (Model.absC F s))
