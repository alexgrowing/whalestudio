import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.ExistsRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CRes

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private def blkEquiv {k Γ J X : Type} [Field k] [Group Γ] (s : J → Γ) (β : J → X) :
    (Γ × J → k) ≃ₗ[k] ∀ p : Γ × X, ({j // β j = p.2} → k) where
  toFun v p j := v (p.1 * s j.1, j.1)
  invFun w p := w (p.1 * (s p.2)⁻¹, β p.2) ⟨p.2, rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by ext p; simp
  right_inv w := by
    ext ⟨a, x⟩ ⟨j, hj⟩
    dsimp only at hj ⊢
    subst hj
    have key : ∀ a' : Γ, a' = a → w (a', β j) ⟨j, rfl⟩ = w (a, β j) ⟨j, rfl⟩ := by rintro _ rfl; rfl
    exact key _ (by simp)

theorem UpperTheory.V.ZK.Cl.cVal :
    UpperTheory.V.ZK.Cl.CVal := by
  intro L F _ _ _ _ _ J _ q _ e ζ h kap hkap k _ _ r b hb hS μ hμ hζ v θ hθ hv f hf χ 𝔟 δ g ρ ⟨_, s, β, g', hB, hs, hδ⟩ hρ
  classical
  obtain ⟨q1, q2, q3, -⟩ := cRes L F k r
  have hloc := ((cBlock L F J _ s β g').2 g.1 hB).2.1 b g.2
  choose g₁ hg₁ hg₂ using fun (x : ZMod q) => (cMat L F _ k r b hb (g' x) (hloc x)).2
  have hint : ∀ (I : Type) (a : I → 𝓞 F), InLoc b fun i => (a i : F) := fun I a i P _ => P.valuation_le_one (a i)
  have hlift : ∀ w : (F ≃ₐ[L] F) × J → k, ∃ a : J → 𝓞 F, ∀ σ j, r (actO σ (a j)) = w (σ, j) := fun w => by
    choose a ha using fun j => hS.1 fun σ => w (σ, j)
    exact ⟨a, fun σ j => ha j σ⟩
  have hred : ∀ (σ : F ≃ₐ[L] F) (a : 𝓞 F), ResF r (σ a) (r (actO σ a)) := fun σ a => q2 (actO σ a)
  rw [cBlockVal k q e _ hζ v θ hθ hv ((F ≃ₐ[L] F) × ZMod q) (fun p => {j // β j = p.2} → k) _ (blkEquiv s β) (μ.comp ρ) (μ g)
    (fun p => kap p.1 * p.2.val) (fun p => g₁ p.2 p.1), Fintype.sum_prod_type]
  · refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun x _ => ?_
    rw [← hδ, hf _ _ (hg₁ x σ)]
    simp
  · rintro c w ⟨σ, x⟩
    obtain ⟨a, ha⟩ := hlift w
    ext ⟨j, hj⟩
    dsimp only at hj
    have h1 := hμ (ρ c) _ w (hint J a) (fun τ j => ha τ j ▸ hred τ (a j)) (σ * s j) j
    refine q1 _ _ _ h1 ?_
    have h2 : (σ * s j) ((ρ c).1 (fun i => (a i : F)) j) =
        ((ζ ^ (kap σ * x.val * (Multiplicative.toAdd c).val) : (𝓞 F)ˣ) : 𝓞 F) * (σ * s j) (a j) := by
      rw [hρ]
      change (σ * s j) (((toF ζ ^ ((χ j).val * (Multiplicative.toAdd c).val) : Fˣ) : F) * a j) = _
      rw [map_mul]
      congr 1
      have h3 : actU σ (actU (s j) (toF ζ ^ ((χ j).val * (Multiplicative.toAdd c).val))) =
          toF ζ ^ (kap σ * x.val * (Multiplicative.toAdd c).val) := by
        rw [pow_mul, map_pow, map_pow (actU (s j)), hs, hj, map_pow, map_pow, hkap, pow_mul, pow_mul]
      have h4 := congrArg Units.val h3
      simpa [actU, toF] using h4
    rw [h2]
    have h5 := (q3 _ _ _ _ (q2 ((ζ ^ (kap σ * x.val * (Multiplicative.toAdd c).val) : (𝓞 F)ˣ) : 𝓞 F))
      (hred (σ * s j) (a j))).2
    rw [ha] at h5
    convert h5 using 1
    simp [chi, blkEquiv]
  · rintro w ⟨σ, x⟩
    obtain ⟨a, ha⟩ := hlift w
    ext ⟨j, hj⟩
    dsimp only at hj
    subst hj
    have h1 := hμ g _ w (hint J a) (fun τ j => ha τ j ▸ hred τ (a j)) (σ * s j) j
    refine q1 _ _ _ h1 ?_
    rw [AlgEquiv.mul_apply, hB]
    exact hg₂ (β j) σ _ _ (hint _ fun i : {i // β i = β j} => actO (s i.1) (a i.1))
      (fun i => by
        have := hred (σ * s i.1) (a i.1)
        rw [ha] at this
        exact this) ⟨j, rfl⟩
