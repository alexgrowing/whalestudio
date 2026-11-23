import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V.Hi

namespace UpperTheory.V.Z.J.D.Dc

theorem core3 {E : Type} [Field E] [NumberField E] [IsCMField E] {n m d : ℕ} {Γ Ga Gp D Jx : Type} [Group Γ] [Group Ga]
    [Group Gp] [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] [Fintype Jx] (X : Frame Γ Ga Gp)
    (ξ : Gp →* GL (Fin d) ℂ) (τ : X.Ub →* GL (Fin m) ℂ) (U₀ : Subgroup X.Ub) (I : Subgroup Gp) (J : UA E n →* Ga × Gp)
    (tf : (Ga × Gp → Fin d → ℂ) →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ)) (r : UA E n → D → D)
    (hJinf : ∀ x ∈ infU E n, J x = 1) (hRfin : ∀ k ∈ finU E n, ∀ ℓ, r k ℓ = ℓ)
    (hinj : ∀ F ∈ X.AF ξ, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (haut : ∀ F ∈ X.AF ξ, IsOpen {k : finU E n | ∀ g, F (g * J k) = F g} → ∀ ℓ, IsAutFormU (tf F ℓ))
    (htr : ∀ F ℓ x, RU E n x (tf F ℓ) = tf (fun g => F (g * J x)) (r x ℓ))
    (hsurj : Function.Surjective fun k : finU E n => J k)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ X.AF ξ, ∀ ℓ, tf F ℓ = Φ ℓ)
    (hev : ∀ᶠ k : finU E n in nhds 1, (∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I)
    (Kf : Subgroup (finU E n)) (hKf : ∀ k ∈ Kf, (∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I)
    (Pw : Submodule ℂ (UA E n → ℂ) → Prop)
    (hwt : ∀ σ, IsAutRepU σ → (Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
      Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ} ≠ ⊥ → Pw σ)
    (σ : Jx → Submodule ℂ (UA E n → ℂ)) (hσ : ∀ j, IsAutRepU (σ j)) (hind : iSupIndep σ)
    (hcov : ∀ π, IsAutRepU π → Pw π → π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF E n) Kf ≤ ⨆ j, σ j)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀)
    (hb : F ∈ fixd (X.rpF ℂ d m) I) :
    F ∈ ⨆ j, ((Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
      Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ j}) ⊓ fixd (X.rpF ℂ d m) I := by
  have hra : ∀ (u : X.Ub) (G : Fin m → Ga × Gp → Fin d → ℂ) (i : Fin m),
      X.raF d τ u G i = ∑ j, (τ u).val i j • fun g => G j (g * ((u : Ga), 1)) := fun u G i => by
    funext g t
    rw [Finset.sum_apply, Finset.sum_apply]
    rfl
  choose k1 hk1 using fun u : U₀ => hsurj (((u : X.Ub) : Ga), 1)
  choose k2 hk2 using fun p : I => hsurj (1, (p : Gp))
  let T : U₀ ⊕ I → (Ga × Gp → Fin d → ℂ) → (Ga × Gp → Fin d → ℂ) :=
    Sum.elim (fun u G g => G (g * (((u : X.Ub) : Ga), 1))) (fun p G g => G (g * (1, (p : Gp))))
  let kk : U₀ ⊕ I → UA E n := Sum.elim (fun u => (k1 u : UA E n)) (fun p => (k2 p : UA E n))
  let a : U₀ ⊕ I → Fin m → Fin m → ℂ := Sum.elim (fun u => (τ u.1).val) (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
  have hone : ∀ (p : I) (G : Fin m → Ga × Gp → Fin d → ℂ) (i : Fin m),
      ∑ j, a (.inr p) i j • T (.inr p) (G j) = T (.inr p) (G i) := fun p G i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by
      change (1 : Matrix (Fin m) (Fin m) ℂ) i j • _ = 0
      rw [Matrix.one_apply_ne hj.symm, zero_smul]) (fun h => (h (Finset.mem_univ _)).elim)]
    change (1 : Matrix (Fin m) (Fin m) ℂ) i i • _ = _
    rw [Matrix.one_apply_eq, one_smul]
  have hfixG : ∀ G : Fin m → Ga × Gp → Fin d → ℂ, (∀ u i, ∑ j, a u i j • T u (G j) = G i) →
      ∀ k : finU E n, ((∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I) → ∀ i g, G i (g * J k) = G i g := by
    rintro G hG k ⟨⟨u, hu, huk, h1⟩, hk⟩ i g
    have h2 : ∑ j, (τ u).val i j • (fun g => G j (g * ((u : Ga), 1))) = G i := hG (.inl ⟨u, hu⟩) i
    rw [h1] at h2
    have h3 : ∀ g, G i (g * ((u : Ga), 1)) = G i g := fun g => by
      have h4 := congrFun h2 g
      rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by
        rw [Units.val_one, Matrix.one_apply_ne hj.symm, zero_smul]; rfl) (fun h => (h (Finset.mem_univ _)).elim),
        Units.val_one, Matrix.one_apply_eq, one_smul] at h4
      exact h4
    have h5 : ∀ g, G i (g * (1, (J k).2)) = G i g := fun g => by
      have h6 := (hone ⟨_, hk⟩ G i).symm.trans (hG (.inr ⟨_, hk⟩) i)
      exact congrFun h6 g
    have h6 : J k = ((u : Ga), 1) * (1, (J k).2) := Prod.ext (huk.symm.trans (mul_one _).symm) (one_mul _).symm
    rw [h6, ← mul_assoc, h5, h3]
  have hFA : ∀ i, F i ∈ X.AF ξ := fun i => hF.1 i trivial
  have hinvF : ∀ u i, ∑ j, a u i j • T u (F j) = F i := by
    rintro (u | p) i
    · exact (hra u.1 F i).symm.trans (congrFun (hF.2 u.1 u.2) i)
    · exact (hone p F i).trans (congrFun (hb p.1 p.2) i)
  obtain ⟨G, hGA, hGi, hGσ, hsum⟩ := absMain (X.AF ξ) tf r hinj hsur T kk a
    (by
      rintro (u | p) G hG γ g
      · have := hG γ (g * (((u : X.Ub) : Ga), 1))
        rw [← mul_assoc] at this
        exact this
      · have := hG γ (g * (1, (p : Gp)))
        rw [← mul_assoc] at this
        exact this)
    (by
      rintro (u | p) G ℓ
      · have h1 := htr G ℓ (k1 u)
        rw [hRfin _ (k1 u).2, show J (k1 u) = _ from hk1 u] at h1
        exact h1.symm
      · have h1 := htr G ℓ (k2 p)
        rw [hRfin _ (k2 p).2, show J (k2 p) = _ from hk2 p] at h1
        exact h1.symm)
    (GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF E n) Kf) Pw
    (fun G hGA hG i ℓ => haut (G i) (hGA i) (by
      let S : Subgroup (finU E n) :=
        { carrier := {k | ∀ g, G i (g * J k) = G i g}
          one_mem' := fun g => by rw [OneMemClass.coe_one, map_one, mul_one]
          mul_mem' := fun {x y} hx hy g => by rw [Subgroup.coe_mul, map_mul, ← mul_assoc, hy, hx]
          inv_mem' := fun {x} hx g => by rw [← hx, Subgroup.coe_inv, map_inv, inv_mul_cancel_right] }
      refine S.isOpen_of_mem_nhds (g := 1) ?_
      filter_upwards [hev] with k hk g
      exact hfixG G hG k hk i g) ℓ)
    (fun G _ ℓ x hx => by
      have h1 := htr G ℓ x
      simp only [hJinf x hx, mul_one] at h1
      exact h1)
    (fun G _ hG i ℓ k => by
      have h1 := htr (G i) ℓ (k.1 : UA E n)
      rw [hRfin _ k.1.2] at h1
      have h2 : (fun g => G i (g * J (k.1 : UA E n))) = G i := funext (hfixG G hG k.1 (hKf k.1 k.2) i)
      rw [h2] at h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact h1)
    (fun σ' hσ' G hGA hG h0 hm => hwt σ' hσ' fun hbot => h0 <| by
      have hmem : G ∈ (Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
          Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ'} :=
        ⟨⟨fun i _ => hGA i, fun u hu => funext fun i => (hra u G i).trans (hG (.inl ⟨u, hu⟩) i)⟩,
          Submodule.subset_span hm⟩
      rw [hbot] at hmem
      exact (Submodule.mem_bot _).1 hmem)
    σ hσ hind hcov F hFA hinvF
  rw [← hsum]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨⟨⟨fun i _ => hGA j i, fun u hu =>
    funext fun i => (hra u (G j) i).trans (hGi j (.inl ⟨u, hu⟩) i)⟩, Submodule.subset_span (hGσ j)⟩,
    fun p hp => funext fun i => ?_⟩
  exact (hone ⟨p, hp⟩ (G j) i).symm.trans (hGi j (.inr ⟨p, hp⟩) i)

end UpperTheory.V.Z.J.D.Dc
