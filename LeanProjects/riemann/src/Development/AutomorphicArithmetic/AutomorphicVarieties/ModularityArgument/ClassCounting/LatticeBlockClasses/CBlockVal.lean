import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrism
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.FirstFace

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

noncomputable section

namespace UpperTheory.V.ZK.Cl.BlockValuationRep

private theorem cyc_cm {A : Type} [CommRing A] {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ}
    {z : Ch A G (m + 1)} (hz : Cyc z) : Cyc (cm A f (m + 1) z) := by
  rw [Cyc, (sChain A).2.1, show bd A G m z = 0 from hz, map_zero]

private def piRep {k : Type} [Field k] {G : Type} [Group G] {B : Type} (U : B → Type) [∀ b, AddCommGroup (U b)]
    [∀ b, Module k (U b)] (ρ : ∀ b, G →* (U b ≃ₗ[k] U b)) : G →* ((∀ b, U b) ≃ₗ[k] ∀ b, U b) where
  toFun g := LinearEquiv.piCongrRight fun b => ρ b g
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

private def blk {k : Type} [Field k] {C : Type} [Group C] {B : Type} (U : B → Type) [∀ b, AddCommGroup (U b)]
    [∀ b, Module k (U b)] (χ : B → C →* kˣ) (b : B) : (C × ∀ b, U b ≃ₗ[k] U b) →* (U b ≃ₗ[k] U b) where
  toFun p := scal (U b) (χ b p.1) * p.2 b
  map_one' := by simp
  map_mul' p p' := by
    ext w
    simp [scal, Units.smul_def, smul_smul, mul_comm]

private theorem pi_add {k : Type} [Field k] {A : Type} [CommRing A] {m : ℕ} {θ : Fam k A (m + 1)} (hθ : IsAdd θ)
    {G : Type} [Group G] {z : Ch A G (m + 1)} (hz : Cyc z) (B : Type) [Fintype B] :
    ∀ (U : B → Type) [∀ b, AddCommGroup (U b)] [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (ρ : G →* (V ≃ₗ[k] V))
      (ρ' : ∀ b, G →* (U b ≃ₗ[k] U b)), (∀ g w b, φ (ρ g w) b = ρ' b g (φ w b)) →
        θ V (cm A ρ (m + 1) z) = ∑ b, θ (U b) (cm A (ρ' b) (m + 1) z) := by
  refine Fintype.induction_empty_option (P := fun B _ => ∀ (U : B → Type) [∀ b, AddCommGroup (U b)]
      [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (ρ : G →* (V ≃ₗ[k] V))
      (ρ' : ∀ b, G →* (U b ≃ₗ[k] U b)), (∀ g w b, φ (ρ g w) b = ρ' b g (φ w b)) →
        θ V (cm A ρ (m + 1) z) = ∑ b, θ (U b) (cm A (ρ' b) (m + 1) z)) ?_ ?_ ?_ B
  · intro α β _ e ih U _ _ _ V _ _ _ φ ρ ρ' h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← e.sum_comp]
    exact ih (fun a => U (e a)) V (φ.trans (LinearEquiv.piCongrLeft k U e).symm) ρ (fun a => ρ' (e a))
      fun g w a => h g w (e a)
  · intro U _ _ _ V _ _ _ φ ρ ρ' h
    haveI : Subsingleton V := φ.toEquiv.subsingleton
    haveI : Subsingleton (V ≃ₗ[k] V) := ⟨fun a b => LinearEquiv.ext fun _ => Subsingleton.elim _ _⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact hθ.bdry V _ ((sChain A).2.2.2.2 _ m _ (cyc_cm ρ hz))
  · intro α _ ih U _ _ _ V _ _ _ φ ρ ρ' h
    let ψ : V ≃ₗ[k] (U none × ∀ a, U (some a)) := φ.trans (LinearEquiv.piOptionEquivProd k)
    have hψ : (cj ψ).comp ρ = sumRep (ρ' none) (piRep (fun a => U (some a)) fun a => ρ' (some a)) := by
      refine MonoidHom.ext fun g => LinearEquiv.ext fun y => ?_
      obtain ⟨w, rfl⟩ := ψ.surjective y
      change ψ (ρ g (ψ.symm (ψ w))) = _
      rw [ψ.symm_apply_apply]
      exact Prod.ext (h g w none) (funext fun a => h g w (some a))
    rw [Fintype.sum_option, ← hθ.iso V _ ψ _ (cyc_cm ρ hz), ← (sChain A).2.2.1, hψ, hθ.add _ _ _ _ _ _ hz,
      ih (fun a => U (some a)) _ (LinearEquiv.refl k _) _ (fun a => ρ' (some a)) fun _ _ _ => rfl]

end UpperTheory.V.ZK.Cl.BlockValuationRep

open UpperTheory.V.ZK.Cl.BlockValuationRep in
theorem UpperTheory.V.ZK.Cl.cBlockVal :
    UpperTheory.V.ZK.Cl.CBlockVal := by
  unfold UpperTheory.V.ZK.Cl.CBlockVal
  intro k _ q _ e ζ hζ v θ hθ hv B _ U _ _ _ V _ _ _ φ σ g x g' hσ hg
  obtain ⟨-, -, h2, h3, -⟩ := sChain (ZMod q)
  let χ : B → Cq q →* kˣ := fun b => chi q ζ hζ (x b)
  let R : (Cq q × ∀ b, U b ≃ₗ[k] U b) →* (V ≃ₗ[k] V) := (cj φ.symm).comp (piRep U (blk U χ))
  have hR : ∀ p w b, φ (R p w) b = blk U χ b p (φ w b) := by
    intro p w b
    simp [R, cj, piRep]
  have hRg : R (1, g') = g := by
    refine LinearEquiv.ext fun w => φ.injective (funext fun b => ?_)
    rw [hR, hg]
    simp [blk]
  have hRσ : R.comp (MonoidHom.inl _ _) = σ := by
    refine MonoidHom.ext fun c => LinearEquiv.ext fun w => φ.injective (funext fun b => ?_)
    rw [hσ, MonoidHom.comp_apply, MonoidHom.inl_apply, hR]
    simp [blk, scal, Units.smul_def, χ]
  have hblk : ∀ b, (blk U χ b).comp (MonoidHom.inl _ _) = (scal (U b)).comp (χ b) := by
    intro b
    refine MonoidHom.ext fun c => ?_
    simp [blk]
  have hk0 : ∀ b, blk U χ b (1, g') = g' b := by
    intro b
    simp [blk]
  have hy : Cyc (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e)) :=
    cyc_cm _ (sZc q e)
  have hconj : (MulAut.conj ((1 : Cq q), g')⁻¹).toMonoidHom.comp (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) =
      MonoidHom.inl _ _ := by
    refine MonoidHom.ext fun c => ?_
    simp
  have hZ : Cyc (prism (ZMod q) ((1 : Cq q), g') (2 * e + 1 + 1)
      (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e))) := by
    show bd _ _ (2 * e + 1 + 1) _ = 0
    have s := sPrism (ZMod q) _ ((1 : Cq q), g') (2 * e + 1) (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e))
    have hy' : bd (ZMod q) _ (2 * e + 1) (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e)) = 0 := hy
    rw [hy', map_zero, add_zero, ← h2, hconj, sub_self] at s
    exact s
  show θ V (prism (ZMod q) g (2 * e + 1 + 1) (cm (ZMod q) σ (2 * e + 1 + 1) (zc q e))) = _
  rw [← hRg, ← hRσ, h2, ← h3]
  refine (pi_add hθ hZ B U V φ R (blk U χ) hR).trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [h3, ← h2, hblk b, hk0 b]
  exact hv (U b) (x b) (g' b)

end
