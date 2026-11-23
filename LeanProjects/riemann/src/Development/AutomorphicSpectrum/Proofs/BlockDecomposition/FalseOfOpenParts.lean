import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingTwistedModulusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMirabolicInvariantPairingScalarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionsEmbedCuspidalDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateUnipotentPairingSchwartzStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingIteratedDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingSegmentProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalContragredientCentralCharacterStatement

noncomputable section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.BZShell

theorem false_of_open_parts {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) (R R' : MRep k d) (hR' : IsSmooth R'.ρ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Nontrivial V]
    (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V') (hX : IsSmooth X) (hY : IsSmooth Y)
    (P : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hP : ∀ g a a', P (X g a) (Y g a') = ((dpow d (-2) g : ℂˣ) : ℂ) * P a a')
    (e : Fin d → k) (he : e ≠ 0)
    (hU : ∀ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin d) k, (g : Matrix (Fin d) (Fin d) k).mulVec e = e → ∀ a a', β (X g a) (Y g a') =
        ((dpow d (-2) g : ℂˣ) : ℂ) * β a a') → ∃ c : ℂ, ∀ a a', β a a' = c * P a a')
    (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (ω ω' : ℂ) (hω : ∀ a, X z a = ω • a) (hω' : ∀ a, Y z a = ω' • a)
    (hωω : ω * ω' = ((dpow d (-2) z : ℂˣ) : ℂ))
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ p v v', B (R.ρ p v) (R'.ρ p v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k d V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM d x) (ι f))
    (hιg : ∀ g f, ι (actF X g f) = R.ρ (levi k d g) (ι f))
    (ι' : SchF k d V' →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM d x) (ι' f))
    (hιg' : ∀ g f, ι' (actF Y g f) = R'.ρ (levi k d g) (ι' f))
    (hr : ∀ x v, R'.ρ (uM d x) v - v ∈ LinearMap.range ι') : False := by
  let c : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ := B.compl₁₂ ι ι'
  have hcv : ∀ f f', c f f' = B (ι f) (ι' f') := fun _ _ => rfl
  have hT : ∀ x f f', c (shiftF x f) (shiftF x f') = c f f' := by
    intro x f f'
    rw [hcv, hcv, hιs, hιs']
    exact hB _ _ _
  have hG : ∀ g f f', c (actF X g f) (actF Y g f') = c f f' := by
    intro g f f'
    rw [hcv, hcv, hιg, hιg']
    exact hB _ _ _
  have hC := GlobalTheory.T.invariant_pairing_twisted_modulus d hd X Y hX hY P hP e he hU z ϖ hz hϖ hϖ0 ω ω' hω hω' hωω c hT hG
  exact GlobalTheory.T.nondegenerate_unipotent_pairing_schwartz d hd R R' hR' B (fun x v v' => hB _ v v') hn ι hι hιs ι' hιs' hr hC

theorem false_of_open_dual {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ) (R R' : MRep k (m + 1)) (hR' : IsSmooth R'.ρ)
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ p v v', B (R.ρ p v) (R'.ρ p v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k (m + 1) σ.V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM (m + 1) x) (ι f))
    (hιg : ∀ g f, ι (actF ((gOf σ).tw (-1 / 2)).ρ g f) = R.ρ (levi k (m + 1) g) (ι f))
    (ι' : SchF k (m + 1) (smoothPart σ.ρ.dual) →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM (m + 1) x) (ι' f))
    (hιg' : ∀ g f, ι' (actF (((gDual σ).tw (-1)).tw (-1 / 2)).ρ g f) = R'.ρ (levi k (m + 1) g) (ι' f))
    (hr : ∀ x v, R'.ρ (uM (m + 1) x) v - v ∈ LinearMap.range ι') : False := by
  obtain ⟨hci, hcc, z, ϖ, ω, hz, hϖ, hϖ0, hω0, hzσ, hzc⟩ := GlobalTheory.T.cuspidal_contragredient_central_character m σ hc
  have hsm : ∀ s : ℝ, IsSmoothChar (absPow k (s : ℂ)) := fun s => GlobalTheory.LocGL.isSmoothChar_absPow _
  have hsB' : IsSmooth ((gDual σ).tw (-1)).ρ := isSmooth_twist (isSmooth_contra _) (hsm (-1)).detChar
  let X : Representation ℂ (GL (Fin (m + 1)) k) σ.V := twist σ.ρ (dpow (m + 1) (-1 / 2))
  let Y : Representation ℂ (GL (Fin (m + 1)) k) (smoothPart σ.ρ.dual) := twist (twist (contra σ.ρ) (dpow (m + 1) (-1))) (dpow (m + 1) (-1 / 2))
  let P : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ := LinearMap.flip (smoothPart σ.ρ.dual).subtype
  have hadd : ∀ (s t : ℝ) (g : GL (Fin (m + 1)) k), ((dpow (m + 1) (s + t) g : ℂˣ) : ℂ) =
      ((dpow (m + 1) s g : ℂˣ) : ℂ) * ((dpow (m + 1) t g : ℂˣ) : ℂ) := by
    intro s t g
    simp only [dpow, detChar_apply, Complex.ofReal_add, absPow_add, MonoidHom.mul_apply, Units.val_mul]
  have hne : ∀ (s : ℝ) (g : GL (Fin (m + 1)) k), ((dpow (m + 1) s g : ℂˣ) : ℂ) ≠ 0 := fun s g => Units.ne_zero _
  have hXa : ∀ g a, X g a = ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) • σ.ρ g a := fun g a => rfl
  have hYa : ∀ g l, Y g l = ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) • ((dpow (m + 1) (-1) g : ℂˣ) : ℂ) • contra σ.ρ g l := fun g l => rfl
  have hsc : ∀ g : GL (Fin (m + 1)) k, ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * (((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * ((dpow (m + 1) (-1) g : ℂˣ) : ℂ)) =
      ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) := by
    intro g
    rw [← hadd, ← hadd]
    congr 3
    norm_num
  have hPinv : ∀ g a l, P (σ.ρ g a) (contra σ.ρ g l) = P a l := by
    intro g a l
    show (contra σ.ρ g l : Module.Dual ℂ σ.V) (σ.ρ g a) = (l : Module.Dual ℂ σ.V) a
    rw [contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hP : ∀ g a l, P (X g a) (Y g l) = ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) * P a l := by
    intro g a l
    rw [hXa, hYa]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hPinv]
    rw [← hsc g]
    ring
  have hsX : IsSmooth X := isSmooth_twist σ.smooth (hsm _).detChar
  have hsY : IsSmooth Y := isSmooth_twist hsB' (hsm _).detChar
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ≠ 0 := by
    intro h
    simpa using congrFun h (Fin.last m)
  have hU : ∀ β : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin (m + 1)) k, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 →
        ∀ a a', β (X g a) (Y g a') = ((dpow (m + 1) (-2) g : ℂˣ) : ℂ) * β a a') →
      ∃ c : ℂ, ∀ a a', β a a' = c * P a a' := by
    intro β hβ
    refine GlobalTheory.T.cuspidal_mirabolic_invariant_pairing_scalar m σ hc β fun g hg a l => ?_
    have h := hβ g hg a l
    rw [hXa, hYa] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← hsc g] at h
    have h2 : ((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * (((dpow (m + 1) (-1 / 2) g : ℂˣ) : ℂ) * ((dpow (m + 1) (-1) g : ℂˣ) : ℂ)) ≠ 0 :=
      mul_ne_zero (hne _ _) (mul_ne_zero (hne _ _) (hne _ _))
    refine mul_left_cancel₀ h2 ?_
    rw [← h]
    ring
  have hzX : ∀ a, X z a = (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * ω) • a := by
    intro a
    rw [hXa, hzσ, smul_smul]
  have hzY : ∀ l, Y z l = (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * (((dpow (m + 1) (-1) z : ℂˣ) : ℂ) * ω⁻¹)) • l := by
    intro l
    rw [hYa, hzc, smul_smul, smul_smul, mul_assoc]
  have hωω : (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * ω) * (((dpow (m + 1) (-1 / 2) z : ℂˣ) : ℂ) * (((dpow (m + 1) (-1) z : ℂˣ) : ℂ) * ω⁻¹)) =
      ((dpow (m + 1) (-2) z : ℂˣ) : ℂ) := by
    rw [← hsc z]
    field_simp
  haveI : Nontrivial σ.V := by
    have hi := σ.irr
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    apply Subrepresentation.ext
    ext x
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  exact false_of_open_parts (m + 1) (Nat.succ_pos m) R R' hR' X Y hsX hsY P hP _ he hU z ϖ hz hϖ hϖ0 _ _ hzX hzY hωω B hB hn ι hι hιs hιg ι' hιs' hιg' hr

theorem red_cusp_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible := by
  intro k _ _ _ _ d hd σ hc hirr
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨ψ, hψc, hψ1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  have hψc' : Continuous (ψ⁻¹ : AddChar k Circle) := by
    have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
    rw [this]
    exact hψc.comp continuous_neg
  have hψ1' : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ1
  obtain ⟨hci, hcc, -⟩ := GlobalTheory.T.cuspidal_contragredient_central_character m σ hc
  have hsm : ∀ s : ℝ, IsSmoothChar (absPow k (s : ℂ)) := fun s => GlobalTheory.LocGL.isSmoothChar_absPow _
  have hsA : IsSmooth ((gOf σ).tw 1).ρ := isSmooth_twist σ.smooth (hsm 1).detChar
  have hsB : IsSmooth (gOf σ).ρ := σ.smooth
  have hsA' : IsSmooth (gDual σ).ρ := isSmooth_contra _
  have hsB' : IsSmooth ((gDual σ).tw (-1)).ρ := isSmooth_twist (isSmooth_contra _) (hsm (-1)).detChar
  obtain ⟨B₀, hB₀, hn₀⟩ := GlobalTheory.T.invariant_pairing_segment_product m σ hc hirr
  obtain ⟨B, hB, hn⟩ := GlobalTheory.T.invariant_pairing_iterated_derivative ψ hψc hψ1 m _ _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _))
    (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _)) B₀ hB₀ hn₀
  obtain ⟨ι, hι, hιs, hιg, -⟩ := GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative ψ hψc hψ1 m ((gOf σ).tw 1) (gOf σ) hsA hsB
    (GlobalTheory.LocGL.isIrreducible_twist σ.irr _) (GlobalTheory.LocGL.isCuspidal_twist hc (hsm 1))
  obtain ⟨ι', -, hιs', hιg', hr⟩ := GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative ψ⁻¹ hψc' hψ1' m (gDual σ) ((gDual σ).tw (-1)) hsA' hsB' hci hcc
  exact false_of_open_dual m σ hc _ _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_iterN ψ⁻¹ m
    (isSmooth_gres (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_prod _ _))))
    B hB hn ι hι hιs hιg ι' hιs' hιg' hr

end GlobalTheory.CompanionTheory.BZShell
end
