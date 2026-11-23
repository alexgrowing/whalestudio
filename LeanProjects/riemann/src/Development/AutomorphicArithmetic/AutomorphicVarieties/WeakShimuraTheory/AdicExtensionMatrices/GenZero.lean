import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.EqMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxZMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxExtGr0

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxGenZero :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} [IsCO Λ (W.gr 0)], Φ.Ok ((residue Λ).comp a) → Φ.Near a 0 D → D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ cp : Γ → (W.gr 0)[X], (∀ g, (cp g).map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly) → ∀ ψ : ∀ v, Fin 4 → Φ.Gv v → W.gr 0, (∀ v i s, algebraMap (W.gr 0) W.A (ψ v i s) = D'.ψ v i s) → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.gr 0 →ₐ[Λ] R'), (∀ g n, f ((cp g).coeff n) = f' ((cp g).coeff n)) → (∀ v i s, f (ψ v i s) = f' (ψ v i s)) → f = f' := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W _ hok hnear hgr D' hD cp hcp ψ hψ R' _ _ _ f f' h1 h2
  let φ : W.gr 0 →ₐ[Λ] R := W.A.val.comp { algebraMap (W.gr 0) W.A with commutes' := fun _ => rfl }
  let E : Subalgebra Λ R := (AlgHom.equalizer f f').map φ
  have hE : ∀ x : R, x ∈ E ↔ ∃ b : W.gr 0, ((b : W.A) : R) = x ∧ f b = f' b := fun x =>
    ⟨fun ⟨b, hb, e⟩ => ⟨b, e, hb⟩, fun ⟨b, e, hb⟩ => ⟨b, hb, e⟩⟩
  refine sxExtGr0 W hgr.max R' f f' fun b n hn hb => ?_
  have hz := sxZMono E hgr (fun x hx => (hE x).2 (sxEqMono hok hnear hgr D' hD cp hcp R' f f' h1 x hx))
    (fun v i s => (hE _).2 ⟨ψ v i s, ?_, h2 v i s⟩) n hn
  · obtain ⟨b', e, hb'⟩ := (hE _).1 hz
    have : b' = b := Subtype.ext (Subtype.ext (e.trans hb.symm))
    exact this ▸ hb'
  · have e : ((ψ v i s : W.gr 0) : W.A) = D'.ψ v i s := hψ v i s
    rw [e, ← hD]
    rfl
