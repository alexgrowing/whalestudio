import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

private theorem UpperTheory.exists_basis_subfamily_local {R M ι : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] {r : ℕ} (c : Module.Basis (Fin r) R M) (v : ι → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    ∃ t : Fin r → ι, Function.Injective t ∧
      Function.Bijective (Fintype.linearCombination R fun k => v (t k)) := by
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis c
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat (R := R) v hv
  let ε := c.indexEquiv b
  refine ⟨fun k => a (ε k), fun i j h => ?_, ?_⟩
  · apply ε.injective
    apply b.injective
    rw [hb, hb]
    exact congrArg v h
  · rw [Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
      ← LinearMap.range_eq_top, Fintype.range_linearCombination]
    have e : (fun k => v (a (ε k))) = b.reindex ε.symm := by
      funext k
      simp [hb]
    rw [e]
    exact ⟨(b.reindex ε.symm).linearIndependent, (b.reindex ε.symm).span_eq⟩

theorem UpperTheory.quotient_frame_from_permutation :
    ∀ (X : Scheme.{0}) (E Q : X.Modules) (p : E ⟶ Q) (m r : ℕ) (U : X.Opens) (e : Fin m ⊕ Fin r → Γ(E, U)) (x : X),
        Epi p → IsFrame e → IsVB Q r → x ∈ U →
        ∃ (σ : Equiv.Perm (Fin m ⊕ Fin r)) (W : X.Opens) (hW : W ≤ U), x ∈ W ∧
          IsFrame fun k => resM Q hW (p.app U (e (σ (Sum.inr k)))) := by
  intro X E Q p m r U e x hp he hQ hx
  obtain ⟨V, c, -, hxV, hle, hc⟩ := hQ.exists_affine hx
  have hspan : Submodule.span (X.presheaf.stalk x) (Set.range fun i =>
      (Q.presheaf.germ U x hx (p.app U (e i)) : (Q.presheaf.stalk x :))) = ⊤ := by
    have h1 := (he.stalkBasis x hx).span_eq
    have h2 := congrArg (Submodule.map (QCoh.stalkLinear p x)) h1
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.2 (QCoh.stalkLinear_surjective p x), ← Set.range_comp] at h2
    have h3 : (⇑(QCoh.stalkLinear p x) ∘ ⇑(he.stalkBasis x hx)) = fun i =>
        (Q.presheaf.germ U x hx (p.app U (e i)) : (Q.presheaf.stalk x :)) := by
      funext i
      rw [Function.comp_apply, he.stalkBasis_apply, QCoh.stalkLinear_germ]
    rw [h3] at h2
    exact h2
  obtain ⟨t, ht, hb⟩ := UpperTheory.exists_basis_subfamily_local (hc.stalkBasis x hxV) _ hspan
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (f := (Sum.inr : Fin r → Fin m ⊕ Fin r))
    (g := t) Sum.inr_injective ht
  obtain ⟨W, hW, hxW, hv⟩ := Ker.exists_isFrame_of_bijective_stalk hc
    (fun k => resM Q hle (p.app U (e (t k)))) hxV (by
      simp only [Twist.germ_resM]
      exact hb)
  refine ⟨σ, W, hW.trans hle, hxW, ?_⟩
  simp only [Twist.resM_resM] at hv
  simp only [hσ]
  exact hv
