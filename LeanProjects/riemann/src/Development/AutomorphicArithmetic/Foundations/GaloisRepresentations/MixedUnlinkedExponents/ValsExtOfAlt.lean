import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem map_eq_of_injOn {α β : Type*} (S : Set α) (g : α → β) (hg : Set.InjOn g S)
    (A B : Multiset α) (hA : ∀ x ∈ A, x ∈ S) (hB : ∀ x ∈ B, x ∈ S)
    (h : A.map g = B.map g) : A = B := by
  have key : ∀ C : Multiset α, (∀ x ∈ C, x ∈ S) → ∀ ξ ∈ S, C.count ξ = (C.map g).count (g ξ) := by
    intro C hC ξ hξ
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    apply Multiset.filter_congr
    intro x hx
    exact ⟨fun e => congrArg g e, fun e => hg hξ (hC x hx) e⟩
  ext ξ
  by_cases hξ : ξ ∈ S
  · rw [key A hA ξ hξ, key B hB ξ hξ, h]
  · rw [Multiset.count_eq_zero_of_notMem (fun m => hξ (hA _ m)),
      Multiset.count_eq_zero_of_notMem (fun m => hξ (hB _ m))]

theorem UpperTheory.Gal.GamX.valsExtOf :
    UpperTheory.Gal.GamX.ValsExtOf := by
  unfold ValsExtOf ValsExt
  intro hP k _ _ _ _ c c' θ h
  have hinj : Set.InjOn (fun ξ : kˣ →* ℂˣ => (ξ * θ) (unif k)) {ξ | IsUnram (ξ * θ)} := by
    intro ξ hξ ξ' hξ' e
    have hu : IsUnram ((ξ * θ) * (ξ' * θ)⁻¹) := isUnram_mul hξ (isUnram_inv hξ')
    exact mul_right_cancel ((hP k).2.1 _ _ hu e)
  exact map_eq_of_injOn _ _ hinj _ _ (fun x hx => (Multiset.mem_filter.1 hx).2)
    (fun x hx => (Multiset.mem_filter.1 hx).2) h
