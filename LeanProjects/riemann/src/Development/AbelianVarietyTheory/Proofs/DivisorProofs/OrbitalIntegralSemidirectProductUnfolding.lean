import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCompEqFinsumCardFiberMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldSumInvariantLeviConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetRelIndexInfConjConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUnfoldSemidirectProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCountParabolicUnfoldLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSemidirectRepSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRelIndexNeZeroParabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplexStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Unfold

theorem lhs_eq {P : Type} [Group P] [TopologicalSpace P] (KP : Subgroup P) (δ : P) (F : P → ℂ)
    (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) :
    twOrb (MonoidHom.id P) KP δ F = ∑ᶠ d : DoubleCoset.Quotient (twCent (MonoidHom.id P) δ : Set P) (KP : Set P),
      (((twCent (MonoidHom.id P) δ ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id P) δ)) : ℕ) : ℂ) * F ((Quotient.out d)⁻¹ * δ * Quotient.out d) := by
  unfold twOrb
  refine finsum_congr fun d => ?_
  congr 1
  have h : (fun k : KP => F ((Quotient.out d * k)⁻¹ * δ * (MonoidHom.id P) (Quotient.out d * k))) =
      fun _ => F ((Quotient.out d)⁻¹ * δ * Quotient.out d) := by
    funext k
    rw [MonoidHom.id_apply, ← hF k k.2 ((Quotient.out d)⁻¹ * δ * Quotient.out d)]
    congr 1
    group
  rw [h, GlobalTheory.IwRed.avg_const]

theorem hint_eq {P N : Type} [Group P] [Group N] (u : N →* P) (KP : Subgroup P) (L : Subgroup N)
    (huK : ∀ X, u X ∈ KP ↔ X ∈ L) (F : P → ℂ) (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) (y : P) :
    hint L (fun X => F ((u X)⁻¹ * y * u X)) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  have hL : L ≤ rStab (fun X => F ((u X)⁻¹ * y * u X)) := by
    intro l hl x
    show F ((u (x * l))⁻¹ * y * u (x * l)) = F ((u x)⁻¹ * y * u x)
    rw [← hF (u l) ((huK l).2 hl) ((u x)⁻¹ * y * u x)]
    congr 1
    simp only [map_mul]
    group
  have he : rStab (fun X => F ((u X)⁻¹ * y * u X)) ⊓ L = L := inf_eq_right.2 hL
  unfold hint
  rw [he, Subgroup.relIndex_self]
  simp

end GlobalTheory.Unfold

noncomputable section
namespace GlobalTheory.Unfold

theorem rhs_eq (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace M] (s : M →* P) (π : P →* M)
    (u : N →* P) (hs : ∀ m, π (s m) = m) (hinj : Function.Injective u) (hker : ∀ p, π p = 1 ↔ ∃ X, u X = p)
    (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N) (hsK : ∀ k ∈ KM, s k ∈ KP) (hπK : ∀ k ∈ KP, π k ∈ KM)
    (huK : ∀ X, u X ∈ KP ↔ X ∈ L) (γ : M) (F : P → ℂ) (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) :
    twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) =
      ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id M) γ : Set M) (KM : Set M),
        (((twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
          (cptPart (twCent (MonoidHom.id M) γ)) : ℕ) : ℂ) *
        ∑ᶠ x : N ⧸ L, F ((s (Quotient.out q) * u (Quotient.out x))⁻¹ * s γ * (s (Quotient.out q) * u (Quotient.out x))) := by
  unfold twOrb
  refine finsum_congr fun q => ?_
  congr 1
  have h : (fun k : KM => hint L (fun X => F ((u X)⁻¹ * s ((Quotient.out q * k)⁻¹ * γ *
      (MonoidHom.id M) (Quotient.out q * k)) * u X))) = fun _ =>
      ∑ᶠ x : N ⧸ L, F ((s (Quotient.out q) * u (Quotient.out x))⁻¹ * s γ * (s (Quotient.out q) * u (Quotient.out x))) := by
    funext k
    rw [hint_eq u KP L huK F hF]
    have e : s ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id M) (Quotient.out q * k)) =
        (s k)⁻¹ * s ((Quotient.out q)⁻¹ * γ * Quotient.out q) * s k := by
      simp only [MonoidHom.id_apply, map_mul, map_inv]
      group
    rw [e, GlobalTheory.T.unfold_sum_invariant_levi_conj P M N s π u hs hinj hker KP KM L hsK hπK huK F hF k k.2]
    refine finsum_congr fun x => ?_
    congr 1
    simp only [map_mul, map_inv]
    group
  rw [h, GlobalTheory.IwRed.avg_const]

theorem core : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ G : P → ℂ, (∀ t ∈ TP, ∀ p, G (t * p) = G p) → (∀ k ∈ KP, ∀ p, G (p * k) = G p) →
    (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) →
    {d : DoubleCoset.Quotient (TP : Set P) (KP : Set P) | G (Quotient.out d) ≠ 0}.Finite →
    ∑ᶠ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P),
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex CP : ℕ) : ℂ) * G (Quotient.out d) =
    ∑ᶠ q : DoubleCoset.Quotient (TM : Set M) (KM : Set M),
      (((TM ⊓ KM.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex CM : ℕ) : ℂ) *
        ∑ᶠ x : N ⧸ L, G (s (Quotient.out q) * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC G hGT hGK hU hfin
  have hGout : ∀ p, G (Quotient.out (DoubleCoset.mk TP KP p)) = G p := by
    intro p
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1 (DoubleCoset.out_eq' TP KP (DoubleCoset.mk TP KP p)).symm
    rw [he, hGK k hk, hGT t ht]
  have hTCP : ∀ p : P, TP ⊓ KP.map (MulAut.conj p).toMonoidHom ≤ CP := by
    intro p x hx
    obtain ⟨hxT, hxK⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨t, ht, rfl⟩ := (hTP x).1 hxT
    refine (hCP _).2 ⟨t, hTC (π p) (Subgroup.mem_inf.2 ⟨ht, ?_⟩), rfl⟩
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 hxK
    refine Subgroup.mem_map.2 ⟨π k, hπK k hk, ?_⟩
    have := congrArg π hke
    simpa [MulAut.conj_apply, hs] using this
  let ρ : DoubleCoset.Quotient (TP : Set P) (KP : Set P) → DoubleCoset.Quotient (TM : Set M) (KM : Set M) :=
    fun d => DoubleCoset.mk TM KM (π (Quotient.out d))
  have hρmk : ∀ p, ρ (DoubleCoset.mk TP KP p) = DoubleCoset.mk TM KM (π p) := by
    intro p
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1 (DoubleCoset.out_eq' TP KP (DoubleCoset.mk TP KP p)).symm
    show DoubleCoset.mk TM KM (π (Quotient.out (DoubleCoset.mk TP KP p))) = _
    rw [he, DoubleCoset.eq]
    obtain ⟨t', ht', rfl⟩ := (hTP t).1 ht
    refine ⟨t'⁻¹, TM.inv_mem ht', (π k)⁻¹, KM.inv_mem (hπK k hk), ?_⟩
    simp only [map_mul, hs]
    group
  have hsupp : (Function.support fun d : DoubleCoset.Quotient (TP : Set P) (KP : Set P) =>
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex CP : ℕ) : ℂ) * G (Quotient.out d)).Finite :=
    hfin.subset fun d hd => right_ne_zero_of_mul hd
  rw [GlobalTheory.T.finsum_fiberwise_of_finite_support_complex ρ _ hsupp]
  refine finsum_congr fun q => ?_
  set q0 := Quotient.out q with hq0def
  have hq0 : DoubleCoset.mk TM KM q0 = q := DoubleCoset.out_eq' TM KM q
  have hψ : ∀ x : N ⧸ L, ρ (DoubleCoset.mk TP KP (s q0 * u (Quotient.out x))) = q := fun x => by
    rw [hρmk, map_mul, hs, (hker _).2 ⟨_, rfl⟩, mul_one]
    exact hq0
  let ψ : N ⧸ L → {d // ρ d = q} := fun x => ⟨DoubleCoset.mk TP KP (s q0 * u (Quotient.out x)), hψ x⟩
  have hfib : ∀ d : {d // ρ d = q}, ∃ X : N, DoubleCoset.mk TP KP (s q0 * u X) = d.1 ∧
      Nat.card (ψ ⁻¹' {d}) = (TM.map (MulAut.conj q0⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q0⁻¹).toMonoidHom ⊓ KM) := by
    intro d
    obtain ⟨X, hX⟩ := GlobalTheory.T.doubleCoset_semidirect_rep_surjective P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC d.1
    have e : Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d.1))) = q0 := by
      rw [show DoubleCoset.mk TM KM (π (Quotient.out d.1)) = q from d.2]
    rw [e] at hX
    refine ⟨X, hX, ?_⟩
    rw [← GlobalTheory.T.orbit_count_parabolic_unfold_levi P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC q0 X]
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff, hX]
  have hwt : ∀ d : {d // ρ d = q},
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d.1)).toMonoidHom).relIndex CP : ℕ) : ℂ) =
      (((TM ⊓ KM.map (MulAut.conj q0).toMonoidHom).relIndex CM : ℕ) : ℂ) * (Nat.card (ψ ⁻¹' {d}) : ℂ) := by
    intro d
    obtain ⟨X, hX, hc⟩ := hfib d
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1 (hX.trans (DoubleCoset.out_eq' TP KP d.1).symm)
    rw [he, GlobalTheory.T.doubleCoset_relIndex_inf_conj_const P TP CP KP hTCP t ht k hk,
      GlobalTheory.T.relIndex_unfold_semidirect_product P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC q0 X, hc]
    push_cast
    rfl
  have hR : ∑ᶠ x : N ⧸ L, G (s q0 * u (Quotient.out x)) =
      ∑ᶠ d : {d // ρ d = q}, (Nat.card (ψ ⁻¹' {d}) : ℂ) * G (Quotient.out d.1) := by
    rw [← GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul ψ (fun d => G (Quotient.out d.1)) (Or.inl ?_)]
    · exact finsum_congr fun x => (hGout _).symm
    · intro d _
      obtain ⟨X, -, hc⟩ := hfib d
      have h0 := GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic P M N s π u hs hinj hker KP KM L hsK hπK huK TM hU q0 X
      rw [← hc] at h0
      haveI := Nat.finite_of_card_ne_zero h0
      exact Set.toFinite _
  rw [hR, mul_finsum]
  refine finsum_congr fun d => ?_
  rw [hwt d, mul_assoc]

theorem twOrb_unfold : ∀ (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace P] [TopologicalSpace M] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ γ : M, (∀ p, p ∈ twCent (MonoidHom.id P) (s γ) ↔ ∃ t ∈ twCent (MonoidHom.id M) γ, s t = p) → (∀ p, p ∈ cptPart (twCent (MonoidHom.id P) (s γ)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id M) γ), s t = p) → (∀ q : M, twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id M) γ)) → (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → {d : DoubleCoset.Quotient (twCent (MonoidHom.id P) (s γ) : Set P) (KP : Set P) | F ((Quotient.out d)⁻¹ * s γ * Quotient.out d) ≠ 0}.Finite → twOrb (MonoidHom.id P) KP (s γ) F = twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) := by
  intro P M N _ _ _ _ _ s π u hs hinj hker KP KM L hsK hπK huK γ hTP hCP hTC hU F hF hfin
  rw [lhs_eq KP (s γ) F hF, rhs_eq P M N s π u hs hinj hker KP KM L hsK hπK huK γ F hF]
  refine core P M N s π u hs hinj hker KP KM L hsK hπK huK (twCent (MonoidHom.id M) γ)
    (cptPart (twCent (MonoidHom.id M) γ)) (twCent (MonoidHom.id P) (s γ)) (cptPart (twCent (MonoidHom.id P) (s γ)))
    ((Subgroup.closure_le _).2 fun t ht => ht.1) hTP hCP hTC (fun p => F (p⁻¹ * s γ * p)) ?_ ?_ hU hfin
  · intro t ht p
    have ht' : t * s γ = s γ * t := ht
    show F ((t * p)⁻¹ * s γ * (t * p)) = F (p⁻¹ * s γ * p)
    rw [show (t * p)⁻¹ * s γ * (t * p) = p⁻¹ * (t⁻¹ * (s γ * t)) * p by group, ← ht', inv_mul_cancel_left]
  · intro k hk p
    show F ((p * k)⁻¹ * s γ * (p * k)) = F (p⁻¹ * s γ * p)
    rw [← hF k hk (p⁻¹ * s γ * p)]
    congr 1
    group

end GlobalTheory.Unfold
