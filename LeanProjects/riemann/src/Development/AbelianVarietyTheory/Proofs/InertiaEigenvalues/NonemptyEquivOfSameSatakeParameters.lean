import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL.SphUniq

section Abstract

variable {G X V V' : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']

theorem map_eq_top {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hπ : π.IsIrreducible)
    (f : ρ.IntertwiningMap π) (U : Submodule ℂ X) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) {u : X} (hu : u ∈ U)
    (h0 : f u ≠ 0) (v : V) : ∃ x ∈ U, f x = v := by
  let R : Subrepresentation π := ⟨U.map f.toLinearMap, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, hU g x hx, f.isIntertwining _ _ g x⟩⟩
  rcases eq_bot_or_eq_top R with h | h
  · have h1 : f u ∈ R.toSubmodule := ⟨u, hu, rfl⟩
    rw [h] at h1
    exact absurd h1 h0
  · have h1 : v ∈ R.toSubmodule := by rw [h]; trivial
    exact h1

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem ker_le {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap π) (f' : ρ.IntertwiningMap π') {w : X} (hw : w ∈ fixed ρ K) (h0 : f w ≠ 0)
    (h0' : f' w ≠ 0) (hl : ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • w) :
    LinearMap.ker f.toLinearMap ≤ LinearMap.ker f'.toLinearMap := by
  intro u hu
  by_contra hu'
  obtain ⟨x, hx, e⟩ := map_eq_top hπ' f' (LinearMap.ker f.toLinearMap) (fun g y hy => by
    have hy' : f y = 0 := hy
    show f (ρ g y) = 0
    rw [f.isIntertwining, hy', map_zero]) hu hu' (f' w)
  have hx' : f x = 0 := hx
  obtain ⟨v, hv, ev⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK (f.toLinearMap.prod f'.toLinearMap) x fun g hg => by
    have h1 : ρ g w = w := by simpa using hw ⟨g, hg⟩
    refine Prod.ext ?_ ?_
    · show f (ρ g x) = f x
      rw [f.isIntertwining, hx', map_zero]
    · show f' (ρ g x) = f' x
      rw [f'.isIntertwining, e, ← f'.isIntertwining, h1]
  obtain ⟨c, rfl⟩ := hl v hv
  have e1 : f (c • w) = f x := congrArg Prod.fst ev
  have e2 : f' (c • w) = f' x := congrArg Prod.snd ev
  rw [hx', map_smul, smul_eq_zero] at e1
  rw [e1.resolve_right h0, zero_smul, map_zero, e] at e2
  exact h0' e2.symm

theorem equiv_of_line {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap π) (f' : ρ.IntertwiningMap π') {w : X} (hw : w ∈ fixed ρ K) (h0 : f w ≠ 0)
    (h0' : f' w ≠ 0) (hl : ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • w) : Nonempty (π.Equiv π') := by
  have hk := le_antisymm (ker_le hρ hπ' hK f f' hw h0 h0' hl) (ker_le hρ hπ hK f' f hw h0' h0 hl)
  have hs : Function.Surjective f.toLinearMap := fun v => by
    obtain ⟨x, -, e⟩ := map_eq_top hπ f ⊤ (fun _ _ _ => trivial) trivial h0 v
    exact ⟨x, e⟩
  have hs' : Function.Surjective f'.toLinearMap := fun v => by
    obtain ⟨x, -, e⟩ := map_eq_top hπ' f' ⊤ (fun _ _ _ => trivial) trivial h0' v
    exact ⟨x, e⟩
  let L : V ≃ₗ[ℂ] V' := (f.toLinearMap.quotKerEquivOfSurjective hs).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    f'.toLinearMap.quotKerEquivOfSurjective hs'
  have hL : ∀ x, L (f x) = f' x := fun x => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hs).symm (f x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [L, LinearEquiv.trans_apply, this]
    rfl
  refine ⟨Representation.Equiv.mk L fun g => LinearMap.ext fun v => ?_⟩
  obtain ⟨x, rfl⟩ := hs v
  show L (π g (f x)) = π' g (L (f x))
  rw [← f.isIntertwining, hL, hL, f'.isIntertwining]

theorem exists_vector {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) (hs : fixed π K ≠ ⊥) :
    ∃ w : S.toSubmodule, w.1 ∈ fixed ρ K ∧ f w ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS hK f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  exact ⟨w, fun g => congrArg Subtype.val (hw g), fun h => hv0 (hfw.symm.trans h)⟩

theorem equiv_of_form {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u ∈ fixed ρ K, E u = 0 → u = 0) (h : IsSubquotient π ρ) (h' : IsSubquotient π' ρ)
    (hs : fixed π K ≠ ⊥) (hs' : fixed π' K ≠ ⊥) : Nonempty (π.Equiv π') := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨S', f', hf'⟩ := h'
  obtain ⟨w, hw, h0⟩ := exists_vector hρ hK S f hf hs
  obtain ⟨w', hw', h0'⟩ := exists_vector hρ hK S' f' hf' hs'
  have hl : ∀ z ∈ fixed ρ K, z ≠ 0 → ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • z := fun z hz hz0 v hv => by
    have hEz : E z ≠ 0 := fun e => hz0 (hE z hz e)
    refine ⟨E v / E z, sub_eq_zero.1 (hE _ (sub_mem hv (Submodule.smul_mem _ _ hz)) ?_)⟩
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hEz, sub_self]
  have hw0 : w.1 ≠ 0 := fun e => h0 (by rw [show w = 0 from Subtype.ext e, map_zero])
  have hw0' : w'.1 ≠ 0 := fun e => h0' (by rw [show w' = 0 from Subtype.ext e, map_zero])
  obtain ⟨c, hc⟩ := hl _ hw' hw0' _ hw
  have hc0 : c ≠ 0 := fun e => hw0 (by rw [hc, e, zero_smul])
  let R : Subrepresentation ρ := ⟨S.toSubmodule ⊓ S'.toSubmodule, fun g _ hv =>
    ⟨S.apply_mem_toSubmodule g hv.1, S'.apply_mem_toSubmodule g hv.2⟩⟩
  have hR : IsSmooth R.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨R, .id _, Function.surjective_id⟩ hρ
  let F : R.toRepresentation.IntertwiningMap π :=
    ⟨f.toLinearMap ∘ₗ Submodule.inclusion inf_le_left, fun g => LinearMap.ext fun x =>
      f.isIntertwining _ _ g (Submodule.inclusion inf_le_left x)⟩
  let F' : R.toRepresentation.IntertwiningMap π' :=
    ⟨f'.toLinearMap ∘ₗ Submodule.inclusion inf_le_right, fun g => LinearMap.ext fun x =>
      f'.isIntertwining _ _ g (Submodule.inclusion inf_le_right x)⟩
  have hm : w.1 ∈ S'.toSubmodule := hc ▸ Submodule.smul_mem _ _ w'.2
  refine equiv_of_line hR hπ hπ' hK F F' (w := ⟨w.1, w.2, hm⟩) (fun g => Subtype.ext (hw g)) h0 (fun e => ?_)
    fun v hv => ?_
  · have e1 : f' (c • w') = 0 := by
      rw [← e]
      exact congrArg f' (Subtype.ext hc.symm)
    rw [map_smul, smul_eq_zero] at e1
    exact e1.elim hc0 h0'
  · obtain ⟨d, hd⟩ := hl _ hw hw0 v.1 fun g => congrArg Subtype.val (hv g)
    exact ⟨d, Subtype.ext hd⟩

end Abstract

theorem equiv_of_parInd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (σ : Representation ℂ (Levi k m) ℂ)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (GL n k) V} {π' : Representation ℂ (GL n k) V'}
    (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) (h : IsSubquotient π (parInd e σ))
    (h' : IsSubquotient π' (parInd e σ)) (hs : IsSpherical π) (hs' : IsSpherical π') : Nonempty (π.Equiv π') := by
  let E : IndSp e σ →ₗ[ℂ] ℂ := ⟨⟨fun f => f.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  refine equiv_of_form (isSmooth_parInd e σ) hπ hπ' SplitFlip.isCompact_KO E (fun u hu h0 => ?_) h h' hs hs'
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  have h1 := congrArg (fun F : IndSp e σ => F.1.1 1) (hu ⟨c, hc⟩)
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul, one_mul] at h1
  have h2 : u.1.1 1 = 0 := h0
  rw [parInd_law, h1, h2, map_zero, smul_zero]
  rfl

theorem equiv_of_hasSatake : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (α : Fin n → ℂˣ) (π π' : IrrRep (GL (Fin n) k)), HasSatake π.ρ α → HasSatake π'.ρ α → Nonempty (π.ρ.Equiv π'.ρ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ h h' => equiv_of_parInd _ _ h.1 h'.1 h.2.2 h'.2.2 h.2.1 h'.2.1

end GlobalTheory.SmGL.SphUniq

end
