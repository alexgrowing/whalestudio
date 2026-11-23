import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.ProdLength

section General
variable {F G U V X : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V]
  [Module F V] [AddCommGroup X] [Module F X]

def comapSub {α : Representation F G U} {β : Representation F G V} (ι : α.IntertwiningMap β)
    (S : Subrepresentation β) : Subrepresentation α :=
  ⟨S.toSubmodule.comap ι.toLinearMap, fun g v hv => by
    show ι (α g v) ∈ S.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩

def mapSub {β : Representation F G V} {γ : Representation F G X} (p : β.IntertwiningMap γ)
    (S : Subrepresentation β) : Subrepresentation γ :=
  ⟨S.toSubmodule.map p.toLinearMap, by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨β g v, S.apply_mem_toSubmodule g hv, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ p g v⟩

theorem hasFiniteLength_of_exact {α : Representation F G U} {β : Representation F G V}
    {γ : Representation F G X} (ι : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) (hα : HasFiniteLength α) (hγ : HasFiniteLength γ) :
    HasFiniteLength β := by
  obtain ⟨hα1, hα2⟩ := (hasFiniteLength_iff_wellFounded α).1 hα
  obtain ⟨hγ1, hγ2⟩ := (hasFiniteLength_iff_wellFounded γ).1 hγ
  let f : Subrepresentation β → Subrepresentation α × Subrepresentation γ :=
    fun S => (comapSub ι S, mapSub p S)
  have hmono : Monotone f := fun S T h =>
    ⟨fun v hv => h hv, Submodule.map_mono (f := p.toLinearMap) h⟩
  have hf : StrictMono f := by
    intro S T hST
    refine lt_of_le_of_ne (hmono hST.le) fun heq => hST.not_ge ?_
    have h1 : (comapSub ι S).toSubmodule = (comapSub ι T).toSubmodule := congrArg (fun x => x.1.toSubmodule) heq
    have h2 : (mapSub p S).toSubmodule = (mapSub p T).toSubmodule := congrArg (fun x => x.2.toSubmodule) heq
    intro x hx
    have hpx : p x ∈ (mapSub p T).toSubmodule := ⟨x, hx, rfl⟩
    rw [← h2] at hpx
    obtain ⟨y, hy, hyx⟩ := hpx
    have hyx' : p y = p x := hyx
    obtain ⟨u, hu⟩ := hex (x - y) (by rw [map_sub, hyx', sub_self])
    have huT : u ∈ (comapSub ι T).toSubmodule := by
      show ι u ∈ T.toSubmodule
      rw [hu]
      exact T.toSubmodule.sub_mem hx (hST.le hy)
    rw [← h1] at huT
    have huS : ι u ∈ S.toSubmodule := huT
    rw [hu] at huS
    have := S.toSubmodule.add_mem huS hy
    rwa [sub_add_cancel] at this
  exact (hasFiniteLength_iff_wellFounded β).2 ⟨hf.wellFoundedGT, hf.wellFoundedLT⟩

theorem hasFiniteLength_of_injective {α : Representation F G U} {β : Representation F G V}
    (ι : α.IntertwiningMap β) (hι : Function.Injective ι) (hβ : HasFiniteLength β) :
    HasFiniteLength α := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded β).1 hβ
  have hmono : Monotone (mapSub ι) := fun S T h => Submodule.map_mono (f := ι.toLinearMap) h
  have hf : StrictMono (mapSub ι) := by
    intro S T hST
    refine lt_of_le_of_ne (hmono hST.le) fun heq => hST.not_ge ?_
    have h3 : (mapSub ι S).toSubmodule = (mapSub ι T).toSubmodule := congrArg (·.toSubmodule) heq
    intro x hx
    have hx' : ι x ∈ (mapSub ι T).toSubmodule := ⟨x, hx, rfl⟩
    rw [← h3] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← hι hyx]
  exact (hasFiniteLength_iff_wellFounded α).2 ⟨hf.wellFoundedGT, hf.wellFoundedLT⟩

theorem hasFiniteLength_of_subsingleton [Subsingleton V] (β : Representation F G V) :
    HasFiniteLength β := by
  haveI : Subsingleton (Subrepresentation β) := ⟨fun S T => by
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => T.toSubmodule.zero_mem, fun _ => S.toSubmodule.zero_mem⟩⟩
  exact (hasFiniteLength_iff_wellFounded β).2 ⟨Finite.to_wellFoundedGT, Finite.to_wellFoundedLT⟩

end General

section Tensor
open GlobalTheory.ParIndExact
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasFiniteLength_extTensor_left (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hA : HasFiniteLength A)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y), σ.IsIrreducible →
      IsSubquotient σ A → HasFiniteLength (extTensor σ B)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded A).1 hA
  have key : ∀ S T : Subrepresentation A, T ≤ S → HasFiniteLength (extTensor (subQuot S T) B) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_left (F := ℂ)
        (V := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule) (W := W)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := A) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_left B ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot A
  obtain ⟨ι', hι'⟩ := extTensor_injective_left B ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

theorem hasFiniteLength_extTensor_right (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hB : HasFiniteLength B)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H Y), τ.IsIrreducible →
      IsSubquotient τ B → HasFiniteLength (extTensor A τ)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded B).1 hB
  have key : ∀ S T : Subrepresentation B, T ≤ S → HasFiniteLength (extTensor A (subQuot S T)) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_right (F := ℂ) (V := V)
        (W := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := B) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_right A ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot B
  obtain ⟨ι', hι'⟩ := extTensor_injective_right A ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

end Tensor
end GlobalTheory.ProdLength

theorem GlobalTheory.ProdLength.prod₂_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ → HasFiniteLength (prod₂ π₁ π₂) := by
  intro hBZ k _ _ _ _ r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂
  obtain ⟨hAdm, -, hInd, -⟩ := hBZ k
  have schur : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ (GL (Fin n) k) Y),
      IsSmooth σ → σ.IsIrreducible → ∀ φ : Y →ₗ[ℂ] Y, (∀ g x, φ (σ g x) = σ g (φ x)) →
        ∃ c : ℂ, φ = c • LinearMap.id := fun n Y _ _ σ hs hi =>
    GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO Y σ hi
      (hAdm (Fin n) Y σ hs hi)
  have hT : HasFiniteLength (extTensor π₁ π₂) :=
    GlobalTheory.ProdLength.hasFiniteLength_extTensor_left π₁ π₂ h₁ fun Y _ _ σ hσ hsq =>
      GlobalTheory.ProdLength.hasFiniteLength_extTensor_right σ π₂ h₂ fun Z _ _ τ hτ hsq' =>
        hasFiniteLength_of_isIrreducible (GlobalTheory.JacFactor.isIrreducible_extTensor σ τ hσ hτ
          (schur r Y σ (hsq.isSmooth s₁) hσ) (schur t Z τ (hsq'.isSmooth s₂) hτ))
  have hc : Continuous (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom :=
    (continuous_apply false).prodMk (continuous_apply true)
  exact hInd Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    (isSmooth_comp (isSmooth_extTensor s₁ s₂) _ hc)
    ((hasFiniteLength_comp_iff _ _ (leviTwo k (Fin r) (Fin t)).symm.surjective).2 hT)
