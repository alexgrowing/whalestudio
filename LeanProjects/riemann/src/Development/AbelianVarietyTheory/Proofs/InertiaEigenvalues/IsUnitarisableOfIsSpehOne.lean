import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitarisStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh

namespace GlobalTheory.DiscreteSpectrumCM

theorem isUnitarisable_of_injective {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (q : ρ.IntertwiningMap τ)
    (hq : Function.Injective q) (hu : IsUnitarisable τ) : IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := hu
  let B' : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ := (B.compl₂ q.toLinearMap).comp q.toLinearMap
  have hB : ∀ v w, B' v w = B (q v) (q w) := fun _ _ => rfl
  refine ⟨B', fun v w => by rw [hB, hB, h1], fun v hv => by
    rw [hB]; exact h2 _ fun e => hv (hq (e.trans (map_zero q).symm)), fun g v w => ?_⟩
  rw [hB, hB, ← h3 g (q v) (q w)]
  rw [q.isIntertwining _ _ g v, q.isIntertwining _ _ g w]

section Local

open GlobalTheory.PRep GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem injective_of_irreducible {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (hi : ρ.IsIrreducible)
    (q : ρ.IntertwiningMap τ) (h0 : q.toLinearMap ≠ 0) : Function.Injective q := by
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hi).2 (LinearMap.ker q.toLinearMap) (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    change q (ρ g v) = 0
    rw [q.isIntertwining _ _ g v]
    change τ g (q.toLinearMap v) = 0
    rw [hv, map_zero]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem isUnitarisable_of_isSpeh_one {a : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GL (Fin a) k) X} (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    {τ : Representation ℂ (GL (Fin a) k) Y} (h : IsSpeh (IrrGL.of ρ hs hi) 1 τ) (hu : IsUnitarisable τ) :
    IsUnitarisable ρ := by
  obtain ⟨hd, hτ, p, hp, -⟩ := h
  have key : ∀ y : Fin 1 → IrrGL k, y = (fun _ => IrrGL.of ρ hs hi) → ∀ hd : ∑ i, (y i).1 = a,
      Nonempty ((IrrGL.of ρ hs hi).rep.Equiv (prodIrr y hd)) := by
    rintro _ rfl hd
    exact nonempty_equiv_prodIrr_one _ hd
  obtain ⟨e⟩ := key _ (funext fun _ => by simp [spehFactor]) hd
  let q : ρ.IntertwiningMap τ := p.comp (e.toIntertwiningMap.comp (IrrGL.equivOf ρ hs hi).toIntertwiningMap)
  have hq : Function.Surjective q :=
    hp.comp (e.toLinearEquiv.surjective.comp (IrrGL.equivOf ρ hs hi).toLinearEquiv.surjective)
  refine isUnitarisable_of_injective q (injective_of_irreducible hi q fun h0 => ?_) hu
  have : Nontrivial Y := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hτ).1
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨v, rfl⟩ := hq y
  exact hy (LinearMap.congr_fun h0 v)

end Local

section Speh

open GlobalTheory.PRep GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

theorem isSpehQuot_of_isSpeh {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hs : IsSpeh (IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ) : IsSpehQuot h σ σ' := by
  obtain ⟨hd, -, p, hp, -⟩ := hs
  let T : ∀ i : Fin d, (twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans
      ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  exact ⟨p.comp M.toIntertwiningMap, hp.comp M.toLinearEquiv.surjective⟩

end Speh

section Inf

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem hasInfCharGL_unique {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (h : HasInfCharGL V τ m) (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

end Inf

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  simp only [GlobalTheory.SphGal.spehInf, GlobalTheory.DefiniteBC.spehInf]
  rw [← List.sum_ofFn, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem discreteSpectrum_of_discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], DiscreteSpectrum E := by
  intro H E _ _ _ N hN V hV
  obtain ⟨a, d, π, -, hπ, hS⟩ := (H E N hN).1 V hV
  have hSp := hS
  obtain ⟨h, -⟩ := hSp
  have hda : d * a = N := hS.mul_eq
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_left (by omega : 0 < d * a)
  have hC := (H E N hN).2.2.2.2 V hV a d π hπ hS
  obtain ⟨V₁, ⟨hV₁, hS₁⟩, -⟩ := (H E a ha).2.1 a 1 π (one_mul a) hπ
  have hC₁ := (H E a ha).2.2.2.2 V₁ hV₁ a 1 π hπ hS₁
  refine ⟨a, d, h, π, fun hc => GlobalTheory.DiscSpec.isCsd_of_isSpehOf H hN hV hc hπ hS, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · refine ⟨GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E N V hV w σ' hσ', ?_⟩
    obtain ⟨σ, -, hσ, -⟩ := hC.exLoc w
    obtain ⟨-, τ, -, hτ⟩ := hC₁.exLoc w
    refine ⟨σ, hσ, isUnitarisable_of_isSpeh_one σ.smooth σ.irred (hC₁.loc w σ τ hσ hτ)
      (GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V₁ hV₁ w τ hτ), isSpehQuot_of_isSpeh h σ σ' (hC.loc w σ σ' hσ hσ')⟩
  · obtain ⟨m, hm, hm''⟩ := hC.inf τ
    exact ⟨m, hm, (hasInfCharGL_unique hV.ne_bot hm' hm'').trans (spehInf_eq d m)⟩

end GlobalTheory.DiscreteSpectrumCM

end
