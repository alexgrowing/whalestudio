import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.FormInner

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_reps (J : Subgroup (GAf L n)) (S : Finset (GAf L n))
    (hS : ∀ g : GAf L n, ∃ s ∈ S, ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * s * κ) :
    ∃ T, IsClassReps J T := by
  classical
  let q : GAf L n → DoubleCoset.Quotient (GQ L n : Set (GAf L n)) (J : Set (GAf L n)) := DoubleCoset.mk (GQ L n) J
  have hq : ∀ a b, q a = q b ↔ ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ b = (γ : GAf L n) * a * κ := fun a b => by
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨h, hh, k, hk, e⟩ => ⟨⟨h, hh⟩, k, hk, e⟩, fun ⟨h, k, hk, e⟩ => ⟨h, h.2, k, hk, e⟩⟩
  refine ⟨S.image fun s => (q s).out, fun g => ?_⟩
  obtain ⟨s, hs, e⟩ := hS g
  have e1 : q s = q g := (hq _ _).2 e
  have ho : ∀ c : DoubleCoset.Quotient (GQ L n : Set (GAf L n)) (J : Set (GAf L n)), q c.out = c := fun c => Quotient.out_eq c
  refine ⟨(q s).out, ⟨Finset.mem_image_of_mem _ hs, (hq _ _).1 ((ho _).trans e1)⟩, ?_⟩
  rintro t ⟨ht, h⟩
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 ht
  have := (hq _ _).2 h
  rw [ho] at this
  rw [this, e1]

theorem relIndex_ne_zero_of_reps {J K : Subgroup (GAf L n)} (hJ : IsBounded J) (hle : K ≤ J) {T : Finset (GAf L n)}
    (hT : IsClassReps K T) : K.relIndex J ≠ 0 := by
  classical
  have hfin : ∀ t : GAf L n, {γ : GQ L n | (γ : GAf L n) * t ∈ J}.Finite := by
    intro t
    rcases Set.eq_empty_or_nonempty {γ : GQ L n | (γ : GAf L n) * t ∈ J} with h | ⟨γ₀, h₀⟩
    · rw [h]; exact Set.finite_empty
    · haveI := GlobalTheory.StabFin.finite_conj_mem L n J hJ 1
      refine Set.Finite.subset (Set.finite_range fun δ : {γ : GQ L n // (1 : GAf L n)⁻¹ * (γ : GAf L n) * 1 ∈ J} => δ.1 * γ₀) ?_
      intro γ hγ
      refine ⟨⟨γ * γ₀⁻¹, ?_⟩, by simp⟩
      have := J.mul_mem hγ (J.inv_mem h₀)
      simpa [mul_assoc] using this
  refine relIndex_ne_zero_of_cover (T.biUnion fun t => (hfin t).toFinset.image fun γ : GQ L n => (γ : GAf L n) * t) (fun κ hκ => ?_) hle
  obtain ⟨t, ⟨ht, γ, k, hk, e⟩, -⟩ := hT κ
  refine ⟨γ * t, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).2 ?_)⟩, by rw [e, inv_mul_cancel_left]; exact hk⟩
  have := J.mul_mem hκ (J.inv_mem (hle hk))
  rw [e] at this
  simpa using this

theorem form_inv {a : NG.AlgWt L n} (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) {J : Subgroup (GAf L n)} (hJ : IsBounded J) {χ : J →* ℂˣ}
    {f f' : GAf L n → a.W} (hf : f ∈ NG.TypeSp a.ρ J χ) (hf' : f' ∈ NG.TypeSp a.ρ J χ) :
    ∀ κ ∈ J, ∀ g, β (f (g * κ)) (f' (g * κ)) = β (f g) (f' g) := by
  intro κ hκ g
  have e : ∀ k : J, f (g * k) = ((χ k : ℂˣ) : ℂ) • f g := fun k => congrFun (hf.2 k) g
  have e' : f' (g * κ) = ((χ ⟨κ, hκ⟩ : ℂˣ) : ℂ) • f' g := congrFun (hf'.2 ⟨κ, hκ⟩) g
  rw [e ⟨κ, hκ⟩, e']
  by_cases h0 : f g = 0
  · simp [h0]
  obtain ⟨N, hN, hinv⟩ := hf.1.2
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J hJ 1 N hN).2.1
  have hle : J ⊓ congSub L n N ≤ J := inf_le_left
  have hne : (J ⊓ congSub L n N).relIndex J ≠ 0 := by
    classical
    have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ J, f₀⁻¹ * κ ∈ congSub L n N) → u ∈ J ∧ f₀⁻¹ * u ∈ congSub L n N := fun f₀ _ => by
      by_cases h : ∃ κ ∈ J, f₀⁻¹ * κ ∈ congSub L n N
      · obtain ⟨u, hu⟩ := h
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' h⟩
    choose! u hu using this
    refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) hle
    obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
    obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, h₁⟩
    refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, J.mul_mem (J.inv_mem h2) hκ, ?_⟩
    have := (congSub L n N).mul_mem ((congSub L n N).inv_mem h3) h₁
    simpa [mul_assoc] using this
  have hn := norm_eq_one_of_relIndex hle hne χ (fun k hk => by
    have h1 := e ⟨k, hle hk⟩
    rw [hinv k hk.2 g] at h1
    have h2 : (((χ ⟨k, hle hk⟩ : ℂˣ) : ℂ) - 1) • f g = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact Units.ext (sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right h0))) ⟨κ, hκ⟩
  rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, Complex.conj_mul', hn]
  simp

theorem classSum_index {a : NG.AlgWt L n} {β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ} (hβ : IsInvForm a β) {J K : Subgroup (GAf L n)}
    {T T' : Finset (GAf L n)} (hJ : IsBounded J) (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (hT : IsClassReps J T)
    (hT' : IsClassReps K T') {χ : J →* ℂˣ} {f f' : GAf L n → a.W} (hf : f ∈ NG.TypeSp a.ρ J χ) (hf' : f' ∈ NG.TypeSp a.ρ J χ) :
    classSum a β K T' f f' = (K.relIndex J : ℂ) * classSum a β J T f f' := by
  obtain ⟨F, h1, h2, h3⟩ := exists_cosetReps hle hne
  have hi := form_inv β hJ hf hf'
  rw [GlobalTheory.ClassRefine.classSum_smaller_level L n a β hβ J K T T' hJ hle hne hT hT' f hf.1 f' hf'.1
    (fun κ hκ => hi κ (hle hκ)) F h1 h2, classSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl fun u hu => hi u (h1 u hu) t, Finset.sum_const, h3, nsmul_eq_mul]
  ring

theorem classSum_compare {a : NG.AlgWt L n} {β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ} (hβ : IsInvForm a β) {J J' : Subgroup (GAf L n)}
    (hJ : IsBounded J) {N : ℕ} (hN : 0 < N) (hNJ : ∀ κ, NG.Cong L n N κ → κ ∈ J) (hJ' : IsBounded J') {T' : Finset (GAf L n)}
    (hT' : IsClassReps J' T') : ∃ (T : Finset (GAf L n)) (c : ℝ), IsClassReps J T ∧ 0 < c ∧
      ∀ (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (f f' : GAf L n → a.W), f ∈ NG.TypeSp a.ρ J χ → f' ∈ NG.TypeSp a.ρ J χ →
        f ∈ NG.TypeSp a.ρ J' χ' → f' ∈ NG.TypeSp a.ρ J' χ' → classSum a β J' T' f f' = (c : ℂ) * classSum a β J T f f' := by
  classical
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J' hJ' 1 N hN).2.1
  have hne' : (J ⊓ J').relIndex J' ≠ 0 := by
    have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ J', f₀⁻¹ * κ ∈ J) → u ∈ J' ∧ f₀⁻¹ * u ∈ J := fun f₀ _ => by
      by_cases h : ∃ κ ∈ J', f₀⁻¹ * κ ∈ J
      · obtain ⟨u, hu⟩ := h
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' h⟩
    choose! u hu using this
    refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) inf_le_right
    obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
    obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, hNJ _ h₁⟩
    refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, ?_, J'.mul_mem (J'.inv_mem h2) hκ⟩
    have := J.mul_mem (J.inv_mem h3) (hNJ _ h₁)
    simpa [mul_assoc] using this
  obtain ⟨U, hU1, hU2, -⟩ := exists_cosetReps (inf_le_right : J ⊓ J' ≤ J') hne'
  obtain ⟨T₀, hT₀⟩ := exists_reps (J ⊓ J') ((T' ×ˢ U).image fun p => p.1 * p.2) fun g => by
    obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, -⟩ := hT' g
    obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hU2 κ hκ
    exact ⟨t * u, Finset.mem_image.2 ⟨(t, u), Finset.mem_product.2 ⟨ht, hu⟩, rfl⟩, γ, u⁻¹ * κ, hu', by rw [e]; group⟩
  have hne : (J ⊓ J').relIndex J ≠ 0 := relIndex_ne_zero_of_reps hJ inf_le_left hT₀
  obtain ⟨T, hT⟩ := exists_reps J T₀ fun g => by
    obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, -⟩ := hT₀ g
    exact ⟨t, ht, γ, κ, hκ.1, e⟩
  refine ⟨T, ((J ⊓ J').relIndex J : ℝ) / ((J ⊓ J').relIndex J' : ℝ), hT,
    div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hne)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hne')), ?_⟩
  intro χ χ' f f' h1 h2 h3 h4
  have e1 := classSum_index hβ hJ inf_le_left hne hT hT₀ h1 h2
  have e2 := classSum_index hβ hJ' inf_le_right hne' hT' hT₀ h3 h4
  have hc : (((J ⊓ J').relIndex J' : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne'
  push_cast
  rw [div_mul_eq_mul_div, ← e1, e2, mul_div_cancel_left₀ _ hc]

theorem classSum_transport {G Γ W I : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I]
    (ι : Γ →* G) (hι : Function.Injective ι) (φ : GAf L n ≃* G) (hrat : ∀ h, h ∈ GQ L n ↔ ∃ γ, ι γ = φ h)
    (J : Subgroup G) (y : I → G) (hy : Formalism.IndefR.Bridge.IsReps ι J y) :
    ∃ T, IsClassReps (J.comap φ.toMonoidHom) T ∧ ∀ (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (f f' : GAf L n → a.W)
      (F F' : G → W), (∀ g, β (f g) (f' g) = inner ℂ (F (φ g)) (F' (φ g))) →
      classSum a β (J.comap φ.toMonoidHom) T f f' = Formalism.IndefR.Bridge.adInner ι J y F F' := by
  classical
  have hinj : Function.Injective fun i => φ.symm (y i) := fun i j e => by
    have e' : y i = y j := φ.symm.injective e
    exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [e']⟩
  have key : ∀ g i, (∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J.comap φ.toMonoidHom ∧ g = (γ : GAf L n) * φ.symm (y i) * κ) ↔
      ∃ (γ : Γ) (k : J), φ g = ι γ * y i * k := fun g i => by
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨δ, hδ⟩ := (hrat _).1 γ.2
      exact ⟨δ, ⟨φ κ, hκ⟩, by simp [hδ]⟩
    · rintro ⟨γ, k, e⟩
      refine ⟨⟨φ.symm (ι γ), (hrat _).2 ⟨γ, by simp⟩⟩, φ.symm k, by simp, φ.injective (by simp [e])⟩
  refine ⟨Finset.univ.image fun i => φ.symm (y i), fun g => ?_, fun a β f f' F F' h => ?_⟩
  · obtain ⟨i, hi, hu⟩ := hy (φ g)
    refine ⟨φ.symm (y i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 hi⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hu j ((key g j).1 h)]
  · rw [classSum, Finset.sum_image fun i _ j _ e => hinj e, Formalism.IndefR.Bridge.adInner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h, MulEquiv.apply_symm_apply]
    congr 3
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun δ : Formalism.IndefR.Bridge.stab ι J (y i) =>
      (⟨⟨φ.symm (ι δ), (hrat _).2 ⟨δ, by simp⟩⟩, by simpa using (Formalism.IndefR.Bridge.mem_stab ι).1 δ.2⟩ :
        {γ : GQ L n // (φ.symm (y i))⁻¹ * (γ : GAf L n) * φ.symm (y i) ∈ J.comap φ.toMonoidHom})) ⟨fun δ δ' e => ?_, fun γ => ?_⟩)
    · exact Subtype.ext (hι (φ.symm.injective (congrArg (fun z => (z.1 : GAf L n)) e)))
    · obtain ⟨δ, hδ⟩ := (hrat _).1 γ.1.2
      refine ⟨⟨δ, (Formalism.IndefR.Bridge.mem_stab ι).2 ?_⟩, Subtype.ext (Subtype.ext (by simp [hδ]))⟩
      simpa [hδ] using γ.2

end GlobalTheory.FormInner

end
