import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

noncomputable section
namespace GlobalTheory.CoefDuty.Model
open GlobalTheory.CoefDuty

section Record
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def locExtRefl (N : NData R H what₂) (A : NAut N) (i : N.Loc) : LocExt N N A A i i where
  l_eq := rfl
  φ := RingHom.id _
  φ_iota _ := rfl
  φ_alg z z' h := by cases h; rfl
  e := Equiv.refl _
  out _ := Iff.rfl
  hT _ _ _ _ _ _ := rfl
  Z _ := Iff.rfl
  γ := MulEquiv.refl _
  γ_cont := continuous_id
  γ_cont' := continuous_id
  frob _ _ := Iff.rfl
  ine _ _ := Iff.rfl
  wild _ _ := Iff.rfl
  cyc _ := HEq.rfl
  chi _ _ _ _ := rfl

theorem exists_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) : ∃ z' : ℤ_[q], HEq z z' := by
  subst h
  exact ⟨z, HEq.rfl⟩

variable {N₀ N₁ N₂ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {A₂ : NAut N₂} {i₀ : N₀.Loc} {i₁ : N₁.Loc} {i₂ : N₂.Loc}

def locExtTrans (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (b : LocExt N₁ N₂ A₁ A₂ i₁ i₂) : LocExt N₀ N₂ A₀ A₂ i₀ i₂ where
  l_eq := a.l_eq.trans b.l_eq
  φ := b.φ.comp a.φ
  φ_iota z := (b.φ_iota _).trans (a.φ_iota z)
  φ_alg z z'' h := by
    obtain ⟨z', h'⟩ := exists_heq a.l_eq z
    rw [RingHom.comp_apply, a.φ_alg z z' h', b.φ_alg z' z'' (h'.symm.trans h)]
  e := b.e.trans a.e
  out v := (b.out v).trans (a.out v)
  hT v k x h h1 h2 := by
    rw [b.hT v k x h h1 h2, a.hT v k _ ((b.out v).1 h) h1 h2]; rfl
  Z x := (b.Z x).trans (a.Z _)
  γ := b.γ.trans a.γ
  γ_cont := a.γ_cont.comp b.γ_cont
  γ_cont' := b.γ_cont'.comp a.γ_cont'
  frob w σ := (b.frob w σ).trans (a.frob w _)
  ine w σ := (b.ine w σ).trans (a.ine w _)
  wild w σ := (b.wild w σ).trans (a.wild w _)
  cyc σ := (a.cyc _).trans (b.cyc σ)
  chi c h1 h2 σ := by rw [b.chi c h1 h2 σ, a.chi c h1 h2]; rfl

theorem iotaO_injective (N : NData R H what₂) (A : NAut N) (i : N.Loc) : Function.Injective (iotaO N A i) :=
  (((A.iotaQC i).toRingHom.comp (A.iotaQ i)).injective).comp (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))

theorem φ_injective (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Function.Injective a.φ := fun x y h =>
  iotaO_injective N₀ A₀ i₀ (by rw [← a.φ_iota, ← a.φ_iota, h])

theorem s0_eq (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : N₀.s0 i₀ = N₁.s0 i₁ := by
  by_cases h : N₀.l i₀ = 2
  · rw [N₀.restNLevelExponent_of_two i₀ h, N₁.restNLevelExponent_of_two i₁ (a.l_eq ▸ h)]
  · rw [N₀.restNLevelExponent_of_odd i₀ h, N₁.restNLevelExponent_of_odd i₁ (a.l_eq ▸ h), a.l_eq]

theorem heckePol_map (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁) (w : PlE H) (hw : SplitOut N₁ i₁ w) :
    heckePol N₁ i₁ x w = (heckePol N₀ i₀ (a.e x) w).map a.φ := by
  unfold heckePol
  rw [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [a.hT w k x hw hk.1 hk.2]
  simp

theorem gen_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (s : ℕ) (z : ℤ_[p]ˣ) (z' : ℤ_[q]ˣ) (hz : HEq z z') :
    (∃ u : ℤ_[p]ˣ, (z : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ s * (u : ℤ_[p])) ↔
    ∃ u : ℤ_[q]ˣ, (z' : ℤ_[q]) = 1 + (q : ℤ_[q]) ^ s * (u : ℤ_[q]) := by
  subst h
  cases hz
  rfl

theorem localisationCoefficientExtension_isWildInertiaCyclotomic_iff (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (g : GE N₁) : IsWildInertiaCyclotomicElement N₁ i₁ g ↔ IsWildInertiaCyclotomicElement N₀ i₀ (a.γ g) := by
  unfold IsWildInertiaCyclotomicElement GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsInertiaCyclotomicGeneratorElement
  rw [gen_heq a.l_eq (N₀.s0 i₀) _ _ (a.cyc g), s0_eq a]
  simp only [a.ine, a.wild, a.l_eq]

theorem contains_ext (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (S : Set ℂ) (h : Contains N₀ A₀ i₀ S) : Contains N₁ A₁ i₁ S := by
  intro z hz
  obtain ⟨x, rfl⟩ := h z hz
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := N₀.O i₀) x
  refine ⟨algebraMap _ _ (a.φ p) / algebraMap _ _ (a.φ q), ?_⟩
  have hp := a.φ_iota p
  have hq := a.φ_iota q
  simp only [iotaO, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hp hq
  simp only [map_div₀, hp, hq]

theorem takenAfter_of_takenWild (N : NData R H what₂) (i : N.Loc) (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (h : TakenWild N i rep ρ) : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.TakenAfter N i rep ρ := by
  obtain ⟨A, a1, a2, a3, a4, a5, a6, a7, TA, repA, ρA, χA, hE, hS, hC⟩ := h
  refine ⟨A, a1, a2, a3, a4, a5, a6, a7, TA, repA, ρA, χA, hE, hS, fun π hπ => ?_⟩
  obtain ⟨g0, L, eB, e1, X0, hg, hc, hr⟩ := hC π hπ
  exact ⟨g0, L, eB, e1, X0, hg.1, hc, hr⟩

theorem takenWild_of_chosen (N : NData R H what₂) (A : NAut N) (i : N.Loc) (S : Set ℂ) (hC : Chosen N A i S)
    (hS : Contains N A i S) : ∃ r ρ, GoodR N i r ∧ TakenWild N i r ρ := by
  obtain ⟨rep, ρ, hG, hSet, hch⟩ := hC
  refine ⟨rep, ρ, hG, N.O i, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, N.T i, rep, ρ, N.chi i, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.isEnlargement_self N i rep ρ, hSet, fun π hπ => ?_⟩
  obtain ⟨g0, L, eB, e1, X0, hg, hc, hr⟩ := hch π hπ
  refine ⟨g0, L, eB, e1, X0, hg, hc, fun x => ?_⟩
  obtain ⟨α, hα, hP⟩ := hr x
  choose β hβ using fun c => hS (α c) (hα c)
  refine ⟨β, ?_⟩
  apply Polynomial.map_injective ((A.iotaQC i).toRingHom.comp (A.iotaQ i)) (RingHom.injective _)
  rw [Polynomial.map_map, Polynomial.map_prod]
  refine Eq.trans ?_ (hP.trans ?_)
  · congr 1
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp [← hβ c]

end Record

section Plain
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isBounded_umax : IsBounded (Umax L n) := ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using hκ⟩⟩

def trivWt (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : NG.AlgWt L n where
  W := ℂ
  ρ := Representation.trivial ℂ (GQ L n) ℂ
  alg := ⟨inferInstance, Unit, inferInstance, inferInstance, Module.Basis.singleton Unit ℂ, fun _ _ => 1, fun γ γ₀ _ => by
    ext i j
    simp [LinearMap.toMatrix_apply]⟩
  irr := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
    · have : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top this
    · rcases eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem isInvForm_triv : IsInvForm (trivWt L n) (innerₛₗ ℂ : ℂ →ₗ⋆[ℂ] ℂ →ₗ[ℂ] ℂ) := by
  refine ⟨fun (x y : ℂ) => (inner_conj_symm x y).symm, fun (x : ℂ) hx => ?_, fun γ (x y : ℂ) => rfl⟩
  exact (re_inner_self_pos (𝕜 := ℂ) (x := x)).2 hx

theorem exists_isClassReps (J : Subgroup (GAf L n)) (T : Finset (GAf L n))
    (hT : ∀ g : GAf L n, ∃ t ∈ T, ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ) :
    ∃ T', IsClassReps J T' := by
  classical
  let q : GAf L n → DoubleCoset.Quotient (GQ L n : Set (GAf L n)) J := DoubleCoset.mk _ _
  have key : ∀ g t : GAf L n, (∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ) ↔ q t = q g := by
    intro g t
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨γ, κ, h, e⟩ => ⟨γ, γ.2, κ, h, e⟩, fun ⟨γ, hγ, κ, h, e⟩ => ⟨⟨γ, hγ⟩, κ, h, e⟩⟩
  have hout : ∀ c, q (Quotient.out c) = c := fun c => Quotient.out_eq c
  refine ⟨T.image fun t => (q t).out, fun g => ⟨(q g).out, ⟨?_, (key _ _).2 (hout _)⟩, ?_⟩⟩
  · obtain ⟨t, ht, h⟩ := hT g
    exact Finset.mem_image.2 ⟨t, ht, by rw [(key _ _).1 h]⟩
  · rintro y ⟨hy, h⟩
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy
    rw [← (key _ _).1 h, hout]

theorem card_class (J : Subgroup (GAf L n)) (t κ : GAf L n) (δ : GQ L n) (hκ : κ ∈ J) :
    Nat.card {γ : GQ L n // ((δ : GAf L n) * t * κ)⁻¹ * (γ : GAf L n) * ((δ : GAf L n) * t * κ) ∈ J} =
      Nat.card {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} := by
  refine Nat.card_congr ((MulAut.conj δ⁻¹).toEquiv.subtypeEquiv fun γ => ?_)
  have e : ((δ : GAf L n) * t * κ)⁻¹ * (γ : GAf L n) * ((δ : GAf L n) * t * κ) =
      κ⁻¹ * (t⁻¹ * (((MulAut.conj δ⁻¹).toEquiv γ : GQ L n) : GAf L n) * t) * κ := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right hκ, J.mul_mem_cancel_left (J.inv_mem hκ)]

theorem classSum_indep (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (hβ : IsInvForm a β) (J : Subgroup (GAf L n))
    (χ : J →* ℂˣ) (hχ : ∀ κ, starRingEnd ℂ (χ κ : ℂ) * (χ κ : ℂ) = 1) (T T' : Finset (GAf L n))
    (hT : IsClassReps J T) (hT' : IsClassReps J T') (f f' : GAf L n → a.W) (hf : f ∈ NG.TypeSp a.ρ J χ)
    (hf' : f' ∈ NG.TypeSp a.ρ J χ) : classSum a β J T f f' = classSum a β J T' f f' := by
  have val : ∀ u ∈ NG.TypeSp a.ρ J χ, ∀ (δ : GQ L n) (t : GAf L n) (κ : J),
      u ((δ : GAf L n) * t * κ) = (χ κ : ℂ) • a.ρ δ (u t) := by
    intro u hu δ t κ
    have := congrFun (hu.2 κ) ((δ : GAf L n) * t)
    rw [← hu.1.1 δ t]
    exact this
  have symm : ∀ {g t : GAf L n}, (∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ) →
      ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ t = (γ : GAf L n) * g * κ := by
    rintro g t ⟨γ, κ, h, rfl⟩
    exact ⟨γ⁻¹, κ⁻¹, J.inv_mem h, by simp [mul_assoc]⟩
  have self : ∀ t : GAf L n, ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ t = (γ : GAf L n) * t * κ :=
    fun t => ⟨1, 1, J.one_mem, by simp⟩
  unfold classSum
  refine Finset.sum_bij' (fun t _ => (hT' t).exists.choose) (fun t _ => (hT t).exists.choose)
    (fun t _ => (hT' t).exists.choose_spec.1) (fun t _ => (hT t).exists.choose_spec.1) ?_ ?_ ?_
  · intro t ht
    exact (hT _).unique (hT _).exists.choose_spec ⟨ht, symm (hT' t).exists.choose_spec.2⟩
  · intro t ht
    exact (hT' _).unique (hT' _).exists.choose_spec ⟨ht, symm (hT t).exists.choose_spec.2⟩
  · intro t _
    obtain ⟨δ, κ, hκ, e⟩ := (hT' t).exists.choose_spec.2
    generalize (hT' t).exists.choose = s at e
    subst e
    rw [card_class J s κ δ hκ, val f hf δ s ⟨κ, hκ⟩, val f' hf' δ s ⟨κ, hκ⟩]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, hβ.2.2]
    rw [← mul_assoc (χ ⟨κ, hκ⟩ : ℂ), mul_comm (χ ⟨κ, hκ⟩ : ℂ), hχ, one_mul]

end Plain
end GlobalTheory.CoefDuty.Model
end
