import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Herbrand
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandF

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

noncomputable def uE (h : K ≤ L) [(subG p K L).Normal] :
    (layerU p K L).V →+ Additive (IntermediateField.extendScalars h)ˣ where
  toFun w := Additive.ofMul (Units.mk0 (⟨uval w, uval_mem h w⟩ : IntermediateField.extendScalars h)
    (fun h0 => uval_ne_zero w (congrArg Subtype.val h0)))
  map_zero' := Units.ext (Subtype.ext rfl)
  map_add' _ _ := Units.ext (Subtype.ext rfl)

theorem finiteIndex_of_ball (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal]
    (X : AddSubgroup (layerU p K L).V) {ε : ℝ} (hε : 0 < ε) (hX : ∀ w, ‖uval w - 1‖ < ε → w ∈ X) :
    X.FiniteIndex := by
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have hc : IsCompact (Metric.closedBall (0 : L) 1) := isCompact_closedBall 0 1
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hc (e := ε) hε
  have hex : ∀ w : (layerU p K L).V, ∃ y : t, ‖uval w - ((y : L) : PadicAlgCl p)‖ < ε := by
    intro w
    have hw : (⟨uval w, uval_mem h w⟩ : L) ∈ Metric.closedBall (0 : L) 1 := by
      rw [mem_closedBall_zero_iff]; exact (norm_uval w).le
    obtain ⟨y, hy, hwy⟩ := Set.mem_iUnion₂.1 (hcov hw)
    rw [Metric.mem_ball, dist_eq_norm] at hwy
    exact ⟨⟨y, hy⟩, hwy⟩
  choose c hc' using hex
  have hsub : ∀ w w', c w = c w' → w - w' ∈ X := by
    intro w w' hww
    apply hX
    have h1 : uval (w - w') - 1 = (uval w - uval w') * (uval w')⁻¹ := by
      rw [uval_sub, sub_mul, mul_inv_cancel₀ (uval_ne_zero w')]
    rw [h1, norm_mul, norm_inv, norm_uval, inv_one, mul_one]
    have h2 : uval w - uval w' = (uval w - ((c w : L) : PadicAlgCl p)) - (uval w' - ((c w : L) : PadicAlgCl p)) := by
      ring
    rw [h2, sub_eq_add_neg]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hc' w) ?_)
    rw [norm_neg, hww]; exact hc' w'
  have : Finite t := htf
  have hfin : Finite ((layerU p K L).V ⧸ X) := by
    refine Finite.of_injective (fun q => c q.out) fun q q' hqq => ?_
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    have := hsub _ _ hqq.symm
    rwa [sub_eq_neg_add] at this
  exact AddSubgroup.finiteIndex_of_finite_quotient

theorem exists_layerU_sub (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] :
    ∃ W : Submodule ℤ (layerU p K L).V, (∀ g, ∀ w ∈ W, (layerU p K L).rho g w ∈ W) ∧
      W.toAddSubgroup.FiniteIndex ∧
      (∀ w ∈ W, (∀ g, (layerU p K L).rho g w = w) → ∃ w' ∈ W, ∑ g, (layerU p K L).rho g w' = w) ∧
      ∀ g₀ : GalLK p K L, (∀ g, g ∈ Subgroup.zpowers g₀) → ∀ w ∈ W, ∑ g, (layerU p K L).rho g w = 0 →
        ∃ w' ∈ W, (layerU p K L).rho g₀ w' - w' = w := by
  classical
  let E : IntermediateField K (PadicAlgCl p) := IntermediateField.extendScalars h
  have hfd : FiniteDimensional K E := by
    have : FiniteDimensional ℚ_[p] E := hL
    exact FiniteDimensional.right ℚ_[p] K _
  have hst : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L := (subG_normal_iff h).1 inferInstance
  have hnorm : Normal K E := by
    rw [IntermediateField.normal_iff_forall_map_le']
    rintro σ _ ⟨x, hx, rfl⟩
    exact hst σ x hx
  have hgal : IsGalois K E := ⟨⟩
  obtain ⟨S, hS1, hS2, ⟨ε, hε, hS3⟩, hS4, hS5⟩ := exists_units_subgroup_padic hK E
  let r : GK p K →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  have hr : ∀ (σ : GK p K) (x : E), ((r σ x : E) : PadicAlgCl p) = σ x := fun σ x =>
    AlgEquiv.restrictNormalHom_apply E σ x
  have hrs : Surjective r := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (PadicAlgCl p)
  have hker : ∀ σ : GK p K, r σ = 1 ↔ σ ∈ subG p K L := by
    intro σ
    constructor
    · intro h1 x hx
      have := hr σ ⟨x, hx⟩
      rw [h1] at this
      exact this.symm
    · intro hσ
      ext x
      rw [hr]
      exact hσ x.1 x.2
  let f : GalLK p K L →* (E ≃ₐ[K] E) := QuotientGroup.lift (subG p K L) r fun σ hσ => (hker σ).2 hσ
  have hf : ∀ σ : GK p K, f (QuotientGroup.mk σ) = r σ := fun σ => rfl
  have hfb : Bijective f := by
    refine ⟨(injective_iff_map_eq_one f).2 fun q hq => ?_, fun τ => ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H σ => exact (QuotientGroup.eq_one_iff σ).2 ((hker σ).1 hq)
    · obtain ⟨σ, rfl⟩ := hrs τ
      exact ⟨QuotientGroup.mk σ, rfl⟩
  let e : GalLK p K L ≃* (E ≃ₐ[K] E) := MulEquiv.ofBijective f hfb
  let ι : (layerU p K L).V → Eˣ := fun w => Additive.toMul (uE h w)
  have hι : ∀ w, (((ι w : Eˣ) : E) : PadicAlgCl p) = uval w := fun w => rfl
  have hιrho : ∀ g w, ((ι ((layerU p K L).rho g w) : Eˣ) : E) = e g (ι w : E) := by
    intro g w
    induction g using QuotientGroup.induction_on with
    | H σ =>
      apply Subtype.ext
      rw [hι, uval_rho]
      exact (hr σ (ι w : E)).symm
  have hιsurj : ∀ v ∈ S, ∃ w, ι w = v := by
    intro v hv
    obtain ⟨w, hw⟩ := exists_uval (K := K) (L := L) (x := ((v : E) : PadicAlgCl p)) (v : E).2 (hS2 v hv)
    exact ⟨w, Units.ext (Subtype.ext hw)⟩
  have hprod : ∀ w, uval (∑ g, (layerU p K L).rho g w) = ((∏ τ : E ≃ₐ[K] E, τ (ι w : E) : E) : PadicAlgCl p) := by
    intro w
    rw [uval_sum, ← Fintype.prod_equiv e.toEquiv (fun g => e g (ι w : E)) (fun τ => τ (ι w : E)) (fun _ => rfl),
      IntermediateField.coe_prod]
    exact Finset.prod_congr rfl fun g _ => by rw [← hιrho, hι]
  let X : AddSubgroup (layerU p K L).V := (Subgroup.toAddSubgroup S).comap (uE h)
  have hX : ∀ w, w ∈ X ↔ ι w ∈ S := fun w => Iff.rfl
  refine ⟨AddSubgroup.toIntSubmodule X, fun g w hw => ?_, ?_, fun w hw hfix => ?_, fun g₀ hg₀ w hw hN => ?_⟩
  · exact hS1 (e g) (ι w) _ hw (hιrho g w)
  · rw [AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact finiteIndex_of_ball hL h X hε fun w hw => hS3 (ι w) hw
  · obtain ⟨v, hv, hvw⟩ := hS4 (ι w) hw fun τ => by
      obtain ⟨g, rfl⟩ := e.surjective τ
      rw [← hιrho, hfix]
    obtain ⟨w', rfl⟩ := hιsurj v hv
    refine ⟨w', hv, uval_injective ?_⟩
    rw [hprod, hvw, hι]
  · obtain ⟨v, hv, hvw⟩ := hS5 (e g₀) (fun τ => by
      obtain ⟨g, rfl⟩ := e.surjective τ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ g)
      rw [map_zpow]
      exact Subgroup.zpow_mem_zpowers _ _) (ι w) hw (by
        apply Subtype.ext
        rw [← hprod, hN]
        rfl)
    obtain ⟨w', rfl⟩ := hιsurj v hv
    refine ⟨w', hv, uval_injective ?_⟩
    rw [uval_sub, ← hι, hιrho, hvw, MulMemClass.coe_mul, hι, hι, mul_assoc, mul_inv_cancel₀ (uval_ne_zero w'),
      mul_one]

theorem herbrand_of_sub {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] (ρ : Representation ℤ G M) (g₀ : G)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (W : Submodule ℤ M) (hW1 : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hW2 : W.toAddSubgroup.FiniteIndex)
    (hW3 : ∀ w ∈ W, (∀ g, ρ g w = w) → ∃ w' ∈ W, ∑ g, ρ g w' = w)
    (hW4 : ∀ w ∈ W, ∑ g, ρ g w = 0 → ∃ w' ∈ W, ρ g₀ w' - w' = w) :
    Herbrand.HFin ρ g₀ ∧ Herbrand.h ρ g₀ = 1 := by
  let ρW : Representation ℤ G W :=
    { toFun := fun g => (ρ g).restrict (p := W) (q := W) (hW1 g)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show ρ 1 x.1 = x.1
        rw [map_one]; rfl)
      map_mul' := fun a b => LinearMap.ext fun x => Subtype.ext (by
        show ρ (a * b) x.1 = ρ a (ρ b x.1)
        rw [map_mul]; rfl) }
  have hρ : ∀ g (x : W), ((ρW g x : W) : M) = ρ g x.1 := fun _ _ => rfl
  have hsum : ∀ x : W, ((∑ g, ρW g x : W) : M) = ∑ g, ρ g x.1 := by
    intro x
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun g _ => hρ g x
  have h0 : Subsingleton (Herbrand.TateZerothCohomology ρW g₀) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
    rw [Herbrand.mk_eq_mk_iff]
    have hab : ((a : W) - (b : W)) ∈ (Herbrand.dHom ρW g₀).ker := (a - b).2
    rw [Herbrand.mem_ker_dHom_iff ρW g₀ hg] at hab
    obtain ⟨w', hw', hw⟩ := hW3 ((a : W) - (b : W) : W).1 ((a : W) - (b : W) : W).2
      (fun g => congrArg Subtype.val (hab g))
    refine ⟨⟨w', hw'⟩, ?_⟩
    rw [Herbrand.nHom_apply]
    exact Subtype.ext ((hsum _).trans hw)
  have h1 : Subsingleton (Herbrand.H1 ρW g₀) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
    induction b using QuotientAddGroup.induction_on with
    | H b =>
    rw [Herbrand.mk_eq_mk_iff]
    have hab : ((a : W) - (b : W)) ∈ (Herbrand.nHom ρW).ker := (a - b).2
    rw [AddMonoidHom.mem_ker, Herbrand.nHom_apply] at hab
    obtain ⟨w', hw', hw⟩ := hW4 ((a : W) - (b : W) : W).1 ((a : W) - (b : W) : W).2
      ((hsum _).symm.trans (congrArg Subtype.val hab))
    exact ⟨⟨w', hw'⟩, Subtype.ext hw⟩
  obtain ⟨hf, hh⟩ := Herbrand.h_of_subsingleton ρW g₀
  have hfi : (W.subtype.toAddMonoidHom).range.FiniteIndex := by
    have : (W.subtype.toAddMonoidHom).range = W.toAddSubgroup := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    rw [this]; exact hW2
  obtain ⟨hiff, heq⟩ := Herbrand.h_eq_of_finiteIndex ρW ρ g₀ W.subtype.toAddMonoidHom
    Subtype.val_injective hfi (fun _ _ => rfl)
  exact ⟨hiff.1 hf, (heq hf).symm.trans hh⟩

theorem herbrand_layerU (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Herbrand.HFin (layerU p K L).rho g₀ ∧ Herbrand.h (layerU p K L).rho g₀ = 1 := by
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := exists_layerU_sub hK hL h
  exact herbrand_of_sub (layerU p K L).rho g₀ hg W hW1 hW2 hW3 (hW4 g₀ hg)

end ReciprocityTheory.DiscreteGroups.LocalClassField
