import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.SplitHeckeComm

theorem gelfand {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Subgroup G)
    (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂) (hJ : ∀ k ∈ J, τ k ∈ J) (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂)
    (hR' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * β * k₂)
    (hS' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * β * k₂) → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J)
    (x : W) (hx : ∀ k ∈ J, ρ k x = x) :
    ∑ γ ∈ R, ρ γ (∑ δ ∈ S, ρ δ x) = ∑ δ ∈ S, ρ δ (∑ γ ∈ R, ρ γ x) := by
  classical
  let f : G ⧸ J → W := fun c => ρ c.out x
  have hf : ∀ g : G, f (g : G ⧸ J) = ρ g x := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J g
    simp only [f, hk, map_mul, Module.End.mul_apply, hx k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ρ γ (∑ δ ∈ B, ρ δ x)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ J) := fun A B => by
    rw [Finset.sum_product]
    simp only [hf, map_sum, map_mul, Module.End.mul_apply]
  rw [key, key]
  let T : Finset (G ⧸ J) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ J)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ J))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ α β R S hR hR' hS hS' c
  · convert GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ β α S R hS hS' hR hR' c

theorem gelfand_sub {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (H U : Subgroup G)
    (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a) (hH : ∀ k ∈ H, τ k ∈ H)
    (hU : ∀ k ∈ U, τ k ∈ U)
    (hdc : ∀ g ∈ H, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ τ g = k₁ * g * k₂) (α β : G) (R S : Finset G)
    (hα : α ∈ H) (hβ : β ∈ H)
    (hR' : ∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ U)
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * α * k₂)
    (hS' : ∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ U)
    (hS : ∀ γ ∈ S, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * β * k₂)
    (x : W) (hx : ∀ k ∈ U, k ∈ H → ρ k x = x) :
    ∑ γ ∈ R, ρ γ (∑ δ ∈ S, ρ δ x) = ∑ δ ∈ S, ρ δ (∑ γ ∈ R, ρ γ x) := by
  classical
  have hmem : ∀ (a : G) (A : Finset G), a ∈ H →
      (∀ γ ∈ A, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * a * k₂) → ∀ γ ∈ A, γ ∈ H := by
    intro a A ha h γ hγ
    obtain ⟨k₁, -, k₂, -, h₁, h₂, rfl⟩ := h γ hγ
    exact H.mul_mem (H.mul_mem h₁ ha) h₂
  have hsum : ∀ A : Finset G, (∀ γ ∈ A, γ ∈ H) → ∀ y : W,
      ∑ γ ∈ A, ρ γ y = ∑ γ ∈ A.subtype (· ∈ H), ρ (γ : G) y := fun A hA y =>
    (Finset.sum_subtype_of_mem (fun γ => ρ γ y) hA).symm
  have h1 : ∀ (a : G) (ha : a ∈ H) (A : Finset G),
      (∀ γ ∈ A, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * a * k₂) →
      ∀ γ ∈ (A.subtype (· ∈ H) : Finset H), ∃ k₁ ∈ U.subgroupOf H, ∃ k₂ ∈ U.subgroupOf H, γ = k₁ * ⟨a, ha⟩ * k₂ := by
    intro a ha A h γ hγ
    obtain ⟨k₁, u₁, k₂, u₂, h₁, h₂, e⟩ := h γ (Finset.mem_subtype.1 hγ)
    exact ⟨⟨k₁, h₁⟩, u₁, ⟨k₂, h₂⟩, u₂, Subtype.ext e⟩
  have h2 : ∀ (a : G) (ha : a ∈ H) (A : Finset G), (∀ γ ∈ A, γ ∈ H) →
      (∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * a * k₂) → ∃! γ, γ ∈ A ∧ γ⁻¹ * x ∈ U) →
      ∀ x : H, (∃ k₁ ∈ U.subgroupOf H, ∃ k₂ ∈ U.subgroupOf H, x = k₁ * ⟨a, ha⟩ * k₂) →
        ∃! γ, γ ∈ (A.subtype (· ∈ H) : Finset H) ∧ γ⁻¹ * x ∈ U.subgroupOf H := by
    rintro a ha A hA h x ⟨k₁, u₁, k₂, u₂, e⟩
    obtain ⟨γ, ⟨hγ, hu⟩, huniq⟩ := h x ⟨k₁, u₁, k₂, u₂, k₁.2, k₂.2, congrArg Subtype.val e⟩
    refine ⟨⟨γ, hA γ hγ⟩, ⟨Finset.mem_subtype.2 hγ, hu⟩, fun δ hδ => Subtype.ext ?_⟩
    exact huniq δ ⟨Finset.mem_subtype.1 hδ.1, hδ.2⟩
  have hRH := hmem α R hα hR
  have hSH := hmem β S hβ hS
  rw [hsum R hRH, hsum S hSH x, hsum S hSH, hsum R hRH x]
  refine gelfand (ρ.comp H.subtype) (U.subgroupOf H) (fun g => ⟨τ g, hH g g.2⟩)
    (fun a b => Subtype.ext (hmul a b)) (fun a => Subtype.ext (hinv a)) (fun g => ?_) (fun k hk => hU k hk)
    ⟨α, hα⟩ ⟨β, hβ⟩ _ _ (h1 α hα R hR) (h2 α hα R hRH hR') (h1 β hβ S hS) (h2 β hβ S hSH hS') x
    (fun k hk => hx k hk k.2)
  obtain ⟨k₁, u₁, k₂, u₂, h₁, h₂, e⟩ := hdc g g.2
  exact ⟨⟨k₁, h₁⟩, u₁, ⟨k₂, h₂⟩, u₂, Subtype.ext e⟩

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

def trivSub (n : ℕ) (T : Set (HeightOneSpectrum (𝓞 L⁺))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside T x}
  mul_mem' := by
    intro x y hx hy w hw
    show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1
    rw [Units.val_mul, Matrix.map_mul, hx w hw, hy w hw, mul_one]
  one_mem' := by
    intro w _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  inv_mem' := by
    intro x hx w hw
    have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
        (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    have h2 := congrArg (fun M => M.map (compAt L w)) h1
    simp only [Matrix.map_mul, hx w hw, mul_one] at h2
    rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

def tr (x : GAf L n) : GAf L n :=
  ⟨Formalism.UG.P.heckecomm_tr x.1, by
    have hm : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x.1 = 1 := x.2
    have h := congrArg Matrix.transpose (mul_eq_one_comm.mp hm)
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h
    exact h⟩

theorem loc_tr (s : SplitPlace L) (x : GAf L n) : s.loc n (tr x) = Formalism.UG.P.heckecomm_tr (s.loc n x) :=
  Units.ext rfl

theorem mem_Umax_of_loc (s : SplitPlace L) (x : GAf L n) (hx : TrivOutside {s.v} x)
    (h : s.loc n x ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L⁺ s.v)) : x ∈ Umax L n := by
  have hint : ∀ a ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L⁺ s.v), ∀ i j,
      Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := by
    rintro _ ⟨g, rfl⟩ i j
    exact ((g : Matrix (Fin n) (Fin n) (Formalism.UG.Ov L⁺ s.v)) i j).2
  have h1 := hint _ h
  have h2 := hint _ (inv_mem h)
  rw [← map_inv] at h2
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  intro i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x.1 = 1 := x.2
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using this

theorem tr_mem_trivSub (T : Set (HeightOneSpectrum (𝓞 L⁺))) (x : GAf L n) (hx : x ∈ trivSub n T) :
    tr x ∈ trivSub n T := by
  intro w hw
  have h := congrArg Matrix.transpose (hx w hw)
  rw [Matrix.transpose_one] at h
  exact h

theorem tr_doubleCoset (s : SplitPlace L) (g : GAf L n) (hg : g ∈ trivSub n {s.v}) :
    ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, k₁ ∈ trivSub n {s.v} ∧ k₂ ∈ trivSub n {s.v} ∧ tr g = k₁ * g * k₂ := by
  obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp L⁺ s.v n (s.loc n g)
  obtain ⟨k, hk, ek⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s a.1
  have hk' : k ∈ trivSub n {s.v} := hk
  have ht : (k * g)⁻¹ * tr g ∈ trivSub n {s.v} := mul_mem (inv_mem (mul_mem hk' hg)) (tr_mem_trivSub _ g hg)
  refine ⟨k, mem_Umax_of_loc s k hk (ek ▸ a.2), (k * g)⁻¹ * tr g, mem_Umax_of_loc s _ ht ?_, hk', ht, by group⟩
  rw [map_mul, map_inv, map_mul, loc_tr, e, ek, inv_mul_cancel_left]
  exact b.2

def rtRep (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (GAf L n) (GAf L n → W) where
  toFun := NG.rt L n
  map_one' := LinearMap.ext fun f => funext fun g => congrArg f (mul_one g)
  map_mul' x y := LinearMap.ext fun f => funext fun g => congrArg f (mul_assoc g x y).symm

theorem doubleCoset_comm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L) (α β : GAf L n) (Ra Rb : Finset (GAf L n)), TrivOutside {s.v} α → TrivOutside {s.v} β → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ Ra ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Ra, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * α * k₂) → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ Rb ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Rb, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * β * k₂) → ∀ f : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → ∑ γ ∈ Ra, NG.rt L n γ (∑ δ ∈ Rb, NG.rt L n δ f) = ∑ δ ∈ Rb, NG.rt L n δ (∑ γ ∈ Ra, NG.rt L n γ f) := by
  intro L _ _ _ n W _ _ s α β Ra Rb hα hβ hR' hR hS' hS f hf
  exact gelfand_sub (rtRep L n W) (trivSub n {s.v}) (Umax L n) tr
    (fun a b => Subtype.ext (Formalism.UG.P.heckecomm_tr_mul a.1 b.1)) (fun a => Subtype.ext (Formalism.UG.P.heckecomm_tr_tr a.1))
    (tr_mem_trivSub _) (fun k hk i j => hk j i) (tr_doubleCoset s) α β Ra Rb hα hβ hR' hR hS' hS f hf

end GlobalTheory.SplitHeckeComm

end
