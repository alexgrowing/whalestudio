import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSmulOfMapResidueEqZero
import Formalism.SubspaceCounting.ChoiceOfTopsRefined
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.SplitCosetCount

section Grp

open Classical

variable {G : Type} [Group G]

theorem card_le_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card ≤ B.card := by
  classical
  have f : ∀ a ∈ A, ∃ b, b ∈ B ∧ b⁻¹ * a ∈ J := fun a ha => (hB.2 a (hA.1 a ha)).exists
  choose! φ hφB hφJ using f
  refine Finset.card_le_card_of_injOn φ (fun a ha => hφB a ha) ?_
  intro a₁ ha₁ a₂ ha₂ he
  have h1 : a₁⁻¹ * a₂ ∈ J := by
    have h := J.mul_mem (J.inv_mem (hφJ a₁ ha₁)) (hφJ a₂ ha₂)
    have e : ((φ a₁)⁻¹ * a₁)⁻¹ * ((φ a₂)⁻¹ * a₂) = a₁⁻¹ * a₂ := by rw [he]; group
    rwa [e] at h
  exact (hA.2 a₂ (hA.1 a₂ ha₂)).unique ⟨ha₁, h1⟩ ⟨ha₂, by simp⟩

theorem card_eq_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card = B.card :=
  le_antisymm (card_le_of_isDC hA hB) (card_le_of_isDC hB hA)

variable {H : Type} [Group H] {ρ : G →* H} {S : G → Prop} {K : Set G} {K' : Subgroup H}

theorem lift_isReps (hm : ∀ x y, S x → S y → S (x * y)) (hi : ∀ x, S x → S x⁻¹)
    (hinj : ∀ x y, S x → S y → ρ x = ρ y → x = y) (hK : ∀ g, S g → (g ∈ K ↔ ρ g ∈ K'))
    {g : G} (hg : S g) {R₀ : Finset H} (hR : Formalism.IndefR.Fin.HCount.IsReps K' (ρ g) R₀)
    (ψ : H → G) (hψs : ∀ a, S (ψ a)) (hψ : ∀ a, ρ (ψ a) = a) :
    (∀ γ ∈ R₀.image ψ, ∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R₀.image ψ ∧ γ⁻¹ * x ∈ {k | k ∈ K ∧ S k} := by
  classical
  have hex : ∀ a, ∃ g, S g ∧ ρ g = a := fun a => ⟨ψ a, hψs a, hψ a⟩
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact GlobalTheory.SplitPlace.lift_dc hm hex hinj hK hg (hψs a) (by rw [hψ]; exact hR.1 a ha)
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have hx := hm _ _ (hm _ _ hk₁.2 hg) hk₂.2
    have key : ∀ a, (ψ a)⁻¹ * (k₁ * g * k₂) ∈ {k | k ∈ K ∧ S k} ↔ a⁻¹ * ρ (k₁ * g * k₂) ∈ K' := by
      intro a
      have hs := hm _ _ (hi _ (hψs a)) hx
      have := hK _ hs
      rw [map_mul, map_inv, hψ] at this
      exact ⟨fun h => this.1 h.1, fun h => ⟨this.2 h, hs⟩⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := hR.2 (ρ (k₁ * g * k₂)) ⟨_, (hK _ hk₁.2).1 hk₁.1, _, (hK _ hk₂.2).1 hk₂.1,
      by rw [map_mul, map_mul]⟩
    refine ⟨ψ a, ⟨Finset.mem_image_of_mem _ ha, (key a).2 ha'⟩, ?_⟩
    rintro γ ⟨hγ, h⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
    rw [hu b ⟨hb, (key b).1 h⟩]

theorem card_image_section {R₀ : Finset H} (ψ : H → G) (hψ : ∀ a, ρ (ψ a) = a) :
    (R₀.image ψ).card = R₀.card := by
  classical
  refine Finset.card_image_of_injective _ fun a b h => ?_
  rw [← hψ a, ← hψ b, h]

end Grp

theorem gaussBinom_eq (κ : Type) [Field κ] [Fintype κ] (n k : ℕ) :
    Formalism.G0.gaussBinom (Fintype.card κ) n k = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Fintype.card κ) n k := by
  have h1 := Formalism.G0.Top.subspaceCount (F := κ) (W := Fin n → κ) k
  have h2 := GlobalTheory.GaussCount.subspaceCount κ (Fin n → κ) k
  rw [Module.finrank_fin_fun] at h1 h2
  rw [Nat.card_eq_fintype_card (α := κ)] at h2
  rw [← h1, ← h2]
  unfold Formalism.G0.countBelow
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun U => by simp

end GlobalTheory.SplitCosetCount

namespace GlobalTheory.SplitCosetCount

open Classical
open Formalism.IndefR.Lev GlobalTheory.HeckeParts Formalism.L2.NTheta

set_option maxHeartbeats 1000000 in

theorem card_cosets : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))), Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → k ≤ D.R.r →
    IsHeckeAt (Wc D i) P k α → Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Rc.card = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm P.asIdeal) D.R.r k := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hk hα hRc
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨e, ϖ, he, h1, h2, hαe⟩ := hα
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨v, π, s, c1, c2, c3, c4, c5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis (Wc D i) e v π s he.1.1 c2 c3 c4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module (Wc D i)).2
  obtain ⟨hex, hinj⟩ := GlobalTheory.SplitPlace.comp_bij (V := Wc D i) (B := B) he.1 c1 c2
  have hKc := fun g => GlobalTheory.SplitPlace.K_iff (V := Wc D i) (g := g) he.1 c2 c3 hB
  have hu := GlobalTheory.SplitPlace.isUnif he c4 c5 ϖ h1 h2
  obtain ⟨hu0, hu1⟩ := GlobalTheory.SplitPlace.unif_facts hu
  have hH := (GlobalTheory.SplitPlace.hecke_iff he.1 c1 c2 c3 c4 hB hu0 k α).1 hαe

  obtain ⟨w, hw⟩ : ∃ w, π (finPart D (incA D (ϖ : D.host.E))) = w := ⟨_, rfl⟩
  rw [hw] at hu hu0 hu1 hH
  have hirr : Irreducible (⟨w, hu1⟩ : Formalism.UG.Ov D.host.F v) :=
    Formalism.IndefR.Fin.HCount.irreducible_of_unif D.host.F v ⟨w, hu1⟩ hu
  have hv0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have htype : Formalism.IndefR.Fin.HCount.IsType (Formalism.UG.Ov D.host.F v) ⟨w, hu1⟩ k
      (GlobalTheory.SplitPlace.comp (Wc D i) π B α) := by
    refine ⟨fun a b => hH.2.1 a b, fun a b => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact hH.2.2.1 a b
    · obtain ⟨d, hd⟩ : ∃ d, (GlobalTheory.SplitPlace.comp (Wc D i) π B α).1.det = d := ⟨_, rfl⟩
      have hdv' := hH.2.2.2
      rw [hd] at hdv'
      have hdv : Valued.v (d / w ^ k) = 1 := by
        rw [map_div₀, map_pow, hdv', div_self (pow_ne_zero _ hv0)]
      have hne : d / w ^ k ≠ 0 := fun h => by rw [h, map_zero] at hdv; exact zero_ne_one hdv
      have hm : d / w ^ k ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)) ≤ 1; exact le_of_eq hdv
      have hmi : (d / w ^ k)⁻¹ ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)⁻¹) ≤ 1; rw [map_inv₀, hdv, inv_one]
      refine ⟨⟨d / w ^ k, hm⟩, isUnit_iff_exists_inv.2 ⟨⟨_, hmi⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩, ?_⟩
      show _ = w ^ k * (d / w ^ k)
      rw [hd, mul_div_cancel₀ _ (pow_ne_zero _ hu0)]

  obtain ⟨R₀, hR₀⟩ := GlobalTheory.SplitPlace.exists_reps (Formalism.UG.Final.GLintComm D.host.F v (Wc D i).rank)
    (GlobalTheory.SplitPlace.comp (Wc D i) π B α)
  have hc0 := Formalism.IndefR.Fin.HCount.card_reps (Formalism.UG.Ov D.host.F v) hirr htype (R := R₀) hR₀
  choose ψ hψs hψ using hex
  have hl := lift_isReps (ρ := GlobalTheory.SplitPlace.comp (Wc D i) π B) (S := SuppAt e (Wc D i))
    (K := (KsphC (Wc D i) ∅ : Set (GA D (Wc D i)))) (fun _ _ => GlobalTheory.SplitPlace.suppAt_mul)
    (fun _ => GlobalTheory.SplitPlace.suppAt_inv) hinj hKc hH.1 hR₀ ψ hψs hψ
  have hdc : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α (R₀.image ψ) := by
    refine isDC_of_splits hs levG_le_flag ((hLp α).2 hH.1) (fun a ha => ?_) hK hl.1 hl.2
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 ha
    exact (hLp _).2 (hψs b)
  let φ : D.host.E →+* v.adicCompletion D.host.F := (π.comp (finPart D)).comp (incA D)
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, map_mul, c4]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  have hq : Fintype.card (IsLocalRing.ResidueField (Formalism.UG.Ov D.host.F v)) = Ideal.absNorm P.asIdeal := by
    rw [← Nat.card_eq_fintype_card]
    exact GlobalTheory.SplitUnif.card_residueField v φ P c5 hP
  rw [card_eq_of_isDC hRc hdc, card_image_section ψ hψ, hc0, gaussBinom_eq, hq, rank_Wc]

end GlobalTheory.SplitCosetCount
