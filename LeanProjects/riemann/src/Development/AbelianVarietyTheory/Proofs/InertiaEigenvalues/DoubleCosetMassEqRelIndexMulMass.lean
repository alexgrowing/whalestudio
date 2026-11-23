import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDcOfCover

noncomputable section
namespace GlobalTheory.UnimodMass
variable {G : Type*} [Group G]

def dcMapLe {Γ W K : Subgroup G} (hWK : W ≤ K) : DC Γ W → DC Γ K :=
  Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)

def dcOfCoset (Γ W K : Subgroup G) (t : G) : K ⧸ W.subgroupOf K → DC Γ W :=
  Quotient.lift (fun k : K => (Quotient.mk (dcSetoid Γ W) (t * k))) (by
    intro a b hab
    apply Quotient.sound
    have h := (QuotientGroup.leftRel_apply).1 hab
    rw [Subgroup.mem_subgroupOf] at h
    refine ⟨1, Γ.one_mem, (a : G)⁻¹ * b, by simpa using h, ?_⟩
    simp [mul_assoc])

theorem dcOfCoset_mk (Γ W K : Subgroup G) (t : G) (k : K) :
    dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) = Quotient.mk (dcSetoid Γ W) (t * k) := rfl

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass

theorem fiber_card_mul_stabCard {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K) (t : G)
    (ht : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) (k : K) :
    Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} *
      stabCard Γ W (t * k) = stabCard Γ K t := by
  classical
  set A := {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}
  set B := {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)}
  set T := {δ : Γ // (t * k)⁻¹ * (δ : G) * (t * k) ∈ W}
  have hT : stabCard Γ W (t * k) = Nat.card T := rfl
  have hA : stabCard Γ K t = Nat.card A := rfl
  let φ : A → K := fun γ => ⟨t⁻¹ * (γ.1 : G) * t, γ.2⟩
  have hα : ∀ γ : A, dcOfCoset Γ W K t ((φ γ * k : K) : K ⧸ W.subgroupOf K) =
      dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
    intro γ
    rw [dcOfCoset_mk, dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨(γ.1 : G)⁻¹, Γ.inv_mem γ.1.2, 1, W.one_mem, ?_⟩
    simp [φ, mul_assoc]
  let α : A → B := fun γ => ⟨(φ γ * k : K), hα γ⟩
  have hsurj : Function.Surjective α := by
    rintro ⟨x, hx⟩
    induction x using QuotientGroup.induction_on with
    | H k' =>
      rw [dcOfCoset_mk, dcOfCoset_mk] at hx
      obtain ⟨γ, hγ, w, hw, e⟩ := Quotient.exact hx

      have hmem : t⁻¹ * γ⁻¹ * t ∈ K := by
        have : t⁻¹ * γ⁻¹ * t = (k' : G) * w * (k : G)⁻¹ := by
          have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
            calc (k : G) = t⁻¹ * (t * k) := by group
              _ = _ := by rw [e]; group
          rw [e']; group
        rw [this]
        exact K.mul_mem (K.mul_mem k'.2 (hWK hw)) (K.inv_mem k.2)
      refine ⟨⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩, ?_⟩
      apply Subtype.ext
      show ((φ _ * k : K) : K ⧸ W.subgroupOf K) = (k' : K ⧸ W.subgroupOf K)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
        calc (k : G) = t⁻¹ * (t * k) := by group
          _ = _ := by rw [e]; group
      have : ((φ ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩ * k)⁻¹ * k' : K) = (w⁻¹ : G) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
        rw [e']; group
      rw [this]; exact W.inv_mem hw
  have hfib : ∀ γ₀ : A, Nonempty ({γ : A // α γ = α γ₀} ≃ T) := by
    intro γ₀
    have key : ∀ γ : A, α γ = α γ₀ ↔ (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) ∈ W := by
      intro γ
      rw [Subtype.ext_iff]
      show ((φ γ * k : K) : K ⧸ W.subgroupOf K) = ((φ γ₀ * k : K) : K ⧸ W.subgroupOf K) ↔ _
      rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((φ γ₀ * k)⁻¹ * (φ γ * k) : K) : G) = (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]; group
      rw [this]
    refine ⟨{ toFun := fun γ => ⟨⟨(γ₀.1 : G)⁻¹ * γ.1.1, Γ.mul_mem (Γ.inv_mem γ₀.1.2) γ.1.1.2⟩, (key γ.1).1 γ.2⟩
              invFun := fun δ => ⟨⟨⟨(γ₀.1 : G) * δ.1, Γ.mul_mem γ₀.1.2 δ.1.2⟩, ?_⟩, ?_⟩
              left_inv := fun γ => by ext; simp
              right_inv := fun δ => by ext; simp }⟩
    · have h1 : t⁻¹ * ((γ₀.1 : G) * δ.1) * t =
          (t⁻¹ * γ₀.1 * t) * ((k : G) * ((t * k)⁻¹ * δ.1 * (t * k)) * (k : G)⁻¹) := by group
      rw [h1]
      exact K.mul_mem γ₀.2 (K.mul_mem (K.mul_mem k.2 (hWK δ.2)) (K.inv_mem k.2))
    · rw [key]
      simpa using δ.2
  have e : A ≃ B × T :=
    (Equiv.sigmaFiberEquiv α).symm.trans
      ((Equiv.sigmaCongrRight (fun b => by
          have hb := hsurj b
          exact Classical.choice (by
            obtain ⟨γ₀, hγ₀⟩ := hb
            subst hγ₀
            exact hfib γ₀))).trans (Equiv.sigmaEquivProd B T))
  rw [hT, hA, Nat.card_congr e, Nat.card_prod]

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass
open scoped BigOperators

theorem dcOfCoset_surj {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (d : DC Γ W) (hd : dcMapLe hWK d = Quotient.mk (dcSetoid Γ K) t) :
    ∃ k : K, d = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
  induction d using Quotient.inductionOn with
  | h g =>
    have h2 : (dcSetoid Γ K) g t := Quotient.exact hd
    obtain ⟨γ, hγ, κ, hκ, e⟩ := (dcSetoid Γ K).iseqv.symm h2
    refine ⟨⟨κ, hκ⟩, ?_⟩
    rw [dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨γ⁻¹, Γ.inv_mem hγ, 1, W.one_mem, ?_⟩
    simp [e, mul_assoc]

theorem dcMapLe_dcOfCoset {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (x : K ⧸ W.subgroupOf K) : dcMapLe hWK (dcOfCoset Γ W K t x) = Quotient.mk (dcSetoid Γ K) t := by
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [dcOfCoset_mk]
    apply Quotient.sound
    exact ⟨1, Γ.one_mem, (k : G)⁻¹, K.inv_mem k.2, by simp⟩

theorem mass_eq_relIndex_mul {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K)
    (hW : Finite (DC Γ W)) (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    W.relIndex K ≠ 0 ∧ mass Γ W = (W.relIndex K : ℚ) * mass Γ K := by
  classical
  haveI := hW
  haveI : Finite (DC Γ K) := finite_dc_of_le hWK

  have hfibre : ∀ d : DC Γ W, Finite {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K 1 x = d} := by
    intro d
    by_cases hne : ∃ x : K ⧸ W.subgroupOf K, dcOfCoset Γ W K 1 x = d
    · obtain ⟨x, rfl⟩ := hne
      induction x using QuotientGroup.induction_on with
      | H k =>
        have h1 := fiber_card_mul_stabCard Γ W K hWK 1 (hfin 1) k
        have h2 := stabCard_pos (Γ := Γ) (K := K) 1 (hfin 1)
        have h3 : 0 < Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)} := by
          rcases Nat.eq_zero_or_pos (Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)}) with h | h
          · rw [h, zero_mul] at h1; omega
          · exact h
        exact (Nat.card_pos_iff.1 h3).2
    · push_neg at hne
      exact Finite.of_injective (β := Empty) (fun x => (hne x.1 x.2).elim) (fun x => (hne x.1 x.2).elim)
  haveI : Finite (K ⧸ W.subgroupOf K) :=
    Finite.of_equiv _ (Equiv.sigmaFiberEquiv (dcOfCoset Γ W K 1))
  have hidx : W.relIndex K = Nat.card (K ⧸ W.subgroupOf K) := rfl
  have hne0 : W.relIndex K ≠ 0 := by
    rw [hidx]; exact Nat.card_ne_zero.2 ⟨⟨(1 : K)⟩, inferInstance⟩
  refine ⟨hne0, ?_⟩
  haveI := Fintype.ofFinite (DC Γ W)
  haveI := Fintype.ofFinite (DC Γ K)
  haveI := Fintype.ofFinite (K ⧸ W.subgroupOf K)

  have hfib : ∀ c : DC Γ K,
      ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c), ((stabCard Γ W d.out : ℕ) : ℚ)⁻¹ =
        (W.relIndex K : ℚ) * ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹ := by
    intro c
    set t := c.out with htdef
    have hct : c = Quotient.mk (dcSetoid Γ K) t := (Quotient.out_eq c).symm
    have hsK : (0 : ℚ) < stabCard Γ K t := by exact_mod_cast stabCard_pos t (hfin t)
    have hcard : (W.relIndex K : ℚ) = ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c),
        ((Finset.univ.filter (fun x => dcOfCoset Γ W K t x = d)).card : ℚ) := by
      rw [hidx, Nat.card_eq_fintype_card, ← Finset.card_univ]
      rw [Finset.card_eq_sum_card_fiberwise (f := dcOfCoset Γ W K t)
        (t := Finset.univ.filter (fun d => dcMapLe hWK d = c))]
      · push_cast; rfl
      · intro x _
        simp [dcMapLe_dcOfCoset, hct]
    rw [hcard, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    obtain ⟨k, rfl⟩ := dcOfCoset_surj hWK t _ (hd.trans hct)
    have h1 := fiber_card_mul_stabCard Γ W K hWK t (hfin t) k
    rw [dcOfCoset_mk, stabCard_out]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← dcOfCoset_mk]
    have hsW : (0 : ℚ) < stabCard Γ W (t * k) := by
      have := stabCard_pos t (hfin t)
      rcases Nat.eq_zero_or_pos (stabCard Γ W (t * k)) with h | h
      · rw [h, mul_zero] at h1; omega
      · exact_mod_cast h
    have h1' : (Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x =
        dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} : ℚ) * stabCard Γ W (t * k) = stabCard Γ K t := by
      exact_mod_cast h1
    field_simp
    linarith [h1']
  unfold mass
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ (dcMapLe hWK)]
  exact Finset.sum_congr rfl (fun c _ => hfib c)

end GlobalTheory.UnimodMass
