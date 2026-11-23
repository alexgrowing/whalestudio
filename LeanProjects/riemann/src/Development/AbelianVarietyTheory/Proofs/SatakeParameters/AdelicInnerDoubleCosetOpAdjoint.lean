import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightedFibreSumsEq
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory
namespace DoubleCosetAdjoint

variable {G : Type} [Group G]

def Rel (J L : Subgroup G) (x : G) (u v : G ⧸ J) : Prop :=
  ∃ h a : G, a ∈ L ∧ (∃ k₁ k₂ : J, a = (k₁ : G) * x * k₂) ∧ u = (h : G ⧸ J) ∧ v = ((h * a : G) : G ⧸ J)

theorem Rel.symm {J L : Subgroup G} {x : G} {u v : G ⧸ J} (h : Rel J L x u v) : Rel J L x⁻¹ v u := by
  obtain ⟨h, a, ha, ⟨k₁, k₂, hk⟩, rfl, rfl⟩ := h
  refine ⟨h * a, a⁻¹, L.inv_mem ha, ⟨k₂⁻¹, k₁⁻¹, ?_⟩, rfl, by simp⟩
  rw [hk]; simp [mul_assoc]

theorem rel_iff {J L : Subgroup G} {x : G} {A : Finset G} (hL : ∀ a ∈ A, a ∈ L) (hA : IsDC J x A)
    (y : G) (v : G ⧸ J) : Rel J L x (y : G ⧸ J) v ↔ ∃ a ∈ A, v = ((y * a : G) : G ⧸ J) := by
  constructor
  · rintro ⟨h, b, -, ⟨k₁, k₂, hk⟩, hy, rfl⟩
    have hy' : y⁻¹ * h ∈ J := QuotientGroup.eq.1 hy
    obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hA.2 (y⁻¹ * h * b) ⟨⟨_, hy'⟩ * k₁, k₂, by rw [hk]; simp [mul_assoc]⟩
    refine ⟨a, ha, (QuotientGroup.eq.2 ?_).symm⟩
    simpa [mul_assoc] using ha'
  · rintro ⟨a, ha, rfl⟩
    exact ⟨y, a, hL a ha, hA.1 a ha, rfl, rfl⟩

theorem injOn_coset {J : Subgroup G} {x : G} {A : Finset G} (hA : IsDC J x A) (y : G) :
    Set.InjOn (fun a : G => ((y * a : G) : G ⧸ J)) (A : Set G) := by
  intro a ha a' ha' h
  have h' : (y * a)⁻¹ * (y * a') ∈ J := QuotientGroup.eq.1 h
  have h'' : a⁻¹ * a' ∈ J := by simpa [mul_assoc] using h'
  exact (hA.2 a' (hA.1 a' ha')).unique ⟨ha, h''⟩ ⟨ha', by simp⟩

theorem char_eq {J L : Subgroup G} (χ : J →* ℂˣ)
    (hd : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {a b : G} (ha : a ∈ L) (hb : b ∈ L) (k k' : J)
    (h : (k : G) * b = a * k') : χ k = χ k' := by
  obtain ⟨k₁, h₁, k₂, h₂, hL, hk, hc⟩ := hd k k.2
  obtain ⟨m₁, g₁, m₂, g₂, gL, gk, -⟩ := hd k' k'.2
  have e1 : k = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := Subtype.ext hk
  have e2 : k' = ⟨m₁, g₁⟩ * ⟨m₂, g₂⟩ := Subtype.ext gk
  have e3 : k₂ * m₂⁻¹ = (k₁ * b)⁻¹ * (a * m₁) := by
    rw [hk, gk, mul_assoc, (hc b hb).eq] at h
    have : k₂ = (k₁ * b)⁻¹ * (a * (m₁ * m₂)) := by rw [← h]; group
    rw [this]; group
  have e4 : χ (⟨k₂, h₂⟩ * ⟨m₂, g₂⟩⁻¹) = 1 := hχ _ (by
    show k₂ * m₂⁻¹ ∈ L
    rw [e3]; exact L.mul_mem (L.inv_mem (L.mul_mem hL hb)) (L.mul_mem ha gL))
  rw [map_mul, map_inv, mul_inv_eq_one] at e4
  rw [e1, e2, map_mul, map_mul, hχ ⟨k₁, h₁⟩ hL, hχ ⟨m₁, g₁⟩ gL, e4]

theorem exists_pairing {Γ W : Type} [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) {J L : Subgroup G} (χ : J →* ℂˣ) (x : G)
    (hn : ∀ k, ‖(χ k : ℂ)‖ = 1)
    (hd : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ)
    (hF' : F' ∈ AdForms ι ρ J χ) :
    ∃ φ : (G ⧸ J) × (G ⧸ J) → ℂ, ∀ h a : G, a ∈ L → (∃ k₁ k₂ : J, a = (k₁ : G) * x * k₂) →
      φ ((h : G ⧸ J), ((h * a : G) : G ⧸ J)) = inner ℂ (F (h * a)) (F' h) := by
  classical
  refine ⟨fun z => if H : Rel J L x z.1 z.2 then
    inner ℂ (F (H.choose * H.choose_spec.choose)) (F' H.choose) else 0, ?_⟩
  intro h a ha hx
  have H : Rel J L x (h : G ⧸ J) ((h * a : G) : G ⧸ J) := ⟨h, a, ha, hx, rfl, rfl⟩
  simp only [dif_pos H]
  obtain ⟨hb, -, e1, e2⟩ := H.choose_spec.choose_spec
  generalize H.choose_spec.choose = b at hb e2 ⊢
  generalize H.choose = g at e1 e2 ⊢
  have f1 : h⁻¹ * g ∈ J := QuotientGroup.eq.1 e1
  have f2 : (h * a)⁻¹ * (g * b) ∈ J := QuotientGroup.eq.1 e2
  have c := char_eq χ hd hχ ha hb ⟨_, f1⟩ ⟨_, f2⟩ (by simp [mul_assoc])
  have u1 := hF 1 (h * a) ⟨_, f2⟩
  have u2 := hF' 1 h ⟨_, f1⟩
  simp only [map_one, one_mul, mul_inv_cancel_left, Module.End.one_apply] at u1 u2
  rw [u1, u2, c, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hn]
  simp

omit [Group G] in
theorem finsum_fibre {Q : Type} {P : Q → Prop} (s : Set {z // P z}) (A : Finset G) (m : G → Q)
    (hm : Set.InjOn m (A : Set G)) (hs : Subtype.val '' s = m '' (A : Set G)) (φ : Q → ℂ) :
    s.Finite ∧ ∑ᶠ z ∈ s, φ z.1 = ∑ a ∈ A, φ (m a) := by
  constructor
  · refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    rw [hs]; exact A.finite_toSet.image _
  · rw [← finsum_mem_image Subtype.val_injective.injOn, hs, finsum_mem_image hm,
      finsum_mem_coe_finset]

end DoubleCosetAdjoint

open DoubleCosetAdjoint in

theorem adInner_dcOp_adjoint : ∀ {G Γ W I : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J L : Subgroup G) (χ : J →* ℂˣ) (y : I → G) (x : G) (A A' : Finset G), (∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') → (∀ k, ‖(χ k : ℂ)‖ = 1) → IsReps ι J y → (∀ i, Finite (stab ι J (y i))) → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J x⁻¹ A' → ∀ F ∈ AdForms ι ρ J χ, ∀ F' ∈ AdForms ι ρ J χ, adInner ι J y (dcOp A F) F' = adInner ι J y F (dcOp A' F') := by
  intro G Γ W I _ _ _ _ _ ι ρ J L χ y x A A' hρ hn hy hfin hd hχ hA hA' hD hD' F hF F' hF'
  obtain ⟨φ, hφ⟩ := exists_pairing ι ρ χ x hn hd hχ hF hF'
  letI : MulAction Γ (G ⧸ J) := MulAction.compHom (G ⧸ J) ι
  have hs : ∀ (γ : Γ) (g : G), γ • (g : G ⧸ J) = ((ι γ * g : G) : G ⧸ J) := fun _ _ => rfl
  let S : SubMulAction Γ ((G ⧸ J) × (G ⧸ J)) :=
    { carrier := {z | Rel J L x z.1 z.2}
      smul_mem' := by
        rintro γ ⟨u, v⟩ ⟨h, a, ha, hx, e1, e2⟩
        refine ⟨ι γ * h, a, ha, hx, ?_, ?_⟩
        · show γ • u = _
          rw [show u = _ from e1, hs]
        · show γ • v = _
          rw [show v = _ from e2, hs, mul_assoc] }
  have hst : ∀ g : G, MulAction.stabilizer Γ (g : G ⧸ J) = stab ι J g := by
    intro g
    ext γ
    rw [MulAction.mem_stabilizer_iff, hs, eq_comm, QuotientGroup.eq, mem_stab, mul_assoc]
  have horb : ∀ u : G ⧸ J, ∃! i, u ∈ MulAction.orbit Γ ((y i : G) : G ⧸ J) := by
    intro u
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective u
    refine (existsUnique_congr fun i => ?_).1 (hy h)
    constructor
    · rintro ⟨γ, k, rfl⟩
      exact ⟨γ, by simp only [hs]; exact (QuotientGroup.mk_mul_of_mem _ k.2).symm⟩
    · rintro ⟨γ, hγ⟩
      simp only [hs] at hγ
      exact ⟨γ, ⟨_, QuotientGroup.eq.1 hγ⟩, by simp only [mul_inv_cancel_left]⟩
  have hf : ∀ i, Finite (MulAction.stabilizer Γ ((y i : G) : G ⧸ J)) := fun i => by
    rw [hst]; exact hfin i
  have h1 := fun g : G => finsum_fibre (P := fun z => z ∈ S) {z | z.1.1 = (g : G ⧸ J)} A
    (fun a => ((g : G ⧸ J), ((g * a : G) : G ⧸ J)))
    (fun a ha a' ha' h => injOn_coset hD g ha ha' (congrArg Prod.snd h)) (by
      ext ⟨u, v⟩
      constructor
      · rintro ⟨⟨z, hz⟩, hz', rfl⟩
        obtain rfl : u = _ := hz'
        obtain ⟨a, ha, e⟩ := (rel_iff hA hD g v).1 hz
        exact ⟨a, ha, by rw [e]⟩
      · rintro ⟨a, ha, e⟩
        exact ⟨⟨(_, _), (rel_iff hA hD g _).2 ⟨a, ha, rfl⟩⟩, rfl, e⟩) φ
  have h2 := fun g : G => finsum_fibre (P := fun z => z ∈ S) {z | z.1.2 = (g : G ⧸ J)} A'
    (fun a => (((g * a : G) : G ⧸ J), (g : G ⧸ J)))
    (fun a ha a' ha' h => injOn_coset hD' g ha ha' (congrArg Prod.fst h)) (by
      ext ⟨u, v⟩
      constructor
      · rintro ⟨⟨z, hz⟩, hz', rfl⟩
        obtain rfl : v = _ := hz'
        obtain ⟨a, ha, e⟩ := (rel_iff hA' hD' g u).1 (Rel.symm hz)
        exact ⟨a, ha, by rw [e]⟩
      · rintro ⟨a, ha, e⟩
        have := ((rel_iff hA' hD' g _).2 ⟨a, ha, rfl⟩).symm
        rw [inv_inv] at this
        exact ⟨⟨(_, _), this⟩, rfl, e⟩) φ
  have key := weighted_fibre_sums_eq (Γ := Γ) (Z := S) (fun z => z.1.1) (fun z => z.1.2)
    (fun i => ((y i : G) : G ⧸ J)) (fun i => ((y i : G) : G ⧸ J)) (fun z => φ z.1)
    (fun _ _ => rfl) (fun _ _ => rfl) horb horb hf hf (fun i => (h1 _).1) (fun i => (h2 _).1) (by
      rintro γ ⟨⟨u, v⟩, h, a, ha, hx, e1, e2⟩
      obtain rfl : u = _ := e1
      obtain rfl : v = _ := e2
      show φ (γ • (h : G ⧸ J), γ • ((h * a : G) : G ⧸ J)) = φ (_, _)
      rw [hs, hs, ← mul_assoc, hφ _ a ha hx, hφ _ a ha hx]
      have u1 := hF γ (h * a) 1
      have u2 := hF' γ h 1
      simp only [map_one, OneMemClass.coe_one, mul_one, Units.val_one, one_smul] at u1 u2
      rw [mul_assoc, u1, u2, hρ])
  simp only [(h1 _).2, (h2 _).2, hst] at key
  unfold adInner dcOp
  convert key using 3 with i _ i _
  · rw [sum_inner]
    exact Finset.sum_congr rfl fun a ha => (hφ _ a (hA a ha) (hD.1 a ha)).symm
  · rw [inner_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨k₁, k₂, hk⟩ := hD'.1 a ha
    have := hφ (y i * a) a⁻¹ (L.inv_mem (hA' a ha)) ⟨k₂⁻¹, k₁⁻¹, by rw [hk]; simp [mul_assoc]⟩
    rw [mul_inv_cancel_right] at this
    exact this.symm

end GlobalTheory
