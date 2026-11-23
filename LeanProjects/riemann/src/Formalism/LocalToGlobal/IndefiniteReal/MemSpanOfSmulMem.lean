import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer.Lat

open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer

section

variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] in
theorem mem_cut {A : Submodule (𝓞 K) V} {p : V →ₗ[K] V} (hp : ∀ a, p (p a) = p a) {a : V} :
    a ∈ cut A p ↔ a ∈ A ∧ p a = a := by
  unfold cut
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_range]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨a, h⟩⟩
  rintro ⟨z, rfl⟩
  exact hp z

theorem exists_smul_mem {A : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (A : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K
    (A : Set V) x hx
  refine ⟨t, nonZeroDivisors.coe_ne_zero t, ?_⟩
  rw [Submodule.span_eq] at ht
  exact ht

theorem mem_span_of_smul_mem {A : Submodule (𝓞 K) V} {x : V} {d : 𝓞 K} (hd : d ≠ 0)
    (hx : d • x ∈ A) : x ∈ Submodule.span K (A : Set V) := by
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have h1 : x = (d : K)⁻¹ • (d • x) := by
    rw [← IsScalarTower.algebraMap_smul K d x, smul_smul]
    simp [hdK]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem span_cut {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (p : V →ₗ[K] V) : Submodule.span K (cut A p : Set V) = LinearMap.range p := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro a ha
    exact ha.2
  · intro u hu
    obtain ⟨d, hd, hdu⟩ := exists_smul_mem (A := A) (x := u) (by rw [hA]; trivial)
    refine mem_span_of_smul_mem hd ⟨hdu, ?_⟩
    have : d • u = (d : K) • u := (IsScalarTower.algebraMap_smul K d u).symm
    change d • u ∈ LinearMap.range p
    rw [this]
    exact Submodule.smul_mem _ _ hu

theorem rkK_cut {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (p : V →ₗ[K] V) : rkK (cut A p) = finrank K (LinearMap.range p) := by
  unfold rkK
  rw [span_cut hA]

theorem fg_cut {A : Submodule (𝓞 K) V} (hA : A.FG) (p : V →ₗ[K] V) : (cut A p).FG :=
  hA.of_le inf_le_left

omit [NumberField K] in
theorem map_osmul {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (p : V →ₗ[K] W) (d : 𝓞 K) (a : V) : p (d • a) = d • p a := by
  rw [← IsScalarTower.algebraMap_smul K d a, map_smul, IsScalarTower.algebraMap_smul]

end

section

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}

def Tr (p₀ p : V →ₗ[K] V) (x y : Fin n → V →ₗ[K] V) (c : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a, p₀ (p₀ a) = p₀ a) ∧ (∀ a, p (p a) = p a) ∧
  (∀ j a, p₀ a = a → p (x j a) = x j a) ∧ (∀ i a, p a = a → p₀ (y i a) = y i a) ∧
  c.det ≠ 0 ∧ (∀ i j a, p₀ a = a → y i (x j a) = c i j • a) ∧
  (∀ a, p a = a → ∑ j, ∑ i, c⁻¹ j i • x j (y i a) = a)

variable {p₀ p : V →ₗ[K] V} {x y : Fin n → V →ₗ[K] V} {c : Matrix (Fin n) (Fin n) K}

theorem Tr.yx_sum (h : Tr p₀ p x y c) (a : Fin n → V) (ha : ∀ j, p₀ (a j) = a j) (i : Fin n) :
    y i (∑ j, x j (a j)) = ∑ j, c i j • a j := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => h.2.2.2.2.2.1 i j _ (ha j)

theorem Tr.first_axis_injective (h : Tr p₀ p x y c) (a : Fin n → V) (ha : ∀ j, p₀ (a j) = a j)
    (h0 : ∑ j, x j (a j) = 0) : a = 0 := by
  have h1 : ∀ i, ∑ j, c i j • a j = 0 := fun i => by
    rw [← h.yx_sum a ha i, h0, map_zero]
  have hu : IsUnit c.det := isUnit_iff_ne_zero.mpr h.2.2.2.2.1
  funext k
  have h2 : ∑ i, c⁻¹ k i • ∑ j, c i j • a j = a k := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hu, Matrix.one_apply]
    simp
  rw [← h2]
  simp [h1]

theorem Tr.inj_y (h : Tr p₀ p x y c) (a : V) (ha : p a = a) (h0 : ∀ i, y i a = 0) : a = 0 := by
  rw [← h.2.2.2.2.2.2 a ha]
  simp [h0]

theorem Tr.rank [FiniteDimensional K V] (h : Tr p₀ p x y c) :
    finrank K (LinearMap.range p) = n * finrank K (LinearMap.range p₀) := by
  have hfix0 : ∀ a : LinearMap.range p₀, p₀ a = a := by
    rintro ⟨_, z, rfl⟩; exact h.1 z
  have hfix : ∀ a : LinearMap.range p, p a = a := by
    rintro ⟨_, z, rfl⟩; exact h.2.1 z
  have hpi : finrank K (Fin n → LinearMap.range p₀) = n * finrank K (LinearMap.range p₀) := by
    rw [Module.finrank_pi_fintype]; simp
  rw [← hpi]
  apply le_antisymm
  · let Y : LinearMap.range p →ₗ[K] (Fin n → LinearMap.range p₀) :=
      LinearMap.pi fun i => LinearMap.codRestrict _ (y i ∘ₗ (LinearMap.range p).subtype)
        fun a => ⟨_, h.2.2.2.1 i a (hfix a)⟩
    refine LinearMap.finrank_le_finrank_of_injective (f := Y) ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply Subtype.ext
    refine h.inj_y a (hfix a) fun i => ?_
    exact congrArg Subtype.val (congrFun ha i)
  · let X : (Fin n → LinearMap.range p₀) →ₗ[K] LinearMap.range p :=
      LinearMap.codRestrict _ (∑ j, x j ∘ₗ (LinearMap.range p₀).subtype ∘ₗ LinearMap.proj j)
        fun a => by
          rw [LinearMap.sum_apply]
          exact Submodule.sum_mem _ fun j _ => ⟨_, h.2.2.1 j (a j) (hfix0 _)⟩
    refine LinearMap.finrank_le_finrank_of_injective (f := X) ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 := congrArg Subtype.val ha
    simp only [X, LinearMap.codRestrict_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.proj_apply, ZeroMemClass.coe_zero] at h1
    have h2 := h.first_axis_injective (fun j => (a j : V)) (fun j => hfix0 _) h1
    funext j
    exact Subtype.ext (congrFun h2 j)

end

section

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem pe_facts {ε e : V →ₗ[K] V} (hε : ε ∘ₗ ε = ε) (he : e ∘ₗ e = e) (hc : e ∘ₗ ε = ε ∘ₗ e) :
    (∀ a, (ε ∘ₗ e) ((ε ∘ₗ e) a) = (ε ∘ₗ e) a) ∧
    ∀ a, (ε ∘ₗ e) a = a ↔ ε a = a ∧ e a = a := by
  have h1 : ∀ a, ε (ε a) = ε a := fun a => LinearMap.congr_fun hε a
  have h2 : ∀ a, e (e a) = e a := fun a => LinearMap.congr_fun he a
  have h3 : ∀ a, e (ε a) = ε (e a) := fun a => LinearMap.congr_fun hc a
  refine ⟨fun a => ?_, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simp only [LinearMap.comp_apply, h3, h1, h2]
  · simp only [LinearMap.comp_apply] at h
    constructor
    · rw [← h, h1]
    · rw [← h, h3, h2]
  · simp only [LinearMap.comp_apply, h.1, h.2]

theorem tr_of_core (hP : IdemP) {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    {τ : Representation K G T} {H₀ : Subgroup G} {χ₀ : H₀ →* (𝓞 K)ˣ} {H : Subgroup G}
    {χ : H →* (𝓞 K)ˣ} {n : ℕ} {γ δ : Fin n → G} {c : Matrix (Fin n) (Fin n) K}
    {Γ : Matrix (Fin n) (Fin n) (𝓞 K)} (h : CoreData τ H₀ χ₀ H χ γ δ c Γ)
    (ρ : Representation K G V) (he : eS τ ρ ∘ₗ eS τ ρ = eS τ ρ) :
    Tr (epP H₀ χ₀ ρ ∘ₗ eS τ ρ) (epP H χ ρ ∘ₗ eS τ ρ) (fun j => epP H χ ρ ∘ₗ ρ (γ j))
      (fun i => epP H₀ χ₀ ρ ∘ₗ ρ (δ i)) c := by
  obtain ⟨hE, hEp⟩ := hP K G V ρ
  obtain ⟨hc, hcp, -⟩ := hE T τ
  have f0 := pe_facts (hEp H₀ χ₀).1 he (hcp H₀ χ₀)
  have f1 := pe_facts (hEp H χ).1 he (hcp H χ)
  have key : ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G) (a : V), eS τ ρ a = a →
      (epP H χ ρ ∘ₗ eS τ ρ) ((epP H χ ρ ∘ₗ ρ g) a) = (epP H χ ρ ∘ₗ ρ g) a := by
    intro H χ g a ha
    have h1 : ∀ a, epP H χ ρ (epP H χ ρ a) = epP H χ ρ a :=
      fun a => LinearMap.congr_fun (hEp H χ).1 a
    have h2 : ∀ a, eS τ ρ (epP H χ ρ a) = epP H χ ρ (eS τ ρ a) :=
      fun a => LinearMap.congr_fun (hcp H χ) a
    have h3 : eS τ ρ (ρ g a) = ρ g (eS τ ρ a) := LinearMap.congr_fun (hc g) a
    simp only [LinearMap.comp_apply, h2, h1, h3, ha]
  obtain ⟨hd, -, -, hV⟩ := h
  refine ⟨f0.1, f1.1, fun j a ha => key H χ _ a ((f0.2 a).1 ha).2,
    fun i a ha => key H₀ χ₀ _ a ((f1.2 a).1 ha).2, hd, fun i j a ha => (hV V ρ).1 i j a ha,
    fun a ha => (hV V ρ).2 a ha⟩

theorem smul_mem_cut (hP : IdemP) (ρ : Representation K G V) {A : Submodule (𝓞 K) V}
    (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G)
    {p : V →ₗ[K] V} (hp : ∀ a, p (p a) = p a) {a : V} (ha : a ∈ A)
    (hx : p ((epP H χ ρ ∘ₗ ρ g) a) = (epP H χ ρ ∘ₗ ρ g) a) :
    (Fintype.card G : 𝓞 K) • (epP H χ ρ ∘ₗ ρ g) a ∈ cut A p := by
  rw [mem_cut hp]
  refine ⟨((hP K G V ρ).2 H χ).2 A hA _ (hA g a ha), ?_⟩
  rw [map_osmul, hx]

variable {S : Type} [Fintype S] {T : S → Type} [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
  [∀ s, FiniteDimensional K (T s)] {τ : ∀ s, Representation K G (T s)}

theorem sandwich (hE : IdemE) (hP : IdemP) (hτ : IsGood τ) (ρ : Representation K G V)
    {A : Submodule (𝓞 K) V} (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) :
    (∀ s, cut A (epP H χ ρ ∘ₗ eS (τ s) ρ) ≤ cut A (epP H χ ρ ∘ₗ eGood τ ρ)) ∧
    (∀ a ∈ cut A (epP H χ ρ ∘ₗ eGood τ ρ),
      (Fintype.card G : 𝓞 K) • a ∈ ⨆ s, cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) ∧
    ∀ s, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ), eS (τ s) ρ a = a := by
  obtain ⟨he, ho⟩ := hE K G S T τ hτ V ρ
  obtain ⟨hE', hEp⟩ := hP K G V ρ
  have f := fun s => pe_facts (hEp H χ).1 (he s) ((hE' (T s) (τ s)).2.1 H χ)
  have hge : ∀ s a, eGood τ ρ (eS (τ s) ρ a) = eS (τ s) ρ a := by
    intro s a
    classical
    unfold eGood
    rw [LinearMap.sum_apply, Finset.sum_eq_single s]
    · exact LinearMap.congr_fun (he s) a
    · intro t _ hts
      exact LinearMap.congr_fun (ho t s hts) a
    · simp
  refine ⟨fun s a ha => ⟨ha.1, ?_⟩, fun a ha => ?_, fun s a ha => ?_⟩
  · obtain ⟨z, hz⟩ := ha.2
    refine ⟨eS (τ s) ρ z, ?_⟩
    rw [← hz]
    simp only [LinearMap.comp_apply, hge]
  · obtain ⟨haA, z, hz⟩ := ha
    have hz' : a = ∑ s, epP H χ ρ (eS (τ s) ρ z) := by
      rw [← hz]
      simp only [LinearMap.comp_apply, eGood, LinearMap.sum_apply, map_sum]
    have hs : ∀ s, eS (τ s) ρ a = epP H χ ρ (eS (τ s) ρ z) := by
      intro s
      have h2 : ∀ a, eS (τ s) ρ (epP H χ ρ a) = epP H χ ρ (eS (τ s) ρ a) :=
        fun a => LinearMap.congr_fun ((hE' (T s) (τ s)).2.1 H χ) a
      have h3 : eS (τ s) ρ (eGood τ ρ z) = eS (τ s) ρ z := by
        classical
        unfold eGood
        rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single s]
        · exact LinearMap.congr_fun (he s) z
        · intro t _ hts
          exact LinearMap.congr_fun (ho s t hts.symm) z
        · simp
      rw [← hz, LinearMap.comp_apply, h2, h3]
    have : (Fintype.card G : 𝓞 K) • a = ∑ s, (Fintype.card G : 𝓞 K) • eS (τ s) ρ a := by
      rw [← Finset.smul_sum]
      simp only [hs]
      rw [← hz']
    rw [this]
    refine Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s ?_
    rw [mem_cut (f s).1]
    refine ⟨(hE' (T s) (τ s)).2.2 A hA a haA, ?_⟩
    rw [map_osmul, hs]
    exact congrArg _ ((f s).1 z)
  · exact (((f s).2 a).1 ((mem_cut (f s).1).1 ha).2).2

end

end Formalism.IndefR.LatticeTransfer.Lat
