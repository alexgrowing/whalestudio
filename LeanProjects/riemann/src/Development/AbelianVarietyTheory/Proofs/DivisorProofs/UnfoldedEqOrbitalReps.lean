import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEquivLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassFormulaConjugationActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumLocalParts

open scoped Classical

namespace GlobalTheory.FinTrace

theorem unfolded_eq_orbital : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  {c : ConjClasses Γ | ∃ g : G, f (g⁻¹ * (Quotient.out c : Γ) * g) ≠ 0}.Finite ∧
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ) =
  ∑ᶠ c : ConjClasses Γ, LinearMap.trace ℂ W (ξ (Quotient.out c)) *
    ∑ᶠ y : DoubleCoset.Quotient ((Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) : Set G) (K : Set G),
      (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)}) K y.out) : ℂ)) *
        f (y.out⁻¹ * (Quotient.out c : Γ) * y.out) := by
  intro G _ Γ K W _ _ _ ξ hfin hloc f hf hsupp
  have hR : ∀ k ∈ K, ∀ g, f (g * k) = f g := fun k hk g => by simpa using hf 1 K.one_mem k hk g
  have hmk : ∀ (g : G) (y : G), f (((QuotientGroup.mk g : G ⧸ K).out)⁻¹ * y * (QuotientGroup.mk g : G ⧸ K).out)
      = f (g⁻¹ * y * g) := by
    intro g y
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, mul_inv_rev, show (k : G)⁻¹ * g⁻¹ * y * (g * k) = (k : G)⁻¹ * (g⁻¹ * y * g) * k by group]
    exact hf _ (K.inv_mem k.2) _ k.2 _
  let Φ : (Γ → ℂ) → Γ → G ⧸ K → ℂ := fun χ γ x => f (x.out⁻¹ * γ * x.out) * χ γ
  have hΦmk : ∀ χ γ (g : G), Φ χ γ (QuotientGroup.mk g) = f (g⁻¹ * γ * g) * χ γ := fun χ γ g => by
    simp only [Φ, hmk]
  have hinv : ∀ (χ : Γ → ℂ), (∀ δ γ : Γ, χ (δ * γ * δ⁻¹) = χ γ) → ∀ δ γ : Γ, ∀ x : G ⧸ K,
      Φ χ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ χ γ x := by
    intro χ hχ δ γ x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, hΦmk, hΦmk, hχ]
      congr 2
      simp only [smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have htr : ∀ δ γ : Γ, LinearMap.trace ℂ W (ξ (δ * γ * δ⁻¹)) = LinearMap.trace ℂ W (ξ γ) := by
    intro δ γ
    rw [map_mul ξ, map_mul ξ, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul ξ, inv_mul_cancel, map_one, one_mul]
  have hstab : ∀ (H : Subgroup G) (x : G ⧸ K), H ≤ Γ → Finite (MulAction.stabilizer H x) := by
    intro H x hH
    obtain ⟨e⟩ := GlobalTheory.FinTrace.stabilizer_equiv_locPart G H K x.out
    rw [QuotientGroup.out_eq'] at e
    have hle : GlobalTheory.LKLoc.locPart H K x.out ≤ GlobalTheory.LKLoc.locPart Γ K x.out := inf_le_inf_right _ hH
    haveI : Finite (GlobalTheory.LKLoc.locPart H K x.out) :=
      Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    exact Finite.of_equiv _ e.symm
  have hsuppΦ : ∀ χ (x : G ⧸ K), (Function.support fun γ : Γ => Φ χ γ x).Finite := by
    intro χ x
    induction x using QuotientGroup.induction_on with
    | H g =>
      refine (GlobalTheory.FinTrace.finite_support_conj G Γ K f hR hsupp g (hloc g)).subset fun γ hγ => ?_
      simp only [Function.mem_support, hΦmk] at hγ ⊢
      exact left_ne_zero_of_mul hγ
  have hOrb : Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K)) := by
    refine Finite.of_surjective (fun q : DoubleCoset.Quotient (Γ : Set G) (K : Set G) =>
      (Quotient.mk _ (QuotientGroup.mk (Quotient.out q) : G ⧸ K) : MulAction.orbitRel.Quotient Γ (G ⧸ K))) ?_
    intro a
    induction a using Quotient.inductionOn with
    | h x =>
    induction x using QuotientGroup.induction_on with
    | H g =>
    obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
    refine ⟨DoubleCoset.mk Γ K g, Quotient.sound ⟨⟨h, hh⟩, ?_⟩⟩
    show (h : G) • (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk (Quotient.out (DoubleCoset.mk Γ K g))
    rw [MulAction.Quotient.smul_mk, e, QuotientGroup.eq]
    simpa [smul_eq_mul, mul_assoc] using hk
  obtain ⟨-, hcE⟩ := GlobalTheory.T.massFormula_conjugation_action G (G ⧸ K) Γ (Φ fun γ => LinearMap.trace ℂ W (ξ γ))
    (hinv (fun γ => LinearMap.trace ℂ W (ξ γ)) htr) hOrb (fun x => hstab Γ x le_rfl) (hsuppΦ _)
  obtain ⟨hcF, -⟩ := GlobalTheory.T.massFormula_conjugation_action G (G ⧸ K) Γ (Φ fun _ => 1)
    (hinv (fun _ => 1) fun _ _ => rfl) hOrb (fun x => hstab Γ x le_rfl) (hsuppΦ _)
  refine ⟨hcF.subset fun c hc => ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hc
    exact ⟨QuotientGroup.mk g, by rw [hΦmk (fun _ => 1) (Quotient.out c) g, mul_one]; exact hg⟩
  let F : G ⧸ K → ℂ := fun x => ∑ᶠ γ : Γ, Φ (fun γ => LinearMap.trace ℂ W (ξ γ)) γ x
  have hFinv : ∀ h : Γ, ∀ x : G ⧸ K, F (h • x) = F x := by
    intro h x
    calc F (h • x) = ∑ᶠ γ : Γ, Φ (fun γ => LinearMap.trace ℂ W (ξ γ)) (MulAut.conj h γ) ((h : G) • x) :=
          (finsum_comp_equiv (MulAut.conj h).toEquiv).symm
      _ = F x := finsum_congr fun γ => hinv (fun γ => LinearMap.trace ℂ W (ξ γ)) htr h γ x
  have hL : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ∑ᶠ γ : Γ, f ((Quotient.out q)⁻¹ * γ * Quotient.out q) * LinearMap.trace ℂ W (ξ γ) =
        F (QuotientGroup.mk (Quotient.out q)) := fun q => finsum_congr fun γ => (hΦmk (fun γ => LinearMap.trace ℂ W (ξ γ)) γ (Quotient.out q)).symm
  simp_rw [hL]
  rw [GlobalTheory.T.orbit_sum_local_parts G Γ K F hFinv]
  refine Eq.trans hcE ?_
  refine finsum_congr fun c => ?_
  set Hc : Subgroup G := Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} with hHc
  have hcinv : ∀ h : Hc, ∀ x : G ⧸ K, Φ (fun γ => LinearMap.trace ℂ W (ξ γ)) (Quotient.out c) (h • x) =
      Φ (fun γ => LinearMap.trace ℂ W (ξ γ)) (Quotient.out c) x := by
    intro h x
    let δ : Γ := ⟨h, h.2.1⟩
    have hδ : δ * Quotient.out c * δ⁻¹ = Quotient.out c := by
      have hm := Subgroup.mem_centralizer_iff.mp h.2.2 _ (Set.mem_singleton _)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, δ]
      rw [← hm]; group
    have := hinv (fun γ => LinearMap.trace ℂ W (ξ γ)) htr δ (Quotient.out c) x
    rw [hδ] at this
    exact this
  rw [mul_finsum]
  refine (GlobalTheory.T.orbit_sum_local_parts G Hc K _ hcinv).symm.trans (finsum_congr fun y => ?_)
  rw [hΦmk (fun γ => LinearMap.trace ℂ W (ξ γ)) (Quotient.out c) (Quotient.out y)]; ring

theorem card_locPart_conj {G : Type} [Group G] (A B K : Subgroup G) (a g : G) {k : G} (hk : k ∈ K)
    (hAB : ∀ y, y ∈ A ↔ a⁻¹ * y * a ∈ B) :
    Nat.card (GlobalTheory.LKLoc.locPart A K (a * g * k)) = Nat.card (GlobalTheory.LKLoc.locPart B K g) := by
  have hEq : GlobalTheory.LKLoc.locPart A K (a * g * k) = (GlobalTheory.LKLoc.locPart B K g).map (MulAut.conj a).toMonoidHom := by
    ext y
    simp only [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨hyA, k', hk', e⟩
      refine ⟨a⁻¹ * y * a, ⟨(hAB y).1 hyA, k * k' * k⁻¹, K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk), ?_⟩, by group⟩
      rw [← e]; group
    · rintro ⟨z, ⟨hzB, k', hk', e⟩, rfl⟩
      refine ⟨(hAB _).2 (by convert hzB using 1; group), k⁻¹ * k' * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hk') hk, ?_⟩
      rw [← e]; group
  rw [hEq]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (fun x y h => (MulAut.conj a).injective h)).toEquiv.symm

theorem finsum_doubleCoset_conj {G : Type} [Group G] (A B K : Subgroup G) (f : G → ℂ)
    (hf : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) (a ρA ρB : G)
    (hAB : ∀ y, y ∈ A ↔ a⁻¹ * y * a ∈ B) (hA : ∀ y ∈ A, y * ρA = ρA * y) (hρ : a⁻¹ * ρA * a = ρB) :
    ∑ᶠ q : DoubleCoset.Quotient (A : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart A K (Quotient.out q)) : ℂ)) * f ((Quotient.out q)⁻¹ * ρA * Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (B : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart B K (Quotient.out q)) : ℂ)) * f ((Quotient.out q)⁻¹ * ρB * Quotient.out q) := by
  let F : DoubleCoset.Quotient (B : Set G) (K : Set G) → DoubleCoset.Quotient (A : Set G) (K : Set G) :=
    fun q => DoubleCoset.mk A K (a * Quotient.out q)
  have hB : ∀ y, y ∈ B → a * y * a⁻¹ ∈ A := fun y hy => (hAB _).2 (by convert hy using 1; group)
  have hbij : Function.Bijective F := by
    constructor
    · intro q1 q2 h
      rw [DoubleCoset.eq] at h
      obtain ⟨h', hh', k, hk, e⟩ := h
      rw [← DoubleCoset.out_eq' B K q1, ← DoubleCoset.out_eq' B K q2, DoubleCoset.eq]
      refine ⟨a⁻¹ * h' * a, (hAB h').1 hh', k, hk, ?_⟩
      calc Quotient.out q2 = a⁻¹ * (a * Quotient.out q2) := by group
        _ = _ := by rw [e]; group
    · intro p
      refine ⟨DoubleCoset.mk B K (a⁻¹ * Quotient.out p), ?_⟩
      obtain ⟨b, k, hb, hk, e⟩ := DoubleCoset.mk_out_eq_mul B K (a⁻¹ * Quotient.out p)
      show DoubleCoset.mk A K (a * Quotient.out (DoubleCoset.mk B K (a⁻¹ * Quotient.out p))) = p
      conv_rhs => rw [← DoubleCoset.out_eq' A K p]
      rw [e, DoubleCoset.eq]
      refine ⟨(a * b * a⁻¹)⁻¹, A.inv_mem (hB b hb), k⁻¹, K.inv_mem hk, by group⟩
  rw [← finsum_comp_equiv (Equiv.ofBijective F hbij)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.ofBijective_apply, F]
  obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul A K (a * Quotient.out q)
  rw [e, show h * (a * Quotient.out q) * k = (h * a) * Quotient.out q * k by group]
  have hAB' : ∀ y, y ∈ A ↔ (h * a)⁻¹ * y * (h * a) ∈ B := by
    intro y
    rw [show (h * a)⁻¹ * y * (h * a) = a⁻¹ * (h⁻¹ * y * h) * a by group, ← hAB]
    constructor
    · intro hy; exact A.mul_mem (A.mul_mem (A.inv_mem hh) hy) hh
    · intro hy
      have := A.mul_mem (A.mul_mem hh hy) (A.inv_mem hh)
      convert this using 1; group
  rw [card_locPart_conj A B K (h * a) (Quotient.out q) hk hAB']
  have hc : (h * a)⁻¹ * ρA * (h * a) = ρB := by
    rw [show (h * a)⁻¹ * ρA * (h * a) = a⁻¹ * (h⁻¹ * (h * ρA)) * a by rw [hA h hh]; group]
    rw [show a⁻¹ * (h⁻¹ * (h * ρA)) * a = a⁻¹ * ρA * a by group, hρ]
  rw [show ((h * a) * Quotient.out q * k)⁻¹ * ρA * ((h * a) * Quotient.out q * k) =
      k⁻¹ * ((Quotient.out q)⁻¹ * ((h * a)⁻¹ * ρA * (h * a)) * Quotient.out q) * k by group, hc,
    hf _ (K.inv_mem hk) _ hk]

theorem orbital_conj : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (f : G → ℂ), (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) →
    ∀ ρ δ : Γ,
    ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {((δ * ρ * δ⁻¹ : Γ) : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {((δ * ρ * δ⁻¹ : Γ) : G)} ⊓ Γ) K (Quotient.out q)) : ℂ)) *
          f ((Quotient.out q)⁻¹ * ((δ * ρ * δ⁻¹ : Γ) : G) * Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ρ : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ρ : G)} ⊓ Γ) K (Quotient.out q)) : ℂ)) *
          f ((Quotient.out q)⁻¹ * (ρ : G) * Quotient.out q) := by
  intro G _ Γ K f hf ρ δ
  refine finsum_doubleCoset_conj _ _ K f hf (δ : G) _ _ ?_ ?_ ?_
  · intro y
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨hc, hy⟩
      refine ⟨?_, Γ.mul_mem (Γ.mul_mem (Γ.inv_mem δ.2) hy) δ.2⟩
      calc (δ : G)⁻¹ * y * δ * ρ = (δ : G)⁻¹ * (y * (δ * ρ * (δ : G)⁻¹)) * δ := by group
        _ = (δ : G)⁻¹ * ((δ * ρ * (δ : G)⁻¹) * y) * δ := by rw [hc]
        _ = ρ * ((δ : G)⁻¹ * y * δ) := by group
    · rintro ⟨hc, hy⟩
      refine ⟨?_, ?_⟩
      · calc y * (δ * ρ * (δ : G)⁻¹) = δ * (((δ : G)⁻¹ * y * δ) * ρ) * (δ : G)⁻¹ := by group
          _ = δ * (ρ * ((δ : G)⁻¹ * y * δ)) * (δ : G)⁻¹ := by rw [hc]
          _ = (δ * ρ * (δ : G)⁻¹) * y := by group
      · have := Γ.mul_mem (Γ.mul_mem δ.2 hy) (Γ.inv_mem δ.2)
        convert this using 1; group
  · intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).1)
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group

theorem unfolded_eq_orbital_reps : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  ∀ R : Set Γ, (∀ γ : Γ, ∃! ρ, ρ ∈ R ∧ IsConj γ ρ) →
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ)
  = ∑ᶠ ρ ∈ R, LinearMap.trace ℂ W (ξ ρ) *
      ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ρ : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ρ : G)} ⊓ Γ) K q.out) : ℂ)) * f (q.out⁻¹ * ρ * q.out) := by
  intro G _ Γ K W _ _ _ ξ hfin hloc f hf hsupp R hR
  rw [(unfolded_eq_orbital G Γ K W ξ hfin hloc f hf hsupp).2]
  let T : Γ → ℂ := fun ρ => LinearMap.trace ℂ W (ξ ρ) *
      ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ρ : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ρ : G)} ⊓ Γ) K (Quotient.out q)) : ℂ)) *
          f ((Quotient.out q)⁻¹ * (ρ : G) * Quotient.out q)
  have htr : ∀ δ γ : Γ, LinearMap.trace ℂ W (ξ (δ * γ * δ⁻¹)) = LinearMap.trace ℂ W (ξ γ) := by
    intro δ γ
    rw [map_mul ξ, map_mul ξ, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul ξ, inv_mul_cancel, map_one, one_mul]
  have hT : ∀ a b : Γ, IsConj a b → T a = T b := by
    intro a b hab
    obtain ⟨δ, hδ⟩ := isConj_iff.1 hab
    subst hδ
    simp only [T]
    rw [htr, orbital_conj G Γ K f hf a δ]
  have hL : ∀ c : ConjClasses Γ, LinearMap.trace ℂ W (ξ (Quotient.out c)) *
      ∑ᶠ y : DoubleCoset.Quotient ((Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)}) K y.out) : ℂ)) *
          f (y.out⁻¹ * (Quotient.out c : Γ) * y.out) = T (Quotient.out c) := by
    intro c
    rw [show (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)}) =
      Subgroup.centralizer {((Quotient.out c : Γ) : G)} ⊓ Γ from inf_comm _ _]
  simp_rw [hL]
  let e : R → ConjClasses Γ := fun ρ => ConjClasses.mk ρ.1
  have he : Function.Bijective e := by
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · have h1 : IsConj a.1 b.1 := ConjClasses.mk_eq_mk_iff_isConj.1 hab
      obtain ⟨ρ, -, hu⟩ := hR a.1
      exact Subtype.ext ((hu a.1 ⟨a.2, IsConj.refl _⟩).trans (hu b.1 ⟨b.2, h1⟩).symm)
    · obtain ⟨γ, rfl⟩ := ConjClasses.mk_surjective c
      obtain ⟨ρ, ⟨hρ, hc⟩, -⟩ := hR γ
      exact ⟨⟨ρ, hρ⟩, ConjClasses.mk_eq_mk_iff_isConj.2 hc.symm⟩
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv (Equiv.ofBijective e he)]
  refine finsum_congr fun ρ => ?_
  apply hT
  show IsConj (Quotient.out (ConjClasses.mk ρ.1)) ρ.1
  rw [← ConjClasses.mk_eq_mk_iff_isConj]
  exact Quotient.out_eq _

end GlobalTheory.FinTrace
