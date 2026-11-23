import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteOrthogonalLengths

namespace GlobalTheory.HermClass

open Module Submodule NumberField

theorem finite_between {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (L₀ : Submodule ℤ V) (h₀ : L₀.FG) {M : ℤ} (hM : M ≠ 0) :
    {L : Submodule ℤ V | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀}.Finite := by
  classical
  have hcast : ∀ x : V, (M : E) • x = M • x := fun x => Int.cast_smul_eq_zsmul E M x
  let μ : V →ₗ[ℤ] V := M • LinearMap.id
  have hμ : ∀ x, μ x = M • x := fun x => rfl
  have hinj : Function.Injective μ := by
    intro x y hxy
    rw [hμ, hμ, ← hcast, ← hcast] at hxy
    exact smul_right_injective V (Int.cast_ne_zero.mpr hM) hxy
  let L' := L₀.comap μ
  have hL'fg : L'.FG :=
    Submodule.fg_of_fg_map_injective μ hinj (h₀.of_le (Submodule.map_comap_le μ L₀))
  let K : Submodule ℤ L' := L₀.comap L'.subtype
  have : Module.Finite ℤ L' := Module.Finite.iff_fg.mpr hL'fg
  have : Finite (L' ⧸ K) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
    rw [Submonoid.smul_def, ← LinearMap.map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact x.2
  have : Finite (Submodule ℤ (L' ⧸ K)) :=
    Finite.of_injective (fun P : Submodule ℤ (L' ⧸ K) => (P : Set (L' ⧸ K))) SetLike.coe_injective
  let g : Submodule ℤ V → Submodule ℤ (L' ⧸ K) := fun L => (L.comap L'.subtype).map K.mkQ
  have key : ∀ L : Submodule ℤ V, L ∈ {L : Submodule ℤ V | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀} →
      ((g L).comap K.mkQ).map L'.subtype = L := by
    rintro L ⟨hle, hM'⟩
    have hK : K ≤ L.comap L'.subtype := fun x hx => hle hx
    have hL' : L ≤ L' := fun x hx => show μ x ∈ L₀ by rw [hμ, ← hcast]; exact hM' x hx
    simp only [g, Submodule.comap_map_mkQ, sup_eq_right.mpr hK, Submodule.map_comap_subtype,
      inf_eq_right.mpr hL']
  refine Set.Finite.of_finite_image (Set.toFinite _) (f := g) ?_
  intro L₁ h₁ L₂ h₂ h12
  exact (key L₁ h₁).symm.trans
    ((congrArg (fun P => (P.comap K.mkQ).map L'.subtype) h12).trans (key L₂ h₂))

theorem exists_finite_representatives {α : Type*} {β : Type*} (f : α → β)
    (hf : (Set.range f).Finite) : ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, f s = f a := by
  classical
  have : Finite (Set.range f) := hf.to_subtype
  refine ⟨Set.range (fun b : Set.range f => b.2.choose), Set.finite_range _, fun a => ?_⟩
  exact ⟨(⟨f a, a, rfl⟩ : Set.range f).2.choose, ⟨⟨f a, a, rfl⟩, rfl⟩,
    (⟨f a, a, rfl⟩ : Set.range f).2.choose_spec⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_finite_classes {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (hs : ∀ x y, h y x = star (h x y))
    (hnd : ∀ y, (∀ x, h y x = 0) → y = 0) {N m : ℤ} (hN : N ≠ 0) (hm : m ≠ 0)
    {α : Type*} {ι : Type*} [Finite ι] (Λ : α → Submodule ℤ V) (t : α → ι → V)
    (hfg : ∀ a, (Λ a).FG) (hsp : ∀ a, span E (Λ a : Set V) = ⊤)
    (hO : ∀ a, ∀ c : E, IsIntegral ℤ c → ∀ x ∈ Λ a, c • x ∈ Λ a)
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ (h x y))
    (hdual : ∀ a y, (∀ x ∈ Λ a, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ a)
    (ht : ∀ a i, t a i ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : V ≃ₗ[E] V, (∀ x y, h (γ x) (γ y) = h x y) ∧
      (∀ x, x ∈ Λ a ↔ γ x ∈ Λ s) ∧ ∀ i, ∃ y ∈ Λ s, γ (t a i) - t s i = m • y := by
  classical
  set n := finrank E V with hn
  obtain ⟨S₀, hS₀f, hS₀0, hS₀⟩ := exists_finite_orthogonal_lengths (E := E) n hN
  have hv : ∀ a, ∃ v : Fin n → V, (∀ i, v i ∈ Λ a) ∧
      (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ∈ S₀ := fun a =>
    hS₀ V h (Λ a) hn.symm hs hnd (hfg a) (hsp a) (hO a) (hint a) (hdual a)
  choose v hvΛ hvo hvS using hv
  have hexp : ∀ a (c : Fin n → E) (y : V), h (∑ i, c i • v a i) y = ∑ i, c i * h (v a i) y := by
    intro a c y
    simp [map_sum, LinearMap.sum_apply, smul_eq_mul]
  have hexp2 : ∀ a (x : V) (c : Fin n → E),
      h x (∑ j, c j • v a j) = ∑ j, star (c j) * h x (v a j) := by
    intro a x c
    simp [map_sum, smul_eq_mul, starRingEnd_apply]
  have hcoef : ∀ a (c : Fin n → E) j, h (∑ i, c i • v a i) (v a j) = c j * h (v a j) (v a j) := by
    intro a c j
    rw [hexp, Finset.sum_eq_single j]
    · intro i _ hij
      rw [hvo a i j hij, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hd0 : ∀ a j, h (v a j) (v a j) ≠ 0 := fun a j h0 => hS₀0 (h0 ▸ hvS a j)
  have hli : ∀ a, LinearIndependent E (v a) := by
    intro a
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := hcoef a c j
    rw [hc, map_zero, LinearMap.zero_apply] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (hd0 a j)
  let b : α → Basis (Fin n) E V := fun a =>
    basisOfLinearIndependentOfCardEqFinrank' (v a) (hli a) ((Fintype.card_fin n).trans hn)
  let Φ : α → V ≃ₗ[E] (Fin n → E) := fun a => (b a).equivFun
  have hΦsymm : ∀ a c, (Φ a).symm c = ∑ i, c i • v a i := by
    intro a c
    simp [Φ, b, Basis.equivFun_symm_apply]
  have hgram : ∀ a (c c' : Fin n → E), h (∑ i, c i • v a i) (∑ j, c' j • v a j) =
      ∑ i, c i * (star (c' i) * h (v a i) (v a i)) := by
    intro a c c'
    rw [hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hexp2, Finset.sum_eq_single i]
    · intro j _ hji
      rw [hvo a i j (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  obtain ⟨M, hM0, hMT⟩ := exists_int_mul_isIntegral E (hS₀f.image fun d => d⁻¹)
  let L₀ : Submodule ℤ (Fin n → E) :=
    Submodule.pi Set.univ fun _ => Subalgebra.toSubmodule (integralClosure ℤ E)
  have hL₀ : ∀ c, c ∈ L₀ ↔ ∀ i, IsIntegral ℤ (c i) := by
    intro c
    simp [L₀, Submodule.mem_pi, mem_integralClosure_iff]
  have hL₀fg : L₀.FG := Submodule.fg_pi fun _ => fg_integers E
  let P : α → Submodule ℤ (Fin n → E) := fun a => (Λ a).map ((Φ a : V →ₗ[E] (Fin n → E)).restrictScalars ℤ)
  have hmemP : ∀ a c, c ∈ P a ↔ (Φ a).symm c ∈ Λ a := by
    intro a c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hc
      exact ⟨_, hc, by simp⟩
  have hPfg : ∀ a, (P a).FG := fun a => (hfg a).map _
  have hPB : ∀ a, P a ∈ {L : Submodule ℤ (Fin n → E) | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀} := by
    intro a
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · rw [hmemP, hΦsymm]
      exact Submodule.sum_mem _ fun i _ => hO a (c i) ((hL₀ c).1 hc i) _ (hvΛ a i)
    · rw [hL₀]
      intro i
      have hx := (hmemP a c).1 hc
      have hci := hcoef a c i
      rw [← hΦsymm] at hci
      have : (M : E) * c i = ((M : E) * (h (v a i) (v a i))⁻¹) * h ((Φ a).symm c) (v a i) := by
        rw [hci]
        field_simp [hd0 a i]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact (hMT _ ⟨_, hvS a i, rfl⟩).mul (hint a _ hx _ (hvΛ a i))
  have hB := finite_between (E := E) L₀ hL₀fg hM0
  have hres : ∀ Q : Submodule ℤ (Fin n → E), ∃ R : Set (Fin n → E), R.Finite ∧
      (Q.FG → ∀ x ∈ Q, ∃ ρ ∈ R, ∃ y ∈ Q, x = ρ + m • y) := by
    intro Q
    by_cases hQ : Q.FG
    · obtain ⟨R, hRf, -, hR⟩ := exists_finite_residues Q hQ hm
      exact ⟨R, hRf, fun _ => hR⟩
    · exact ⟨∅, Set.finite_empty, fun h' => absurd h' hQ⟩
  choose R hRf hR using hres
  have hρ : ∀ a i, ∃ ρ ∈ R (P a), ∃ y ∈ P a, Φ a (t a i) = ρ + m • y := fun a i =>
    hR (P a) (hPfg a) _ ((hmemP a _).2 (by simpa using ht a i))
  choose ρ hρR y hyP hρeq using hρ
  let f : α → (Fin n → E) × Submodule ℤ (Fin n → E) × (ι → Fin n → E) := fun a =>
    (fun i => h (v a i) (v a i), P a, ρ a)
  have hfin : (Set.range f).Finite := by
    refine ((Set.Finite.pi fun _ => hS₀f).prod (hB.prod
      (Set.Finite.pi fun _ => hB.biUnion fun Q _ => hRf Q))).subset ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨fun i _ => hvS a i, hPB a, fun i _ => Set.mem_biUnion (hPB a) (hρR a i)⟩
  obtain ⟨S, hSf, hS⟩ := exists_finite_representatives f hfin
  refine ⟨S, hSf, fun a => ?_⟩
  obtain ⟨s, hsS, hfs⟩ := hS a
  simp only [f, Prod.mk.injEq] at hfs
  obtain ⟨hd, hP, hρ'⟩ := hfs
  refine ⟨s, hsS, (Φ a).trans (Φ s).symm, ?_, ?_, ?_⟩
  · intro x z
    obtain ⟨cx, rfl⟩ := (Φ a).symm.surjective x
    obtain ⟨cz, rfl⟩ := (Φ a).symm.surjective z
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    simp only [hΦsymm, hgram]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [congrFun hd i]
  · intro x
    have e1 := hmemP a (Φ a x)
    have e2 := hmemP s (Φ a x)
    rw [LinearEquiv.symm_apply_apply] at e1
    rw [hP] at e2
    simp only [LinearEquiv.trans_apply]
    exact e1.symm.trans e2
  · intro i
    refine ⟨(Φ s).symm (y a i - y s i), (hmemP s _).1 (sub_mem (by rw [hP]; exact hyP a i) (hyP s i)), ?_⟩
    apply (Φ s).injective
    simp only [LinearEquiv.trans_apply, map_sub, map_zsmul, LinearEquiv.apply_symm_apply]
    rw [hρeq a i, hρeq s i, congrFun hρ' i, smul_sub]
    abel

end GlobalTheory.HermClass
