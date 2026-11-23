import Mathlib

noncomputable section

namespace PositivityTheory.ThKF.Abs

open scoped InnerProductSpace

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem orth_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (z : U) (hz : z ∈ Yᗮ) : κ k z ∈ Yᗮ := by
  rw [Submodule.mem_orthogonal] at hz ⊢
  intro y hy
  have e : y = κ k (κ k⁻¹ y) := by rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [e, hi]
  exact hz _ (hY _ _ hy)

theorem proj_equiv {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) [FiniteDimensional ℂ Y] (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (x : U) :
    Y.starProjection (κ k x) = κ k (Y.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (hY _ _ (Y.starProjection_apply_mem x))
  rw [← map_sub]
  exact orth_stab κ hi Y hY k _ (Y.sub_starProjection_mem_orthogonal x)

theorem span_orbit_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) (k : K) :
    ∀ y ∈ Submodule.span ℂ (Set.range fun k => κ k x), κ k y ∈ Submodule.span ℂ (Set.range fun k => κ k x) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => obtain ⟨k', rfl⟩ := h; exact Submodule.subset_span ⟨k * k', by simp⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

def orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : Submodule ℂ U := Submodule.span ℂ (Set.range fun k => κ k x)

theorem mem_orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : x ∈ orb κ x := Submodule.subset_span ⟨1, by simp⟩

def homs {K : Type} [Group K] (κ : K →* Module.End ℂ U) (W : Submodule ℂ U) : Submodule ℂ (U →ₗ[ℂ] U) where
  carrier := {L | (∀ x, L x ∈ W) ∧ ∀ k x, L (κ k x) = κ k (L x)}
  add_mem' := fun {a b} ha hb => ⟨fun x => add_mem (ha.1 x) (hb.1 x), fun k x => by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨fun x => by simp, fun k x => by simp⟩
  smul_mem' := fun c a ha => ⟨fun x => W.smul_mem c (ha.1 x), fun k x => by simp [ha.2]⟩

def ck (H : Submodule ℂ (U →ₗ[ℂ] U)) : Submodule ℂ U where
  carrier := {z | ∀ L ∈ H, L z = 0}
  add_mem' := fun {a b} ha hb L hL => by rw [map_add, ha L hL, hb L hL, add_zero]
  zero_mem' := fun L _ => map_zero L
  smul_mem' := fun c a ha L hL => by rw [map_smul, ha L hL, smul_zero]

theorem fd_orth {K : Type} [Group K] (κ : K →* Module.End ℂ U) (W : Submodule ℂ U) [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ (homs κ W)] : FiniteDimensional ℂ ↥(ck (homs κ W))ᗮ := by
  let ev : ↥(ck (homs κ W))ᗮ →ₗ[ℂ] (homs κ W →ₗ[ℂ] W) :=
    { toFun := fun z => { toFun := fun L => ⟨L.1 z, L.2.1 z⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      map_add' := fun a b => LinearMap.ext fun L => Subtype.ext (map_add L.1 a.1 b.1)
      map_smul' := fun c a => LinearMap.ext fun L => Subtype.ext (map_smul L.1 c a.1) }
  refine Module.Finite.of_injective ev ((injective_iff_map_eq_zero ev).2 fun z hz => ?_)
  have h1 : z.1 ∈ ck (homs κ W) := fun L hL => congrArg Subtype.val (LinearMap.congr_fun hz ⟨L, hL⟩)
  exact Subtype.ext (inner_self_eq_zero.1 (z.2 _ h1))

theorem split {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (W V : Submodule ℂ U) [FiniteDimensional ℂ V] (sV : ∀ k, ∀ y ∈ V, κ k y ∈ V) (u : U) (uV : u ∈ V) :
    ∃ y ∈ V, ∃ z ∈ V, y ∈ (ck (homs κ W))ᗮ ∧ z ∈ ck (homs κ W) ∧ u = y + z := by
  have sZ' : ∀ k, ∀ z ∈ ck (homs κ W), κ k z ∈ ck (homs κ W) := fun k z hz L hL => by rw [hL.2, hz L hL, map_zero]
  obtain ⟨A, hA⟩ : ∃ A, A = V ⊓ ck (homs κ W) := ⟨_, rfl⟩
  have : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le (S₂ := V) (hA ▸ inf_le_left)
  have mA : ∀ y, y ∈ A ↔ y ∈ V ∧ y ∈ ck (homs κ W) := fun y => by rw [hA]; rfl
  have sA : ∀ k, ∀ y ∈ A, κ k y ∈ A := fun k y hy => (mA _).2 ⟨sV k y ((mA _).1 hy).1, sZ' k y ((mA _).1 hy).2⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = V ⊓ Aᗮ := ⟨_, rfl⟩
  have : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le (S₂ := V) (hY ▸ inf_le_left)
  have mY : ∀ y, y ∈ Y ↔ y ∈ V ∧ y ∈ Aᗮ := fun y => by rw [hY]; rfl
  have sY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y := fun k y hy =>
    (mY _).2 ⟨sV k y ((mY _).1 hy).1, orth_stab κ hi A sA k y ((mY _).1 hy).2⟩
  have hz := (mA _).1 (A.starProjection_apply_mem u)
  have hy : u - A.starProjection u ∈ Y := (mY _).2 ⟨sub_mem uV hz.1, A.sub_starProjection_mem_orthogonal u⟩
  refine ⟨_, ((mY _).1 hy).1, _, hz.1, fun z hz' => ?_, hz.2, (sub_add_cancel _ _).symm⟩
  have h1 : Y.starProjection z ∈ ck (homs κ W) := fun L hL =>
    hz' (L ∘ₗ (Y.starProjection : U →ₗ[ℂ] U)) ⟨fun x => hL.1 _, fun k x => by
      show L (Y.starProjection (κ k x)) = κ k (L (Y.starProjection x))
      rw [proj_equiv κ hi Y sY, hL.2]⟩
  have h2 := (mY _).1 (Y.starProjection_apply_mem z)
  have h3 : Y.starProjection z = 0 := inner_self_eq_zero.1 (h2.2 _ ((mA _).2 ⟨h2.1, h1⟩))
  have h4 := Y.sub_starProjection_mem_orthogonal z
  rw [h3, sub_zero] at h4
  rw [inner_eq_zero_symm]
  exact h4 _ hy

theorem exists_e {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hf : ∀ x, FiniteDimensional ℂ (orb κ x)) (f : U) (hH : FiniteDimensional ℂ (homs κ (orb κ f))) :
    ∃ Z Z' : Submodule ℂ U, FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z = Z'ᗮ ∧
      ∀ S : Submodule ℂ U, (∀ k, ∀ y ∈ S, κ k y ∈ S) → ∀ u ∈ S, ∃ y ∈ S, ∃ z ∈ S, y ∈ Z ∧ z ∈ Z' ∧ u = y + z := by
  have := hf f
  refine ⟨_, ck (homs κ (orb κ f)), fd_orth κ _, fun z hz => ?_, rfl, fun S hS u hu => ?_⟩
  · have h0 : (orb κ f).starProjection z = 0 := hz ((orb κ f).starProjection : U →ₗ[ℂ] U)
      ⟨fun x => (orb κ f).starProjection_apply_mem x, fun k x => proj_equiv κ hi (orb κ f) (span_orbit_stab κ f) k x⟩
    have h1 := (orb κ f).sub_starProjection_mem_orthogonal z
    rw [h0, sub_zero] at h1
    rw [inner_eq_zero_symm]
    exact h1 f (mem_orb κ f)
  · have := hf u
    have VS : orb κ u ≤ S := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hS k u hu)
    obtain ⟨y, hy, z, hz, h⟩ := split κ hi (orb κ f) (orb κ u) (span_orbit_stab κ u) u (mem_orb κ u)
    exact ⟨y, VS hy, z, VS hz, h⟩

def Proj (St : Submodule ℂ U → Prop) : Prop :=
  ∀ f : U, ∃ Z Z' : Submodule ℂ U, FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z = Z'ᗮ ∧
    ∀ S : Submodule ℂ U, St S → ∀ u ∈ S, ∃ y ∈ S, ∃ z ∈ S, y ∈ Z ∧ z ∈ Z' ∧ u = y + z

theorem compl {St : Submodule ℂ U → Prop} (h : Proj St) (S : Submodule ℂ U) (hS : St S) (f : U) :
    ∃ a ∈ S, f - a ∈ Sᗮ := by
  obtain ⟨Z, Z', hZ, hf, e, hd⟩ := h f
  let A : Submodule ℂ U := S ⊓ Z
  haveI : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le (S₂ := Z) inf_le_right
  have ha := A.starProjection_apply_mem f
  refine ⟨_, ha.1, fun u hu => ?_⟩
  obtain ⟨y, hy, z, -, hyZ, hz, rfl⟩ := hd S hS u hu
  have h1 : f - A.starProjection f ∈ Z'ᗮ := e ▸ sub_mem hf ha.2
  rw [inner_add_left, A.sub_starProjection_mem_orthogonal f y ⟨hy, hyZ⟩, h1 z hz, add_zero]

theorem simple {St : Submodule ℂ U → Prop} (h : Proj St) (hinf : ∀ s : Set (Submodule ℂ U), (∀ S ∈ s, St S) → St (sInf s))
    (horth : ∀ S, St S → St Sᗮ) (N : Submodule ℂ U) (hN : St N) (hne : N ≠ ⊥) :
    ∃ S, St S ∧ S ≤ N ∧ S ≠ ⊥ ∧ ∀ P, St P → P ≤ S → P = ⊥ ∨ P = S := by
  classical
  obtain ⟨f, hfN, hf0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨Z, Z', hZ, hf, e, hd⟩ := h f
  have ex : ∃ m, ∃ S, St S ∧ S ≤ N ∧ S ⊓ Z ≠ ⊥ ∧ Module.finrank ℂ ↥(S ⊓ Z) = m :=
    ⟨_, N, hN, le_rfl, (Submodule.ne_bot_iff _).2 ⟨f, ⟨hfN, hf⟩, hf0⟩, rfl⟩
  obtain ⟨S₀, h0, h0N, h0ne, h0r⟩ := Nat.find_spec ex
  have hmin : ∀ P, St P → P ≤ S₀ → P ⊓ Z = ⊥ ∨ P ⊓ Z = S₀ ⊓ Z := fun P hP hle => by
    by_cases hb : P ⊓ Z = ⊥
    · exact Or.inl hb
    · haveI : FiniteDimensional ℂ ↥(S₀ ⊓ Z) := Submodule.finiteDimensional_of_le (S₂ := Z) inf_le_right
      refine Or.inr (Submodule.eq_of_le_of_finrank_le (inf_le_inf_right _ hle) ?_)
      rw [h0r]
      exact Nat.find_min' ex ⟨P, hP, hle.trans h0N, hb, rfl⟩
  let S := sInf {P | St P ∧ S₀ ⊓ Z ≤ P}
  have hS : St S := hinf _ fun P hP => hP.1
  have hS0 : S ≤ S₀ := sInf_le ⟨h0, inf_le_left⟩
  have hZS : S₀ ⊓ Z ≤ S := le_sInf fun P hP => hP.2
  have inf2 : ∀ P Q, St P → St Q → St (P ⊓ Q) := fun P Q hP hQ => by
    rw [← sInf_pair]; exact hinf _ (by rintro _ (rfl | rfl) <;> assumption)
  refine ⟨S, hS, hS0.trans h0N, fun hb => h0ne (le_bot_iff.1 (hb ▸ hZS)), fun P hP hle => ?_⟩
  rcases hmin P hP (hle.trans hS0) with hb | hb
  · left
    have h2 : S₀ ⊓ Z ≤ Pᗮ := fun x hx u hu => by
      obtain ⟨y, hy, z, -, hyZ, hz, rfl⟩ := hd P hP u hu
      have y0 : y = 0 := by
        have : y ∈ P ⊓ Z := ⟨hy, hyZ⟩
        rwa [hb, Submodule.mem_bot] at this
      have hx' : x ∈ Z'ᗮ := e ▸ hx.2
      rw [y0, zero_add]
      exact hx' z hz
    have h3 : S ≤ Pᗮ := sInf_le ⟨horth P hP, h2⟩
    exact (Submodule.eq_bot_iff _).2 fun x hx => inner_self_eq_zero.1 (h3 (hle hx) x hx)
  · exact Or.inr (le_antisymm hle (sInf_le ⟨hP, hb ▸ inf_le_left⟩))

theorem eq_bot {St : Submodule ℂ U → Prop} (h : Proj St) (hinf : ∀ s : Set (Submodule ℂ U), (∀ S ∈ s, St S) → St (sInf s))
    (horth : ∀ S, St S → St Sᗮ) (N : Submodule ℂ U) (hN : St N)
    (hu : ∀ M, Maximal (fun P => St P ∧ P ≠ ⊤) M → N ≤ M) : N = ⊥ := by
  by_contra hne
  obtain ⟨S, hS, hSN, hS0, hs⟩ := simple h hinf horth N hN hne
  have nle : ¬ S ≤ Sᗮ := fun hle => hS0 ((Submodule.eq_bot_iff _).2 fun x hx => inner_self_eq_zero.1 (hle hx x hx))
  refine nle (hSN.trans (hu _ ⟨⟨horth S hS, fun ht => nle (ht ▸ le_top)⟩, fun P hP hle => ?_⟩))
  have hPS : St (P ⊓ S) := by
    rw [← sInf_pair]; exact hinf _ (by rintro _ (rfl | rfl); exacts [hP.1, hS])
  rcases hs _ hPS inf_le_right with hb | hb
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := compl h S hS x
    have : a ∈ P ⊓ S := ⟨by simpa using P.sub_mem hx (hle hxa), ha⟩
    rw [hb, Submodule.mem_bot] at this
    simpa [this] using hxa
  · exfalso
    refine hP.2 (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨a, ha, hxa⟩ := compl h S hS x
    have : a ∈ P := (by rw [hb]; exact ha : a ∈ P ⊓ S).1
    simpa using P.add_mem (hle hxa) this

end PositivityTheory.ThKF.Abs

end
