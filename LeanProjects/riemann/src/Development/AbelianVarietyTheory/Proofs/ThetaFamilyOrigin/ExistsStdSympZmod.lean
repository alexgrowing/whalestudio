import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

set_option autoImplicit false

namespace GlobalTheory.SympMod

theorem card_torsion_zmod {M d : ℕ} [NeZero M] (hd : d ∣ M) :
    Nat.card {a : ZMod M // d • a = 0} = d := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod M) d
  rw [Nat.card_zmod, Nat.gcd_eq_right hd] at h
  exact h

theorem exists_pair_eq_one {M g : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (N : Submodule (ZMod M) V)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // x ∈ N ∧ d • x = 0} = d ^ (2 * (g + 1))) :
    ∃ e ∈ N, ∃ f ∈ N, B e f = 1 := by
  have : IsPrincipalIdealRing (ZMod M) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod M)) (ZMod.ringHom_surjective _)
  obtain ⟨e, he, f, hf, h₁, h₂, h₃⟩ := exists_pair_dvd_of_bilinForm B N
  have hall : ∀ x ∈ N, ∀ y ∈ N, B e f ∣ B x y := by
    intro x hx y hy
    obtain ⟨b, hb⟩ := h₁ y hy
    obtain ⟨a, ha⟩ := h₂ x hx
    have k₁ : B (x - a • e) f = 0 := by simp [ha, mul_comm]
    have k := h₃ (x - a • e) (N.sub_mem hx (N.smul_mem _ he)) (y - b • f)
      (N.sub_mem hy (N.smul_mem _ hf)) (by simp [hb, mul_comm]) k₁
    rw [map_sub, map_smul, k₁, smul_zero, sub_zero] at k
    have : B x y = B (x - a • e) y + a * B e y := by simp
    rw [this]
    exact dvd_add k (Dvd.dvd.mul_left (h₁ y hy) a)
  have hu : IsUnit (B e f) := by
    by_contra hnu
    obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective (B e f)
    rw [← hm, ZMod.isUnit_iff_coprime, Nat.Prime.not_coprime_iff_dvd] at hnu
    obtain ⟨p, hp, ⟨c, rfl⟩, ⟨q, hq⟩⟩ := hnu
    have hkill : ∀ x ∈ N, q • x = 0 := by
      intro x hx
      refine hN _ (N.toAddSubgroup.nsmul_mem hx q) fun y hy => ?_
      obtain ⟨r, hr⟩ := hall x hx y hy
      rw [map_nsmul, LinearMap.smul_apply, hr, ← hm, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, ← mul_assoc,
        mul_comm q p, ← hq, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
    have hM : ∀ x : V, M • x = 0 := fun x => by
      rw [← Nat.cast_smul_eq_nsmul (ZMod M), ZMod.natCast_self, zero_smul]
    have k₁ := hc q ⟨p, by rw [hq, mul_comm]⟩
    have k₂ := hc M dvd_rfl
    have k₃ : Nat.card {x : V // x ∈ N ∧ q • x = 0} = Nat.card {x : V // x ∈ N ∧ M • x = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        ⟨fun h => ⟨h.1, hM x⟩, fun h => ⟨h.1, hkill x h.1⟩⟩)
    rw [k₁, k₂] at k₃
    have k₄ : q = M := Nat.pow_left_injective (by omega) k₃
    have k₅ := NeZero.pos M
    have := hp.two_le
    nlinarith
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  exact ⟨e, he, u • f, N.smul_mem _ hf, by simpa using hu⟩

theorem exists_isSymplecticFamily {M : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (hB : B.IsAlt) (g : ℕ) (N : Submodule (ZMod M) V)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // x ∈ N ∧ d • x = 0} = d ^ (2 * g)) :
    ∃ e f : Fin g → V, IsSymplecticFamily B e f (fun _ => 1) ∧ (∀ i, e i ∈ N) ∧ ∀ i, f i ∈ N := by
  induction g generalizing N with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0⟩
  | succ g ih =>
  obtain ⟨e, he, f, hf, hd⟩ := exists_pair_eq_one N hN hc
  have hd' : B f e = -1 := by rw [← hB.neg_eq, hd]
  let N' : Submodule (ZMod M) V := N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
  have hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0 := fun y => Iff.rfl
  have hpr : ∀ y ∈ N, y - B y f • e - B e y • f ∈ N' := fun y hy =>
    (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he)) (N.smul_mem _ hf),
      by simp [hd, hB.self_eq_zero], by simp [← hB.neg_eq y f, hd', hB.self_eq_zero]⟩
  have hdec : ∀ y ∈ N, ∃ a b : ZMod M, ∃ y' ∈ N', y = a • e + b • f + y' := fun y hy =>
    ⟨B y f, B e y, _, hpr y hy, by abel⟩
  obtain ⟨e', f', hs, he', hf'⟩ := ih N' (by
    intro x hx hx0
    refine hN x hx.1 fun y hy => ?_
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
    simp [hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2]) (by
    intro d hdM
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdM (NeZero.pos M)
    let F : {a : ZMod M // d • a = 0} × {a : ZMod M // d • a = 0} × {x : V // x ∈ N' ∧ d • x = 0} →
        {x : V // x ∈ N ∧ d • x = 0} := fun t =>
      ⟨t.1.1 • e + t.2.1.1 • f + t.2.2.1,
        N.add_mem (N.add_mem (N.smul_mem _ he) (N.smul_mem _ hf)) t.2.2.2.1.1, by
          rw [smul_add, smul_add, ← smul_assoc, ← smul_assoc, t.1.2, t.2.1.2, t.2.2.2.2]
          simp⟩
    have hF : Function.Bijective F := by
      constructor
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨y, hy, hy'⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨z, hz, hz'⟩⟩ h
        have h : a • e + b • f + y = a' • e + b' • f + z := congrArg Subtype.val h
        obtain rfl : b = b' := by
          simpa [hd, hB.self_eq_zero, ((hmem _).1 hy).2.1, ((hmem _).1 hz).2.1] using congrArg (B e) h
        obtain rfl : a = a' := by
          simpa [hd', hB.self_eq_zero, ((hmem _).1 hy).2.2, ((hmem _).1 hz).2.2] using congrArg (B f) h
        obtain rfl : y = z := add_left_cancel h
        rfl
      · rintro ⟨x, hx, hx'⟩
        have k₁ : d • B x f = 0 := by rw [← LinearMap.smul_apply, ← map_nsmul, hx']; simp
        have k₂ : d • B e x = 0 := by rw [← map_nsmul, hx', map_zero]
        refine ⟨⟨⟨B x f, k₁⟩, ⟨B e x, k₂⟩, ⟨_, hpr x hx, ?_⟩⟩, Subtype.ext ?_⟩
        · rw [smul_sub, smul_sub, ← smul_assoc, ← smul_assoc, k₁, k₂, hx']
          simp
        · show B x f • e + B e x • f + (x - B x f • e - B e x • f) = x
          abel
    have h := Nat.card_eq_of_bijective F hF
    rw [hc d hdM, Nat.card_prod, Nat.card_prod, card_torsion_zmod hdM,
      show d ^ (2 * (g + 1)) = d * (d * d ^ (2 * g)) by ring] at h
    exact Nat.eq_of_mul_eq_mul_left hd0 (Nat.eq_of_mul_eq_mul_left hd0 h))
  refine ⟨Fin.cons e e', Fin.cons f f', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (he' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.1]
    · simp [hs.left_left]
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (hf' _)).2.2]
    · simp [hB.eq_iff.1 ((hmem _).1 (hf' _)).2.2]
    · simp [hs.right_right]
  · intro i
    cases i using Fin.cases
    · simp [hd]
    · simp [hs.left_right_self]
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact absurd rfl hij
    · simp [((hmem _).1 (hf' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]
    · simpa using hs.left_right_ne _ _ fun a => hij (congrArg _ a)
  · intro i
    cases i using Fin.cases
    · exact he
    · exact (he' _).1
  · intro i
    cases i using Fin.cases
    · exact hf
    · exact (hf' _).1

open ReciprocityTheory.ChartRestriction.G.Out in

theorem exists_stdSymp_zmod {M g : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (hB : B.IsAlt) (hN : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // d • x = 0} = d ^ (2 * g)) :
    ∃ v : Fin (2 * g) → V, ∀ i k, B (v i) (v k) = (stdSymp g i k : ℤ) := by
  obtain ⟨e, f, hs, -, -⟩ := exists_isSymplecticFamily hB g ⊤ (fun x _ h => hN x fun y => h y trivial)
    (fun d hd => by simpa using hc d hd)
  let σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm
  refine ⟨Sum.elim e f ∘ σ, fun i k => ?_⟩
  obtain ⟨a, rfl⟩ := σ.symm.surjective i
  obtain ⟨b, rfl⟩ := σ.symm.surjective k
  simp only [Function.comp, Equiv.apply_symm_apply, stdSymp]
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g + a := fun _ => rfl
  rcases a with a | a <;> rcases b with b | b <;> have := a.2 <;> have := b.2 <;>
    simp only [l, r, Sum.elim_inl, Sum.elim_inr, hs.left_left, hs.right_right, hs.left_right, hs.right_left hB,
      Fin.ext_iff] <;> split_ifs <;> first | omega | simp

end GlobalTheory.SympMod

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Out in

theorem exists_stdSymp_of_alternating_pairing :
    ∀ (M g : ℕ) (G : Type) [CommGroup G] (R : Type) [CommRing R] [IsDomain R] (ζ : Rˣ), 0 < M →
    IsPrimitiveRoot ζ M → (∀ x : G, x ^ M = 1) →
    (∀ d : ℕ, d ∣ M → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) →
    ∀ e : G →* G →* Rˣ, (∀ x, e x x = 1) → (∀ x, (∀ y, e x y = 1) → x = 1) →
    ∃ x : Fin (2 * g) → G, ∀ i j, e (x i) (x j) = ζ ^ stdSymp g i j := by
  intro M g G _ R _ _ ze hM hz hG hc w halt hnd
  have : NeZero M := ⟨hM.ne'⟩
  have wm : ∀ x y, w x y ∈ Subgroup.zpowers ze := fun x y => by
    rw [hz.zpowers_eq, mem_rootsOfUnity, ← map_pow, hG, map_one]
  have hT : ∀ x : Additive G, M • x = 0 := fun x => hG x.toMul
  let _ : Module (ZMod M) (Additive G) := AddCommGroup.zmodModule hT
  let β : Additive G → Additive G → ZMod M := fun x y =>
    hz.zmodEquivZPowers.symm (Additive.ofMul ⟨w x.toMul y.toMul, wm _ _⟩)
  have βl : ∀ x x' y, β (x + x') y = β x y + β x' y := fun x x' y => by
    simp only [β, ← map_add]
    exact congrArg _ (Subtype.ext (by
      show w (x.toMul * x'.toMul) y.toMul = w x.toMul y.toMul * w x'.toMul y.toMul
      rw [map_mul, MonoidHom.mul_apply]))
  have βr : ∀ x y y', β x (y + y') = β x y + β x y' := fun x y y' => by
    simp only [β, ← map_add]
    exact congrArg _ (Subtype.ext (map_mul (w x.toMul) y.toMul y'.toMul))
  have βw : ∀ x y (n : ℤ), β x y = n ↔ w x.toMul y.toMul = ze ^ n := fun x y n => by
    simp only [β]
    rw [AddEquiv.symm_apply_eq, hz.zmodEquivZPowers_apply_coe_int]
    exact Subtype.ext_iff
  let B : LinearMap.BilinForm (ZMod M) (Additive G) := LinearMap.mk₂ _ β βl
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β · y) fun x x' => βl x x' y) c x) βr
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β x) (βr x)) c y)
  obtain ⟨v, hv⟩ := SympMod.exists_stdSymp_zmod (V := Additive G) (g := g) (B := B)
    (fun x => ((βw x x 0).2 (by simpa using halt _)).trans Int.cast_zero)
    (fun x hx => hnd x.toMul fun y => by
      have h := (βw x (Additive.ofMul y) 0).1 ((hx _).trans Int.cast_zero.symm)
      rwa [zpow_zero] at h) (fun d hd => hc d hd)
  exact ⟨fun i => (v i).toMul, fun i k => (βw _ _ _).1 (hv i k)⟩

end GlobalTheory
