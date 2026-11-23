import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem finrank_span_finset_le_of_indep {G : Type} [AddCommGroup G] [IsAddTorsionFree G] (T : Finset G) (r : ℕ)
    (hr : ∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ (T : Set G)) → n ≤ r) :
    Module.finrank ℤ (Submodule.span ℤ (T : Set G)) ≤ r := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn ℤ (Subtype.val : ↥(T : Set G) → G)
  have ha : ∀ i : (T : Set G), ∃ a : ℤ, a ≠ 0 ∧ a • (i : G) ∈ Submodule.span ℤ (Subtype.val '' s) := by
    intro i
    by_cases h : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, h, rfl⟩⟩
    · exact hmax i h
  choose a ha0 ha using ha
  set M : ℤ := ∏ i, a i with hMdef
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)
  have hMmem : ∀ x ∈ Submodule.span ℤ (T : Set G), M • x ∈ Submodule.span ℤ (Subtype.val '' s) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have e : M = a ⟨y, hy⟩ * ∏ i ∈ Finset.univ.erase ⟨y, hy⟩, a i :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
      rw [e, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ha ⟨y, hy⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  let f : Submodule.span ℤ (T : Set G) →ₗ[ℤ] Submodule.span ℤ (Subtype.val '' s) :=
    { toFun := fun x => ⟨M • (x : G), hMmem x x.2⟩
      map_add' := by intro x y; ext; simp [smul_add]
      map_smul' := by
        intro c x; ext
        change M • (c • (x : G)) = c • (M • (x : G))
        exact smul_comm _ _ _ }
  have hf : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (smul_right_injective G hM0 e)
  have hsfin : (Subtype.val '' s : Set G).Finite := (Set.toFinite s).image _
  haveI : Module.Finite ℤ (Submodule.span ℤ (Subtype.val '' s)) := Module.Finite.span_of_finite ℤ hsfin
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  have hli : LinearIndepOn ℤ id (Subtype.val '' s) := hs.id_image
  haveI := hsfin.fintype
  rw [finrank_span_set_eq_card hli, Set.toFinset_card] at h1
  let eqv := Fintype.equivFin (Subtype.val '' s : Set G)
  have h2 := hr _ (fun j => (eqv.symm j : G)) (hli.comp _ eqv.symm.injective) (by
    intro j
    obtain ⟨i, _, hi⟩ := (eqv.symm j).2
    rw [← hi]; exact i.2)
  exact h1.trans h2

theorem encard_finset_le_pow_mul {G : Type} [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G)
    (B : ℝ → Set G) (hB : IsBallFam Λ B) (R : ℝ) (q r : ℕ) (hq : 0 < q)
    (hr : ∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r)
    (T : Finset G) (hT : (T : Set G) ⊆ B R) :
    (T : Set G).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  classical
  haveI : NeZero q := ⟨hq.ne'⟩
  set L := Submodule.span ℤ (T : Set G) with hLdef
  have hd : Module.finrank ℤ L ≤ r :=
    finrank_span_finset_le_of_indep T r (fun n e he hmem => hr n e he (fun j => hT (hmem j)))
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set d := Module.finrank ℤ L with hddef
  let b := Module.finBasis ℤ L
  let v : G → (Fin d → ℤ) := fun x => if hx : x ∈ L then b.equivFun ⟨x, hx⟩ else 0
  let c : G → (Fin d → ZMod q) := fun x i => ((v x i : ℤ) : ZMod q)
  let z : G → G → G := fun x y => ((b.equivFun.symm (fun i => (v x i - v y i) / (q : ℤ)) : L) : G)
  have hkey : ∀ x ∈ L, ∀ y ∈ L, c x = c y → q • z x y = x - y := by
    intro x hx y hy hc
    have hdvd : ∀ i, (q : ℤ) ∣ v x i - v y i := by
      intro i
      have e := congrFun hc i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      exact sub_eq_zero.2 e
    have hvx : v x = b.equivFun ⟨x, hx⟩ := dif_pos hx
    have hvy : v y = b.equivFun ⟨y, hy⟩ := dif_pos hy
    have e : q • (b.equivFun.symm (fun i => (v x i - v y i) / (q : ℤ)) : L) = ⟨x, hx⟩ - ⟨y, hy⟩ := by
      apply b.equivFun.injective
      rw [map_nsmul, LinearEquiv.apply_symm_apply, map_sub, ← hvx, ← hvy]
      funext i
      simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul]
      exact Int.mul_ediv_cancel' (hdvd i)
    have e2 := congrArg Subtype.val e
    simpa [z] using e2
  have hLΛ : ∀ x ∈ L, x ∈ Λ := by
    intro x hx
    have : L ≤ Λ.toIntSubmodule := Submodule.span_le.2 (fun y hy => hB.subset R (hT hy))
    exact this hx
  let ρ : (Fin d → ZMod q) → G := Function.invFunOn c (T : Set G)
  have hρ : ∀ x ∈ (T : Set G), ρ (c x) ∈ (T : Set G) ∧ c (ρ (c x)) = c x := fun x hx =>
    ⟨Function.invFunOn_mem ⟨x, hx, rfl⟩, Function.invFunOn_eq ⟨x, hx, rfl⟩⟩
  let φ : G → (Fin d → ZMod q) × G := fun x => (c x, z x (ρ (c x)))
  have hsub : ∀ x ∈ (T : Set G), x ∈ L := fun x hx => Submodule.subset_span hx
  have hmaps : Set.MapsTo φ (T : Set G) (Set.univ ×ˢ B (2 * R / q)) := by
    intro x hx
    refine ⟨Set.mem_univ _, ?_⟩
    obtain ⟨hyT, hyc⟩ := hρ x hx
    have h1 := hkey x (hsub x hx) _ (hsub _ hyT) hyc.symm
    have h2 : x - ρ (c x) ∈ B (R + R) := hB.sub_mem R R _ _ (hT hx) (hT hyT)
    have hqR : ((q : ℝ)) * (2 * R / q) = R + R := by
      have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp; ring
    have hzΛ : z x (ρ (c x)) ∈ Λ := hLΛ _ (Subtype.property _)
    refine (hB.nsmul_iff q (2 * R / q) _ hq hzΛ).1 ?_
    rw [hqR, h1]; exact h2
  have hinj : Set.InjOn φ (T : Set G) := by
    intro x hx x' hx' h
    have hc : c x = c x' := congrArg Prod.fst h
    have hz : z x (ρ (c x)) = z x' (ρ (c x')) := congrArg Prod.snd h
    obtain ⟨hyT, hyc⟩ := hρ x hx
    have h1 := hkey x (hsub x hx) _ (hsub _ hyT) hyc.symm
    have h1' := hkey x' (hsub x' hx') (ρ (c x)) (hsub _ hyT) (by rw [hyc, hc])
    rw [← hc] at hz
    rw [hz] at h1
    exact sub_left_injective (h1.symm.trans h1')
  have hle := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_prod, Set.encard_univ] at hle
  refine hle.trans ?_
  gcongr
  rw [ENat.card_eq_coe_fintype_card]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact_mod_cast Nat.pow_le_pow_right hq hd

theorem encard_ball_le_pow_mul : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G),
    IsBallFam Λ B → ∀ (R : ℝ) (q r : ℕ), 0 < q →
    (∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r) →
    (B R).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  intro G _ _ Λ B hB R q r hq hr
  by_contra hlt
  push_neg at hlt
  have hC := hlt.ne_top
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hC
  have htfin : t.Finite := Set.encard_ne_top_iff.1 (by rw [htc, ← hm]; exact ENat.coe_ne_top (m + 1))
  have h := encard_finset_le_pow_mul Λ B hB R q r hq hr htfin.toFinset (by simpa using hts)
  rw [Set.Finite.coe_toFinset, htc, ← hm] at h
  norm_cast at h
  omega

end GlobalTheory.VolBr
