import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagTorus

theorem witt_partners {E V : Type} [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (hsymm : ∀ x y, star (h x y) = h y x)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {r : ℕ} (e : Fin r → V) (he : LinearIndependent E e)
    (hee : ∀ a b, h (e a) (e b) = 0) :
    ∃ f : Fin r → V, (∀ a b, h (e a) (f b) = if a = b then 1 else 0) ∧ ∀ a b, h (f a) (f b) = 0 := by
  classical
  let Φ : V →ₗ[E] (Fin r → E) := LinearMap.pi (fun a => h (e a))
  have hΦ : ∀ y a, Φ y a = h (e a) y := fun y a => rfl
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    apply hφ0
    have hvan : ∀ y, ∑ a, φ (Pi.single a 1) * h (e a) y = 0 := by
      intro y
      have hcomp : φ ∘ₗ Φ = 0 := by
        rw [← LinearMap.range_eq_bot, LinearMap.range_comp, hφ]
      have h0 : φ (Φ y) = 0 := LinearMap.congr_fun hcomp y
      rw [← h0]
      conv_rhs => rw [pi_eq_sum_univ (Φ y)]
      simp only [map_sum, map_smul, smul_eq_mul, hΦ, mul_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 2; ext j; simp [Pi.single_apply, eq_comm]
    have hz : ∑ a, star (φ (Pi.single a 1)) • e a = 0 := hnd _ (fun y => by
      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, RingHom.id_apply, Finset.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply, star_star]
      exact hvan y)
    have hc := Fintype.linearIndependent_iff.1 he _ hz
    ext a
    have := hc a
    simpa using this
  choose g hg using fun b : Fin r => hsurj (Pi.single b 1)
  have hge : ∀ a b, h (e a) (g b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hΦ, hg b, Pi.single_apply]
  have hg'e : ∀ a b, h (g a) (e b) = if b = a then 1 else 0 := by
    intro a b; rw [← hsymm, hge b a]; split_ifs <;> simp
  refine ⟨fun b => g b - ∑ c, (h (g c) (g b) / 2) • e c, ?_, ?_⟩
  · intro a b
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, hee, mul_zero, Finset.sum_const_zero, sub_zero, hge]
  · intro a b
    simp only [map_sub, map_sum, map_smulₛₗ, LinearMap.sub_apply, LinearMap.sum_apply, RingHom.id_apply, Finset.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hee, hge, hg'e, mul_zero, Finset.sum_const_zero, sub_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply]
    have hM : star (h (g b) (g a)) = h (g a) (g b) := hsymm _ _
    have h2 : star (2 : E) = 2 := by simp
    rw [star_div₀, hM, h2]
    have : (2 : E) ≠ 0 := two_ne_zero
    field_simp
    ring

theorem diag_isometry {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E) (hsymm : ∀ x y, star (h x y) = h y x)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {r : ℕ} (e f : Fin r → V)
    (hee : ∀ a b, h (e a) (e b) = 0) (hef : ∀ a b, h (e a) (f b) = if a = b then 1 else 0)
    (hff : ∀ a b, h (f a) (f b) = 0) (α : Fin r → E) (hα : ∀ a, α a ≠ 0) :
    ∃ t : V ≃ₗ[E] V, (∀ x y, h (t x) (t y) = h x y) ∧ (∀ a, t (e a) = α a • e a) ∧
      ∀ x, (∀ a, h (e a) x = 0) → t x - x ∈ Submodule.span E (Set.range e) := by
  classical
  set β : Fin r → E := fun a => (star (α a))⁻¹ with hβ
  have hβ1 : ∀ a, star (β a) * α a = 1 := by
    intro a; simp only [hβ, star_inv₀, star_star]; exact inv_mul_cancel₀ (hα a)
  have hβ2 : ∀ a, star (α a) * β a = 1 := by
    intro a; simp only [hβ]; exact mul_inv_cancel₀ (star_ne_zero.2 (hα a))
  have hfe : ∀ a b, h (f a) (e b) = if a = b then 1 else 0 := by
    intro a b; rw [← hsymm, hef b a]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  let L : V →ₗ[E] V := LinearMap.id + ∑ a, (α a - 1) • (h (f a)).smulRight (e a) +
    ∑ a, (β a - 1) • (h (e a)).smulRight (f a)
  have hL : ∀ x, L x = x + ∑ a, ((α a - 1) * h (f a) x) • e a + ∑ a, ((β a - 1) * h (e a) x) • f a := by
    intro x; simp [L, LinearMap.sum_apply, mul_smul]
  have key_e : ∀ b y, h (e b) (L y) = β b * h (e b) y := by
    intro b y
    rw [hL]
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hee, hef, mul_zero, Finset.sum_const_zero, add_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have key_f : ∀ b y, h (f b) (L y) = α b * h (f b) y := by
    intro b y
    rw [hL]
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hff, hfe, mul_zero, Finset.sum_const_zero, add_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have key_x : ∀ x y, h x (L y) = h x y + ∑ a, ((α a - 1) * h (f a) y) * star (h (e a) x) +
      ∑ a, ((β a - 1) * h (e a) y) * star (h (f a) x) := by
    intro x y
    rw [hL]
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hsymm]
  have hiso : ∀ x y, h (L x) (L y) = h x y := by
    intro x y
    rw [hL x]
    simp only [map_add, LinearMap.add_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, key_e, key_f, key_x, RingHom.id_apply, starRingEnd_apply]
    have : ∀ a, ((α a - 1) * h (f a) y) * star (h (e a) x) + ((β a - 1) * h (e a) y) * star (h (f a) x) +
        star ((α a - 1) * h (f a) x) * (β a * h (e a) y) + star ((β a - 1) * h (e a) x) * (α a * h (f a) y) = 0 := by
      intro a
      simp only [star_mul', star_sub, star_one]
      linear_combination (star (h (e a) x) * h (f a) y) * hβ1 a + (star (h (f a) x) * h (e a) y) * hβ2 a
    have hsum := Finset.sum_eq_zero (s := Finset.univ) (fun a _ => this a)
    simp only [Finset.sum_add_distrib] at hsum
    linear_combination hsum
  have hinj : Function.Injective L := by
    intro x y hxy
    have : x - y = 0 := hnd _ (fun z => by
      rw [← hiso, map_sub, hxy, sub_self, map_zero, LinearMap.zero_apply])
    exact sub_eq_zero.1 this
  refine ⟨LinearEquiv.ofInjectiveEndo L hinj, ?_, ?_, ?_⟩
  · intro x y; simpa using hiso x y
  · intro a
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    rw [hL]
    simp only [hfe, hee, mul_zero, zero_smul, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      ite_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_smul, one_smul]; abel
  · intro x hx
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    rw [hL]
    simp only [hx, mul_zero, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem flag_torus (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (γ : GV D) (hγ : γ ∈ stabF D F0) :
    ∃ t ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, (∀ x ∈ perpS (VS D) F0.X, t x - x ∈ F0.X) ∧
      Adapt (t * γ) (lf D F0) (lf D F0) := by
  obtain ⟨hγi, hγX, hγz⟩ := hγ
  have hsymm : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have hnd : ∀ x, (∀ y, (VS D).hT x y = 0) → x = 0 := fun x hx => (VS D).nondeg.1 x hx
  obtain ⟨f, hef, hff⟩ := witt_partners (VS D).hT hsymm hnd F0.e F0.e_indep F0.e_iso

  have hXa_succ : ∀ i : Fin D.R.rS, F0.Xa ((i : ℕ) + 1) = F0.Xa i ⊔ Submodule.span D.host.E {F0.e i} := by
    intro i
    have : {j : Fin D.R.rS | (j : ℕ) < (i : ℕ) + 1} = {j : Fin D.R.rS | (j : ℕ) < i} ∪ ({i} : Set (Fin D.R.rS)) := by
      ext j; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hj; rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact Or.inl h
        · exact Or.inr (Fin.ext h)
      · rintro (h | rfl) <;> omega
    simp only [FlagG.Xa, this, Set.image_union, Set.image_singleton, Submodule.span_union]
  have hXa_top : F0.Xa D.R.rS = F0.X := by
    have : {j : Fin D.R.rS | (j : ℕ) < D.R.rS} = Set.univ := by ext j; simp [j.2]
    simp only [FlagG.Xa, FlagG.X, this, Set.image_univ]
  have he_mem : ∀ i : Fin D.R.rS, F0.e i ∈ F0.Xa ((i : ℕ) + 1) := fun i =>
    Submodule.subset_span ⟨i, by simp, rfl⟩
  have he_not : ∀ i : Fin D.R.rS, F0.e i ∉ F0.Xa i := fun i =>
    F0.e_indep.notMem_span_image (s := {j | (j : ℕ) < i}) (x := i) (by simp)
  have hdiag : ∀ i : Fin D.R.rS, ∃ u : D.host.E, u ≠ 0 ∧ γ (F0.e i) - u • F0.e i ∈ F0.Xa i := by
    intro i
    have h1 : γ (F0.e i) ∈ F0.Xa ((i : ℕ) + 1) := by
      rw [← hγX ((i : ℕ) + 1)]; exact Submodule.mem_map_of_mem (he_mem i)
    rw [hXa_succ i, Submodule.mem_sup] at h1
    obtain ⟨y, hy, w, hw, hyw⟩ := h1
    obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hw
    refine ⟨u, ?_, ?_⟩
    · rintro rfl
      apply he_not i
      have : γ (F0.e i) ∈ (F0.Xa i).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
        rw [hγX i, ← hyw]; simpa using hy
      obtain ⟨w', hw', hw'e⟩ := Submodule.mem_map.1 this
      have : w' = F0.e i := γ.injective hw'e
      exact this ▸ hw'
    · rw [← hyw]; simpa using hy
  choose u hu0 hu using hdiag
  obtain ⟨t, ht_iso, ht_e, ht_perp⟩ := diag_isometry (VS D).hT hsymm hnd F0.e f F0.e_iso hef hff
    (fun i => (u i)⁻¹) (fun i => inv_ne_zero (hu0 i))
  have ht_mem : t ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun x y => ht_iso x y
  have ht_Xa : ∀ (j : ℕ), ∀ y ∈ F0.Xa j, t y ∈ F0.Xa j := by
    intro j y hy
    have : F0.Xa j ≤ (F0.Xa j).comap (t : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [FlagG.Xa, Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, ht_e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    exact this hy
  have hperp : ∀ x ∈ perpS (VS D) F0.X, t x - x ∈ F0.X := by
    intro x hx
    exact ht_perp x (fun a => hx (F0.e a) (Submodule.subset_span ⟨a, rfl⟩))
  refine ⟨t, ht_mem, hperp, Subgroup.mul_mem _ ht_mem hγi, ?_⟩
  intro a
  induction a using Fin.lastCases with
  | last =>
    simp only [frame, lf, FlagG.fvec, Fin.snoc_last, Fin.val_last, LinearEquiv.mul_apply, hγz, Xflag]
    rw [hXa_top]
    exact hperp _ (fun x hx => by
      have := Submodule.span_le (p := LinearMap.ker ((VS D).hT.flip F0.z)) |>.2 (by
        rintro _ ⟨a, rfl⟩; simpa using F0.z_orth a) hx
      simpa using this)
  | cast i =>
    simp only [frame, lf, FlagG.fvec, Fin.snoc_castSucc, Fin.coe_castSucc, LinearEquiv.mul_apply, Xflag]
    have : γ (F0.e i) = (γ (F0.e i) - u i • F0.e i) + u i • F0.e i := by abel
    rw [this, map_add, map_smul, ht_e, smul_smul, mul_inv_cancel₀ (hu0 i), one_smul, add_sub_cancel_right]
    exact ht_Xa _ _ (hu i)

end GlobalTheory.FlagTorus
