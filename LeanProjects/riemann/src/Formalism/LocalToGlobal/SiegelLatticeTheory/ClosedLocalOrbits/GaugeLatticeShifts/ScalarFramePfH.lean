import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfG

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth finrank_orth fvec_castSucc fvec_last mem_orth_Xplus
  X_le_orth_Xplus mem_ThPairs hT_add_left hT_sub_left hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem exists_hos : ∃ _P : HeightOneSpectrum (𝓞 E), True := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField E)
  exact ⟨⟨p, hp, hp0⟩, trivial⟩

theorem X_le_spanE_of_conv (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (g : ℕ) (hc : IsFixedConv Λ g F) :
    Xsp F ≤ spanE S (XLam Λ F) := by
  obtain ⟨P, -⟩ := exists_hos (E := E)
  have := P.isPrime
  obtain ⟨c, hc0, -, heq⟩ := hc.1 P
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have h1 : c a • F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
    rw [heq]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
  obtain ⟨s, hs, hsx⟩ := h1
  have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h, map_zero])
    rw [this]
    exact P.asIdeal.zero_mem
  have hmem : s • (c a • F.fl.e a) ∈ spanE S (XLam Λ F) := Submodule.subset_span hsx
  have e : F.fl.e a = ((algebraMap (𝓞 E) E s) * c a)⁻¹ • (s • (c a • F.fl.e a)) := by
    rw [algebra_compatible_smul E s, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs0 (hc0 a)),
      one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ hmem

theorem Xs_fvec (F : FlagG S r T) : Xs (S := S) F.fvec = F.X := by
  have h : (fun a : Fin r => F.fvec a.castSucc) = F.e := funext fun a => fvec_castSucc F a
  show Submodule.span E (Set.range fun a : Fin r => F.fvec a.castSucc) = _
  rw [h]
  rfl

theorem Xflag_top (F : LFlag S r T) : Xflag F r = Xsp F := by
  rw [Xflag, FlagG.Xa, Xsp, FlagG.X]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

theorem hT_X_X (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  refine key y (fun a => ?_) x hx
  rw [hT_swap]
  have h1 : S.hT y (F.e a) = 0 := key (F.e a) (fun b => F.e_iso b a) y hy
  rw [h1, star_zero]

theorem hT_z_X (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) : S.hT F.z y = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  rw [hT_swap, key F.z F.z_orth y hy, star_zero]

theorem hT_X_alt (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT x F.z = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  exact key F.z F.z_orth x hx

theorem theta_eq (Λ : Submodule (𝓞 E) S.V) (k : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (hn : finrank E S.V = k + 2 * r + 1)
    (hd1 : finrank E (UUE Λ F F') = 2 * r + 2) (hd2 : finrank E (UUE Λ F F'') = 2 * r + 2)
    (hU1 : UUE Λ F F' = Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)))
    (hG' : Gval F F' ≠ 0) (hs : s0 Λ F F' F'' β k = 1) :
    Th Λ F F' F'' β = Hp Λ F F' ∧ Th'' Λ F F' F'' β = Hp Λ F F'' := by
  have hH1 : finrank E (Hp Λ F F') + 1 = k := by
    have := finrank_orth S (UUE Λ F F')
    rw [Hp]
    omega
  have hH2 : finrank E (Hp Λ F F'') + 1 = k := by
    have := finrank_orth S (UUE Λ F F'')
    rw [Hp]
    omega
  have hTh : finrank E (Th Λ F F' F'' β) + 1 = k := by
    unfold s0 at hs
    omega
  have hThle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).1
  refine ⟨Submodule.eq_of_le_of_finrank_eq hThle (by omega), ?_⟩
  have hTh''le : Th'' Λ F F' F'' β ≤ Hp Λ F F'' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).2.1
  refine Submodule.eq_of_le_of_finrank_eq hTh''le ?_
  let f := (LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have hm := (mem_ThPairs Λ F F' F'' β p.1).1 p.2
    have h2 : p.1.2 = 0 := hp
    have hx1 : p.1.1 ∈ F.fl.X := by
      have := hm.2.2.1
      rwa [h2, sub_zero] at this
    have h1 : p.1.1 = 0 := by
      refine PI.ScalarPairDr.W.eq_zero_of_orth F.fl F'.fl hG' hx1 fun b => ?_
      have hm1 := hm.1
      rw [Hp, mem_orth] at hm1
      exact hm1 _ (by rw [hU1]; exact Submodule.subset_span ⟨Sum.inr b, rfl⟩)
    exact Subtype.ext (Prod.ext h1 h2)
  have hrange : LinearMap.range f = Th'' Λ F F' F'' β := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, hrange, finrank_bot] at h1
  have h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (ThPairs Λ F F' F'' β) :=
    Submodule.finrank_map_le _ _
  have h3 := Submodule.finrank_mono hTh''le
  omega

theorem ylift_tr (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hTh : Th Λ F F' F'' β = Hp Λ F F') {y : S.V} (hy : y ∈ UUE Λ F F'') (hyo : y ∈ orth S (Xplus F)) :
    y ∈ UUE Λ F F' := by
  rw [← orth_orth S (UUE Λ F F'), mem_orth]
  intro v hv
  have hv' : v ∈ Th Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT p.2 y = 0 := by
    have := (mem_orth S).1 hm.2.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (p.1 - p.2) y = 0 := (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
  have : p.1 = (p.1 - p.2) + p.2 := by abel
  show S.hT p.1 y = 0
  rw [this, hT_add_left, e1, e2, add_zero]

theorem ylift_tr' (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ UUE Λ F F') (hyo : y ∈ orth S (Xplus F)) :
    y ∈ UUE Λ F F'' := by
  rw [← orth_orth S (UUE Λ F F''), mem_orth]
  intro v hv
  have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT p.1 y = 0 := by
    have := (mem_orth S).1 hm.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (p.1 - p.2) y = 0 := (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
  have : p.2 = p.1 - (p.1 - p.2) := by abel
  show S.hT p.2 y = 0
  rw [this, hT_sub_left, e1, e2, sub_zero]

theorem ylift_beta (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hiso : ∀ x y, S.hT (β x) (β y) = S.hT x y) (hX : ∀ x ∈ Xsp F'', β.symm x ∈ Xsp F')
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ UUE Λ F F') (hyo : y ∈ orth S (Xsp F')) :
    β y ∈ UUE Λ F F'' := by
  rw [← orth_orth S (UUE Λ F F''), mem_orth]
  intro v hv
  have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT (β p.1) (β y) = 0 := by
    rw [hiso]
    have := (mem_orth S).1 hm.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (β p.1 - p.2) (β y) = 0 := by
    have h := hX _ hm.2.2.2
    have : β p.1 - p.2 = β (β.symm (β p.1 - p.2)) := (β.apply_symm_apply _).symm
    rw [this, hiso]
    exact (mem_orth S).1 hyo _ h
  have : p.2 = β p.1 - (β p.1 - p.2) := by abel
  show S.hT p.2 (β y) = 0
  rw [this, hT_sub_left, e1, e2, sub_zero]

end Lat

end Formalism.L2.SG.Pf.ScalarFramePf
