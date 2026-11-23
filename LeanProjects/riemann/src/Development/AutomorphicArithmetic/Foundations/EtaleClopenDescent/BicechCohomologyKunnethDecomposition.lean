import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BicechC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZero

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD
open scoped TensorProduct

namespace UpperTheory.Cb.Kun

section Abstract

variable {k : Type} [Field k] {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

structure Gr (k V : Type) [Field k] [AddCommGroup V] [Module k V] where
  d : V →ₗ[k] V
  π : ℕ → V →ₗ[k] V
  σ : V →ₗ[k] V
  N : ℕ
  dd : ∀ a, d (d a) = 0
  idem : ∀ c a, π c (π c a) = π c a
  orth : ∀ c c' a, c ≠ c' → π c (π c' a) = 0
  sum : ∀ a, ∑ c ∈ Finset.range N, π c a = a
  zero : ∀ a, π 0 a = 0
  dπ : ∀ c a, d (π c a) = π (c + 1) (d a)
  σπ : ∀ c a, σ (π c a) = ((-1 : ℤ) ^ (c + 1)) • π c a

theorem exists_reg (f : V →ₗ[k] V) : ∃ g : V →ₗ[k] V, ∀ a, f (g (f a)) = f a := by
  obtain ⟨g', hg'⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g'
  refine ⟨g, fun a => ?_⟩
  have h1 : g (f a) = g' (f.rangeRestrict a) := by
    have := LinearMap.congr_fun hg (f.rangeRestrict a)
    simpa using this
  rw [h1]
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hg' (f.rangeRestrict a))
  simpa using h2

namespace Gr

variable (G : Gr k V)

theorem big {c : ℕ} (hc : G.N ≤ c) (a : V) : G.π c a = 0 := by
  rw [← G.sum a, map_sum]
  refine Finset.sum_eq_zero fun c' hc' => G.orth _ _ _ ?_
  have := Finset.mem_range.1 hc'
  omega

theorem ext' {U : Type} [AddCommGroup U] [Module k U] {X Y : V →ₗ[k] U}
    (h : ∀ c a, X (G.π c a) = Y (G.π c a)) (a : V) : X a = Y a := by
  rw [← G.sum a, map_sum, map_sum]
  exact Finset.sum_congr rfl fun c _ => h c a

theorem σσ (a : V) : G.σ (G.σ a) = a := by
  refine G.ext' (X := G.σ ∘ₗ G.σ) (Y := LinearMap.id) (fun c a => ?_) a
  simp only [LinearMap.comp_apply, LinearMap.id_apply, G.σπ, map_zsmul, smul_smul]
  rw [← mul_pow]
  simp

theorem σd (a : V) : G.σ (G.d a) = - G.d (G.σ a) := by
  refine G.ext' (X := G.σ ∘ₗ G.d) (Y := -(G.d ∘ₗ G.σ)) (fun c a => ?_) a
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, G.σπ, map_zsmul, G.dπ, pow_succ]
  simp

theorem exists_contraction : ∃ e h : V →ₗ[k] V,
    (∀ a, G.d (e a) = 0) ∧ (∀ a, e (G.d a) = 0) ∧ (∀ a, G.d (h a) + h (G.d a) + e a = a) ∧
    (∀ c a, h (G.π (c + 1) a) = G.π c (h a)) ∧ (∀ c a, e (G.π c a) = G.π c (e a)) := by
  obtain ⟨g, hg⟩ := exists_reg G.d
  let h : V →ₗ[k] V := ∑ c ∈ Finset.range G.N, G.π c ∘ₗ g ∘ₗ G.π (c + 1)
  have happ : ∀ a, h a = ∑ c ∈ Finset.range G.N, G.π c (g (G.π (c + 1) a)) := fun a => by
    simp [h, LinearMap.sum_apply]
  have hπ : ∀ c a, h (G.π (c + 1) a) = G.π c (h a) := by
    intro c a
    rw [happ, happ, map_sum]
    by_cases hc : c < G.N
    · rw [Finset.sum_eq_single c, Finset.sum_eq_single c]
      · rw [G.idem, G.idem]
      · intro b _ hb
        rw [G.orth _ _ _ hb.symm]
      · intro h'; exact absurd (Finset.mem_range.2 hc) h'
      · intro b _ hb
        rw [G.orth (b + 1) (c + 1) _ (by omega)]
        simp
      · intro h'; exact absurd (Finset.mem_range.2 hc) h'
    · have : G.N ≤ c := by omega
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro b _
        rw [G.big this]
      · intro b hb
        have := Finset.mem_range.1 hb
        rw [G.orth (b + 1) (c + 1) _ (by omega)]
        simp
  have hdhd : ∀ a, G.d (h (G.d a)) = G.d a := by
    intro a
    rw [happ, map_sum]
    conv_rhs => rw [← G.sum a, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← G.dπ, G.dπ c (g _), hg]
    rw [G.dπ c a, G.idem]
  let e : V →ₗ[k] V := LinearMap.id - G.d ∘ₗ h - h ∘ₗ G.d
  have eapp : ∀ a, e a = a - G.d (h a) - h (G.d a) := fun a => rfl
  refine ⟨e, h, ?_, ?_, ?_, hπ, ?_⟩
  · intro a
    rw [eapp]
    simp [G.dd, hdhd]
  · intro a
    rw [eapp]
    simp [G.dd, hdhd]
  · intro a
    rw [eapp]
    abel
  · intro c a
    rcases c with _ | c
    · rw [G.zero, G.zero]
      simp
    · rw [eapp, eapp, map_sub, map_sub, hπ c a, G.dπ c, G.dπ (c + 1) a, hπ (c + 1)]

end Gr

def Dt (G : Gr k V) (G' : Gr k W) : V ⊗[k] W →ₗ[k] V ⊗[k] W :=
  TensorProduct.map G.d LinearMap.id + TensorProduct.map G.σ G'.d

def Tn (G : Gr k V) (G' : Gr k W) (n : ℤ) : Submodule k (V ⊗[k] W) :=
  Submodule.span k {x | ∃ (a : V) (b : W) (p q : ℕ), G.π p a = a ∧ G'.π q b = b ∧ ((p + q : ℕ) : ℤ) = n ∧ x = a ⊗ₜ[k] b}

def Zn (G : Gr k V) (G' : Gr k W) (n : ℤ) : Submodule k (V ⊗[k] W) :=
  Submodule.span k {x | ∃ (a : V) (b : W) (p q : ℕ), G.π p a = a ∧ G'.π q b = b ∧ ((p + q : ℕ) : ℤ) = n ∧
    G.d a = 0 ∧ G'.d b = 0 ∧ x = a ⊗ₜ[k] b}

theorem tensor_kunneth (G : Gr k V) (G' : Gr k W) (n : ℤ) (t : V ⊗[k] W) (ht : t ∈ Tn G G' n) (hD : Dt G G' t = 0) :
    ∃ s ∈ Tn G G' (n - 1), t - Dt G G' s ∈ Zn G G' n := by
  obtain ⟨e, h, de, ed, deh, hπ, eπ⟩ := G.exists_contraction
  obtain ⟨e', h', de', ed', deh', hπ', eπ'⟩ := G'.exists_contraction
  have hσ : ∀ a, h (G.σ a) = - G.σ (h a) := by
    intro a
    refine G.ext' (X := h ∘ₗ G.σ) (Y := -(G.σ ∘ₗ h)) (fun c a => ?_) a
    rcases c with _ | c
    · simp [G.zero]
    · simp only [LinearMap.comp_apply, LinearMap.neg_apply, G.σπ, map_zsmul, hπ, pow_succ]
      simp
  have eσ : ∀ a, e (G.σ a) = G.σ (e a) := by
    intro a
    refine G.ext' (X := e ∘ₗ G.σ) (Y := G.σ ∘ₗ e) (fun c a => ?_) a
    simp only [LinearMap.comp_apply, G.σπ, map_zsmul, eπ]
  let H : V ⊗[k] W →ₗ[k] V ⊗[k] W := TensorProduct.map h LinearMap.id + TensorProduct.map (G.σ ∘ₗ e) h'
  have key : (Dt G G') ∘ₗ H + H ∘ₗ (Dt G G') + TensorProduct.map e e' = LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    have e1 : a ⊗ₜ[k] b = (G.d (h a) + h (G.d a) + e a) ⊗ₜ[k] b := by rw [deh]
    have e2 : e a ⊗ₜ[k] b = e a ⊗ₜ[k] (G'.d (h' b) + h' (G'.d b) + e' b) := by rw [deh']
    have e3 : G.d (G.σ (e a)) = 0 := by
      have := G.σd (e a)
      rw [de, map_zero] at this
      exact neg_eq_zero.1 this.symm
    simp only [H, Dt, LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, map_add,
      e3, ed, eσ, hσ, G.σσ, map_zero, TensorProduct.zero_tmul, TensorProduct.tmul_zero, TensorProduct.neg_tmul]
    rw [e1, TensorProduct.add_tmul, TensorProduct.add_tmul, e2, TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel
  have hH : ∀ x ∈ Tn G G' n, H x ∈ Tn G G' (n - 1) := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => H x ∈ Tn G G' (n - 1)) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, b, p, q, hp, hq, hn, rfl⟩
      simp only [H, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply]
      refine add_mem ?_ ?_
      · rcases p with _ | p
        · have : a = 0 := by rw [← hp, G.zero]
          simp [this]
        · have h1 : h a = G.π p (h a) := by rw [← hπ, hp]
          refine Submodule.subset_span ⟨h a, b, p, q, ?_, hq, ?_, rfl⟩
          · exact h1.symm
          · push_cast at hn ⊢
            omega
      · rcases q with _ | q
        · have : b = 0 := by rw [← hq, G'.zero]
          simp [this]
        · have h1 : h' b = G'.π q (h' b) := by rw [← hπ', hq]
          have h2 : e a = G.π p (e a) := by rw [← eπ, hp]
          refine Submodule.subset_span ⟨G.σ (e a), h' b, p, q, ?_, h1.symm, ?_, rfl⟩
          · rw [h2, G.σπ, map_zsmul, G.idem]
          · push_cast at hn ⊢
            omega
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx
  refine ⟨H t, hH t ht, ?_⟩
  have h3 : t - Dt G G' (H t) = TensorProduct.map e e' t := by
    have := LinearMap.congr_fun key t
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hD, map_zero, add_zero] at this
    rw [sub_eq_iff_eq_add]
    rw [add_comm]
    exact this.symm
  rw [h3]
  refine Submodule.span_induction (p := fun x _ => TensorProduct.map e e' x ∈ Zn G G' n) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨a, b, p, q, hp, hq, hn, rfl⟩
    refine Submodule.subset_span ⟨e a, e' b, p, q, ?_, ?_, hn, de a, de' b, by simp⟩
    · rw [← eπ, hp]
    · rw [← eπ', hq]
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

end Abstract

section Concrete

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']

def coch (F : Finset ι → Submodule k E) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s => if s.Nonempty then F s else ⊥

theorem mem_coch {F : Finset ι → Submodule k E} {a : Finset ι → E} : a ∈ coch F ↔ a ∅ = 0 ∧ ∀ s, a s ∈ F s := by
  constructor
  · intro h
    have h' : ∀ s, a s ∈ (if s.Nonempty then F s else ⊥) := fun s => (Submodule.mem_pi.1 h) s (Set.mem_univ _)
    have h0 : a ∅ = 0 := by simpa using h' ∅
    refine ⟨h0, fun s => ?_⟩
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [h0]
      exact zero_mem _
    · simpa [hs] using h' s
  · rintro ⟨h0, h⟩
    refine Submodule.mem_pi.2 fun s _ => ?_
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using h0
    · simpa [hs] using h s

variable (k ι E) in

def prL (c : ℕ) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  LinearMap.pi fun s => if s.card = c then LinearMap.proj s else 0

variable (k ι E) in

def sgL : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  LinearMap.pi fun s => ((-1 : ℤ) ^ (s.card + 1)) • LinearMap.proj s

theorem prL_apply (c : ℕ) (a : Finset ι → E) (s : Finset ι) : prL k ι E c a s = if s.card = c then a s else 0 := by
  simp only [prL, LinearMap.pi_apply]
  split_ifs <;> simp

theorem sgL_apply (a : Finset ι → E) (s : Finset ι) : sgL k ι E a s = ((-1 : ℤ) ^ (s.card + 1)) • a s := by
  simp [sgL]

theorem deltaL_apply (a : Finset ι → E) (s : Finset ι) :
    deltaL k ι E a s = ∑ i ∈ s, GlobalTheory.cubeSign s i • a (s.erase i) := rfl

theorem delta_mem {F : Finset ι → Submodule k E} (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t)
    (a : Finset ι → E) (ha : a ∈ coch F) : deltaL k ι E a ∈ coch F := by
  obtain ⟨h0, h⟩ := mem_coch.1 ha
  refine mem_coch.2 ⟨by simp [deltaL_apply], fun s => ?_⟩
  rw [deltaL_apply]
  refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
  rcases (s.erase i).eq_empty_or_nonempty with h1 | h1
  · rw [h1, h0]
    exact zero_mem _
  · exact hF _ _ h1 (Finset.erase_subset _ _) (h _)

theorem prL_mem {F : Finset ι → Submodule k E} (c : ℕ) (a : Finset ι → E) (ha : a ∈ coch F) :
    prL k ι E c a ∈ coch F := by
  obtain ⟨h0, h⟩ := mem_coch.1 ha
  refine mem_coch.2 ⟨by simp [prL_apply, h0], fun s => ?_⟩
  rw [prL_apply]
  split_ifs
  · exact h s
  · exact zero_mem _

theorem sgL_mem {F : Finset ι → Submodule k E} (a : Finset ι → E) (ha : a ∈ coch F) :
    sgL k ι E a ∈ coch F := by
  obtain ⟨h0, h⟩ := mem_coch.1 ha
  refine mem_coch.2 ⟨by simp [sgL_apply, h0], fun s => ?_⟩
  rw [sgL_apply]
  exact zsmul_mem (h s) _

def grC [Fintype ι] (F : Finset ι → Submodule k E) (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t) : Gr k (coch F) where
  d := (deltaL k ι E).restrict (delta_mem hF)
  π c := (prL k ι E c).restrict (prL_mem c)
  σ := (sgL k ι E).restrict sgL_mem
  N := Fintype.card ι + 1
  dd a := Subtype.ext (GlobalTheory.DI.delta_delta a.1)
  idem c a := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.restrict_coe_apply, prL_apply]
    split_ifs <;> rfl
  orth c c' a h := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.restrict_coe_apply, prL_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    · rfl
    · rfl
  sum a := by
    refine Subtype.ext (funext fun s => ?_)
    have hs : s.card < Fintype.card ι + 1 := Nat.lt_succ_of_le (Finset.card_le_univ s)
    simp [prL_apply, Finset.sum_apply, hs]
  zero a := by
    refine Subtype.ext (funext fun s => ?_)
    have h0 := (mem_coch.1 a.2).1
    simp only [LinearMap.restrict_coe_apply, prL_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    split_ifs with h
    · rw [Finset.card_eq_zero.1 h]
      exact h0
    · rfl
  dπ c a := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.restrict_coe_apply, prL_apply, deltaL_apply]
    split_ifs with h
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [if_pos]
      rw [Finset.card_erase_of_mem hi]
      omega
    · refine Finset.sum_eq_zero fun i hi => ?_
      rw [if_neg, smul_zero]
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
  σπ c a := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.restrict_coe_apply, prL_apply, sgL_apply, Submodule.coe_smul_of_tower, Pi.smul_apply]
    split_ifs with h
    · rw [h]
    · simp

def phi (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') :
    coch A ⊗[k] coch B →ₗ[k] (Finset ι × Finset κ → E'') :=
  TensorProduct.lift (LinearMap.mk₂ k (fun a b => boxC μ a.1 b.1)
    (fun a a' b => by funext x; simp [boxC]) (fun c a b => by funext x; simp [boxC])
    (fun a b b' => by funext x; simp [boxC]) (fun c a b => by funext x; simp [boxC]))

theorem phi_tmul (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E')
    (a : coch A) (b : coch B) : phi μ A B (a ⊗ₜ[k] b) = boxC μ a.1 b.1 := by
  simp [phi]

theorem phi_Dt [Fintype ι] [Fintype κ] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
    (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) (t : coch A ⊗[k] coch B) :
    phi μ A B (Dt (grC A hA) (grC B hB) t) = biD k ι κ E'' (phi μ A B t) := by
  have h : phi μ A B ∘ₗ Dt (grC A hA) (grC B hB) = biD k ι κ E'' ∘ₗ phi μ A B := by
    refine TensorProduct.ext' fun a b => ?_
    funext x
    simp only [LinearMap.comp_apply, Dt, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply, map_add,
      phi_tmul, Pi.add_apply]
    simp only [biD, boxC, grC, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, LinearMap.restrict_coe_apply, deltaL_apply, sgL_apply, map_sum, map_zsmul]
    congr 1
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  exact LinearMap.congr_fun h t

def rL (F : Finset ι → Submodule k E) (I : Finset ι) : coch F →ₗ[k] F I :=
  LinearMap.codRestrict (F I) (LinearMap.proj I ∘ₗ (coch F).subtype) fun a => (mem_coch.1 a.2).2 I

theorem rL_val (F : Finset ι → Submodule k E) (I : Finset ι) (a : coch F) : (rL F I a : E) = a.1 I := rfl

theorem single_mem_coch (F : Finset ι → Submodule k E) {I : Finset ι} (h : I.Nonempty) (x : F I) :
    (LinearMap.single k (fun _ : Finset ι => E) I ∘ₗ (F I).subtype) x ∈ coch F := by
  refine mem_coch.2 ⟨?_, fun s => ?_⟩
  · have : (∅ : Finset ι) ≠ I := fun h' => by simp [← h'] at h
    simp [Pi.single_apply, this]
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_single, Pi.single_apply]
    split_ifs with h'
    · subst h'
      exact x.2
    · exact zero_mem _

open Classical in

def iL (F : Finset ι → Submodule k E) (I : Finset ι) : F I →ₗ[k] coch F :=
  if h : I.Nonempty then LinearMap.codRestrict (coch F) _ (single_mem_coch F h) else 0

open Classical in
theorem iL_val (F : Finset ι → Submodule k E) (I : Finset ι) (x : F I) (s : Finset ι) :
    (iL F I x).1 s = if I.Nonempty ∧ s = I then x.1 else 0 := by
  by_cases h : I.Nonempty
  · by_cases h' : s = I
    · subst h'
      simp [iL, h]
    · simp [iL, h, h', Pi.single_apply]
  · simp [iL, h]

theorem sum_iL [Fintype ι] (F : Finset ι → Submodule k E) (a : coch F) : ∑ I, iL F I (rL F I a) = a := by
  refine Subtype.ext (funext fun s => ?_)
  rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single s]
  · rw [iL_val]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp [(mem_coch.1 a.2).1]
    · simp [hs, rL_val]
  · intro b _ hb
    rw [iL_val, if_neg]
    exact fun h => hb h.2.symm
  · simp

theorem phi_inj [Fintype ι] [Fintype κ] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (h : Disjoint₂ μ A B) : Function.Injective (phi μ A B) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  have ev : ∀ I J, (TensorProduct.lift (μ.compl₁₂ (A I).subtype (B J).subtype)) ∘ₗ TensorProduct.map (rL A I) (rL B J) =
      LinearMap.proj (I, J) ∘ₗ phi μ A B := by
    intro I J
    refine TensorProduct.ext' fun a b => ?_
    simp [phi_tmul, boxC, rL_val]
  have step : ∀ I J, TensorProduct.map (rL A I) (rL B J) t = 0 := by
    intro I J
    apply h I J
    have := LinearMap.congr_fun (ev I J) t
    simp only [LinearMap.comp_apply, ht] at this
    simpa using this
  have tot : (∑ I, ∑ J, TensorProduct.map (iL A I) (iL B J) ∘ₗ TensorProduct.map (rL A I) (rL B J)) =
      (LinearMap.id : coch A ⊗[k] coch B →ₗ[k] coch A ⊗[k] coch B) := by
    refine TensorProduct.ext' fun a b => ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, sum_iL]
  have := LinearMap.congr_fun tot t
  rw [LinearMap.id_apply] at this
  rw [← this]
  simp [LinearMap.sum_apply, step]

theorem val_of_pi [Fintype ι] {F : Finset ι → Submodule k E} (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t) {p : ℕ}
    {a : coch F} (h : (grC F hF).π p a = a) {s : Finset ι} (hs : s.card ≠ p) : a.1 s = 0 := by
  rw [← h]
  show prL k ι E p a.1 s = 0
  rw [prL_apply, if_neg hs]

theorem mem_cechC [Fintype ι] {F : Finset ι → Submodule k E} (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t) {p : ℕ}
    {a : coch F} (h : (grC F hF).π p a = a) : a.1 ∈ cechC F ((p : ℤ) - 1) := by
  refine Submodule.mem_pi.2 fun s _ => ?_
  split_ifs with hs
  · exact (mem_coch.1 a.2).2 s
  · rw [Submodule.mem_bot]
    rcases s.eq_empty_or_nonempty with rfl | h1
    · exact (mem_coch.1 a.2).1
    · refine val_of_pi hF h fun h2 => hs ⟨h1, ?_⟩
      rw [h2]
      ring

theorem pi_iL [Fintype ι] (F : Finset ι → Submodule k E) (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t) (I : Finset ι)
    (x : F I) : (grC F hF).π I.card (iL F I x) = iL F I x := by
  refine Subtype.ext (funext fun s => ?_)
  show prL k ι E I.card (iL F I x).1 s = _
  rw [prL_apply, iL_val]
  split_ifs with h1 h2 h2
  · rfl
  · rfl
  · exact absurd (by rw [h2.2]) h1
  · rfl

theorem phi_mem [Fintype ι] [Fintype κ] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
    (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) (n : ℤ) (t : coch A ⊗[k] coch B)
    (ht : t ∈ Tn (grC A hA) (grC B hB) (n + 2)) : phi μ A B t ∈ bicechC μ A B n := by
  refine Submodule.span_induction (p := fun x _ => phi μ A B x ∈ bicechC μ A B n) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨a, b, p, q, hp, hq, hn, rfl⟩
    rw [phi_tmul]
    refine Submodule.mem_pi.2 fun x _ => ?_
    split_ifs with hx
    · exact Submodule.apply_mem_map₂ _ ((mem_coch.1 a.2).2 x.1) ((mem_coch.1 b.2).2 x.2)
    · rw [Submodule.mem_bot]
      show μ (a.1 x.1) (b.1 x.2) = 0
      rcases x.1.eq_empty_or_nonempty with h1 | h1
      · rw [h1, (mem_coch.1 a.2).1]
        simp
      rcases x.2.eq_empty_or_nonempty with h2 | h2
      · rw [h2, (mem_coch.1 b.2).1]
        simp
      by_cases h3 : x.1.card = p
      · by_cases h4 : x.2.card = q
        · refine absurd ⟨h1, h2, ?_⟩ hx
          rw [h3, h4]
          linarith
        · rw [val_of_pi hB hq h4]
          simp
      · rw [val_of_pi hA hp h3]
        simp
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem phi_surj [Fintype ι] [Fintype κ] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
    (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) (n : ℤ) (z : Finset ι × Finset κ → E'')
    (hz : z ∈ bicechC μ A B n) : ∃ t ∈ Tn (grC A hA) (grC B hB) (n + 2), phi μ A B t = z := by
  suffices h : z ∈ (Tn (grC A hA) (grC B hB) (n + 2)).map (phi μ A B) from h
  rw [← Finset.univ_sum_single z]
  refine Submodule.sum_mem _ fun x _ => ?_
  have hx := (Submodule.mem_pi.1 hz) x (Set.mem_univ _)
  split_ifs at hx with hc
  · have hle : Submodule.map₂ μ (A x.1) (B x.2) ≤
        ((Tn (grC A hA) (grC B hB) (n + 2)).map (phi μ A B)).comap (LinearMap.single k (fun _ => E'') x) := by
      rw [Submodule.map₂_le]
      intro m hm m' hm'
      refine ⟨iL A x.1 ⟨m, hm⟩ ⊗ₜ[k] iL B x.2 ⟨m', hm'⟩, Submodule.subset_span
        ⟨_, _, x.1.card, x.2.card, pi_iL A hA _ _, pi_iL B hB _ _, ?_, rfl⟩, ?_⟩
      · rw [hc.2.2]
      · rw [phi_tmul]
        funext y
        by_cases hy : y = x
        · subst hy
          simp [boxC, iL_val, hc.1, hc.2.1]
        · have : ¬ (y.1 = x.1 ∧ y.2 = x.2) := fun h => hy (Prod.ext h.1 h.2)
          by_cases h1 : y.1 = x.1
          · have h2 : y.2 ≠ x.2 := fun h => this ⟨h1, h⟩
            simp [boxC, iL_val, h2, hy, Pi.single_apply]
          · simp [boxC, iL_val, h1, hy, Pi.single_apply]
    exact hle hx
  · rw [Submodule.mem_bot] at hx
    rw [hx]
    simp

theorem fin_family {M : Type} [AddCommGroup M] [Module k M] (S : Set M) (hS : ∀ (c : k), ∀ x ∈ S, c • x ∈ S) {x : M}
    (hx : x ∈ Submodule.span k S) : ∃ (m : ℕ) (f : Fin m → M), (∀ l, f l ∈ S) ∧ x = ∑ l, f l := by
  refine Submodule.span_induction (p := fun x _ => ∃ (m : ℕ) (f : Fin m → M), (∀ l, f l ∈ S) ∧ x = ∑ l, f l)
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    exact ⟨1, fun _ => x, fun _ => hx, by simp⟩
  · exact ⟨0, Fin.elim0, fun l => l.elim0, by simp⟩
  · rintro x y _ _ ⟨m, f, hf, rfl⟩ ⟨m', g, hg, rfl⟩
    refine ⟨m + m', Fin.append f g, fun l => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l
      · simpa using hf i
      · simpa using hg i
    · simp [Fin.sum_univ_add]
  · rintro c x _ ⟨m, f, hf, rfl⟩
    exact ⟨m, fun l => c • f l, fun l => hS c _ (hf l), by rw [Finset.smul_sum]⟩

def boxes (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (n : ℤ) :
    Set (Finset ι × Finset κ → E'') :=
  {x | ∃ (p : ℤ) (a : Finset ι → E) (b : Finset κ → E'), a ∈ (cech A).Z p ∧ b ∈ (cech B).Z (n - p) ∧ x = boxC μ a b}

theorem phi_boxes [Fintype ι] [Fintype κ] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
    (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) (n : ℤ) (u : coch A ⊗[k] coch B)
    (hu : u ∈ Zn (grC A hA) (grC B hB) (n + 2)) : phi μ A B u ∈ Submodule.span k (boxes μ A B n) := by
  refine Submodule.span_induction (p := fun x _ => phi μ A B x ∈ Submodule.span k (boxes μ A B n)) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨a, b, p, q, hp, hq, hn, ha, hb, rfl⟩
    refine Submodule.subset_span ⟨(p : ℤ) - 1, a.1, b.1, ?_, ?_, phi_tmul μ A B a b⟩
    · exact Submodule.mem_inf.2 ⟨mem_cechC hA hp, congrArg Subtype.val ha⟩
    · have h1 : n - ((p : ℤ) - 1) = (q : ℤ) - 1 := by
        push_cast at hn
        omega
      rw [h1]
      exact Submodule.mem_inf.2 ⟨mem_cechC hB hq, congrArg Subtype.val hb⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem boxes_smul (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (n : ℤ)
    (c : k) (x : Finset ι × Finset κ → E'') (hx : x ∈ boxes μ A B n) : c • x ∈ boxes μ A B n := by
  obtain ⟨p, a, b, ha, hb, rfl⟩ := hx
  refine ⟨p, c • a, b, Submodule.smul_mem _ _ ha, hb, ?_⟩
  funext y
  simp [boxC]

end Concrete

end UpperTheory.Cb.Kun

open UpperTheory.Cb.Kun in
theorem UpperTheory.Cb.bicech_cohomology_kunneth_decomposition : ∀ (k : Type) [Field k] (ι κ : Type) [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ] (E E' E'' : Type) [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E'), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) → Disjoint₂ μ A B → ∀ (n : ℤ), ∀ z ∈ (bicech μ A B).Z n, ∃ (m : ℕ) (p : Fin m → ℤ) (a : Fin m → Finset ι → E) (b : Fin m → Finset κ → E'), (∀ l, a l ∈ (cech A).Z (p l) ∧ b l ∈ (cech B).Z (n - p l)) ∧ z - ∑ l, boxC μ (a l) (b l) ∈ (bicech μ A B).B n := by
  intro k _ ι κ _ _ _ _ E E' E'' _ _ _ _ _ _ μ A B hA hB hD n z hz
  obtain ⟨hzC, hzD⟩ := Submodule.mem_inf.1 hz
  obtain ⟨t, ht, rfl⟩ := phi_surj μ A B hA hB n z hzC
  have hDt : Dt (grC A hA) (grC B hB) t = 0 := by
    apply phi_inj μ A B hD
    rw [phi_Dt, map_zero]
    exact hzD
  obtain ⟨s, hs, hu⟩ := tensor_kunneth (grC A hA) (grC B hB) (n + 2) t ht hDt
  obtain ⟨m, f, hf, hsum⟩ := fin_family _ (boxes_smul μ A B n) (phi_boxes μ A B hA hB n _ hu)
  choose p a b ha hb hfe using hf
  refine ⟨m, p, a, b, fun l => ⟨ha l, hb l⟩, ?_⟩
  have h1 : n + 2 - 1 = n - 1 + 2 := by ring
  rw [h1] at hs
  refine ⟨phi μ A B s, phi_mem μ A B hA hB (n - 1) s hs, ?_⟩
  have h2 : ∑ l, boxC μ (a l) (b l) = phi μ A B t - biD k ι κ E'' (phi μ A B s) := by
    rw [← phi_Dt μ A B hA hB, ← map_sub, hsum]
    exact Finset.sum_congr rfl fun l _ => (hfe l).symm
  rw [h2]
  show biD k ι κ E'' (phi μ A B s) = _
  abel
