import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts

noncomputable section

open scoped Classical

namespace PI.InSClassConstW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.FourParts

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem Xa_mono {T : E} (F : FlagG S r T) {i j : ℕ} (h : i ≤ j) : F.Xa i ≤ F.Xa j := by
  exact Submodule.span_mono (Set.image_mono fun k (hk : k.1 < i) => lt_of_lt_of_le hk h)

theorem Xflag_le_of_inSF {T T' : E} {F : LFlag S r T} {G : LFlag S r T'} (h : InSF F G) (j : ℕ) :
    Xflag G j ≤ Xflag F j := by
  obtain ⟨he, -⟩ := h
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a.1 < j := ha
  have h1 : G.fl.e a - F.fl.e a ∈ Xflag F j := Xa_mono F.fl ha'.le (he a)
  have h2 : F.fl.e a ∈ Xflag F j :=
    Submodule.subset_span (s := F.fl.e '' {i : Fin r | i.1 < j}) ⟨a, ha', rfl⟩
  have h3 := add_mem h1 h2
  rw [sub_add_cancel] at h3
  exact h3

theorem Xflag_ge_of_inSF {T T' : E} {F : LFlag S r T} {G : LFlag S r T'} (h : InSF F G) (j : ℕ) :
    Xflag F j ≤ Xflag G j := by
  obtain ⟨he, -⟩ := h
  induction j with
  | zero => simp only [Xflag_zero, le_refl]
  | succ k ih =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a.1 ≤ k := Nat.lt_succ_iff.mp ha
    have h1 : G.fl.e a - F.fl.e a ∈ Xflag G (k + 1) :=
      Xa_mono G.fl (Nat.le_succ k) (ih (Xa_mono F.fl ha' (he a)))
    have h2 : G.fl.e a ∈ Xflag G (k + 1) :=
      Submodule.subset_span (s := G.fl.e '' {i : Fin r | i.1 < k + 1}) ⟨a, ha, rfl⟩
    have h3 := sub_mem h2 h1
    rw [sub_sub_cancel] at h3
    exact h3

theorem Xflag_eq_of_inSF {T T' : E} {F : LFlag S r T} {G : LFlag S r T'} (h : InSF F G) (j : ℕ) :
    Xflag G j = Xflag F j := le_antisymm (Xflag_le_of_inSF h j) (Xflag_ge_of_inSF h j)

theorem Xsp_eq_of_flag {T T' : E} {F : LFlag S r T} {G : LFlag S r T'} (h : ∀ j, Xflag G j = Xflag F j) :
    Xsp G = Xsp F := by
  rw [← Xflag_r G, ← Xflag_r F]
  exact h r

theorem Xsp_le_orth {T : E} (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := by
  intro y hy
  change y ∈ Submodule.span E (Set.range F.fl.e) at hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  change x ∈ Submodule.span E (Set.range F.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨b, rfl⟩ := hy'
      exact F.fl.e_iso a b
    | zero => simp
    | add y z _ _ h1 h2 => simp [h1, h2]
    | smul c y _ h => simp [h]
  | zero => simp
  | add x z _ _ h1 h2 => simp [h1, h2]
  | smul c x _ h => simp [h]

theorem map_mem_Xflag {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (j : ℕ) {v : S.V} (hv : v ∈ Xflag F j) : n v ∈ Xflag F j := by
  have hn' := hn
  simp only [NLam, Set.mem_setOf_eq] at hn'
  obtain ⟨-, hn1, -⟩ := hn'
  cases j with
  | zero =>
    rw [Xflag_zero, Submodule.mem_bot] at hv
    subst hv
    simp
  | succ k =>
    have h1 : n v - v ∈ Xflag F (k + 1) := Xa_mono F.fl (Nat.le_succ k) (hn1 k v hv)
    have h2 := add_mem h1 hv
    rw [sub_add_cancel] at h2
    exact h2

theorem map_Xflag_eq {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (j : ℕ) : (Xflag F j).map (n : S.V →ₗ[E] S.V) = Xflag F j := by
  have hle : (Xflag F j).map (n : S.V →ₗ[E] S.V) ≤ Xflag F j := by
    rintro _ ⟨v, hv, rfl⟩
    exact map_mem_Xflag hn j hv
  haveI : FiniteDimensional E (Xflag F j) :=
    FiniteDimensional.span_of_finite E (Set.toFinite (F.fl.e '' {i : Fin r | i.1 < j}))
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n _)

theorem e_eq {T' : E} {x y : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hfr : ∀ a, frame y a = n (m (frame x a))) (a : Fin r) : y.fl.e a = n (m (x.fl.e a)) := by
  have h := hfr a.castSucc
  simp only [frame, FlagG.fvec, Fin.snoc_castSucc] at h
  exact h

theorem z_eq {T' : E} {x y : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hfr : ∀ a, frame y a = n (m (frame x a))) : y.fl.z = n (m x.fl.z) := by
  have h := hfr (Fin.last r)
  simp only [frame, FlagG.fvec, Fin.snoc_last] at h
  exact h

theorem diff_of_flag {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {x y : LFlag S r T'}
    {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ x)
    (hfr : ∀ a, frame y a = n (m (frame x a))) (hfl : ∀ j, Xflag x j = Xflag F j) :
    (∀ a : Fin r, y.fl.e a - x.fl.e a ∈ Xflag F a.val) ∧ y.fl.z - x.fl.z ∈ Xsp F := by
  have hn' := hn
  have hm' := hm
  simp only [NLam, Set.mem_setOf_eq] at hn' hm'
  obtain ⟨-, hn1, hn2⟩ := hn'
  obtain ⟨-, hm1, hm2⟩ := hm'
  constructor
  · intro a
    rw [e_eq hfr a]
    have hxa : x.fl.e a ∈ Xflag x (a.val + 1) :=
      Submodule.subset_span (s := x.fl.e '' {i : Fin r | i.1 < a.val + 1}) ⟨a, Nat.lt_succ_self _, rfl⟩
    have h1 : m (x.fl.e a) - x.fl.e a ∈ Xflag F a.val := by
      rw [← hfl]
      exact hm1 a.val _ hxa
    have hmx : m (x.fl.e a) ∈ Xflag F (a.val + 1) := by
      rw [← hfl]
      exact map_mem_Xflag hm _ hxa
    have h2 : n (m (x.fl.e a)) - m (x.fl.e a) ∈ Xflag F a.val := hn1 a.val _ hmx
    have h3 := add_mem h2 h1
    rw [sub_add_sub_cancel] at h3
    exact h3
  · rw [z_eq hfr]
    have hXs : Xsp x = Xsp F := Xsp_eq_of_flag hfl
    have hz : x.fl.z ∈ orth S (Xsp x) := z_mem_orth x
    have h1 : m x.fl.z - x.fl.z ∈ Xsp x := hm2 _ hz
    have hmz : m x.fl.z ∈ orth S (Xsp F) := by
      rw [← hXs]
      have h4 := add_mem (Xsp_le_orth x h1) hz
      rw [sub_add_cancel] at h4
      exact h4
    have h2 : n (m x.fl.z) - m x.fl.z ∈ Xsp F := hn2 _ hmz
    rw [hXs] at h1
    have h3 := add_mem h2 h1
    rw [sub_add_sub_cancel] at h3
    exact h3

theorem flag_of_inSF_right {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {x y : LFlag S r T'}
    {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ x)
    (hfr : ∀ a, frame y a = n (m (frame x a))) (hy : InSF F y) (j : ℕ) : Xflag x j = Xflag F j := by
  have hyF : Xflag y j = Xflag F j := Xflag_eq_of_inSF hy j
  have hmap : Xflag y j = ((Xflag x j).map (m : S.V →ₗ[E] S.V)).map (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (y.fl.e '' {i : Fin r | i.1 < j}) =
      ((Submodule.span E (x.fl.e '' {i : Fin r | i.1 < j})).map (m : S.V →ₗ[E] S.V)).map
        (n : S.V →ₗ[E] S.V)
    rw [Submodule.map_span, Submodule.map_span, Set.image_image, Set.image_image]
    congr 1
    refine Set.image_congr ?_
    intro a _
    simp only [LinearEquiv.coe_coe]
    exact e_eq hfr a
  rw [map_Xflag_eq hm j, hyF, ← map_Xflag_eq hn j] at hmap
  exact (Submodule.map_injective_of_injective (f := (n : S.V →ₗ[E] S.V)) n.injective hmap).symm

theorem inSF_iff_of_dcrel {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {x y : LFlag S r T'}
    (h : DCRel Λ F x y) : InSF F x ↔ InSF F y := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  constructor
  · intro hx
    have hfl : ∀ j, Xflag x j = Xflag F j := Xflag_eq_of_inSF hx
    obtain ⟨hd1, hd2⟩ := diff_of_flag hn hm hfr hfl
    obtain ⟨hx1, hx2⟩ := hx
    unfold InSF
    refine ⟨fun a => ?_, ?_⟩
    · have h3 := add_mem (hd1 a) (hx1 a)
      rw [sub_add_sub_cancel] at h3
      exact h3
    · have h3 := add_mem hd2 hx2
      rw [sub_add_sub_cancel] at h3
      exact h3
  · intro hy
    have hfl := flag_of_inSF_right hn hm hfr hy
    obtain ⟨hd1, hd2⟩ := diff_of_flag hn hm hfr hfl
    obtain ⟨hy1, hy2⟩ := hy
    unfold InSF
    refine ⟨fun a => ?_, ?_⟩
    · have h3 := sub_mem (hy1 a) (hd1 a)
      rw [sub_sub_sub_cancel_left] at h3
      exact h3
    · have h3 := sub_mem hy2 hd2
      rw [sub_sub_sub_cancel_left] at h3
      exact h3

theorem inSFun_all (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop) :
    InSFun Λ F P := by
  unfold InSFun
  intro x y h
  exact inSF_iff_of_dcrel h

end Gen

end PI.InSClassConstW
