import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix

namespace Formalism.HermitianLatticeCounting.P

section Base

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

lemma B_swap0 (H : HermSpace K V) {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by rw [← H.herm x y, h, star_zero]

lemma perp_span (H : HermSpace K V) {S : Set V} {v : V} (h : ∀ s ∈ S, H.B s v = 0) :
    ∀ u ∈ Submodule.span K S, H.B u v = 0 := by
  have hle : Submodule.span K S ≤ LinearMap.ker (H.B.flip v) := by
    rw [Submodule.span_le]
    intro s hs
    simp [h s hs]
  intro u hu
  simpa using hle hu

lemma perp_sup (H : HermSpace K V) {S T : Submodule K V} {v : V} (h : ∀ s ∈ S, H.B s v = 0)
    (h' : ∀ s ∈ T, H.B s v = 0) : ∀ u ∈ S ⊔ T, H.B u v = 0 := by
  have hle : S ⊔ T ≤ LinearMap.ker (H.B.flip v) :=
    sup_le (fun s hs => by simp [h s hs]) (fun s hs => by simp [h' s hs])
  intro u hu
  simpa using hle hu

lemma Xa_mono (F : FlagD H r) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  apply Submodule.span_mono
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b, lt_of_lt_of_le hb h, rfl⟩

lemma e_mem_Xa (F : FlagD H r) (b : Fin r) {a : ℕ} (h : b.val < a) : F.e b.castSucc ∈ F.Xa a := Submodule.subset_span ⟨b, h, rfl⟩

lemma Xa_le_X (F : FlagD H r) (a : ℕ) : F.Xa a ≤ F.X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  apply Submodule.span_mono
  rintro _ ⟨b, -, rfl⟩
  exact ⟨b, b.isLt, rfl⟩

lemma Xa_of_ge (F : FlagD H r) {a : ℕ} (h : r ≤ a) : F.Xa a = F.X := le_antisymm ((Xa_le_X F) a) ((Xa_mono F) h)

lemma e_mem_X (F : FlagD H r) (b : Fin r) : F.e b.castSucc ∈ F.X := (e_mem_Xa F) b b.isLt

lemma Xa_zero (F : FlagD H r) : F.Xa 0 = ⊥ := by simp [Formalism.HermitianLatticeCounting.S6.FlagD.Xa]

lemma Xa_succ (F : FlagD H r) (a : Fin r) :
    F.Xa (a.val + 1) = F.Xa a.val ⊔ K ∙ F.e a.castSucc := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  have hs : {b : Fin r | b.val < a.val + 1} = {b | b.val < a.val} ∪ {a} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
    omega
  rw [hs, Set.image_union, Submodule.span_union, Set.image_singleton]

lemma perp_Xa (F : FlagD H r) {a : ℕ} {v : V}
    (h : ∀ b : Fin r, b.val < a → H.B (F.e b.castSucc) v = 0) : ∀ u ∈ F.Xa a, H.B u v = 0 := by
  intro u hu
  refine perp_span H (S := (fun b : Fin r => F.e b.castSucc) '' {b | b.val < a}) ?_ u hu
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb

lemma perp_X (F : FlagD H r) {v : V}
    (h : ∀ b : Fin r, H.B (F.e b.castSucc) v = 0) : ∀ u ∈ F.X, H.B u v = 0 := perp_Xa F (a := r) (fun b _ => h b)

lemma X_iso (F : FlagD H r) {u v : V} (hu : u ∈ F.X) (hv : v ∈ F.X) : H.B u v = 0 := by
  have h1 : ∀ b : Fin r, ∀ w ∈ F.X, H.B w (F.e b.castSucc) = 0 :=
    fun b => (perp_X F) (fun b' => F.iso b' b)
  exact (perp_X F) (fun b => B_swap0 H (h1 b v hv)) u hu

lemma pairing_isotropicSpan_lastVector (F : FlagD H r) {u : V} (hu : u ∈ F.X) : H.B u F.z = 0 := perp_X F (v := F.z) (fun b => F.zperp b) u hu

lemma z_X (F : FlagD H r) {u : V} (hu : u ∈ F.X) : H.B F.z u = 0 := B_swap0 H ((pairing_isotropicSpan_lastVector F) hu)

lemma pairing_lastVector_lastVector (F : FlagD H r) : H.B F.z F.z = -F.T := F.zz

lemma e_X (F : FlagD H r) (i : Fin (r + 1)) {u : V} (hu : u ∈ F.X) : H.B (F.e i) u = 0 := by
  induction i using Fin.lastCases with
  | last => exact (z_X F) hu
  | cast b => exact B_swap0 H ((perp_X F) (fun b' => F.iso b' b) u hu)

lemma e_notMem_Xa (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∉ F.Xa a.val := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  first
  | exact F.indep.notMem_span_image (s := {b : Fin r | b.val < a.val}) (by simp)
  | exact F.indep.not_mem_span_image (s := {b : Fin r | b.val < a.val}) (by simp)

lemma level_mem (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) :
    x ∈ F.Xa (a.val + 1) := by
  obtain ⟨hal, hx⟩ := h
  have h1 : x - al • F.e a.castSucc ∈ F.Xa (a.val + 1) := (Xa_mono F) (Nat.le_succ _) hx
  have h2 : F.e a.castSucc ∈ F.Xa (a.val + 1) := (e_mem_Xa F) a (Nat.lt_succ_self _)
  simpa using Submodule.add_mem _ h1 (Submodule.smul_mem _ al h2)

lemma level_mem_X (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) :
    x ∈ F.X := (Xa_le_X F) _ ((level_mem F) h)

lemma level_notMem (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) :
    x ∉ F.Xa a.val := by
  obtain ⟨hal, hx'⟩ := h
  intro hx
  have h1 : al • F.e a.castSucc ∈ F.Xa a.val := by
    simpa using Submodule.sub_mem _ hx hx'
  exact (e_notMem_Xa F) a ((Submodule.smul_mem_iff _ hal).1 h1)

lemma level_ne_zero (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) :
    x ≠ 0 := by
  intro h0
  apply (level_notMem F) h
  rw [h0]
  exact Submodule.zero_mem _

lemma level_unique (F : FlagD H r) {x : V} {a b : Fin r} {al bl : K} (h : F.HasLevel x a al)
    (h' : F.HasLevel x b bl) : a = b ∧ al = bl := by
  obtain ⟨hal, hx⟩ := id h
  obtain ⟨hbl, hx'⟩ := id h'
  have hab : a = b := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (level_notMem F) h'
        ((Xa_mono F) (by have := Fin.lt_iff_val_lt_val.1 hlt; omega) ((level_mem F) h))
    · exact (level_notMem F) h
        ((Xa_mono F) (by have := Fin.lt_iff_val_lt_val.1 hlt; omega) ((level_mem F) h'))
  subst hab
  refine ⟨rfl, ?_⟩
  by_contra hne
  have h1 : (bl - al) • F.e a.castSucc ∈ F.Xa a.val := by
    have := Submodule.sub_mem _ hx hx'
    convert this using 1
    rw [sub_smul]
    abel
  exact (e_notMem_Xa F) a ((Submodule.smul_mem_iff _ (sub_ne_zero.2 (Ne.symm hne))).1 h1)

private theorem FlagD_exists_level_lt_of_mem_Xa_of_ne_zero (F : Formalism.HermitianLatticeCounting.S6.FlagD H r) : ∀ n : ℕ, n ≤ r → ∀ x : V, x ∈ F.Xa n → x ≠ 0 →
    ∃ (a : Fin r) (al : K), a.val < n ∧ F.HasLevel x a al := by
  intro n
  induction n with
  | zero =>
    intro _ x hx h0
    rw [(Xa_zero F)] at hx
    exact absurd ((Submodule.mem_bot K).1 hx) h0
  | succ n ih =>
    intro hn x hx h0
    have hnr : n < r := by omega
    have hsb : F.Xa (n + 1) = F.Xa n ⊔ K ∙ F.e (⟨n, hnr⟩ : Fin r).castSucc :=
      (Xa_succ F) ⟨n, hnr⟩
    rw [hsb] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    by_cases hc : c = 0
    · subst hc
      have hy0 : y ≠ 0 := by simpa using h0
      obtain ⟨a, al, ha, hl⟩ := ih (by omega) y hy hy0
      refine ⟨a, al, by omega, ?_⟩
      simpa using hl
    · refine ⟨⟨n, hnr⟩, c, by simp, ?_⟩
      unfold Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
      exact ⟨hc, by simpa using hy⟩

lemma level_exists (F : FlagD H r) {x : V} (hx : x ∈ F.X) (h0 : x ≠ 0) :
    ∃ (a : Fin r) (al : K), F.HasLevel x a al := by
  obtain ⟨a, al, -, h⟩ := FlagD_exists_level_lt_of_mem_Xa_of_ne_zero F r le_rfl x hx h0
  exact ⟨a, al, h⟩

lemma level_lt_of_mem (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) {n : ℕ}
    (hx : x ∈ F.Xa n) : a.val < n := by
  by_contra hlt
  push_neg at hlt
  exact (level_notMem F) h ((Xa_mono F) hlt hx)

private theorem HermSpace_B_add_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B (x + y) z = H.B x z + H.B y z := by
  rw [map_add, LinearMap.add_apply]

private theorem HermSpace_B_sub_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B (x - y) z = H.B x z - H.B y z := by
  rw [map_sub, LinearMap.sub_apply]

private theorem HermSpace_B_smul_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B (c • x) y = c * H.B x y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem HermSpace_B_zero_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (y : V) : H.B 0 y = 0 := by
  rw [map_zero, LinearMap.zero_apply]

private theorem HermSpace_B_neg_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y : V) : H.B (-x) y = -H.B x y := by
  rw [map_neg, LinearMap.neg_apply]

private theorem HermSpace_B_add_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y + z) = H.B x y + H.B x z :=
  map_add _ _ _

private theorem HermSpace_B_sub_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y - z) = H.B x y - H.B x z :=
  map_sub _ _ _

private theorem HermSpace_B_smul_right_eq_star_mul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B x (c • y) = star c * H.B x y := by
  rw [LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]

private theorem xv_apply_eq_B_smul_sub_B_smul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x v y : V) :
    Formalism.HermitianLatticeCounting.S6.xv H x v y = H.B y v • x - H.B y x • v := by
  simp only [Formalism.HermitianLatticeCounting.S6.xv, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]

private theorem eich_apply_eq_add_wedge_add_smul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x v : V) (c : K) (y : V) :
    Formalism.HermitianLatticeCounting.S6.eich H x v c y = y + (H.B y v • x - H.B y x • v) + c • H.B y x • x := by
  simp only [Formalism.HermitianLatticeCounting.S6.eich, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, xv_apply_eq_B_smul_sub_B_smul]

lemma e_level (F : FlagD H r) (a : Fin r) : F.HasLevel (F.e a.castSucc) a 1 := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
  exact ⟨one_ne_zero, by simp⟩

end Base

theorem wedgeMapInLieAlgebra : Formalism.HermitianLatticeCounting.S6.Y1 := by
  intro K V _ _ _ _ H r F x v a al hx hv
  obtain ⟨hal, hxa⟩ := id hx
  have hxI : x ∈ F.X := (level_mem_X F) hx
  have hx1 : x ∈ F.Xa (a.val + 1) := (level_mem F) hx
  have hex : ∀ i : Fin (r + 1), H.B (F.e i) x = 0 := fun i => (e_X F) i hxI
  have hY : ∀ y, Formalism.HermitianLatticeCounting.S6.xv H x v y = H.B y v • x - H.B y x • v := xv_apply_eq_B_smul_sub_B_smul H x v
  have hYe : ∀ i : Fin (r + 1), Formalism.HermitianLatticeCounting.S6.xv H x v (F.e i) = H.B (F.e i) v • x := by
    intro i
    rw [hY, hex i, zero_smul, sub_zero]
  have hv' : ∀ y ∈ F.Xa (a.val + 1), H.B y v = 0 := by
    apply (perp_Xa F)
    intro b hb
    exact hv b (Fin.le_iff_val_le_val.2 (by omega))
  have hx' : ∀ y ∈ F.Xa (a.val + 1), H.B y x = 0 := fun y hy =>
    (X_iso F) ((Xa_le_X F) _ hy) hxI
  have hperp : ∀ y : V, (∀ b : Fin r, H.B (F.e b.castSucc) y = 0) → Formalism.HermitianLatticeCounting.S6.xv H x v y = H.B y v • x := by
    intro y hy
    have h1 : H.B x y = 0 := (perp_X F) hy x hxI
    rw [hY, B_swap0 H h1, zero_smul, sub_zero]
  have har := a.isLt
  refine ⟨fun y hy => by rw [hY, hv' y hy, hx' y hy]; simp, fun y hy => ?_, ?_, ?_⟩
  · rw [hperp y hy]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  · unfold Formalism.HermitianLatticeCounting.S6.FlagD.LieN
    refine ⟨fun y y' => ?_, fun b => ?_, fun y hy => ?_⟩
    · simp only [hY, HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_sub_right, HermSpace_B_smul_right_eq_star_mul]
      rw [H.herm y' v, H.herm y' x]
      ring
    · rw [hYe]
      by_cases hba : b ≤ a
      · rw [hv b hba, zero_smul]
        exact Submodule.zero_mem _
      · push_neg at hba
        exact Submodule.smul_mem _ _ ((Xa_mono F) (by have := Fin.lt_iff_val_lt_val.1 hba; omega) hx1)
    · rw [hperp y hy]
      exact Submodule.smul_mem _ _ hxI
  · unfold Formalism.HermitianLatticeCounting.S6.FlagD.DPsi
    refine ⟨fun b => if b = a then al * H.B (F.e a.succ) v else 0, by simp, fun b => ?_⟩
    dsimp only
    rw [hYe]
    rcases lt_trichotomy b a with hba | hba | hba
    · have hba' := Fin.lt_iff_val_lt_val.1 hba
      have hb1 : b.succ = (⟨b.val + 1, by omega⟩ : Fin r).castSucc := Fin.ext (by simp)
      have h0 : H.B (F.e b.succ) v = 0 := by
        rw [hb1]
        exact hv _ (Fin.le_iff_val_le_val.2 (show b.val + 1 ≤ a.val by omega))
      rw [h0, if_neg (ne_of_lt hba)]
      simp
    · subst hba
      rw [if_pos rfl, mul_comm, ← smul_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hxa
    · rw [if_neg (ne_of_gt hba), zero_smul, sub_zero]
      exact Submodule.smul_mem _ _ ((Xa_mono F) (by have := Fin.lt_iff_val_lt_val.1 hba; omega) hx1)

theorem lastVectorNotMemSup : Formalism.HermitianLatticeCounting.S6.LastVectorNotMemSup := by
  intro K V _ _ _ _ H r F F' hz
  obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.1 hz
  have hzu : H.B F.z u = 0 := (z_X F) hu
  have huu : H.B u u = 0 := (X_iso F) hu hu
  have hu'u' : H.B u' u' = 0 := (X_iso F') hu' hu'
  have e1 : H.B F.z F.z = H.B u u' := by
    have h1 : H.B F.z (u + u') = H.B F.z F.z := by rw [hsum]
    rw [HermSpace_B_add_right, hzu, zero_add] at h1
    rw [← h1, ← hsum, HermSpace_B_add_left, hu'u', add_zero]
  have e2 : H.B F.z F.z = H.B u u' + H.B u' u := by
    rw [← hsum, HermSpace_B_add_left, HermSpace_B_add_right, HermSpace_B_add_right, huu, hu'u']
    ring
  have h3 : H.B u' u = 0 := by
    rw [e1] at e2
    linear_combination -e2
  have h4 : H.B u u' = 0 := B_swap0 H h3
  have h5 : H.B F.z F.z = -F.T := F.zz
  rw [e1, h4] at h5
  exact F.hT (neg_eq_zero.1 h5.symm)

theorem memOfOrthogonalAnisotropic : Formalism.HermitianLatticeCounting.S6.MemOfOrthogonalAnisotropic := by
  intro K V _ _ _ _ H r F F' hA y hy hyo
  exact hA y hyo ((X_iso F') hy hy)

private theorem HermSpace_exists_B_right_eq_linearForm {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (f : V →ₗ[K] K) : ∃ v : V, ∀ u : V, H.B u v = f u := by
  let b := Module.finBasis K V
  let Ψ : V →ₗ[K] (Fin (Module.finrank K V) → K) := LinearMap.pi fun i => H.B.flip (b i)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply H.nondeg v
    have hb : ∀ i, H.B v (b i) = 0 := fun i => by simpa [Ψ] using congrFun hv i
    have h0 : H.B v = 0 := b.ext fun i => by rw [hb i, LinearMap.zero_apply]
    intro y
    rw [h0, LinearMap.zero_apply]
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hΨ
  obtain ⟨v, hv⟩ := hsurj (fun i => star (f (b i)))
  refine ⟨v, fun u => ?_⟩
  have hfl : H.B.flip v = f := b.ext fun i => by
    have h1 := congrFun hv i
    simp only [Ψ, LinearMap.pi_apply, LinearMap.flip_apply] at h1
    rw [LinearMap.flip_apply, ← H.herm v (b i), h1, star_star]
  have := LinearMap.congr_fun hfl u
  simpa using this

theorem memOfOrthogonalOrthogonal : Formalism.HermitianLatticeCounting.S6.PerpPerp := by
  intro K V _ _ _ _ _ H S w hw
  by_contra hwS
  have hq : S.mkQ w ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hwS
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K (V ⧸ S), φ (S.mkQ w) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff K _).1 h)
  obtain ⟨v, hv⟩ := HermSpace_exists_B_right_eq_linearForm H (φ.comp S.mkQ)
  apply hφ
  have h1 := hw v (fun s hs => by
    rw [hv s, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).2 hs, map_zero])
  rw [hv w, LinearMap.comp_apply] at h1
  exact h1

lemma nFStep_of (hY1 : Formalism.HermitianLatticeCounting.S6.Y1) (hPP : Formalism.HermitianLatticeCounting.S6.PerpPerp) : Formalism.HermitianLatticeCounting.S6.NFStep := by
  intro K V _ _ _ _ _ H r F F' x a a' al al' hμ hrel hx hxa hxa'
  apply hPP K V H (F.Xa (a.val + 1) ⊔ F'.Xa (a'.val + 1))
  intro v hv
  have hvF : ∀ b : Fin r, b ≤ a → H.B (F.e b.castSucc) v = 0 := fun b hb =>
    hv _ (Submodule.mem_sup_left ((e_mem_Xa F) b (by have := Fin.le_iff_val_le_val.1 hb; omega)))
  have hvF' : ∀ b : Fin r, b ≤ a' → H.B (F'.e b.castSucc) v = 0 := fun b hb =>
    hv _ (Submodule.mem_sup_right ((e_mem_Xa F') b (by have := Fin.le_iff_val_le_val.1 hb; omega)))
  obtain ⟨d, hd_def⟩ : ∃ d : K, d = al * H.B (F.e a.succ) v - al' * H.B (F'.e a'.succ) v := ⟨_, rfl⟩
  have key : ∀ t : K, t * d + star (t * d) = 0 := by
    intro t
    have hvt : ∀ b : Fin r, b ≤ a → H.B (F.e b.castSucc) (star t • v) = 0 := fun b hb => by
      rw [HermSpace_B_smul_right_eq_star_mul, hvF b hb, mul_zero]
    have hvt' : ∀ b : Fin r, b ≤ a' → H.B (F'.e b.castSucc) (star t • v) = 0 := fun b hb => by
      rw [HermSpace_B_smul_right_eq_star_mul, hvF' b hb, mul_zero]
    obtain ⟨-, -, hL, hc⟩ := hY1 K V H r F x (star t • v) a al hxa hvt
    obtain ⟨-, -, hL', hc'⟩ := hY1 K V H r F' x (star t • v) a' al' hxa' hvt'
    have h1 := hrel _ hL hL' _ _ hc hc'
    simp only [HermSpace_B_smul_right_eq_star_mul, star_star, star_mul', star_add] at h1
    rw [hd_def]
    simp only [star_mul', star_sub]
    linear_combination h1
  obtain ⟨μ, hμ⟩ := hμ
  have hd : d = 0 := by
    have h1 := key (μ * star d)
    have h2 : (μ + star μ) * (star d * d) = 0 := by
      simp only [star_mul', star_star] at h1
      linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hμ
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact star_eq_zero.1 h4
      · exact h4
  rw [HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_smul_left, ← hd_def, hd]

theorem normalFormStep : Formalism.HermitianLatticeCounting.S6.NFStep := nFStep_of wedgeMapInLieAlgebra memOfOrthogonalOrthogonal

section Base2

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

lemma Xa_eq_range (F : FlagD H r) {j : ℕ} (hj : j ≤ r) :
    F.Xa j = Submodule.span K
      (Set.range fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  congr 1
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.val, hb⟩, congrArg F.e (Fin.ext rfl)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, by have := a.isLt; omega⟩, a.isLt, congrArg F.e (Fin.ext rfl)⟩

lemma indep_le (F : FlagD H r) {j : ℕ} (hj : j ≤ r) :
    LinearIndependent K (fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) := by
  have := F.indep.comp (Fin.castLE hj) (Fin.castLE_injective hj)
  exact this

lemma finrank_Xa (F : FlagD H r) {j : ℕ} (hj : j ≤ r) : Module.finrank K (F.Xa j) = j := by
  rw [(Xa_eq_range F) hj, finrank_span_eq_card ((indep_le F) hj), Fintype.card_fin]

lemma finrank_X (F : FlagD H r) : Module.finrank K F.X = r := (finrank_Xa F) le_rfl

lemma mem_Xa_iff (F : FlagD H r) {j : ℕ} (hj : j ≤ r) {x : V} :
    x ∈ F.Xa j ↔ ∃ c : Fin j → K, ∑ a, c a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) = x := by
  rw [(Xa_eq_range F) hj, Submodule.mem_span_range_iff_exists_fun]

lemma finrank_compl [FiniteDimensional K V] (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (I : Submodule K V)
    (h1 : F.X = F.Xa j ⊔ I) (h2 : I ⊓ F.Xa j = ⊥) : Module.finrank K I = r - j := by
  have := Submodule.finrank_sup_add_finrank_inf_eq (F.Xa j) I
  rw [← h1, inf_comm, h2, finrank_bot, (finrank_X F), (finrank_Xa F) hj] at this
  omega

lemma X_eq_of_levels (F : FlagD H r) (j : ℕ) (I : Submodule K V) (hI : I ≤ F.X)
    (h : ∀ a : Fin r, j ≤ a.val → ∃ x ∈ I, ∃ al : K, F.HasLevel x a al) : F.X = F.Xa j ⊔ I := by
  apply le_antisymm
  · have key : ∀ n, n ≤ r → F.Xa n ≤ F.Xa j ⊔ I := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [(Xa_zero F)]
        exact bot_le
      | succ n ih =>
        intro hn
        have hnr : n < r := by omega
        have hsb : F.Xa (n + 1) = F.Xa n ⊔ K ∙ F.e (⟨n, hnr⟩ : Fin r).castSucc :=
          (Xa_succ F) ⟨n, hnr⟩
        rw [hsb]
        refine sup_le (ih (by omega)) ?_
        rw [Submodule.span_singleton_le_iff_mem]
        by_cases hjn : j ≤ n
        · obtain ⟨x, hxI, al, hal⟩ := h ⟨n, hnr⟩ hjn
          obtain ⟨hal0, hxa⟩ := id hal
          have h1 : x - al • F.e (⟨n, hnr⟩ : Fin r).castSucc ∈ F.Xa j ⊔ I := ih (by omega) hxa
          have h2 : x ∈ F.Xa j ⊔ I := Submodule.mem_sup_right hxI
          have h3 : al • F.e (⟨n, hnr⟩ : Fin r).castSucc ∈ F.Xa j ⊔ I := by
            simpa using Submodule.sub_mem _ h2 h1
          exact (Submodule.smul_mem_iff _ hal0).1 h3
        · exact Submodule.mem_sup_left ((e_mem_Xa F) _ (show n < j by omega))
    exact key r le_rfl
  · exact sup_le ((Xa_le_X F) j) hI

end Base2

theorem scalarUnique : Formalism.HermitianLatticeCounting.S6.NFCUnique := by
  intro K V _ _ _ _ H r F F' c₁ c₂ h₁ h₂
  by_contra hne
  have h3 : (c₂ - c₁) • F.z ∈ F.X ⊔ F'.X := by
    have := Submodule.sub_mem _ h₁ h₂
    convert this using 1
    rw [sub_smul]
    abel
  exact lastVectorNotMemSup K V H r F F' ((Submodule.smul_mem_iff _ (sub_ne_zero.2 (Ne.symm hne))).1 h3)

section CaseA

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}

lemma succ_eq_castSucc {r : ℕ} (a : Fin r) (h : a.val + 1 < r) :
    a.succ = (⟨a.val + 1, h⟩ : Fin r).castSucc := Fin.ext (by simp)

lemma succ_eq_last {r : ℕ} (a : Fin r) (h : a.val + 1 = r) : a.succ = Fin.last r := Fin.ext (by simpa using h)

lemma hasLevel_index_eq_of_mem_II (F F' : FlagD H r) (hStep : Formalism.HermitianLatticeCounting.S6.NFStep) (hN0 : Formalism.HermitianLatticeCounting.S6.LastVectorNotMemSup) (hμ : ∃ μ : K, μ + star μ ≠ 0) (hrel : Relevant F F') :
    ∀ (k : ℕ) (x : V) (a a' : Fin r) (al al' : K), a.val + 1 + k = r → x ∈ II F F' →
      F.HasLevel x a al → F'.HasLevel x a' al' →
      a = a' ∧ F'.z - (al / al') • F.z ∈ F.X ⊔ F'.X ∧
      ∀ b : Fin r, a.val ≤ b.val → ∃ y ∈ II F F', F.HasLevel y b al ∧ F'.HasLevel y b al' := by
  intro k
  induction k with
  | zero =>
    intro x a a' al al' hk hx hF hF'
    have ha : a.val + 1 = r := by omega
    have hstep := hStep K V H r F F' x a a' al al' hμ hrel hx hF hF'
    have hsa : a.succ = Fin.last r := succ_eq_last a ha
    obtain ⟨hal, -⟩ := id hF
    obtain ⟨hal', -⟩ := id hF'
    have h3 : F.Xa (a.val + 1) ⊔ F'.Xa (a'.val + 1) ≤ F.X ⊔ F'.X :=
      sup_le_sup ((Xa_le_X F) _) ((Xa_le_X F') _)
    have haa' : a = a' := by
      by_contra hne
      have hne' : a'.val ≠ a.val := fun h => hne (Fin.ext h).symm
      have ha'lt : a'.val + 1 < r := by have := a'.isLt; omega
      have hsa' : a'.succ = (⟨a'.val + 1, ha'lt⟩ : Fin r).castSucc := succ_eq_castSucc a' ha'lt
      have h2 : al' • F'.e a'.succ ∈ F.X ⊔ F'.X := by
        rw [hsa']
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ ((e_mem_X F') _))
      have h4 := Submodule.add_mem _ (h3 hstep) h2
      rw [sub_add_cancel, hsa] at h4
      exact hN0 K V H r F F' ((Submodule.smul_mem_iff _ hal).1 h4)
    subst haa'
    refine ⟨rfl, ?_, fun b hb => ⟨x, hx, ?_⟩⟩
    · have h4 := Submodule.smul_mem _ (-(al')⁻¹) (h3 hstep)
      rw [hsa] at h4
      convert h4 using 1
      show F'.e (Fin.last r) - (al / al') • F.e (Fin.last r) = _
      rw [smul_sub, smul_smul, smul_smul, show -(al')⁻¹ * al' = -1 by rw [neg_mul, inv_mul_cancel₀ hal'],
        show -(al')⁻¹ * al = -(al / al') by ring]
      simp only [neg_smul, one_smul]
      abel
    · have hba : b = a := Fin.ext (by have := b.isLt; have := Fin.le_iff_val_le_val.1 hb; omega)
      subst hba
      exact ⟨hF, hF'⟩
  | succ k ih =>
    intro x a a' al al' hk hx hF hF'
    have ha1 : a.val + 1 < r := by omega
    have hsa : a.succ = (⟨a.val + 1, ha1⟩ : Fin r).castSucc := succ_eq_castSucc a ha1
    have hstep := hStep K V H r F F' x a a' al al' hμ hrel hx hF hF'
    obtain ⟨hal, -⟩ := id hF
    obtain ⟨hal', -⟩ := id hF'
    obtain ⟨s, hs, s', hs', hss⟩ := Submodule.mem_sup.1 hstep
    have hae : al • F.e a.succ = s + s' + al' • F'.e a'.succ := by
      rw [hss]
      abel
    by_cases ha'1 : a'.val + 1 < r
    · have hsa' : a'.succ = (⟨a'.val + 1, ha'1⟩ : Fin r).castSucc := succ_eq_castSucc a' ha'1
      obtain ⟨y, hydef⟩ : ∃ y : V, y = al • F.e a.succ - s := ⟨_, rfl⟩
      have hy2 : y = al' • F'.e a'.succ + s' := by
        rw [hydef, hae]
        abel
      have hyF : y ∈ F.X := by
        rw [hydef, hsa]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ((e_mem_X F) _)) ((Xa_le_X F) _ hs)
      have hyF' : y ∈ F'.X := by
        rw [hy2, hsa']
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ ((e_mem_X F') _)) ((Xa_le_X F') _ hs')
      have hyM : y ∈ Formalism.HermitianLatticeCounting.S6.II F F' := Submodule.mem_inf.2 ⟨hyF, hyF'⟩
      have hyHF : F.HasLevel y ⟨a.val + 1, ha1⟩ al := by
        unfold Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
        refine ⟨hal, ?_⟩
        rw [hydef, ← hsa]
        simpa using hs
      have hyHF' : F'.HasLevel y ⟨a'.val + 1, ha'1⟩ al' := by
        unfold Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
        refine ⟨hal', ?_⟩
        rw [hy2, ← hsa']
        simpa using hs'
      obtain ⟨h1, h2, h3⟩ := ih y ⟨a.val + 1, ha1⟩ ⟨a'.val + 1, ha'1⟩ al al'
        (show a.val + 1 + 1 + k = r by omega) hyM hyHF hyHF'
      have haa' : a = a' := Fin.ext (by have h5 : a.val + 1 = a'.val + 1 := congrArg Fin.val h1; omega)
      refine ⟨haa', h2, fun b hb => ?_⟩
      by_cases hba : b = a
      · subst hba
        refine ⟨x, hx, hF, ?_⟩
        rw [haa']
        exact hF'
      · have hne : b.val ≠ a.val := fun h => hba (Fin.ext h)
        exact h3 b (Fin.le_iff_val_le_val.2 (show a.val + 1 ≤ b.val by have := Fin.le_iff_val_le_val.1 hb; omega))
    · have ha'r : a'.val + 1 = r := by have := a'.isLt; omega
      have hsa' : a'.succ = Fin.last r := succ_eq_last a' ha'r
      exfalso
      apply hN0 K V H r F' F
      have h4 : al' • F'.e a'.succ = al • F.e a.succ - s - s' := by
        rw [hae]
        abel
      have h5 : al • F.e a.succ - s - s' ∈ F'.X ⊔ F.X := by
        rw [hsa]
        exact Submodule.sub_mem _ (Submodule.sub_mem _
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ ((e_mem_X F) _)))
          (Submodule.mem_sup_right ((Xa_le_X F) _ hs)))
          (Submodule.mem_sup_left ((Xa_le_X F') _ hs'))
      rw [← h4, hsa'] at h5
      exact (Submodule.smul_mem_iff _ hal').1 h5

end CaseA

lemma nFCaseA_of_lastVectorNotMemSup (hStep : Formalism.HermitianLatticeCounting.S6.NFStep) (hN0 : Formalism.HermitianLatticeCounting.S6.LastVectorNotMemSup) : Formalism.HermitianLatticeCounting.S6.NFCaseA := by
  intro K V _ _ _ _ _ H r F F' hμ hrel hm
  have key : ∀ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', ∀ (a a' : Fin r) (al al' : K), F.HasLevel x a al →
      F'.HasLevel x a' al' → a = a' ∧
        F'.z - (al / al') • F.z ∈ F.X ⊔ F'.X ∧
        ∀ b : Fin r, a ≤ b → ∃ y ∈ Formalism.HermitianLatticeCounting.S6.II F F', F.HasLevel y b al ∧ F'.HasLevel y b al' :=
    fun x hx a a' al al' hF hF' => hasLevel_index_eq_of_mem_II F F' hStep hN0 hμ hrel
      (r - a.val - 1) x a a' al al' (by have := a.isLt; omega) hx hF hF'
  have hex : ∃ n : ℕ, ∃ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', x ≠ 0 ∧ ∃ (a : Fin r) (al : K), a.val = n ∧ F.HasLevel x a al := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    obtain ⟨a, al, h⟩ := (level_exists F) (Submodule.mem_inf.1 hx).1 hx0
    exact ⟨a.val, x, hx, hx0, a, al, rfl, h⟩
  classical
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = Nat.find hex := ⟨_, rfl⟩
  have hspec := Nat.find_spec hex
  rw [← hjdef] at hspec
  obtain ⟨x₀, hx₀, hx₀0, a₀, al₀, ha₀, hF₀⟩ := hspec
  have hmin : ∀ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', x ≠ 0 → ∀ (a : Fin r) (al : K), F.HasLevel x a al → j ≤ a.val := by
    intro x hx hx0 a al h
    rw [hjdef]
    exact Nat.find_min' hex ⟨x, hx, hx0, a, al, rfl, h⟩
  obtain ⟨a₀', al₀', hF₀'⟩ := (level_exists F') (Submodule.mem_inf.1 hx₀).2 hx₀0
  obtain ⟨-, hz, hall⟩ := key x₀ hx₀ a₀ a₀' al₀ al₀' hF₀ hF₀'
  obtain ⟨hal₀, -⟩ := id hF₀
  obtain ⟨hal₀', -⟩ := id hF₀'
  have hjr : j < r := by rw [← ha₀]; exact a₀.isLt
  have hlead : ∀ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', x ≠ 0 → ∃ (a : Fin r) (al al' : K), F.HasLevel x a al ∧
      F'.HasLevel x a al' ∧ j ≤ a.val ∧ al = al₀ / al₀' * al' := by
    intro x hx hx0
    obtain ⟨a, al, hF⟩ := (level_exists F) (Submodule.mem_inf.1 hx).1 hx0
    obtain ⟨a', al', hF'⟩ := (level_exists F') (Submodule.mem_inf.1 hx).2 hx0
    obtain ⟨rfl, hz', -⟩ := key x hx a a' al al' hF hF'
    have hc := scalarUnique K V H r F F' _ _ hz' hz
    obtain ⟨hal', -⟩ := id hF'
    refine ⟨a, al, al', hF, hF', hmin x hx hx0 a al hF, ?_⟩
    rw [← hc]
    exact (div_mul_cancel₀ al hal').symm
  have hall' : ∀ a : Fin r, j ≤ a.val → ∃ x ∈ Formalism.HermitianLatticeCounting.S6.II F F', ∃ al al' : K,
      F.HasLevel x a al ∧ F'.HasLevel x a al' := by
    intro a ha
    obtain ⟨y, hy, h1, h2⟩ := hall a (Fin.le_iff_val_le_val.2 (by omega))
    exact ⟨y, hy, al₀, al₀', h1, h2⟩
  have hb : Formalism.HermitianLatticeCounting.S6.II F F' ⊓ F.Xa j = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyM, hyS⟩ := Submodule.mem_inf.1 hy
    rw [Submodule.mem_bot]
    by_contra hy0
    obtain ⟨a, al, hF⟩ := (level_exists F) (Submodule.mem_inf.1 hyM).1 hy0
    have h1 := (level_lt_of_mem F) hF hyS
    have h2 := hmin y hyM hy0 a al hF
    omega
  have hb' : Formalism.HermitianLatticeCounting.S6.II F F' ⊓ F'.Xa j = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyM, hyS⟩ := Submodule.mem_inf.1 hy
    rw [Submodule.mem_bot]
    by_contra hy0
    obtain ⟨a', al', hF'⟩ := (level_exists F') (Submodule.mem_inf.1 hyM).2 hy0
    obtain ⟨a, al, hF⟩ := (level_exists F) (Submodule.mem_inf.1 hyM).1 hy0
    obtain ⟨rfl, -, -⟩ := key y hyM a a' al al' hF hF'
    have h1 := (level_lt_of_mem F') hF' hyS
    have h2 := hmin y hyM hy0 a al hF
    omega
  have hI := (X_eq_of_levels F) j (Formalism.HermitianLatticeCounting.S6.II F F') inf_le_left (fun a ha => by
    obtain ⟨x, hx, al, al', h1, -⟩ := hall' a ha
    exact ⟨x, hx, al, h1⟩)
  have hI' := (X_eq_of_levels F') j (Formalism.HermitianLatticeCounting.S6.II F F') inf_le_right (fun a ha => by
    obtain ⟨x, hx, al, al', -, h2⟩ := hall' a ha
    exact ⟨x, hx, al', h2⟩)
  have hfin := (finrank_compl F) hjr.le (Formalism.HermitianLatticeCounting.S6.II F F') hI hb
  refine ⟨j, al₀ / al₀', hjr, ?_⟩
  unfold Formalism.HermitianLatticeCounting.S6.NFShape
  exact ⟨div_ne_zero hal₀ hal₀', hfin, hlead, hall', hb, hb', hI, hI', hz⟩

theorem normalFormMeetNeBot : Formalism.HermitianLatticeCounting.S6.NFCaseA := nFCaseA_of_lastVectorNotMemSup normalFormStep lastVectorNotMemSup

section Gram

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

lemma B_sum_left (H : HermSpace K V) {n : ℕ} (c : Fin n → K) (u : Fin n → V) (y : V) :
    H.B (∑ a, c a • u a) y = ∑ a, c a * H.B (u a) y := by
  first
  | (rw [map_sum, LinearMap.sum_apply]; simp only [HermSpace_B_smul_left])
  | simp [map_sum, HermSpace_B_smul_left]

lemma gram_solve (H : HermSpace K V) {n : ℕ} (u w : Fin n → V)
    (hM : (Matrix.of fun a b => H.B (u a) (w b)).det ≠ 0) (t : Fin n → K) :
    ∃ c : Fin n → K, ∀ b, H.B (∑ a, c a • u a) (w b) = t b := by
  have hu : IsUnit (Matrix.of fun a b => H.B (u a) (w b)).det := isUnit_iff_ne_zero.2 hM
  refine ⟨Matrix.vecMul t (Matrix.of fun a b => H.B (u a) (w b))⁻¹, fun b => ?_⟩
  rw [B_sum_left]
  have h1 : Matrix.vecMul (Matrix.vecMul t (Matrix.of fun a b => H.B (u a) (w b))⁻¹) (Matrix.of fun a b => H.B (u a) (w b)) = t := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  rw [← congrFun h1 b]
  rfl

lemma gram_inj (H : HermSpace K V) {n : ℕ} (u w : Fin n → V)
    (hM : (Matrix.of fun a b => H.B (u a) (w b)).det ≠ 0) (c : Fin n → K)
    (h : ∀ b, H.B (∑ a, c a • u a) (w b) = 0) : c = 0 := by
  have hu : IsUnit (Matrix.of fun a b => H.B (u a) (w b)).det := isUnit_iff_ne_zero.2 hM
  have h1 : Matrix.vecMul c (Matrix.of fun a b => H.B (u a) (w b)) = 0 := by
    funext b
    show _ = (0 : K)
    rw [← h b, B_sum_left]
    rfl
  have h2 := congrArg (fun y => Matrix.vecMul y (Matrix.of fun a b => H.B (u a) (w b))⁻¹) h1
  simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu] using h2

lemma gram_zero (H : HermSpace K V) {n : ℕ} (u w : Fin n → V)
    (hM : (Matrix.of fun a b => H.B (u a) (w b)).det = 0) :
    ∃ c : Fin n → K, c ≠ 0 ∧ ∀ b, H.B (∑ a, c a • u a) (w b) = 0 := by
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM
  refine ⟨c, hc, fun b => ?_⟩
  rw [B_sum_left]
  exact congrFun hc0 b

lemma Dl_eq (F F' : FlagD H r) (l : ℕ) (hl : l ≤ r + 1) :
    Dl F F' l hl = (Matrix.of fun a b : Fin l => H.B (F.e (Fin.castLE hl a)) (F'.e (Fin.castLE hl b))).det := rfl

lemma Dl_swap (F F' : FlagD H r) (l : ℕ) (hl : l ≤ r + 1) : Dl F' F l hl = star (Dl F F' l hl) := by
  rw [Dl_eq, Dl_eq, ← Matrix.det_conjTranspose]
  congr 1
  ext a b
  simp [Matrix.conjTranspose_apply, H.herm]

lemma Dl_solveL (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) (hD : Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0)
    (t : Fin j → K) : ∃ x ∈ F.Xa j, ∀ b : Fin j, H.B x (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) = t b := by
  rw [Dl_eq] at hD
  obtain ⟨c, hc⟩ := gram_solve H (fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a))
    (fun b : Fin j => F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) hD t
  exact ⟨_, ((mem_Xa_iff F) hj).2 ⟨c, rfl⟩, hc⟩

lemma Dl_injL (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) (hD : Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0)
    {x : V} (hx : x ∈ F.Xa j) (h : ∀ u ∈ F'.Xa j, H.B x u = 0) : x = 0 := by
  rw [Dl_eq] at hD
  obtain ⟨c, rfl⟩ := ((mem_Xa_iff F) hj).1 hx
  have hc := gram_inj H (fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a))
    (fun b : Fin j => F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) hD c
    (fun b => h _ ((e_mem_Xa F') ⟨b.val, by have := b.isLt; omega⟩ b.isLt))
  rw [hc]
  simp

lemma Dl_zeroL (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) (hD : Dl F F' j (hj.trans (Nat.le_succ r)) = 0) :
    ∃ x ∈ F.Xa j, x ≠ 0 ∧ ∀ u ∈ F'.Xa j, H.B x u = 0 := by
  rw [Dl_eq] at hD
  obtain ⟨c, hc, hcb⟩ := gram_zero H
    (fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a))
    (fun b : Fin j => F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) hD
  refine ⟨_, ((mem_Xa_iff F) hj).2 ⟨c, rfl⟩, ?_, ?_⟩
  · intro h0
    apply hc
    funext a
    exact Fintype.linearIndependent_iff.1 ((indep_le F) hj) c h0 a
  · intro u hu
    obtain ⟨d, rfl⟩ := ((mem_Xa_iff F') hj).1 hu
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => by rw [HermSpace_B_smul_right_eq_star_mul, hcb b, mul_zero]

lemma II_comm (F F' : FlagD H r) : II F' F = II F F' := by
  unfold Formalism.HermitianLatticeCounting.S6.II
  exact inf_comm _ _

lemma jointSpan_comm (F F' : FlagD H r) : V0 F' F = V0 F F' := by
  unfold Formalism.HermitianLatticeCounting.S6.V0
  rw [sup_comm F'.X, Set.pair_comm]

lemma pairing_eq_zero_of_mem_jointSpan (F F' : FlagD H r) {v : V} (h1 : ∀ u ∈ F.X, H.B u v = 0) (h2 : ∀ u ∈ F'.X, H.B u v = 0)
    (h3 : H.B F.z v = 0) (h4 : H.B F'.z v = 0) : ∀ u ∈ V0 F F', H.B u v = 0 := by
  intro u hu
  unfold Formalism.HermitianLatticeCounting.S6.V0 at hu
  refine perp_sup H (S := F.X ⊔ F'.X)
    (T := Submodule.span K {F.z, F'.z}) (perp_sup H h1 h2) ?_ u hu
  apply perp_span H
  intro s hs
  rcases hs with rfl | hs
  · exact h3
  · rw [Set.mem_singleton_iff.1 hs]
    exact h4

lemma isotropicSpan_le_jointSpan_left (F F' : FlagD H r) : F.X ≤ V0 F F' := by
  unfold Formalism.HermitianLatticeCounting.S6.V0
  exact le_sup_of_le_left le_sup_left
lemma isotropicSpan_le_jointSpan_right (F F' : FlagD H r) : F'.X ≤ V0 F F' := by
  unfold Formalism.HermitianLatticeCounting.S6.V0
  exact le_sup_of_le_left le_sup_right
lemma lastVector_mem_jointSpan_left (F F' : FlagD H r) : F.z ∈ V0 F F' := by
  unfold Formalism.HermitianLatticeCounting.S6.V0
  exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
lemma lastVector_mem_jointSpan_right (F F' : FlagD H r) : F'.z ∈ V0 F F' := by
  unfold Formalism.HermitianLatticeCounting.S6.V0
  exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

private theorem det_eq_last_mul_det_submatrix_of_last_row_eq_zero {R : Type} [CommRing R] {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (h : ∀ j : Fin m, A (Fin.last m) j.castSucc = 0) :
    A.det = A (Fin.last m) (Fin.last m) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last m), Fin.sum_univ_castSucc]
  simp only [h, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last, Fin.val_last]
  rw [show ((-1 : R) ^ (m + m)) = 1 from Even.neg_one_pow ⟨m, rfl⟩, one_mul]

lemma pairing_lastVector_right_eq_zero (F F' : FlagD H r) {c : K} (hz : F'.z - c • F.z ∈ F.X ⊔ F'.X) {v : V}
    (h1 : ∀ u ∈ F.X, H.B u v = 0) (h2 : ∀ u ∈ F'.X, H.B u v = 0) (h3 : H.B F.z v = 0) :
    H.B F'.z v = 0 := by
  have h4 : H.B (F'.z - c • F.z) v = 0 := perp_sup H h1 h2 _ hz
  rw [HermSpace_B_sub_left, HermSpace_B_smul_left, h3, mul_zero, sub_zero] at h4
  exact h4

end Gram

theorem normalFormMinorNeZero : Formalism.HermitianLatticeCounting.S6.NFCaseB := by
  intro K V _ _ _ _ H r F F' hD
  have hD' : Formalism.HermitianLatticeCounting.S6.Dl F' F r (Nat.le_succ r) ≠ 0 := by
    rw [Dl_swap]
    exact fun h => hD (star_eq_zero.1 h)
  obtain ⟨x, hx, hxe⟩ := Dl_solveL F F' (le_refl r) hD
    (fun b => H.B F.z (F'.e b.castSucc))
  obtain ⟨x', hx', hxe'⟩ := Dl_solveL F' F (le_refl r) hD'
    (fun a => H.B F'.z (F.e a.castSucc))
  have hxI : x ∈ F.X := hx
  have hxI' : x' ∈ F'.X := hx'
  have hxe2 : ∀ b : Fin r, H.B x (F'.e b.castSucc) = H.B F.z (F'.e b.castSucc) := fun b => hxe b
  have hxe2' : ∀ a : Fin r, H.B x' (F.e a.castSucc) = H.B F'.z (F.e a.castSucc) := fun a => hxe' a
  have h1 : ∀ w ∈ F.X ⊔ F'.X, H.B w (F.z - x) = 0 := by
    apply perp_sup H
    · intro s hs
      rw [HermSpace_B_sub_right, (pairing_isotropicSpan_lastVector F) hs, (X_iso F) hs hxI, sub_zero]
    · exact (perp_X F')
        (fun b => B_swap0 H (by rw [HermSpace_B_sub_left, hxe2 b, sub_self]))
  have h2 : ∀ w ∈ F.X ⊔ F'.X, H.B w (F'.z - x') = 0 := by
    apply perp_sup H
    · exact (perp_X F)
        (fun a => B_swap0 H (by rw [HermSpace_B_sub_left, hxe2' a, sub_self]))
    · intro s hs
      rw [HermSpace_B_sub_right, (pairing_isotropicSpan_lastVector F') hs, (X_iso F') hs hxI', sub_zero]
  have h3 : H.B (F.z - x) (F.z - x) = -F.T := by
    rw [HermSpace_B_sub_left, h1 x (Submodule.mem_sup_left hxI), sub_zero, HermSpace_B_sub_right,
      (z_X F) hxI, sub_zero]
    exact (pairing_lastVector_lastVector F)
  have h4 : H.B (F'.z - x') (F'.z - x') = -F'.T := by
    rw [HermSpace_B_sub_left, h2 x' (Submodule.mem_sup_right hxI'), sub_zero, HermSpace_B_sub_right,
      (z_X F') hxI', sub_zero]
    exact (pairing_lastVector_lastVector F')
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      P = Matrix.of fun a b => H.B (F.e a) (F'.e b) := ⟨_, rfl⟩
  have hrowdet : ∀ y ∈ F.X, (P.updateRow (Fin.last r) (fun b => H.B y (F'.e b))).det = 0 := by
    let f : V →ₗ[K] K :=
      { toFun := fun y => (P.updateRow (Fin.last r) (fun b => H.B y (F'.e b))).det
        map_add' := fun y y' => by
          simp only [HermSpace_B_add_left]
          exact Matrix.det_updateRow_add P (Fin.last r) (fun b => H.B y (F'.e b)) (fun b => H.B y' (F'.e b))
        map_smul' := fun c y => by
          simp only [HermSpace_B_smul_left, RingHom.id_apply, smul_eq_mul]
          exact Matrix.det_updateRow_smul P (Fin.last r) c (fun b => H.B y (F'.e b)) }
    have hle : F.X ≤ LinearMap.ker f := by
      show Submodule.span K ((fun b : Fin r => F.e b.castSucc) '' {b | b.val < r}) ≤ LinearMap.ker f
      rw [Submodule.span_le]
      rintro _ ⟨a, -, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show (P.updateRow (Fin.last r) (fun b => H.B (F.e a.castSucc) (F'.e b))).det = 0
      apply Matrix.det_zero_of_row_eq (Fin.castSucc_ne_last a)
      rw [Matrix.updateRow_self, Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
      funext b
      simp [hPdef]
    intro y hy
    exact LinearMap.mem_ker.1 (hle hy)
  have hzrow : (fun b => H.B F.z (F'.e b)) = P (Fin.last r) := by
    funext b
    simp [hPdef, Formalism.HermitianLatticeCounting.S6.FlagD.z]
  have hQ : (P.updateRow (Fin.last r) (fun b => H.B (F.z - x) (F'.e b))).det = P.det := by
    have e1 : (fun b => H.B (F.z - x) (F'.e b)) =
        (fun b => H.B F.z (F'.e b)) + (-1 : K) • (fun b => H.B x (F'.e b)) := by
      funext b
      simp only [HermSpace_B_sub_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, hrowdet x hxI, mul_zero, add_zero, hzrow,
      Matrix.updateRow_eq_self]
  have hlast : ∀ j : Fin r,
      (P.updateRow (Fin.last r) (fun b => H.B (F.z - x) (F'.e b))) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self]
    exact B_swap0 H (h1 _ (Submodule.mem_sup_right ((e_mem_X F') j)))
  have hsub : (P.updateRow (Fin.last r) (fun b => H.B (F.z - x) (F'.e b))).submatrix Fin.castSucc Fin.castSucc =
      Matrix.of fun a b : Fin r => H.B (F.e (Fin.castLE (Nat.le_succ r) a)) (F'.e (Fin.castLE (Nat.le_succ r) b)) := by
    ext a b
    simp [hPdef, Matrix.updateRow_ne (Fin.castSucc_ne_last a)] <;> rfl
  have hP : Formalism.HermitianLatticeCounting.S6.Dl F F' (r + 1) le_rfl = P.det := by
    rw [hPdef]
    exact Dl_eq F F' (r + 1) le_rfl
  have hLr := Dl_eq F F' r (Nat.le_succ r)
  have hbb : H.B (F.z - x) (F'.e (Fin.last r)) = H.B (F.z - x) (F'.z - x') := by
    rw [HermSpace_B_sub_right H (F.z - x) F'.z x',
      B_swap0 H (h1 x' (Submodule.mem_sup_right hxI')), sub_zero]
    rfl
  have hlm : Formalism.HermitianLatticeCounting.S6.Dl F F' (r + 1) le_rfl =
      Formalism.HermitianLatticeCounting.S6.Dl F F' r (Nat.le_succ r) * H.B (F.z - x) (F'.z - x') := by
    rw [hP, ← hQ, det_eq_last_mul_det_submatrix_of_last_row_eq_zero _ hlast, hsub, ← hLr, Matrix.updateRow_self, ← hbb]
    exact mul_comm _ _
  refine ⟨x, hxI, x', hxI', h1, h2, h3, h4, hlm, ?_⟩
  unfold Formalism.HermitianLatticeCounting.S6.Gval
  rw [hlm, star_mul']
  ring

theorem normalFormDegenerateImpossible : Formalism.HermitianLatticeCounting.S6.NFCaseC := by
  intro K V _ _ _ _ H r F F' hA hA' hm hDr hg
  have hD : Formalism.HermitianLatticeCounting.S6.Dl F F' (r + 1) le_rfl = 0 := by
    unfold Formalism.HermitianLatticeCounting.S6.Gval at hg
    rw [hDr, star_zero, mul_zero, mul_zero, sub_zero] at hg
    rcases mul_eq_zero.1 hg with h | h
    · exact h
    · exact star_eq_zero.1 h
  have hD' : (Matrix.of fun a b : Fin (r + 1) =>
      H.B (F'.e (Fin.castLE le_rfl a)) (F.e (Fin.castLE le_rfl b))).det = 0 := by
    rw [← Dl_eq, Dl_swap, hD, star_zero]
  obtain ⟨c, hc, hcb⟩ := gram_zero H
    (fun a : Fin (r + 1) => F'.e (Fin.castLE le_rfl a)) (fun b : Fin (r + 1) => F.e (Fin.castLE le_rfl b)) hD'
  obtain ⟨y', hy'def⟩ : ∃ y' : V, y' = ∑ a : Fin (r + 1), c a • F'.e (Fin.castLE le_rfl a) := ⟨_, rfl⟩
  have hy' : ∀ a : Fin (r + 1), H.B (F.e a) y' = 0 := fun a => by
    rw [hy'def]
    exact B_swap0 H (hcb a)
  have hsplit : y' = (∑ a : Fin r, c a.castSucc • F'.e a.castSucc) + c (Fin.last r) • F'.z := by
    rw [hy'def, Fin.sum_univ_castSucc]
    rfl
  have hx₀' : ∑ a : Fin r, c a.castSucc • F'.e a.castSucc ∈ F'.X :=
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ((e_mem_X F') a)
  have hβ : c (Fin.last r) ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero] at hsplit
    have hyI' : y' ∈ F'.X := by rw [hsplit]; exact hx₀'
    have hyI : y' ∈ F.X := hA y' hy' ((X_iso F') hyI' hyI')
    have hy0 : y' = 0 := by
      have hmem : y' ∈ Formalism.HermitianLatticeCounting.S6.II F F' := Submodule.mem_inf.2 ⟨hyI, hyI'⟩
      rw [hm] at hmem
      exact (Submodule.mem_bot K).1 hmem
    have hind := Fintype.linearIndependent_iff.1 F'.indep (fun a => c a.castSucc)
      (by have h5 := hsplit.symm.trans hy0; simpa using h5)
    apply hc
    funext a
    induction a using Fin.lastCases with
    | last => exact h0
    | cast b => exact hind b
  obtain ⟨x, hx, hx0, hxu⟩ := Dl_zeroL F F' (le_refl r) hDr
  have hγ : H.B x F'.z ≠ 0 := by
    intro hγ
    have hxF' : x ∈ F'.X := by
      apply hA' x
      · intro a
        apply B_swap0 H
        induction a using Fin.lastCases with
        | last => exact hγ
        | cast b => exact hxu _ ((e_mem_X F') b)
      · exact (X_iso F) hx hx
    have hmem : x ∈ Formalism.HermitianLatticeCounting.S6.II F F' := Submodule.mem_inf.2 ⟨hx, hxF'⟩
    rw [hm] at hmem
    exact hx0 ((Submodule.mem_bot K).1 hmem)
  have h1 : H.B x y' = 0 := (perp_X F) (fun b => hy' b.castSucc) x hx
  rw [hsplit, HermSpace_B_add_right, HermSpace_B_smul_right_eq_star_mul, hxu _ hx₀', zero_add] at h1
  exact (mul_ne_zero (star_ne_zero.2 hβ) hγ) h1

theorem leadingMinorNeZero : Formalism.HermitianLatticeCounting.S6.NFDj := by
  intro K V _ _ _ _ H r F F' j hj c hA' hb hI' hz hD
  obtain ⟨x, hx, hx0, hxu⟩ := Dl_zeroL F F' hj hD
  have hxI : x ∈ F.X := (Xa_le_X F) j hx
  have hxI' : ∀ u ∈ F'.X, H.B x u = 0 := by
    rw [hI']
    intro u hu
    obtain ⟨y, hy, m, hm, rfl⟩ := Submodule.mem_sup.1 hu
    rw [HermSpace_B_add_right, hxu y hy, (X_iso F) hxI (Submodule.mem_inf.1 hm).1, add_zero]
  have hxS : ∀ u ∈ F.X ⊔ F'.X, H.B u x = 0 := by
    apply perp_sup H
    · intro u hu
      exact (X_iso F) hu hxI
    · intro u hu
      exact B_swap0 H (hxI' u hu)
  have hxz' : H.B x F'.z = 0 := by
    have h1 := B_swap0 H (hxS _ hz)
    rw [HermSpace_B_sub_right, HermSpace_B_smul_right_eq_star_mul, (pairing_isotropicSpan_lastVector F) hxI, mul_zero, sub_zero] at h1
    exact h1
  have hxF' : x ∈ F'.X := by
    apply hA' x
    · intro a
      apply B_swap0 H
      induction a using Fin.lastCases with
      | last => exact hxz'
      | cast b => exact hxI' _ ((e_mem_X F') b)
    · exact (X_iso F) hxI hxI
  have hmem : x ∈ Formalism.HermitianLatticeCounting.S6.II F F' ⊓ F.Xa j := Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hxI, hxF'⟩, hx⟩
  rw [hb] at hmem
  exact hx0 ((Submodule.mem_bot K).1 hmem)

theorem normSqScalarMulEq : Formalism.HermitianLatticeCounting.S6.NFAbsC := by
  intro K V _ _ _ _ H r F F' j hj c _ _ hz _
  obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.1 hz
  obtain ⟨p, hp⟩ : ∃ p : V, p = c • F.z + u := ⟨_, rfl⟩
  have hz' : F'.z = p + u' := by
    rw [hp, add_assoc, hsum]
    abel
  have hpp : H.B p p = -(c * star c * F.T) := by
    rw [hp]
    simp only [HermSpace_B_add_left, HermSpace_B_add_right, HermSpace_B_smul_left, HermSpace_B_smul_right_eq_star_mul, (pairing_lastVector_lastVector F),
      (z_X F) hu, (pairing_isotropicSpan_lastVector F) hu,
      (X_iso F) hu hu]
    ring
  have hu'z' : H.B u' F'.z = 0 := (pairing_isotropicSpan_lastVector F') hu'
  have hu'u' : H.B u' u' = 0 := (X_iso F') hu' hu'
  have hu'p : H.B u' p = 0 := by
    have hp' : p = F'.z - u' := by
      rw [hz']
      abel
    rw [hp', HermSpace_B_sub_right, hu'z', hu'u', sub_zero]
  have hpu' : H.B p u' = 0 := B_swap0 H hu'p
  have h1 : H.B F'.z F'.z = -F'.T := (pairing_lastVector_lastVector F')
  rw [hz', HermSpace_B_add_left, HermSpace_B_add_right, HermSpace_B_add_right, hpp, hpu', hu'p, hu'u'] at h1
  linear_combination -h1

section V0

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

lemma jointSpan_eq (F F' : FlagD H r) {c : K} (hz : F'.z - c • F.z ∈ F.X ⊔ F'.X) :
    V0 F F' = (F.X ⊔ F'.X) ⊔ K ∙ F.z := by
  unfold Formalism.HermitianLatticeCounting.S6.V0
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    intro s hs
    rcases hs with rfl | hs
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [Set.mem_singleton_iff.1 hs, ← sub_add_cancel F'.z (c • F.z)]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hz)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · exact sup_le_sup_left (Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))) _

lemma z_ne_zero (F : FlagD H r) : F.z ≠ 0 := by
  intro h
  apply F.hT
  have h1 : H.B (F.e (Fin.last r)) (F.e (Fin.last r)) = -F.T := F.zz
  rw [show F.e (Fin.last r) = 0 from h, HermSpace_B_zero_left] at h1
  exact neg_eq_zero.1 h1.symm

lemma pairing_jointSpan_isotropicMeet (F F' : FlagD H r) {x : V} (hx : x ∈ II F F') : ∀ w ∈ V0 F F', H.B w x = 0 := by
  obtain ⟨hxF, hxF'⟩ := Submodule.mem_inf.1 hx
  exact pairing_eq_zero_of_mem_jointSpan F F' (fun u hu => (X_iso F) hu hxF)
    (fun u hu => (X_iso F') hu hxF') ((z_X F) hxF)
    ((z_X F') hxF')

end V0

theorem jointSpanRadical : Formalism.HermitianLatticeCounting.S6.JointSpanRadical := by
  intro K V _ _ _ _ _ H r F F' j hj c hA' hb hb' hI hI' hz hD
  have hJ := jointSpan_eq F F' hz
  have hmI : Formalism.HermitianLatticeCounting.S6.II F F' ≤ F.X := inf_le_left
  have hc3 : ∀ x ∈ F.X, (∀ w ∈ Formalism.HermitianLatticeCounting.S6.V0 F F', H.B w x = 0) ↔ x ∈ Formalism.HermitianLatticeCounting.S6.II F F' := by
    intro x hx
    constructor
    · intro hw
      have hxF' : x ∈ F'.X := by
        apply hA' x
        · intro a
          induction a using Fin.lastCases with
          | last => exact hw _ (lastVector_mem_jointSpan_right F F')
          | cast b => exact hw _ (isotropicSpan_le_jointSpan_right F F' ((e_mem_X F') b))
        · exact (X_iso F) hx hx
      exact Submodule.mem_inf.2 ⟨hx, hxF'⟩
    · intro hm w hw
      exact pairing_jointSpan_isotropicMeet F F' hm w hw
  refine ⟨fun v hv => ⟨fun hvw => ?_, fun hm w hw => B_swap0 H (pairing_jointSpan_isotropicMeet F F' hm w hw)⟩,
    ?_, hc3⟩
  · have hw' : ∀ w ∈ Formalism.HermitianLatticeCounting.S6.V0 F F', H.B w v = 0 := fun w hw => B_swap0 H (hvw w hw)
    rw [hJ] at hv
    obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 ht
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy
    rw [hI'] at hu'
    obtain ⟨s', hs', m, hm, rfl⟩ := Submodule.mem_sup.1 hu'
    have hD' : Formalism.HermitianLatticeCounting.S6.Dl F' F j (hj.trans (Nat.le_succ r)) ≠ 0 := by
      rw [Dl_swap]
      exact fun h0 => hD (star_eq_zero.1 h0)
    have hs'0 : s' = 0 := by
      apply Dl_injL F' F hj hD' hs'
      intro x hx
      have hxI : x ∈ F.X := (Xa_le_X F) j hx
      have h1 := hw' x (isotropicSpan_le_jointSpan_left F F' hxI)
      rw [HermSpace_B_add_right, HermSpace_B_add_right, HermSpace_B_add_right, HermSpace_B_smul_right_eq_star_mul, (X_iso F) hxI hu,
        (X_iso F) hxI (hmI hm), (pairing_isotropicSpan_lastVector F) hxI] at h1
      exact B_swap0 H (by simpa using h1)
    subst hs'0
    have hβ : β = 0 := by
      have h1 := hw' F.z (lastVector_mem_jointSpan_left F F')
      rw [zero_add, HermSpace_B_add_right, HermSpace_B_add_right, HermSpace_B_smul_right_eq_star_mul, (z_X F) hu,
        (z_X F) (hmI hm), (pairing_lastVector_lastVector F)] at h1
      have h2 : star β * F.T = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact star_eq_zero.1 h3
      · exact absurd h3 F.hT
    subst hβ
    rw [zero_smul, add_zero, zero_add]
    rw [zero_smul, add_zero, zero_add] at hw'
    exact (hc3 _ (Submodule.add_mem _ hu (hmI hm))).1 hw'
  · have hII : F.X ⊔ F'.X = F.X ⊔ F'.Xa j := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [hI']
        exact sup_le le_sup_right (hmI.trans le_sup_left)
      · exact sup_le le_sup_left (le_sup_of_le_right ((Xa_le_X F') j))
    have hinf1 : F.X ⊓ F'.Xa j = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hmem : y ∈ Formalism.HermitianLatticeCounting.S6.II F F' ⊓ F'.Xa j :=
        Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hy1, (Xa_le_X F') j hy2⟩, hy2⟩
      rwa [hb'] at hmem
    have hfr1 : Module.finrank K ↥(F.X ⊔ F'.X) = r + j := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq F.X (F'.Xa j)
      rw [hinf1, finrank_bot, (finrank_X F), (finrank_Xa F') hj, ← hII] at h1
      omega
    have hinf2 : (F.X ⊔ F'.X) ⊓ (K ∙ F.z) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy2
      by_cases ha : a = 0
      · rw [ha, zero_smul]
        exact Submodule.zero_mem _
      · exact absurd ((Submodule.smul_mem_iff _ ha).1 hy1) (lastVectorNotMemSup K V H r F F')
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (F.X ⊔ F'.X) (K ∙ F.z)
    rw [hinf2, finrank_bot, hfr1, finrank_span_singleton (z_ne_zero F), ← hJ] at h2
    omega

theorem jointSpanComplement : Formalism.HermitianLatticeCounting.S6.JointSpanComplement := by
  intro K V _ _ _ _ H r F F' j hj c hI' hz hD w hw
  obtain ⟨x, hx, hxt⟩ := Dl_solveL F F' hj hD
    (fun b => H.B w (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)))
  have hxI : x ∈ F.X := (Xa_le_X F) j hx
  refine ⟨x, hxI, ?_⟩
  have hwI : ∀ u ∈ F.X, H.B u w = 0 := (perp_X F) (fun b => hw b.castSucc)
  have h1 : ∀ u ∈ F.X, H.B u (w - x) = 0 := fun u hu => by
    rw [HermSpace_B_sub_right, hwI u hu, (X_iso F) hu hxI, sub_zero]
  have h3 : H.B F.z (w - x) = 0 := by
    rw [HermSpace_B_sub_right, (z_X F) hxI, sub_zero]
    exact hw (Fin.last r)
  have h2 : ∀ u ∈ F'.X, H.B u (w - x) = 0 := by
    rw [hI']
    apply perp_sup H
    · apply (perp_Xa F')
      intro b hb
      have h4 : H.B x (F'.e b.castSucc) = H.B w (F'.e b.castSucc) := hxt ⟨b.val, hb⟩
      rw [HermSpace_B_sub_right, ← H.herm x, h4, H.herm, sub_self]
    · intro u hu
      exact h1 u (Submodule.mem_inf.1 hu).1
  exact pairing_eq_zero_of_mem_jointSpan F F' h1 h2 h3 (pairing_lastVector_right_eq_zero F F' hz h1 h2 h3)

theorem normalFormZero : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  intro K V _ _ _ _ H r F F' c hS
  obtain ⟨hc, -, hlead, hex, -, -, hI, hI', hz⟩ := id hS
  rw [(Xa_zero F), bot_sup_eq] at hI
  rw [(Xa_zero F'), bot_sup_eq] at hI'
  have hII : F'.X = F.X := hI'.trans hI.symm
  have hsb : ∀ n, F'.Xa n = F.Xa n := by
    intro n
    induction n with
    | zero => rw [(Xa_zero F), (Xa_zero F')]
    | succ n ih =>
      by_cases hnr : n < r
      · have hsF : F.Xa (n + 1) = F.Xa n ⊔ K ∙ F.e (⟨n, hnr⟩ : Fin r).castSucc :=
          (Xa_succ F) ⟨n, hnr⟩
        have hsF' : F'.Xa (n + 1) = F'.Xa n ⊔ K ∙ F'.e (⟨n, hnr⟩ : Fin r).castSucc :=
          (Xa_succ F') ⟨n, hnr⟩
        obtain ⟨x, hxm, al, al', hF, hF'⟩ := hex ⟨n, hnr⟩ (Nat.zero_le _)
        obtain ⟨hal, hxa⟩ := id hF
        obtain ⟨hal', hxa'⟩ := id hF'
        have hx1 : x ∈ F.Xa (n + 1) := level_mem F (a := ⟨n, hnr⟩) (al := al) hF
        have hx1' : x ∈ F'.Xa (n + 1) := level_mem F' (a := ⟨n, hnr⟩) (al := al') hF'
        have hxa2 : x - al • F.e (⟨n, hnr⟩ : Fin r).castSucc ∈ F'.Xa n := by
          rw [ih]
          exact hxa
        have hxa2' : x - al' • F'.e (⟨n, hnr⟩ : Fin r).castSucc ∈ F.Xa n := by
          rw [← ih]
          exact hxa'
        apply le_antisymm
        · rw [hsF']
          refine sup_le ((le_of_eq ih).trans ((Xa_mono F) (Nat.le_succ n))) ?_
          rw [Submodule.span_singleton_le_iff_mem]
          have h3 := Submodule.sub_mem _ hx1 ((Xa_mono F) (Nat.le_succ n) hxa2')
          rw [sub_sub_cancel] at h3
          exact (Submodule.smul_mem_iff _ hal').1 h3
        · rw [hsF]
          refine sup_le ((le_of_eq ih.symm).trans ((Xa_mono F') (Nat.le_succ n))) ?_
          rw [Submodule.span_singleton_le_iff_mem]
          have h3 := Submodule.sub_mem _ hx1' ((Xa_mono F') (Nat.le_succ n) hxa2)
          rw [sub_sub_cancel] at h3
          exact (Submodule.smul_mem_iff _ hal).1 h3
      · push_neg at hnr
        rw [Xa_of_ge F (a := n + 1) (by omega),
          Xa_of_ge F' (a := n + 1) (by omega), hII]
  have hstep : ∀ a : Fin r, F'.e a.castSucc - c • F.e a.castSucc ∈ F.Xa a.val := by
    intro a
    obtain ⟨x, hxm, al, al', hF, hF'⟩ := hex a (Nat.zero_le _)
    have hx0 : x ≠ 0 := (level_ne_zero F) hF
    obtain ⟨b, bl, bl', hFb, hF'b, -, hbl⟩ := hlead x hxm hx0
    obtain ⟨hab, hal_eq⟩ := (level_unique F) hF hFb
    obtain ⟨-, hal'_eq⟩ := (level_unique F') hF' hF'b
    obtain ⟨hal, hxa⟩ := id hF
    obtain ⟨hal', hxa'⟩ := id hF'
    have hxa2' : x - al' • F'.e a.castSucc ∈ F.Xa a.val := by
      rw [← hsb]
      exact hxa'
    have h3 := Submodule.sub_mem _ hxa hxa2'
    have hcal : al = c * al' := by rw [hal_eq, hal'_eq]; exact hbl
    have h4 : al' • (F'.e a.castSucc - c • F.e a.castSucc) ∈ F.Xa a.val := by
      convert h3 using 1
      rw [hcal, smul_sub, smul_smul, mul_comm al' c]
      abel
    exact (Submodule.smul_mem_iff _ hal').1 h4
  refine ⟨hsb, hstep, ?_⟩
  have h5 := hz
  rwa [hII, sup_idem] at h5

section Sig

variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]

lemma herm_im (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (x : U) : (σ (h x x)).im = 0 := by
  have h1 : σ (h x x) = star (σ (h x x)) := by rw [← hσ, herm]
  have h2 := congrArg Complex.im h1
  have hs : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun z => rfl
  rw [hs, Complex.conj_im] at h2
  linarith

lemma sig_norm (σ : K →+* ℂ) (hσ : ∀ x : K, σ (star x) = star (σ x)) (a b : K) :
    (σ (a * star a * b)).re = Complex.normSq (σ a) * (σ b).re := by
  rw [map_mul, map_mul, hσ]
  have hs : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun z => rfl
  rw [hs]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

lemma negperp_gen (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (A N : Submodule K U)
    (hN : ∀ n ∈ N, ∀ u ∈ A, h n u = 0) (z₀ : U) (_hz₀ : z₀ ∈ A)
    (pos : ∀ w ∈ A, h w z₀ = 0 → w ∉ N → 0 < (σ (h w w)).re)
    (z : U) (hz : z ∈ A) (hzn : (σ (h z z)).re < 0) (w : U) (hw : w ∈ A) (hwz : h w z = 0)
    (hwN : w ∉ N) : 0 < (σ (h w w)).re := by
  by_contra hneg
  push_neg at hneg
  have herm0 : ∀ x y : U, h x y = 0 → h y x = 0 := fun x y hxy => by rw [← herm x y, hxy, star_zero]
  have hzz : h z z ≠ 0 := by
    intro h0
    rw [h0, map_zero, Complex.zero_re] at hzn
    exact lt_irrefl _ hzn
  have hwz' : h z w = 0 := herm0 _ _ hwz
  by_cases hz0 : h z z₀ = 0
  · have hzN : z ∉ N := fun hzN => hzz (hN z hzN z hz)
    have := pos z hz hz0 hzN
    linarith
  · obtain ⟨a, ha_def⟩ : ∃ a : K, a = h w z₀ := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b : K, b = -h z z₀ := ⟨_, rfl⟩
    have hp : a • z + b • w ∈ A := A.add_mem (A.smul_mem _ hz) (A.smul_mem _ hw)
    have hpz0 : h (a • z + b • w) z₀ = 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [ha_def, hb_def]
      ring
    have hb : b ≠ 0 := by
      rw [hb_def]
      exact neg_ne_zero.2 hz0
    have hpN : a • z + b • w ∉ N := by
      intro hpN
      have h1 : h (a • z + b • w) z = 0 := hN _ hpN z hz
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hwz, mul_zero,
        add_zero] at h1
      have ha : a = 0 := (mul_eq_zero.1 h1).resolve_right hzz
      apply hwN
      have hw' : w = b⁻¹ • (a • z + b • w) := by
        rw [ha, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ hb, one_smul]
      rw [hw']
      exact N.smul_mem _ hpN
    have hpos := pos _ hp hpz0 hpN
    have hpp : h (a • z + b • w) (a • z + b • w) = a * star a * h z z + b * star b * h w w := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_smulₛₗ,
        starRingEnd_apply, hwz, hwz']
      ring
    rw [hpp, map_add, Complex.add_re, sig_norm σ hσ, sig_norm σ hσ] at hpos
    have h1 := Complex.normSq_nonneg (σ a)
    have h2 := Complex.normSq_nonneg (σ b)
    nlinarith [mul_nonneg h1 (neg_nonneg.2 hzn.le), mul_nonneg h2 (neg_nonneg.2 hneg)]

lemma reverseCS_gen (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (A N : Submodule K U)
    (hN : ∀ n ∈ N, ∀ u ∈ A, h n u = 0) (z₀ : U) (hz₀ : z₀ ∈ A)
    (pos : ∀ w ∈ A, h w z₀ = 0 → w ∉ N → 0 < (σ (h w w)).re)
    (z : U) (hz : z ∈ A) (hzn : (σ (h z z)).re < 0) (z' : U) (hz' : z' ∈ A) :
    (σ (h z z)).re * (σ (h z' z')).re ≤ Complex.normSq (σ (h z z')) ∧
      (h z z * h z' z' = h z z' * star (h z z') → ∃ c : K, z' - c • z ∈ N) := by
  have hα : h z z ≠ 0 := by
    intro h0
    rw [h0, map_zero, Complex.zero_re] at hzn
    exact lt_irrefl _ hzn
  have hαs : star (h z z) = h z z := herm z z
  obtain ⟨β, hβdef⟩ : ∃ β : K, β = h z' z := ⟨_, rfl⟩
  have hβs : h z z' = star β := by rw [hβdef, herm]
  obtain ⟨w, hwdef⟩ : ∃ w : U, w = z' - (β / h z z) • z := ⟨_, rfl⟩
  have hwA : w ∈ A := by
    rw [hwdef]
    exact A.sub_mem hz' (A.smul_mem _ hz)
  have hwz : h w z = 0 := by
    rw [hwdef]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← hβdef, div_mul_cancel₀ β hα, sub_self]
  have hww : h z z * h w w = h z z * h z' z' - β * star β := by
    rw [hwdef]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_smulₛₗ,
      starRingEnd_apply]
    rw [← hβdef, hβs, star_div₀, hαs]
    field_simp
    ring
  have hwwre : 0 ≤ (σ (h w w)).re := by
    by_cases hwN : w ∈ N
    · rw [hN w hwN w hwA, map_zero, Complex.zero_re]
    · exact (negperp_gen σ h hσ herm A N hN z₀ hz₀ pos z hz hzn w hwA hwz hwN).le
  have him_zz := herm_im σ h hσ herm z
  have him_ww := herm_im σ h hσ herm w
  have him_z'z' := herm_im σ h hσ herm z'
  have hre_mul : ∀ p q : ℂ, p.im = 0 → q.im = 0 → (p * q).re = p.re * q.re := fun p q hp hq => by
    rw [Complex.mul_re, hp, hq, mul_zero, sub_zero]
  have hs : ∀ t : ℂ, star t = (starRingEnd ℂ) t := fun t => rfl
  have hns : (σ β * star (σ β)).re = Complex.normSq (σ β) := by
    rw [hs]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have e1 := congrArg (fun t => (σ t).re) hww
  simp only [map_mul, map_sub] at e1
  rw [hre_mul _ _ him_zz him_ww, Complex.sub_re, hre_mul _ _ him_zz him_z'z', hσ, hns] at e1
  have hnsq : Complex.normSq (σ (h z z')) = Complex.normSq (σ β) := by
    rw [hβs, hσ, hs, Complex.normSq_conj]
  constructor
  · rw [hnsq]
    have h3 : (σ (h z z)).re * (σ (h w w)).re ≤ 0 := mul_nonpos_iff.2 (Or.inr ⟨hzn.le, hwwre⟩)
    linarith
  · intro heq
    have h0 : h z z * h w w = 0 := by
      rw [hww, heq, hβs, star_star]
      ring
    have hw0 : h w w = 0 := (mul_eq_zero.1 h0).resolve_left hα
    have hwN : w ∈ N := by
      by_contra hwN
      have h4 := negperp_gen σ h hσ herm A N hN z₀ hz₀ pos z hz hzn w hwA hwz hwN
      rw [hw0, map_zero, Complex.zero_re] at h4
      exact lt_irrefl _ h4
    refine ⟨β / h z z, ?_⟩
    rw [← hwdef]
    exact hwN

end Sig

section Perp

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def perpS (H : HermSpace K V) (S : Submodule K V) : Submodule K V where
  carrier := {v | ∀ s ∈ S, H.B s v = 0}
  add_mem' := by intro a b ha hb s hs; simp [ha s hs, hb s hs]
  zero_mem' := by intro s _; simp
  smul_mem' := by intro c a ha s hs; simp [ha s hs]

lemma mem_perpS (H : HermSpace K V) (S : Submodule K V) (v : V) :
    v ∈ perpS H S ↔ ∀ s ∈ S, H.B s v = 0 := Iff.rfl

end Perp

theorem isAnisotropicOfPosDef : Formalism.HermitianLatticeCounting.S6.AnisoOfPosDef := by
  intro K V _ _ _ _ σ H r F hpos w hw hww
  by_contra hwI
  have := hpos w hw hwI
  rw [hww, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem signatureOneComplementOfMinorNeZero : Formalism.HermitianLatticeCounting.S6.NFCaseBSig := by
  intro K V _ _ _ _ σ H r F F' hT hP hD
  obtain ⟨x, hx, x', hx', h1, -, h3, -, -, -⟩ := normalFormMinorNeZero K V H r F F' hD
  unfold Formalism.HermitianLatticeCounting.S6.SigPerp
  refine ⟨F.z - x, h1, ?_, fun w hw hwz hw0 => ?_⟩
  · rw [h3, map_neg, Complex.neg_re]
    linarith
  · apply hP w
    · intro a
      induction a using Fin.lastCases with
      | last =>
        have e : F.e (Fin.last r) = (F.z - x) + x := (sub_add_cancel F.z x).symm
        rw [e, HermSpace_B_add_left, B_swap0 H hwz, hw x (Submodule.mem_sup_left hx), add_zero]
      | cast b => exact hw _ (Submodule.mem_sup_left ((e_mem_X F) b))
    · intro hwI
      apply hw0
      exact Dl_injL F F' (le_refl r) hD hwI
        (fun u hu => B_swap0 H (hw u (Submodule.mem_sup_right hu)))

theorem existsScalarOfGramDefectZero : Formalism.HermitianLatticeCounting.S6.NFCaseBConcl := by
  intro K V _ _ _ _ σ H r F F' hσ hT hT' hsig hD hg
  obtain ⟨x, hx, x', hx', h1, h2, h3, h4, -, h6⟩ := normalFormMinorNeZero K V H r F F' hD
  obtain ⟨z₀, hz₀, hz₀n, hpos⟩ := id hsig
  have hDD : Formalism.HermitianLatticeCounting.S6.Dl F F' r (Nat.le_succ r) * star (Formalism.HermitianLatticeCounting.S6.Dl F F' r (Nat.le_succ r)) ≠ 0 :=
    mul_ne_zero hD (star_ne_zero.2 hD)
  have hβ : H.B (F.z - x) (F'.z - x') * star (H.B (F.z - x) (F'.z - x')) =
      F.T * F'.T := by
    rw [hg] at h6
    have h7 := (mul_eq_zero.1 h6.symm).resolve_left hDD
    linear_combination h7
  have hmemA : ∀ y : V, (∀ w ∈ F.X ⊔ F'.X, H.B w y = 0) →
      y ∈ perpS H (F.X ⊔ F'.X) :=
    fun y hy => (mem_perpS H _ y).2 hy
  obtain ⟨-, heq⟩ := reverseCS_gen σ H.B hσ H.herm
    (perpS H (F.X ⊔ F'.X)) ⊥
    (fun n hn u _ => by rw [(Submodule.mem_bot K).1 hn, HermSpace_B_zero_left]) z₀ (hmemA _ hz₀)
    (fun w hw h5 h7 => hpos w ((mem_perpS H _ w).1 hw) h5
      (fun h0 => h7 (by rw [h0]; exact Submodule.zero_mem _)))
    (F.z - x) (hmemA _ h1) (by rw [h3, map_neg, Complex.neg_re]; linarith)
    (F'.z - x') (hmemA _ h2)
  obtain ⟨c, hc⟩ := heq (by rw [h3, h4, hβ]; ring)
  refine ⟨c, ?_⟩
  have hc0 : F'.z - x' - c • (F.z - x) = 0 := (Submodule.mem_bot K).1 hc
  have e : F'.z - c • F.z = (F'.z - x' - c • (F.z - x)) + (x' - c • x) := by
    rw [smul_sub]
    abel
  rw [e, hc0, zero_add]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right hx') (Submodule.mem_sup_left (Submodule.smul_mem _ _ hx))

lemma nf_full {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {H : HermSpace K V} {r : ℕ} (F F' : FlagD H r) (hA : F.Aniso) (hA' : F'.Aniso) (j : ℕ) (hj : j ≤ r)
    (c : K) (hS : NFShape F F' j c) : NFFull F F' j hj c := by
  obtain ⟨hc, hfr, hlead, hex, hb, hb', hI, hI', hz⟩ := id hS
  have hminor := leadingMinorNeZero K V H r F F' j hj c hA' hb hI' hz
  have hnorm := normSqScalarMulEq K V H r F F' j hj c hI hI' hz hminor
  obtain ⟨hrad, hfin, hx⟩ := jointSpanRadical K V H r F F' j hj c hA' hb hb' hI hI' hz hminor
  have hcompl := jointSpanComplement K V H r F F' j hj c hI' hz hminor
  have hz' : F.z - c⁻¹ • F'.z ∈ F'.X ⊔ F.X := by
    rw [sup_comm]
    have := Submodule.smul_mem _ (-c⁻¹) hz
    convert this using 1
    rw [smul_sub, smul_smul, show -c⁻¹ * c = -1 by rw [neg_mul, inv_mul_cancel₀ hc]]
    simp only [neg_smul, one_smul]
    abel
  have hminor' : Formalism.HermitianLatticeCounting.S6.Dl F' F j (hj.trans (Nat.le_succ r)) ≠ 0 := by
    rw [Dl_swap]
    exact fun h0 => hminor (star_eq_zero.1 h0)
  have hb2 : Formalism.HermitianLatticeCounting.S6.II F' F ⊓ F'.Xa j = ⊥ := by rw [II_comm]; exact hb'
  have hb2' : Formalism.HermitianLatticeCounting.S6.II F' F ⊓ F.Xa j = ⊥ := by rw [II_comm]; exact hb
  have hI2 : F'.X = F'.Xa j ⊔ Formalism.HermitianLatticeCounting.S6.II F' F := by rw [II_comm]; exact hI'
  have hI2' : F.X = F.Xa j ⊔ Formalism.HermitianLatticeCounting.S6.II F' F := by rw [II_comm]; exact hI
  obtain ⟨-, -, hx'⟩ := jointSpanRadical K V H r F' F j hj c⁻¹ hA hb2 hb2' hI2 hI2' hz' hminor'
  have hcompl' := jointSpanComplement K V H r F' F j hj c⁻¹ hI2' hz' hminor'
  rw [jointSpan_comm, II_comm] at hx'
  rw [jointSpan_comm] at hcompl'
  unfold Formalism.HermitianLatticeCounting.S6.NFFull
  exact ⟨hS, hnorm, hminor, hrad, hfin, hx, hx', hcompl, hcompl'⟩

theorem existsNormalForm : Formalism.HermitianLatticeCounting.S6.NormalForm := by
  intro K V _ _ _ _ _ σ H r F F' hσ hT hT' hP hP' hrel hg
  have hA := isAnisotropicOfPosDef K V σ H r F hP
  have hA' := isAnisotropicOfPosDef K V σ H r F' hP'
  have hμ : ∃ μ : K, μ + star μ ≠ 0 := by
    refine ⟨F.T, fun h0 => ?_⟩
    have h1 := congrArg (fun t => (σ t).re) h0
    simp only [map_add, hσ, map_zero, Complex.add_re, Complex.zero_re] at h1
    rw [show star (σ F.T) = (starRingEnd ℂ) (σ F.T) from rfl, Complex.conj_re] at h1
    linarith
  by_cases hm : Formalism.HermitianLatticeCounting.S6.II F F' = ⊥
  · have hD : Formalism.HermitianLatticeCounting.S6.Dl F F' r (Nat.le_succ r) ≠ 0 := fun hD =>
      normalFormDegenerateImpossible K V H r F F' hA hA' hm hD hg
    have hsig := signatureOneComplementOfMinorNeZero K V σ H r F F' hT hP hD
    obtain ⟨c, hz⟩ := existsScalarOfGramDefectZero K V σ H r F F' hσ hT hT' hsig hD hg
    have hc : c ≠ 0 := by
      rintro rfl
      apply lastVectorNotMemSup K V H r F' F
      rw [sup_comm]
      simpa using hz
    refine ⟨r, le_rfl, c, nf_full F F' hA hA' r le_rfl c ?_⟩
    unfold Formalism.HermitianLatticeCounting.S6.NFShape
    refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hz⟩
    · rw [hm, finrank_bot, Nat.sub_self]
    · intro x hx hx0
      rw [hm] at hx
      exact absurd ((Submodule.mem_bot K).1 hx) hx0
    · intro a ha
      exact absurd a.isLt (by omega)
    · rw [hm, bot_inf_eq]
    · rw [hm, bot_inf_eq]
    · rw [hm, sup_bot_eq]
      rfl
    · rw [hm, sup_bot_eq]
      rfl
  · obtain ⟨j, c, hj, hS⟩ := normalFormMeetNeBot K V H r F F' hμ hrel hm
    exact ⟨j, hj.le, c, nf_full F F' hA hA' j hj.le c hS⟩

section DetBlocks

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def Esing (p : n) (s : R) : Matrix n n R := Matrix.of fun a b => if a = p ∧ b = p then s else 0

end DetBlocks

theorem eichlerMapIsometry : Formalism.HermitianLatticeCounting.S6.EichlerIsom := by
  intro K V _ _ _ _ H x v c hxx hxv hc
  have hvx : H.B v x = 0 := B_swap0 H hxv
  have hcs : star c = -H.B v v - c := by linear_combination hc
  refine ⟨fun y y' => ?_, fun y => ?_, fun y => ?_⟩
  · simp only [eich_apply_eq_add_wedge_add_smul, HermSpace_B_add_left, HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_add_right, HermSpace_B_sub_right, HermSpace_B_smul_right_eq_star_mul,
      H.herm, hxx, hxv, hvx]
    linear_combination (H.B y x * H.B x y') * hc
  · simp only [eich_apply_eq_add_wedge_add_smul, HermSpace_B_add_left, HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_neg_left, map_neg, LinearMap.neg_apply, hxx, hxv, hvx]
    rw [hcs]
    module
  · simp only [eich_apply_eq_add_wedge_add_smul, HermSpace_B_add_left, HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_neg_left, map_neg, LinearMap.neg_apply, hxx, hxv, hvx]
    rw [hcs]
    module

section Lift

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

lemma eich_apply (H : HermSpace K V) (x v : V) (c : K) (y : V) :
    eich H x v c y = y + (H.B y v • x - H.B y x • v) + c • H.B y x • x := by
  simp only [Formalism.HermitianLatticeCounting.S6.eich, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, xv_apply_eq_B_smul_sub_B_smul]

def GoodMap (F F' : FlagD H r) (g : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (g x) (g y) = H.B x y) ∧ Function.Bijective g ∧ (∀ y ∈ V0 F F', g y = y) ∧
  (∀ y : V, (∀ u ∈ II F F', H.B u y = 0) → g y - y ∈ II F F')

lemma isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' := inf_le_left.trans (isotropicSpan_le_jointSpan_left F F')

lemma GoodMap.inN (F F' : FlagD H r) {g : V →ₗ[K] V} (hg : GoodMap F F' g) : F.InN g ∧ F'.InN g := by
  obtain ⟨hiso, hbij, hfix, hmeet⟩ := id hg
  constructor
  · unfold Formalism.HermitianLatticeCounting.S6.FlagD.InN
    refine ⟨hiso, hbij, fun a => ?_, fun y hy => ?_⟩
    · rw [hfix _ (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left F F' ((Formalism.HermitianLatticeCounting.P.e_mem_X F) a)), sub_self]
      exact Submodule.zero_mem _
    · exact (Submodule.mem_inf.1 (hmeet y fun u hu =>
        (Formalism.HermitianLatticeCounting.P.perp_X F) hy u (Submodule.mem_inf.1 hu).1)).1
  · unfold Formalism.HermitianLatticeCounting.S6.FlagD.InN
    refine ⟨hiso, hbij, fun a => ?_, fun y hy => ?_⟩
    · rw [hfix _ (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right F F' ((Formalism.HermitianLatticeCounting.P.e_mem_X F') a)), sub_self]
      exact Submodule.zero_mem _
    · exact (Submodule.mem_inf.1 (hmeet y fun u hu =>
        (Formalism.HermitianLatticeCounting.P.perp_X F') hy u (Submodule.mem_inf.1 hu).2)).2

lemma GoodMap.comp (F F' : FlagD H r) {g g' : V →ₗ[K] V} (hg : GoodMap F F' g) (hg' : GoodMap F F' g') :
    GoodMap F F' (g ∘ₗ g') := by
  obtain ⟨hiso, hbij, hfix, hmeet⟩ := id hg
  obtain ⟨hiso', hbij', hfix', hmeet'⟩ := id hg'
  unfold Formalism.HermitianLatticeCounting.P.GoodMap
  refine ⟨fun x y => ?_, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · simp only [LinearMap.comp_apply]
    rw [hiso, hiso']
  · rw [LinearMap.coe_comp]
    exact hbij.comp hbij'
  · simp only [LinearMap.comp_apply]
    rw [hfix' y hy, hfix y hy]
  · simp only [LinearMap.comp_apply]
    have h1 := hmeet' y hy
    have h2 : ∀ u ∈ Formalism.HermitianLatticeCounting.S6.II F F', H.B u (g' y) = 0 := by
      intro u hu
      have hgy : g' y = y + (g' y - y) := by abel
      rw [hgy, _root_.Formalism.HermitianLatticeCounting.P.HermSpace_B_add_right, hy u hu, zero_add]
      exact (Formalism.HermitianLatticeCounting.P.X_iso F) (Submodule.mem_inf.1 hu).1 (Submodule.mem_inf.1 h1).1
    have h3 := hmeet (g' y) h2
    have hsplit : g (g' y) - y = (g (g' y) - g' y) + (g' y - y) := by abel
    rw [hsplit]
    exact Submodule.add_mem _ h3 h1

lemma eich_good (hE : Formalism.HermitianLatticeCounting.S6.EichlerIsom) (F F' : FlagD H r) {x v : V} {c : K} (hx : x ∈ II F F')
    (hv : ∀ y ∈ V0 F F', H.B y v = 0) (hc : c + star c = -H.B v v) : GoodMap F F' (eich H x v c) := by
  have hxI : x ∈ F.X := (Submodule.mem_inf.1 hx).1
  have hxx : H.B x x = 0 := (X_iso F) hxI hxI
  have hxv : H.B x v = 0 := hv x (isotropicMeet_le_jointSpan F F' hx)
  obtain ⟨hiso, hl, hr⟩ := hE _ _ H x v c hxx hxv hc
  unfold GoodMap
  refine ⟨hiso, ⟨fun y y' h => ?_, fun y => ⟨_, hr y⟩⟩, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← hl y, h, hl y']
  · have h1 := hv y hy
    have h2 := pairing_jointSpan_isotropicMeet F F' hx y hy
    rw [eich_apply, h1, h2]
    simp
  · have h2 : H.B y x = 0 := B_swap0 H (hy x hx)
    rw [eich_apply, h2]
    simp only [zero_smul, sub_zero, smul_zero, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hx

lemma eich_perp (F F' : FlagD H r) {x v : V} {c : K} (hx : x ∈ II F F') {w : V}
    (hw : ∀ y ∈ V0 F F', H.B y w = 0) : eich H x v c w = w + H.B w v • x := by
  have hwx : H.B w x = 0 := B_swap0 H (hw x (isotropicMeet_le_jointSpan F F' hx))
  rw [eich_apply, hwx]
  simp

lemma exists_half (hμ : ∃ μ : K, μ + star μ ≠ 0) (q : K) (hq : star q = q) :
    ∃ c : K, c + star c = -q := by
  obtain ⟨μ, hμ⟩ := hμ
  refine ⟨-q * μ / (μ + star μ), ?_⟩
  have hs : star (μ + star μ) = μ + star μ := by rw [star_add, star_star, add_comm]
  rw [star_div₀, star_mul', star_neg, hq, hs]
  field_simp
  ring

lemma good_family (hE : Formalism.HermitianLatticeCounting.S6.EichlerIsom) (hR : Formalism.HermitianLatticeCounting.S6.EichlerInR) (F F' : FlagD H r) (hμ : ∃ μ : K, μ + star μ ≠ 0) (n : ℕ) (x v : Fin n → V)
    (hx : ∀ i, x i ∈ II F F') (hv : ∀ i, ∀ y ∈ V0 F F', H.B y (v i) = 0) :
    ∃ g : V →ₗ[K] V, GoodMap F F' g ∧
      ∀ w : V, (∀ y ∈ V0 F F', H.B y w = 0) → g w = w + ∑ i, H.B w (v i) • x i := by
  induction n with
  | zero =>
    refine ⟨LinearMap.id, ?_, fun w _ => by simp⟩
    unfold GoodMap
    refine ⟨fun _ _ => rfl, Function.bijective_id, fun _ _ => rfl, fun y _ => by simp⟩
  | succ n ih =>
    obtain ⟨g₀, hg₀, hg₀w⟩ := ih (fun i => x i.castSucc) (fun i => v i.castSucc) (fun i => hx _) (fun i => hv _)
    obtain ⟨c, hc⟩ := exists_half hμ (H.B (v (Fin.last n)) (v (Fin.last n))) (H.herm _ _)
    have hE' := eich_good hE F F' (hx (Fin.last n)) (hv (Fin.last n)) hc
    refine ⟨Formalism.HermitianLatticeCounting.S6.eich H (x (Fin.last n)) (v (Fin.last n)) c ∘ₗ g₀, Formalism.HermitianLatticeCounting.P.GoodMap.comp F F' hE' hg₀,
      fun w hw => ?_⟩
    rw [LinearMap.comp_apply, hg₀w w hw]
    have hsum : ∑ i : Fin n, H.B w (v i.castSucc) • x i.castSucc ∈ Formalism.HermitianLatticeCounting.S6.II F F' :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx _)
    have hw' : ∀ y ∈ Formalism.HermitianLatticeCounting.S6.V0 F F', H.B y (w + ∑ i : Fin n, H.B w (v i.castSucc) • x i.castSucc) = 0 := by
      intro y hy
      rw [HermSpace_B_add_right, hw y hy, pairing_jointSpan_isotropicMeet F F' hsum y hy, add_zero]
    rw [eich_perp F F' (hx (Fin.last n)) hw', Fin.sum_univ_castSucc]
    have h0 : H.B (∑ i : Fin n, H.B w (v i.castSucc) • x i.castSucc) (v (Fin.last n)) = 0 :=
      hv _ _ (isotropicMeet_le_jointSpan F F' hsum)
    rw [HermSpace_B_add_left, h0, add_zero, add_assoc]

lemma repr_aniso [FiniteDimensional K V] (H : HermSpace K V) (W : Submodule K V)
    (hW : ∀ w ∈ W, H.B w w = 0 → w = 0) (l : V →ₗ[K] K) : ∃ v ∈ W, ∀ w ∈ W, H.B w v = l w := by
  let b := Module.finBasis K W
  let Ψ : W →ₗ[K] (Fin (Module.finrank K W) → K) := LinearMap.pi fun i => (H.B.flip (b i : V)).comp W.subtype
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hb : ∀ i, H.B (w : V) (b i : V) = 0 := fun i => by simpa [Ψ] using congrFun hw i
    have h0 : (H.B (w : V)).comp W.subtype = 0 := b.ext fun i => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
      exact hb i
    have h5 := LinearMap.congr_fun h0 w
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply] at h5
    exact Subtype.ext (hW w w.2 h5)
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hΨ
  obtain ⟨w, hw⟩ := hsurj (fun i => star (l (b i : V)))
  have key : ∀ i, H.B (b i : V) (w : V) = l (b i : V) := by
    intro i
    have h1 := congrFun hw i
    simp only [Ψ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply] at h1
    rw [← H.herm, h1, star_star]
  refine ⟨w, w.2, fun u hu => ?_⟩
  have h2 : (H.B.flip (w : V)).comp W.subtype = l.comp W.subtype := b.ext fun i => by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply]
    exact key i
  have h3 := LinearMap.congr_fun h2 ⟨u, hu⟩
  simpa using h3

end Lift

theorem eichlerMapFixesJointSpan : Formalism.HermitianLatticeCounting.S6.EichlerInR := by
  intro K V _ _ _ _ H r F F' x v c hx hv hc
  have hadm := eich_good eichlerMapIsometry F F' hx hv hc
  obtain ⟨hU, hU'⟩ := Formalism.HermitianLatticeCounting.P.GoodMap.inN F F' hadm
  obtain ⟨-, -, hfix, -⟩ := id hadm
  exact ⟨hfix, hU, hU', fun w hw => eich_perp F F' hx hw⟩

lemma liftTransitive_of (hE : Formalism.HermitianLatticeCounting.S6.EichlerIsom) (hR : Formalism.HermitianLatticeCounting.S6.EichlerInR) :
    Formalism.HermitianLatticeCounting.S6.LiftTransitive := by
  intro K V _ _ _ _ _ H r F F' W₁ W₂ hμ hA hA' hW₁ hW₂
  obtain ⟨hW₁o, hW₁m, hW₁s⟩ := id hW₁
  obtain ⟨hW₂o, hW₂m, hW₂s⟩ := id hW₂
  have heF : ∀ a : Fin (r + 1), F.e a ∈ Formalism.HermitianLatticeCounting.S6.V0 F F' := by
    intro a
    induction a using Fin.lastCases with
    | last => exact lastVector_mem_jointSpan_left F F'
    | cast b => exact isotropicSpan_le_jointSpan_left F F' ((e_mem_X F) b)
  have heF' : ∀ a : Fin (r + 1), F'.e a ∈ Formalism.HermitianLatticeCounting.S6.V0 F F' := by
    intro a
    induction a using Fin.lastCases with
    | last => exact lastVector_mem_jointSpan_right F F'
    | cast b => exact isotropicSpan_le_jointSpan_right F F' ((e_mem_X F') b)
  have hanis : ∀ w ∈ W₁, H.B w w = 0 → w = 0 := by
    intro w hw hww
    have hwF : w ∈ F.X := hA w (fun a => hW₁o w hw _ (heF a)) hww
    have hwF' : w ∈ F'.X := hA' w (fun a => hW₁o w hw _ (heF' a)) hww
    have hmem : w ∈ W₁ ⊓ Formalism.HermitianLatticeCounting.S6.II F F' := Submodule.mem_inf.2 ⟨hw, Submodule.mem_inf.2 ⟨hwF, hwF'⟩⟩
    rw [hW₁m] at hmem
    exact (Submodule.mem_bot K).1 hmem
  let bm := Module.finBasis K (Formalism.HermitianLatticeCounting.S6.II F F')
  let b1 := Module.finBasis K W₁
  have hdec : ∀ k, ∃ m : Formalism.HermitianLatticeCounting.S6.II F F', (b1 k : V) - (m : V) ∈ W₂ := by
    intro k
    obtain ⟨w₂, hw₂, m, hm, hsum⟩ := Submodule.mem_sup.1 (hW₂s _ (hW₁o _ (b1 k).2))
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [← hsum]
    simpa using hw₂
  choose mk hmk using hdec
  let φ : W₁ →ₗ[K] Formalism.HermitianLatticeCounting.S6.II F F' := b1.constr K mk
  have hφ : ∀ w : W₁, (w : V) - (φ w : V) ∈ W₂ := by
    intro w
    rw [← b1.sum_repr w]
    simp only [φ, map_sum, map_smul, Module.Basis.constr_basis, Submodule.coe_sum, Submodule.coe_smul]
    rw [← Finset.sum_sub_distrib]
    exact Submodule.sum_mem _ fun k _ => by
      rw [← smul_sub]
      exact Submodule.smul_mem _ _ (hmk k)
  have hv : ∀ i, ∃ v : V, v ∈ W₁ ∧ ∀ w : W₁, H.B (w : V) v = -(bm.repr (φ w) i) := by
    intro i
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (-((bm.coord i).comp φ))
    obtain ⟨v, hvW, hvl⟩ := repr_aniso H W₁ hanis g
    refine ⟨v, hvW, fun w => ?_⟩
    rw [hvl w w.2]
    have h1 := LinearMap.congr_fun hg w
    simpa using h1
  choose v hvW hvB using hv
  obtain ⟨g, hg, hgw⟩ := good_family hE hR F F' hμ _ (fun i => (bm i : V)) v
    (fun i => (bm i).2) (fun i y hy => hW₁o _ (hvW i) y hy)
  obtain ⟨hU, hU'⟩ := Formalism.HermitianLatticeCounting.P.GoodMap.inN F F' hg
  obtain ⟨-, hbij, hfix, -⟩ := id hg
  refine ⟨g, hU, hU', hfix, ?_⟩
  have hle : W₁.map g ≤ W₂ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hgw w (hW₁o w hw)]
    have h2 : ∀ i, H.B w (v i) = -(bm.repr (φ ⟨w, hw⟩)) i := fun i => hvB i ⟨w, hw⟩
    have h3 : ∑ i, (bm.repr (φ ⟨w, hw⟩)) i • (bm i : V) = (φ ⟨w, hw⟩ : V) := by
      conv_rhs => rw [← bm.sum_repr (φ ⟨w, hw⟩)]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    simp only [h2, neg_smul, Finset.sum_neg_distrib]
    rw [h3, ← sub_eq_add_neg]
    exact hφ ⟨w, hw⟩
  have hsup : W₁ ⊔ Formalism.HermitianLatticeCounting.S6.II F F' = W₂ ⊔ Formalism.HermitianLatticeCounting.S6.II F F' :=
    le_antisymm (sup_le (fun w hw => hW₂s w (hW₁o w hw)) le_sup_right)
      (sup_le (fun w hw => hW₁s w (hW₂o w hw)) le_sup_right)
  have hfr : Module.finrank K W₁ = Module.finrank K W₂ := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq W₁ (Formalism.HermitianLatticeCounting.S6.II F F')
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq W₂ (Formalism.HermitianLatticeCounting.S6.II F F')
    rw [hW₁m, finrank_bot, hsup] at e1
    rw [hW₂m, finrank_bot] at e2
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle
    (by rw [← (Submodule.equivMapOfInjective g hbij.1 W₁).finrank_eq, hfr])

theorem complementLiftTransitive : Formalism.HermitianLatticeCounting.S6.LiftTransitive := liftTransitive_of eichlerMapIsometry eichlerMapFixesJointSpan

end Formalism.HermitianLatticeCounting.P
