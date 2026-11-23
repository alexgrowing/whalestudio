import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def lf (w : V) : V →ₗ[E] E where
  toFun y := H.h y w
  map_add' x y := H.h_add_left x y w
  map_smul' a x := by simp [H.h_smul_left]

lemma h_right (x y : V) : H.h x y = M.L.cj (H.h y x) := H.h_herm y x

lemma h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := (lf H y).map_sub x x'

lemma h_neg_left (x y : V) : H.h (-x) y = -H.h x y := (lf H y).map_neg x

lemma h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [h_right H x, H.h_add_left, map_add, ← h_right, ← h_right]

lemma h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [h_right H x, h_sub_left, map_sub, ← h_right, ← h_right]

lemma h_neg_right (x y : V) : H.h x (-y) = -H.h x y := by
  rw [h_right H x, h_neg_left, map_neg, ← h_right]

lemma h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [h_right H x, H.h_smul_left, map_mul, ← h_right]

lemma h_zero_right (x : V) : H.h x 0 = 0 := by
  rw [h_right, H.h_zero_left, map_zero]

def eichF (x v : V) (c : F) (y : V) : V :=
  y + H.h y v • x - H.h y x • v + (algebraMap F E c * H.h y x) • x

def eichL (x v : V) (c : F) : V →ₗ[E] V where
  toFun := eichF H x v c
  map_add' y y' := by
    simp only [eichF, H.h_add_left, add_smul, mul_add]; abel
  map_smul' a y := by
    simp only [eichF, H.h_smul_left, RingHom.id_apply]; module

lemma eich_hL (x v : V) (c : F) (y w : V) : H.h (eichF H x v c y) w =
    H.h y w + H.h y v * H.h x w - H.h y x * H.h v w + algebraMap F E c * H.h y x * H.h x w := by
  simp only [eichF, H.h_add_left, h_sub_left, H.h_smul_left]

lemma eich_hR (x v : V) (c : F) (w y : V) : H.h w (eichF H x v c y) =
    H.h w y + M.L.cj (H.h y v) * H.h w x - M.L.cj (H.h y x) * H.h w v +
      algebraMap F E c * M.L.cj (H.h y x) * H.h w x := by
  simp only [eichF, h_add_right, h_sub_right, h_smul_right, map_mul, AlgEquiv.commutes]

lemma eich_fix (x v : V) (c : F) (y : V) (h1 : H.h y v = 0) (h2 : H.h y x = 0) : eichF H x v c y = y := by
  simp [eichF, h1, h2]

section Eich
variable {x v : V} {c : F}

lemma eich_isom (hxx : H.h x x = 0) (hxv : H.h x v = 0)
    (hc : 2 * algebraMap F E c + H.h v v = 0) (y y' : V) :
    H.h (eichF H x v c y) (eichF H x v c y') = H.h y y' := by
  have hvx : H.h v x = 0 := by rw [h_right, hxv, map_zero]
  have e1 : H.h x y' = M.L.cj (H.h y' x) := h_right H x y'
  have e2 : H.h v y' = M.L.cj (H.h y' v) := h_right H v y'
  simp only [eich_hL, eich_hR]
  rw [hxx, hxv, hvx, e1, e2]
  linear_combination (H.h y x * M.L.cj (H.h y' x)) * hc

lemma eich_inv (hxx : H.h x x = 0) (hxv : H.h x v = 0)
    (hc : 2 * algebraMap F E c + H.h v v = 0) (y : V) :
    eichF H x v c (eichF H (-x) v c y) = y := by
  have hvx : H.h v x = 0 := by rw [h_right, hxv, map_zero]
  have e1 : H.h (eichF H (-x) v c y) v = H.h y v + H.h y x * H.h v v := by
    rw [eich_hL, h_neg_left, h_neg_right, hxv]; ring
  have e2 : H.h (eichF H (-x) v c y) x = H.h y x := by
    rw [eich_hL, h_neg_left, h_neg_right, hxx, hvx]; ring
  have key : eichF H x v c (eichF H (-x) v c y) - y =
      ((2 * algebraMap F E c + H.h v v) * H.h y x) • x := by
    unfold eichF at e1 e2 ⊢
    rw [e1, e2, h_neg_right]
    module
  rw [hc, zero_mul, zero_smul, sub_eq_zero] at key
  exact key

def eichE (hxx : H.h x x = 0) (hxv : H.h x v = 0) (hc : 2 * algebraMap F E c + H.h v v = 0) :
    V ≃ₗ[E] V :=
  LinearEquiv.ofLinear (eichL H x v c) (eichL H (-x) v c)
    (LinearMap.ext fun y => eich_inv H hxx hxv hc y)
    (LinearMap.ext fun y => by
      have h1 : H.h (-x) (-x) = 0 := by rw [h_neg_left, h_neg_right, neg_neg, hxx]
      have h2 : H.h (-x) v = 0 := by rw [h_neg_left, hxv, neg_zero]
      have := eich_inv H h1 h2 hc y
      rw [neg_neg] at this
      exact this)

lemma eichE_apply (hxx : H.h x x = 0) (hxv : H.h x v = 0) (hc : 2 * algebraMap F E c + H.h v v = 0)
    (y : V) : eichE H hxx hxv hc y = eichF H x v c y := rfl

end Eich

lemma flag_iff {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (A : ℕ → Submodule R W)
    (h0 : A 0 = ⊥) (hm : ∀ j, A j ≤ A (j + 1)) (r : ℕ) (g : W ≃ₗ[R] W)
    (hg : ∀ j, j < r → ∀ v ∈ A (j + 1), g v - v ∈ A j) :
    ∀ j, j ≤ r → ∀ v, g v ∈ A j ↔ v ∈ A j := by
  have hs : ∀ j, j ≤ r → ∀ w ∈ A j, ∃ v ∈ A j, g v = w := by
    intro j
    induction j with
    | zero =>
      intro _ w hw
      rw [h0] at hw ⊢
      exact ⟨0, by simp, by simpa using hw.symm⟩
    | succ j ih =>
      intro hj w hw
      obtain ⟨u, hu, hgu⟩ := ih (by omega) _ (hg j (by omega) w hw)
      refine ⟨w - u, (A (j + 1)).sub_mem hw (hm j hu), ?_⟩
      rw [map_sub, hgu]; abel
  intro j hj v
  constructor
  · intro h
    obtain ⟨u, hu, hgu⟩ := hs j hj _ h
    rwa [← g.injective hgu]
  · intro h
    cases j with
    | zero =>
      rw [h0] at h ⊢
      simpa using h
    | succ j =>
      have h1 := (A (j + 1)).add_mem (hm j (hg j (by omega) v h)) h
      simpa using h1

section Frame
variable {H} {r : ℕ} (Fr : FrameD H r)

lemma Fj_zero : Fr.Fj 0 = ⊥ := by simp [FrameD.Fj]

lemma Fj_mono {j j' : ℕ} (h : j ≤ j') : Fr.Fj j ≤ Fr.Fj j' :=
  Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < j) => (show (i : ℕ) < j' by omega))

lemma Fj_r : Fr.Fj r = H.X Fr.f := by
  unfold FrameD.Fj HermSp.X
  congr 1
  ext x
  simp [FrameD.e]

lemma Fj_le_X (j : ℕ) : Fr.Fj j ≤ H.X Fr.f := by
  unfold FrameD.Fj HermSp.X
  exact Submodule.span_mono (by rintro _ ⟨a, _, rfl⟩; exact ⟨a, rfl⟩)

lemma e_mem (a : Fin r) : Fr.f a.castSucc ∈ Fr.Fj (a.val + 1) :=
  Submodule.subset_span ⟨a, by simp, rfl⟩

lemma span_fin_eq (a : Fin r) :
    Submodule.span E ((fun b : Fin r => Fr.f b.castSucc) '' {b | b < a}) = Fr.Fj a.val := rfl

lemma perp_gen (y : V) (h : ∀ a : Fin r, H.h (Fr.f a.castSucc) y = 0) :
    ∀ w ∈ H.X Fr.f, H.h w y = 0 := by
  have : H.X Fr.f ≤ LinearMap.ker (lf H y) :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h a)
  exact fun w hw => this hw

lemma X_iso : ∀ w ∈ H.X Fr.f, ∀ w' ∈ H.X Fr.f, H.h w w' = 0 := by
  intro w hw w' hw'
  refine perp_gen Fr w' (fun a => ?_) w hw
  rw [h_right, perp_gen Fr _ (fun b => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last b))) w' hw', map_zero]

lemma pairing_isotropicSpan_lastVector : ∀ w ∈ H.X Fr.f, H.h w (Fr.f (Fin.last r)) = 0 :=
  perp_gen Fr _ (fun b => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last b)))

lemma z_X : ∀ w ∈ H.X Fr.f, H.h (Fr.f (Fin.last r)) w = 0 := by
  intro w hw; rw [h_right, pairing_isotropicSpan_lastVector Fr w hw, map_zero]

lemma z_perp : Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := fun w hw => z_X Fr w hw

lemma X_le_perp : H.X Fr.f ≤ H.perp (H.X Fr.f) := fun w hw w' hw' => X_iso Fr w hw w' hw'

lemma Fj_es (j : ℕ) (b : Fin r) (hb : j ≤ b.val) : ∀ w ∈ Fr.Fj j, H.h w (Fr.es b) = 0 := by
  have : Fr.Fj j ≤ LinearMap.ker (lf H (Fr.es b)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hab : a ≠ b := by
      intro h; subst h; exact absurd (show a.val < j from ha) (by omega)
    show H.h (Fr.f a.castSucc) (Fr.es b) = 0
    rw [Fr.h_es, if_neg hab]
  exact fun w hw => this hw

lemma z_es (b : Fin r) : H.h (Fr.f (Fin.last r)) (Fr.es b) = 0 := by
  rw [h_right, Fr.h_sz, map_zero]

end Frame

section NUgrp
variable {H} {r : ℕ} (Fr : FrameD H r)

lemma NU_step {g : V ≃ₗ[E] V} (hg : g ∈ NU H Fr.f) :
    ∀ j, j < r → ∀ v ∈ Fr.Fj (j + 1), g v - v ∈ Fr.Fj j := by
  intro j hj
  have : Fr.Fj (j + 1) ≤ (Fr.Fj j).comap ((g : V →ₗ[E] V) - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 := hg.2.1 a
    rw [span_fin_eq] at h2
    have ha' : a.val < j + 1 := ha
    show g (Fr.f a.castSucc) - Fr.f a.castSucc ∈ Fr.Fj j
    exact Fj_mono Fr (by omega) h2
  intro v hv
  exact this hv

lemma NU_flag {g : V ≃ₗ[E] V} (hg : g ∈ NU H Fr.f) : ∀ j, j ≤ r → ∀ v, g v ∈ Fr.Fj j ↔ v ∈ Fr.Fj j :=
  flag_iff Fr.Fj (Fj_zero Fr) (fun j => Fj_mono Fr (Nat.le_succ j)) r g (NU_step Fr hg)

def NUg : Subgroup (V ≃ₗ[E] V) where
  carrier := NU H Fr.f
  one_mem' := ⟨fun x y => rfl, fun a => by simp, fun v _ => by simp⟩
  mul_mem' := by
    intro g k hg hk
    refine ⟨fun x y => by simp [hg.1 _ _, hk.1 x y], fun a => ?_, fun v hv => ?_⟩
    · have hga := hg.2.1 a
      have hka := hk.2.1 a
      rw [span_fin_eq] at hga hka ⊢
      have h1 : g (k (Fr.f a.castSucc) - Fr.f a.castSucc) ∈ Fr.Fj a.val :=
        (NU_flag Fr hg a.val a.isLt.le _).2 hka
      have : (g * k) (Fr.f a.castSucc) - Fr.f a.castSucc =
          g (k (Fr.f a.castSucc) - Fr.f a.castSucc) + (g (Fr.f a.castSucc) - Fr.f a.castSucc) := by
        rw [map_sub]; simp
      rw [this]; exact add_mem h1 hga
    · have hk3 := hk.2.2 v hv
      have hg3 := hg.2.2 v hv
      rw [← Fj_r] at hk3 hg3 ⊢
      have h1 : g (k v - v) ∈ Fr.Fj r := (NU_flag Fr hg r le_rfl _).2 hk3
      have : (g * k) v - v = g (k v - v) + (g v - v) := by rw [map_sub]; simp
      rw [this]; exact add_mem h1 hg3
  inv_mem' := by
    intro g hg
    refine ⟨fun x y => ?_, fun a => ?_, fun v hv => ?_⟩
    · have := hg.1 (g⁻¹ x) (g⁻¹ y)
      simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at this ⊢
      exact this.symm
    · have hga := hg.2.1 a
      rw [span_fin_eq] at hga ⊢
      refine (NU_flag Fr hg a.val a.isLt.le _).1 ?_
      have : g (g⁻¹ (Fr.f a.castSucc) - Fr.f a.castSucc) = -(g (Fr.f a.castSucc) - Fr.f a.castSucc) := by
        rw [map_sub]; simp
      rw [this]; exact neg_mem hga
    · have hg3 := hg.2.2 v hv
      rw [← Fj_r] at hg3 ⊢
      refine (NU_flag Fr hg r le_rfl _).1 ?_
      have : g (g⁻¹ v - v) = -(g v - v) := by rw [map_sub]; simp
      rw [this]; exact neg_mem hg3

lemma NSet_eq : Fr.NSet = (NUg Fr : Set (V ≃ₗ[E] V)) := by
  ext g
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a => ?_, h3⟩
    rw [span_fin_eq]
    have := h2 (a.val + 1) a.isLt (Fr.f a.castSucc) (e_mem Fr a)
    simpa using this
  · intro hg
    refine ⟨hg.1, fun j hj v hv => ?_, hg.2.2⟩
    cases j with
    | zero =>
      rw [Fj_zero] at hv
      rw [(Submodule.mem_bot E).1 hv]; simp
    | succ j => simpa using NU_step Fr hg j hj v hv

lemma N_eq : Fr.N = NUg Fr := by
  unfold FrameD.N
  rw [NSet_eq, Subgroup.closure_eq]

end NUgrp

section Tri

lemma tri_of_mem {n : ℕ} (f g : Fin n → V)
    (h : ∀ b, g b - f b ∈ Submodule.span E (f '' {a | a.val < b.val})) : Tri E f g := by
  have h' : ∀ b, ∃ l ∈ Finsupp.supported E E {a : Fin n | a.val < b.val},
      Finsupp.linearCombination E f l = g b - f b := fun b =>
    (Finsupp.mem_span_image_iff_linearCombination E).1 (h b)
  choose L hL hLeq using h'
  have hz : ∀ a b : Fin n, ¬ a.val < b.val → L b a = 0 := by
    intro a b hab
    by_contra hne
    exact hab (hL b (Finsupp.mem_support_iff.2 hne))
  refine ⟨fun a b => (if a = b then 1 else 0) + L b a, ⟨fun a b hba => ?_, fun a => ?_⟩, fun b => ?_⟩
  · have hne : a ≠ b := fun h => by subst h; exact lt_irrefl _ hba
    simp only [if_neg hne, zero_add]
    exact hz a b (by have : b.val < a.val := hba; omega)
  · simp [hz a a (lt_irrefl _)]
  · have e1 := hLeq b
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e1
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, e1]
    abel

lemma mem_of_tri {n : ℕ} (f g : Fin n → V) (hg : Tri E f g) :
    ∀ b, g b - f b ∈ Submodule.span E (f '' {a | a.val < b.val}) := by
  obtain ⟨A, ⟨hlow, hdiag⟩, hchg⟩ := hg
  intro b
  have : g b - f b = ∑ a, (A a b - if a = b then 1 else 0) • f a := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hchg b]
  rw [this]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases hab : a.val < b.val
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hab, rfl⟩)
  · by_cases he : a = b
    · subst he; simp [hdiag]
    · have : b < a := by
        have : a.val ≠ b.val := fun h => he (Fin.ext h)
        show b.val < a.val; omega
      simp [hlow a b this, he]

variable {H} {r : ℕ} (Fr : FrameD H r)

lemma spanf_le (j : ℕ) (hj : j ≤ r) : Submodule.span E (Fr.f '' {a | a.val < j}) ≤ Fr.Fj j := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a.val < j := ha
  have : a = (⟨a.val, by omega⟩ : Fin r).castSucc := Fin.ext rfl
  rw [this]
  exact Submodule.subset_span ⟨⟨a.val, by omega⟩, ha', rfl⟩

lemma Fj_le_spanf (j : ℕ) : Fr.Fj j ≤ Submodule.span E (Fr.f '' {a | a.val < j}) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact Submodule.subset_span ⟨a.castSucc, ha, rfl⟩

lemma NU_mem {n : V ≃ₗ[E] V} (hn : n ∈ NU H Fr.f) :
    ∀ b, n (Fr.f b) - Fr.f b ∈ Submodule.span E (Fr.f '' {a | a.val < b.val}) := by
  intro b
  induction b using Fin.lastCases with
  | last =>
    have := hn.2.2 _ (z_perp Fr)
    rw [← Fj_r] at this
    exact Fj_le_spanf Fr r (by simpa using this)
  | cast c =>
    have := hn.2.1 c
    rw [span_fin_eq] at this
    exact Fj_le_spanf Fr c.val (by simpa using this)

end Tri

section Onto
variable {H} {r : ℕ} (Fr : FrameD H r)

lemma eich_mem {x v : V} {c : F} (hx : x ∈ H.X Fr.f) (hxv : H.h x v = 0)
    (hc : 2 * algebraMap F E c + H.h v v = 0)
    (h2 : ∀ a : Fin r, H.h (Fr.f a.castSucc) v • x ∈ Fr.Fj a.val) :
    eichE H (X_iso Fr x hx x hx) hxv hc ∈ NUg Fr := by
  refine ⟨fun y y' => eich_isom H (X_iso Fr x hx x hx) hxv hc y y', fun a => ?_, fun y hy => ?_⟩
  · rw [span_fin_eq, eichE_apply]
    have h0 : H.h (Fr.f a.castSucc) x = 0 :=
      X_iso Fr _ (Fj_le_X Fr (a.val + 1) (e_mem Fr a)) x hx
    have : eichF H x v c (Fr.f a.castSucc) - Fr.f a.castSucc = H.h (Fr.f a.castSucc) v • x := by
      simp [eichF, h0]
    rw [this]; exact h2 a
  · rw [eichE_apply]
    have h0 : H.h y x = 0 := hy x hx
    have : eichF H x v c y - y = H.h y v • x := by simp [eichF, h0]
    rw [this]; exact Submodule.smul_mem _ _ hx

lemma levi (u : Fin r → V) (hu : ∀ c, u c ∈ Fr.Fj c.val) :
    ∀ k, k ≤ r → ∃ n ∈ NUg Fr, (∀ c : Fin r, n (Fr.f c.castSucc) =
      Fr.f c.castSucc + if c.val < k then u c else 0) ∧ n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨1, (NUg Fr).one_mem, fun c => by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨n, hn, hne, hnz⟩ := ih (by omega)
    set kk : Fin r := ⟨k, by omega⟩ with hkk
    have hx : u kk ∈ H.X Fr.f := Fj_le_X Fr _ (hu kk)
    have hxv : H.h (u kk) (Fr.es kk) = 0 := Fj_es Fr kk.val kk le_rfl _ (hu kk)
    have hc : 2 * algebraMap F E (0 : F) + H.h (Fr.es kk) (Fr.es kk) = 0 := by
      rw [Fr.h_ss, map_zero]; ring
    have hM := eich_mem Fr hx hxv hc (fun a => by
      rw [Fr.h_es]
      by_cases hak : a = kk
      · subst hak; simpa using hu _
      · simp [hak])
    refine ⟨_ * n, mul_mem hM hn, fun c => ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, hne c, eichE_apply]
      have hcx : H.h (Fr.f c.castSucc) (u kk) = 0 :=
        X_iso Fr _ (Fj_le_X Fr (c.val + 1) (e_mem Fr c)) _ hx
      by_cases hck : c.val < k
      · have hfix : eichF H (u kk) (Fr.es kk) 0 (u c) = u c :=
          eich_fix H _ _ _ _ (Fj_es Fr c.val kk (by simp [hkk]; omega) _ (hu c))
            (X_iso Fr _ (Fj_le_X Fr _ (hu c)) _ hx)
        have hne' : c ≠ kk := fun h => by subst h; simp [hkk] at hck
        have hadd : eichF H (u kk) (Fr.es kk) 0 (Fr.f c.castSucc + u c) =
            eichF H (u kk) (Fr.es kk) 0 (Fr.f c.castSucc) + eichF H (u kk) (Fr.es kk) 0 (u c) :=
          (eichL H (u kk) (Fr.es kk) 0).map_add _ _
        have hes : H.h (Fr.f c.castSucc) (Fr.es kk) = 0 := by rw [Fr.h_es, if_neg hne']
        rw [if_pos hck, if_pos (by omega), hadd, hfix]
        simp [eichF, hcx, hes]
      · rw [if_neg hck]
        by_cases hce : c = kk
        · subst hce
          have h1 : H.h (Fr.f kk.castSucc) (Fr.es kk) = 1 := by rw [Fr.h_es, if_pos rfl]
          have : kk.val < k + 1 := by simp [hkk]
          rw [if_pos this]
          simp [eichF, hcx, h1]
        · have : ¬ c.val < k + 1 := fun h => hce (Fin.ext (by simp [hkk]; omega))
          have hes : H.h (Fr.f c.castSucc) (Fr.es kk) = 0 := by rw [Fr.h_es, if_neg hce]
          rw [if_neg this]
          simp [eichF, hcx, hes]
    · rw [LinearEquiv.mul_apply, hnz, eichE_apply]
      exact eich_fix H _ _ _ _ (z_es Fr kk) (z_X Fr _ hx)

end Onto

section Final
variable {H} {r : ℕ} (Fr : FrameD H r)

lemma onto [CharZero F] (hT : Fr.T ≠ 0) (g : Fin (r + 1) → V) (hg : Tri E Fr.f g) :
    ∃ n ∈ NUg Fr, g = fun b => n (Fr.f b) := by
  have hm := mem_of_tri Fr.f g hg
  have hu : ∀ c : Fin r, g c.castSucc - Fr.f c.castSucc ∈ Fr.Fj c.val := fun c =>
    spanf_le Fr c.val c.isLt.le (by simpa using hm c.castSucc)
  obtain ⟨n0, hn0, hne, hnz⟩ := levi Fr (fun c => g c.castSucc - Fr.f c.castSucc) hu r le_rfl
  have hx0 : g (Fin.last r) - Fr.f (Fin.last r) ∈ H.X Fr.f := by
    rw [← Fj_r]; exact spanf_le Fr r le_rfl (by simpa using hm (Fin.last r))
  set x0 := g (Fin.last r) - Fr.f (Fin.last r) with hx0d
  set v0 : V := algebraMap F E (-Fr.T⁻¹) • Fr.f (Fin.last r) with hv0d
  have hvz : ∀ y ∈ H.X Fr.f, H.h y v0 = 0 := fun y hy => by
    rw [hv0d, h_smul_right, pairing_isotropicSpan_lastVector Fr y hy, mul_zero]
  have hxv : H.h x0 v0 = 0 := hvz x0 hx0
  have hc : 2 * algebraMap F E ((2 * Fr.T)⁻¹) + H.h v0 v0 = 0 := by
    have key : (2 : F) * (2 * Fr.T)⁻¹ + (-Fr.T⁻¹) * ((-Fr.T⁻¹) * -Fr.T) = 0 := by
      field_simp; ring
    have key' := congrArg (algebraMap F E) key
    simp only [map_add, map_mul, map_neg, map_ofNat, map_zero] at key'
    rw [hv0d, H.h_smul_left, h_smul_right, AlgEquiv.commutes, Fr.h_zz]
    simp only [map_neg]
    linear_combination key'
  have hE0 := eich_mem Fr hx0 hxv hc (fun a => by
    rw [hvz _ (Fj_le_X Fr _ (e_mem Fr a)), zero_smul]; exact Submodule.zero_mem _)
  refine ⟨_ * n0, mul_mem hE0 hn0, funext fun b => ?_⟩
  induction b using Fin.lastCases with
  | last =>
    rw [LinearEquiv.mul_apply, hnz, eichE_apply]
    have hzv : H.h (Fr.f (Fin.last r)) v0 = 1 := by
      rw [hv0d, h_smul_right, AlgEquiv.commutes, Fr.h_zz, ← map_neg, ← map_mul, neg_mul_neg,
        inv_mul_cancel₀ hT, map_one]
    have hz0 : H.h (Fr.f (Fin.last r)) x0 = 0 := z_X Fr _ hx0
    simp only [eichF, hzv, hz0, one_smul, zero_smul, mul_zero, sub_zero, add_zero]
    rw [hx0d]
    abel
  | cast c =>
    rw [LinearEquiv.mul_apply, hne c, if_pos c.isLt, add_sub_cancel, eichE_apply]
    have hgX : g c.castSucc ∈ H.X Fr.f := by
      have : g c.castSucc = Fr.f c.castSucc + (g c.castSucc - Fr.f c.castSucc) := by abel
      rw [this]
      exact add_mem (Fj_le_X Fr _ (e_mem Fr c)) (Fj_le_X Fr _ (hu c))
    exact (eich_fix H _ _ _ _ (hvz _ hgX) (X_iso Fr _ hgX _ hx0)).symm

end Final

end GlobalTheory.LocOver.UnipOnto

namespace GlobalTheory.LocOver.UnipOnto

theorem unipotent_onto : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ Fr : FrameD H r, Fr.T ≠ 0 →
    (∀ n, n ∈ Fr.N ↔ n ∈ NU H Fr.f) ∧ (∀ n ∈ Fr.N, Tri E Fr.f fun b => n (Fr.f b)) ∧
      ∀ g : Fin (r + 1) → V, Tri E Fr.f g → ∃ n ∈ Fr.N, g = fun b => n (Fr.f b) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r Fr hT
  haveI := hOK.char0
  refine ⟨fun n => by rw [N_eq]; exact Iff.rfl, fun n hn => ?_, fun g hg => ?_⟩
  · rw [N_eq] at hn
    exact tri_of_mem _ _ (NU_mem Fr hn)
  · obtain ⟨n, hn, h⟩ := onto Fr hT g hg
    exact ⟨n, by rw [N_eq]; exact hn, h⟩

end GlobalTheory.LocOver.UnipOnto
