import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreMain

noncomputable section

open FockH1Action PositivityTheory.KReal

namespace PositivityTheory.ThKG.CayleyTransformDarboux

section Gen

variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]

def Lie (act : A →ₗ[ℂ] Module.End ℂ M) : Prop := ∀ X Y, act X * act Y - act Y * act X = act (X * Y - Y * X)

def St (act : A →ₗ[ℂ] Module.End ℂ M) (g : Submodule ℂ A) (N : Submodule ℂ M) : Prop := ∀ Z ∈ g, ∀ x ∈ N, act Z x ∈ N

theorem Lie.comm {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) (X Y : A) (x : M) :
    act X (act Y x) = act Y (act X x) + act (X * Y - Y * X) x := by
  have := LinearMap.congr_fun (h X Y) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  rw [← this]; abel

def filt (act : A →ₗ[ℂ] Module.End ℂ M) (l : Submodule ℂ A) (V : Submodule ℂ M) : ℕ → Submodule ℂ M
  | 0 => V
  | n + 1 => filt act l V n ⊔ ⨆ Z ∈ l, (filt act l V n).map (act Z)

theorem gen_le {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {g q l : Submodule ℂ A}
    (hg : ∀ X ∈ g, ∀ Y ∈ g, X * Y - Y * X ∈ g) (hq : q ≤ g) (hl : l ≤ g) (hs : g ≤ q ⊔ l) {V N : Submodule ℂ M}
    (hV : St act q V) (hVN : V ≤ N) (hN : St act l N) : ∃ W, V ≤ W ∧ W ≤ N ∧ St act g W := by
  have up : ∀ n, ∀ Z ∈ l, ∀ x ∈ filt act l V n, act Z x ∈ filt act l V (n + 1) := fun n Z hZ x hx =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem Z (Submodule.mem_iSup_of_mem hZ (Submodule.mem_map_of_mem hx)))
  have mono : ∀ n, filt act l V n ≤ filt act l V (n + 1) := fun n => le_sup_left
  have Q : ∀ n, St act q (filt act l V n) → ∀ Z ∈ g, ∀ x ∈ filt act l V n, act Z x ∈ filt act l V (n + 1) := by
    intro n hn Z hZ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs hZ)
    rw [map_add, LinearMap.add_apply]
    exact add_mem (mono n (hn a ha x hx)) (up n b hb x hx)
  have P : ∀ n, St act q (filt act l V n) := by
    intro n
    induction n with
    | zero => exact hV
    | succ n ih =>
      intro Z hZ
      have : filt act l V (n + 1) ≤ (filt act l V (n + 1)).comap (act Z) := by
        refine sup_le (fun x hx => mono n (ih Z hZ x hx)) (iSup₂_le fun Y hY => ?_)
        rintro _ ⟨x, hx, rfl⟩
        rw [Submodule.mem_comap, h.comm]
        exact add_mem (up n Y hY _ (ih Z hZ x hx)) (Q n ih _ (hg Z (hq hZ) Y (hl hY)) x hx)
      exact fun x hx => this hx
  have le : ∀ n, filt act l V n ≤ N := by
    intro n
    induction n with
    | zero => exact hVN
    | succ n ih =>
      refine sup_le ih (iSup₂_le fun Y hY => ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hN Y hY x (ih hx)
  refine ⟨⨆ n, filt act l V n, le_iSup (filt act l V) 0, iSup_le le, fun Z hZ x hx => ?_⟩
  have : (⨆ n, filt act l V n) ≤ (⨆ n, filt act l V n).comap (act Z) :=
    iSup_le fun n y hy => Submodule.mem_iSup_of_mem (n + 1) (Q n (P n) Z hZ y hy)
  exact this hx

def low (T : Module.End ℂ M) (lam : ℂ) : Submodule ℂ M := ⨆ t : {t : ℝ // 0 < t}, T.eigenspace (lam - (t.1 : ℂ))

theorem shift_eig {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {H Z : A} {k : ℂ} (hk : H * Z - Z * H = k • Z) {mu : ℂ} {x : M}
    (hx : x ∈ (act H).eigenspace mu) : act Z x ∈ (act H).eigenspace (mu + k) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [h.comm, hx, hk, map_smul, map_smul, LinearMap.smul_apply, add_smul]

theorem shift_low {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {H Z : A} {k : ℝ} (h0 : 0 < k)
    (hk : H * Z - Z * H = (-(k : ℂ)) • Z) {lam : ℂ} {V : Submodule ℂ M} (hV : V ≤ (act H).eigenspace lam) :
    ∀ x ∈ V ⊔ low (act H) lam, act Z x ∈ V ⊔ low (act H) lam := by
  have : V ⊔ low (act H) lam ≤ (V ⊔ low (act H) lam).comap (act Z) := by
    refine sup_le (fun x hx => ?_) (iSup_le fun t x hx => ?_)
    · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨k, h0⟩ ?_)
      have := shift_eig h hk (hV hx)
      rwa [← sub_eq_add_neg] at this
    · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨t.1 + k, add_pos t.2 h0⟩ ?_)
      have := shift_eig h hk hx
      convert this using 2
      push_cast; ring
  exact fun x hx => this hx

theorem low_ker {M' : Type} [AddCommGroup M'] [Module ℂ M'] {T : Module.End ℂ M} {lam : ℂ} (D : M →ₗ[ℂ] M')
    (hD : ∀ x, D (T x) = lam • D x) : low T lam ≤ LinearMap.ker D := by
  refine iSup_le fun t x hx => ?_
  rw [Module.End.mem_eigenspace_iff] at hx
  have := hD x
  rw [hx, map_smul, sub_smul, sub_eq_self, smul_eq_zero] at this
  exact this.resolve_left (by exact_mod_cast t.2.ne')

theorem low_eig {T : Module.End ℂ M} {lam : ℂ} {x : M} (h1 : x ∈ low T lam) (h2 : x ∈ T.eigenspace lam) : x = 0 := by
  have hd := (Module.End.eigenspaces_iSupIndep T) lam
  refine (Submodule.disjoint_def.1 hd) x h2 ?_
  refine (iSup_le fun t => ?_ : low T lam ≤ _) h1
  refine le_iSup₂_of_le (f := fun j (_ : j ≠ lam) => T.eigenspace j) (lam - (t.1 : ℂ)) ?_ le_rfl
  intro e
  rw [sub_eq_self] at e
  exact t.2.ne' (by exact_mod_cast e)

theorem low_map {M' : Type} [AddCommGroup M'] [Module ℂ M'] {T : Module.End ℂ M} {T' : Module.End ℂ M'} {lam : ℂ}
    (φ : M →ₗ[ℂ] M') (hφ : ∀ x, φ (T x) = T' (φ x)) {x : M} (hx : x ∈ low T lam) : φ x ∈ low T' lam := by
  refine (iSup_le fun t y hy => ?_ : low T lam ≤ (low T' lam).comap φ) hx
  refine Submodule.mem_iSup_of_mem t ?_
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [← hφ, hy, map_smul]

end Gen

section Units

variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]

def un (w : ι) (a b : I) : ι → Matrix I I ℂ := Pi.single w (Matrix.single a b 1)

def alg (ι : Type) (r : I → I → Prop) : Submodule ℂ (ι → Matrix I I ℂ) where
  carrier := {Z | ∀ w a b, ¬ r a b → Z w a b = 0}
  add_mem' := fun {x y} hx hy w a b h => by simp [hx w a b h, hy w a b h]
  zero_mem' := fun _ _ _ _ => rfl
  smul_mem' := fun c x hx w a b h => by simp [hx w a b h]

theorem eq_sum (Z : ι → Matrix I I ℂ) : Z = ∑ w, ∑ a, ∑ b, Z w a b • un w a b := by
  ext w a b
  simp only [un, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b] <;>
    simp +contextual [Pi.single_apply, Matrix.single_apply, eq_comm]

theorem alg_le {r : I → I → Prop} {S : Submodule ℂ (ι → Matrix I I ℂ)} (h : ∀ w a b, r a b → un w a b ∈ S) : alg ι r ≤ S := by
  intro Z hZ
  rw [eq_sum Z]
  refine S.sum_mem fun w _ => S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
  by_cases e : r a b
  · exact S.smul_mem _ (h w a b e)
  · rw [hZ w a b e, zero_smul]; exact S.zero_mem

theorem un_mem {r : I → I → Prop} (w : ι) {a b : I} (h : r a b) : un w a b ∈ alg ι r := by
  intro w' c d hcd
  by_cases e : w' = w
  · subst e
    simp only [un, Pi.single_eq_same, Matrix.single_apply]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd h
  · simp [un, Pi.single_eq_of_ne e]

theorem alg_br {r : I → I → Prop} (ht : ∀ a b c, r a b → r b c → r a c) :
    ∀ X ∈ alg ι r, ∀ Y ∈ alg ι r, X * Y - Y * X ∈ alg ι r := by
  have m : ∀ X ∈ alg ι r, ∀ Y ∈ alg ι r, X * Y ∈ alg ι r := fun X hX Y hY w a b h => by
    rw [Pi.mul_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases e : r a c
    · rw [hY w c b fun e' => h (ht _ _ _ e e'), mul_zero]
    · rw [hX w a c e, zero_mul]
  exact fun X hX Y hY => sub_mem (m X hX Y hY) (m Y hY X hX)

theorem alg_mono {r r' : I → I → Prop} (h : ∀ a b, r a b → r' a b) : alg ι r ≤ alg ι r' :=
  alg_le fun w a b e => un_mem w (h a b e)

theorem alg_sup {r r₁ r₂ : I → I → Prop} (h : ∀ a b, r a b → r₁ a b ∨ r₂ a b) : alg ι r ≤ alg ι r₁ ⊔ alg ι r₂ :=
  alg_le fun w a b e => (h a b e).elim (fun e => Submodule.mem_sup_left (un_mem w e)) fun e =>
    Submodule.mem_sup_right (un_mem w e)

def stab (act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M) (N : Submodule ℂ M) : Submodule ℂ (ι → Matrix I I ℂ) where
  carrier := {Z | ∀ x ∈ N, act Z x ∈ N}
  add_mem' := fun {a b} ha hb x hx => by rw [map_add, LinearMap.add_apply]; exact add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c a ha x hx => by rw [map_smul, LinearMap.smul_apply]; exact N.smul_mem c (ha x hx)

theorem st_alg {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} {r : I → I → Prop} {N : Submodule ℂ M}
    (h : ∀ w a b, r a b → ∀ x ∈ N, act (un w a b) x ∈ N) : St act (alg ι r) N :=
  fun _ hZ => (alg_le (S := stab act N) h) hZ

def dg (ι : Type) (h : I → ℝ) : ι → Matrix I I ℂ := fun _ => Matrix.diagonal fun a => (h a : ℂ)

theorem dg_br (h : I → ℝ) (w : ι) (a b : I) : dg ι h * un w a b - un w a b * dg ι h = ((h a - h b : ℝ) : ℂ) • un w a b := by
  ext w' c d
  by_cases e : w' = w
  · subst e
    simp only [un, dg, Pi.sub_apply, Pi.mul_apply, Pi.single_eq_same, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Pi.smul_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs with h1
    · obtain ⟨rfl, rfl⟩ := h1; push_cast; ring
    · simp
  · simp [un, Pi.single_eq_of_ne e]

theorem dg_eq (h : I → ℝ) : dg ι h = ∑ w, ∑ a, (h a : ℂ) • un w a a := by
  conv_lhs => rw [eq_sum (dg ι h)]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a] <;> simp +contextual [dg, Matrix.diagonal_apply, eq_comm]

theorem dg_hw {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} (h : I → ℝ) {Λ : ι → I → ℂ} {f : M}
    (hf : ∀ w a, act (un w a a) f = Λ w a • f) : f ∈ (act (dg ι h)).eigenspace (∑ w, ∑ a, h a * Λ w a) := by
  rw [Module.End.mem_eigenspace_iff, dg_eq]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hf, Finset.sum_smul, smul_smul]

theorem cyc_le {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} (hL : Lie act) {sb pos z : I → I → Prop}
    (sbt : ∀ a b c, sb a b → sb b c → sb a c) (sbr : ∀ a, sb a a) (psb : ∀ a b, pos a b → sb a b) (h : I → ℝ)
    (hp : ∀ a b, pos a b → h b ≤ h a) (hz : ∀ a b, z a b → sb a b ∧ h a = h b)
    (hc : ∀ a b, sb a b → h b ≤ h a → (a = b ∨ pos a b) ∨ z a b) {Λ : ι → I → ℂ} {f : M}
    (hf : ∀ w a, act (un w a a) f = Λ w a • f) (hf' : ∀ w a b, pos a b → act (un w a b) f = 0) {N : Submodule ℂ M}
    (hfN : f ∈ N) (hN : ∀ w a b, z a b → ∀ x ∈ N, act (un w a b) x ∈ N) :
    ∃ W, f ∈ W ∧ W ≤ N ⊔ low (act (dg ι h)) (∑ w, ∑ a, h a * Λ w a) ∧ St act (alg ι sb) W := by
  set lam : ℂ := ∑ w, ∑ a, h a * Λ w a
  obtain ⟨V, hV1, hV2, hV3⟩ := gen_le hL (g := alg ι fun a b => sb a b ∧ h b ≤ h a) (q := alg ι fun a b => a = b ∨ pos a b)
    (l := alg ι z) (alg_br fun a b c x y => ⟨sbt _ _ _ x.1 y.1, y.2.trans x.2⟩)
    (alg_mono fun a b e => e.elim (fun e => e ▸ ⟨sbr a, le_rfl⟩) fun e => ⟨psb _ _ e, hp _ _ e⟩)
    (alg_mono fun a b e => ⟨(hz _ _ e).1, (hz _ _ e).2.ge⟩) (alg_sup fun a b e => hc a b e.1 e.2)
    (V := Submodule.span ℂ {f}) (N := N ⊓ (act (dg ι h)).eigenspace lam)
    (st_alg fun w a b e x hx => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      rcases e with rfl | e
      · rw [hf]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)
      · rw [hf' w a b e]; exact zero_mem _)
    ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨hfN, dg_hw h hf⟩)
    (st_alg fun w a b e x hx => ⟨hN w a b e x hx.1, by
      have := shift_eig hL (dg_br h w a b) hx.2
      rwa [(hz _ _ e).2, sub_self, Complex.ofReal_zero, add_zero] at this⟩)
  obtain ⟨W, hW1, hW2, hW3⟩ := gen_le hL (g := alg ι sb) (q := alg ι fun a b => sb a b ∧ h b ≤ h a)
    (l := alg ι fun a b => sb a b ∧ h a < h b) (alg_br sbt) (alg_mono fun a b e => e.1) (alg_mono fun a b e => e.1)
    (alg_sup fun a b e => (le_or_gt (h b) (h a)).imp (fun x => ⟨e, x⟩) fun x => ⟨e, x⟩) hV3
    (N := V ⊔ low (act (dg ι h)) lam) le_sup_left
    (st_alg fun w a b e => shift_low hL (k := h b - h a) (sub_pos.2 e.2)
      (by rw [dg_br]; congr 1; push_cast; ring) (hV2.trans inf_le_right))
  exact ⟨W, hW1 (hV1 (Submodule.mem_span_singleton_self f)), hW2.trans (sup_le_sup_right (hV2.trans inf_le_left) _), hW3⟩

end Units

end PositivityTheory.ThKG.CayleyTransformDarboux

end
