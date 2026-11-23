import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.PolynomialThetaProduct

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def Aa {K : Type} [Field K] {m : ℕ} (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  if vec then g else (g⁻¹).transpose

theorem Aa_inv_mul {K : Type} [Field K] {m : ℕ} (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hg : IsUnit g.det) : Aa vec g⁻¹ * Aa vec g = 1 := by
  cases vec
  · rw [Aa, Aa, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_nonsing_inv g hg, Matrix.nonsing_inv_mul g hg, Matrix.transpose_one]
  · rw [Aa, Aa, if_pos rfl, if_pos rfl]
    exact Matrix.nonsing_inv_mul g hg

theorem Aa_mul_inv {K : Type} [Field K] {m : ℕ} (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hg : IsUnit g.det) : Aa vec g * Aa vec g⁻¹ = 1 := by
  cases vec
  · rw [Aa, Aa, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_nonsing_inv g hg, Matrix.mul_nonsing_inv g hg, Matrix.transpose_one]
  · rw [Aa, Aa, if_pos rfl, if_pos rfl]
    exact Matrix.mul_nonsing_inv g hg

theorem fl_rowAct_one (R : Type) [CommRing R] {k n : ℕ} (F : MvPolynomial (Fin k × Fin n) R) :
    rowAct R (1 : Matrix (Fin k) (Fin k) R) F = F := by
  have : rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro c
    simp [rowAct, Matrix.one_apply]
  exact congrArg (fun f => f F) this

theorem last_ne_zero {m : ℕ} (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_zero] at this
  omega

theorem twist_theta (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (d : ℕ) (vec : Bool)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (Q : MvPolynomial (Fin (m + 1)) K)
    (hQ : Q ∈ Hd K (m + 1) d) :
    g.det ^ (letterWt m d vec (Fin.last m)) • rowAct K g (theta K m vec Q) = theta K m vec (lin (Aa vec g) Q) := by
  rw [rowAct_theta]
  cases vec
  · have h1 : letterWt m d false (Fin.last m) = -(d : ℤ) := by simp [letterWt]
    have h2 : act false g = g.det • (g⁻¹).transpose := by
      simp only [act, Bool.false_eq_true, if_false]
      rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.transpose_smul, smul_smul, mul_inv_cancel₀ hg.ne_zero,
        one_smul]
    rw [h1, h2, lin_smul _ _ _ hQ, map_smul, smul_smul, zpow_neg, zpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]
    rfl
  · have h1 : letterWt m d true (Fin.last m) = 0 := by simp [letterWt, last_ne_zero hm]
    rw [h1, zpow_zero, one_smul]
    rfl

theorem mem_nablaLTw_letter (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ) (hm : 1 ≤ m)
    (d : ℕ) (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (x : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    x ∈ nablaLTw O Kf m (letterWt m d vec) g ↔
      ∃ P ∈ Hd O (m + 1) d, x = theta Kf m vec (lin (Aa vec g⁻¹) (map (algebraMap O Kf) P)) := by
  have hgi : IsUnit (g⁻¹).det := by rw [Matrix.det_nonsing_inv]; exact hg.ringInverse
  have hν : (fun t => (letterWt m d vec t - letterWt m d vec (Fin.last m)).toNat) = nuL m d vec :=
    nuOf_letterWt m hm d vec
  rw [nablaLTwMem O Kf m _ g hg, hν, ← theta_Hd O m hm d vec]
  set e : ℤ := letterWt m d vec (Fin.last m) with he
  constructor
  · rintro ⟨_, ⟨P, hP, rfl⟩, hx⟩
    refine ⟨P, hP, ?_⟩
    have hx' : map (algebraMap O Kf) (theta O m vec P) = g.det ^ e • rowAct Kf g x := hx
    rw [map_theta] at hx'
    rw [← twist_theta Kf m hm d vec g⁻¹ hgi _ (map_Hd _ P hP), hx', map_smul, smul_smul, ← he]
    have h1 : rowAct Kf g⁻¹ (rowAct Kf g x) = x := by
      have := congrArg (fun f => f x) (rowActMul Kf (m + 1) (m + 1) g⁻¹ g)
      simp only [AlgHom.comp_apply] at this
      rw [this, Matrix.mul_nonsing_inv g hg, fl_rowAct_one]
    rw [h1, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ hg.ne_zero),
      one_smul]
  · rintro ⟨P, hP, rfl⟩
    refine ⟨theta O m vec P, ⟨P, hP, rfl⟩, ?_⟩
    show map (algebraMap O Kf) (theta O m vec P) = _
    rw [he, twist_theta Kf m hm d vec g hg _ (lin_Hd _ _ (map_Hd _ P hP)), lin_comp, Aa_inv_mul vec g hg, lin_one,
      map_theta]

section Multi

variable {S : Type} [Fintype S] [DecidableEq S]

theorem map_embS {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {k : ℕ} (s : S)
    (P : MvPolynomial (Fin k) R) : map f (embS R s P) = embS R' s (map f P) := by
  simp only [embS, MvPolynomial.map_rename]

theorem fl_map_smul {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {σ : Type} (a : R) (F : MvPolynomial σ R) :
    map (algebraMap R K) (a • F) = a • map (algebraMap R K) F := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, algebraMap_smul]

theorem tens_iff (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (m : ℕ) (vec : S → Bool) (d : S → ℕ)
    (N : S → Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (M : S → Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))
    (hM : ∀ s x, x ∈ M s ↔ ∃ P ∈ Hd R (m + 1) (d s),
      x = theta K m (vec s) (lin (N s) (map (algebraMap R K) P)))
    (x : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) K) :
    x ∈ tensorLat R K M ↔
      ∃ F ∈ Pol R (m + 1) d, x = Th0 K m vec (Lin N (map (algebraMap R K) F)) := by
  constructor
  · intro hx
    unfold tensorLat at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨F, hF, rfl⟩ := hx
      have h1 := fun s => (hM s (F s)).1 (hF s)
      choose P hP1 hP2 using h1
      refine ⟨∏ s, embS R s (P s), prod_emb_Pol d P hP1, ?_⟩
      rw [map_prod, map_prod, map_prod]
      apply Finset.prod_congr rfl
      intro s _
      rw [map_embS, Lin_emb, Th0_emb, ← hP2 s]
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨F, hF, rfl⟩ := hx
      obtain ⟨G, hG, rfl⟩ := hy
      exact ⟨F + G, Submodule.add_mem _ hF hG, by simp only [map_add]⟩
    | smul a x _ hx =>
      obtain ⟨F, hF, rfl⟩ := hx
      refine ⟨a • F, Submodule.smul_mem _ _ hF, ?_⟩
      rw [fl_map_smul, ← algebraMap_smul K a (map (algebraMap R K) F), map_smul, map_smul, algebraMap_smul]
  · rintro ⟨F, hF, rfl⟩
    unfold Formalism.MainNotions.G.Pol at hF
    rw [restrictSupport_eq_span] at hF
    induction hF using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨μ, hμ, rfl⟩ := hy
      beta_reduce
      rw [mono_factor, map_prod, map_prod, map_prod]
      apply Submodule.subset_span
      refine ⟨fun s => theta K m (vec s) (lin (N s) (map (algebraMap R K) (monomial (partS μ s) 1))),
        fun s => (hM s _).2 ⟨_, partS_Hd R d μ hμ s, rfl⟩, ?_⟩
      apply Finset.prod_congr rfl
      intro s _
      rw [map_embS, Lin_emb, Th0_emb]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [fl_map_smul, ← algebraMap_smul K a (map (algebraMap R K) x), map_smul, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx

theorem mem_tens_nabla (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ) (hm : 1 ≤ m)
    (vec : S → Bool) (d : S → ℕ) (g : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : ∀ s, IsUnit (g s).det)
    (x : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) :
    x ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (letterWt m (d s) (vec s)) (g s)) ↔
      ∃ F ∈ Pol O (m + 1) d, x = Th0 Kf m vec (Lin (fun s => Aa (vec s) (g s)⁻¹) (map (algebraMap O Kf) F)) :=
  tens_iff O Kf m vec d _ _ (fun s x => mem_nablaLTw_letter O Kf m hm (d s) (vec s) (g s) (hg s) x) x

theorem mem_tens_dw (Kf : Type) [Field Kf] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (x : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) :
    x ∈ tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (d s) (vec s)))) ↔
      ∃ F ∈ Pol Kf (m + 1) d, x = Th0 Kf m vec F := by
  have h := tens_iff Kf Kf m vec d (fun _ => 1)
    (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (d s) (vec s))))
    (fun s x => by
      rw [nuOf_letterWt m hm, ← theta_Hd Kf m hm]
      constructor
      · rintro ⟨P, hP, rfl⟩
        refine ⟨P, hP, ?_⟩
        rw [lin_one, Algebra.algebraMap_self, MvPolynomial.map_id]
        rfl
      · rintro ⟨P, hP, rfl⟩
        refine ⟨P, hP, ?_⟩
        rw [lin_one, Algebra.algebraMap_self, MvPolynomial.map_id]
        rfl) x
  rw [h]
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨F, hF, ?_⟩
    rw [Lin_one, Algebra.algebraMap_self, MvPolynomial.map_id]
  · rintro ⟨F, hF, rfl⟩
    refine ⟨F, hF, ?_⟩
    rw [Lin_one, Algebra.algebraMap_self, MvPolynomial.map_id]

theorem map_Pol {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {k : ℕ} {d : S → ℕ}
    (P : MvPolynomial (S × Fin k) R) (hP : P ∈ Pol R k d) : map f P ∈ Pol R' k d := by
  rw [mem_Pol] at hP ⊢
  intro μ hμ
  exact hP μ (MvPolynomial.support_map_subset f P hμ)

theorem key_iff (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ) (hm : 1 ≤ m)
    (vec : S → Bool) (d : S → ℕ) (h M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (hM : ∀ s, IsUnit (M s).det) (c : Kf) (F : MvPolynomial (S × Fin (m + 1)) Kf) (hF : F ∈ Pol Kf (m + 1) d) :
    (∃ y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (letterWt m (d s) (vec s)) (M s)),
      Th0 Kf m vec (Lin (fun s => Aa (vec s) (h s)⁻¹) F) = c • y) ↔
    ∃ G ∈ Pol O (m + 1) d, Lin (fun s => Aa (vec s) (h s)⁻¹ * Aa (vec s) (M s)) F =
      c • map (algebraMap O Kf) G := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨G, hG, rfl⟩ := (mem_tens_nabla O Kf m hm vec d M hM y).1 hy
    refine ⟨G, hG, ?_⟩
    rw [← map_smul, ← map_smul] at hxy
    have h1 := Th0_inj Kf m hm vec d _ _ (Lin_Pol _ _ hF)
      (Lin_Pol _ _ (Submodule.smul_mem _ c (map_Pol _ G hG))) hxy
    have h2 := congrArg (Lin (fun s => Aa (vec s) (M s))) h1
    rw [Lin_comp, Lin_comp] at h2
    rw [h2]
    simp only [Aa_inv_mul _ _ (hM _)]
    rw [Lin_one]
  · rintro ⟨G, hG, hFG⟩
    refine ⟨_, (mem_tens_nabla O Kf m hm vec d M hM _).2 ⟨G, hG, rfl⟩, ?_⟩
    have this : (fun s => Aa (vec s) (h s)⁻¹ * Aa (vec s) (M s) * Aa (vec s) (M s)⁻¹) =
        fun s => Aa (vec s) (h s)⁻¹ := by
      funext s
      rw [Matrix.mul_assoc, Aa_mul_inv _ _ (hM s), Matrix.mul_one]
    rw [← map_smul, ← map_smul, ← hFG, Lin_comp, this]

end Multi

end Formalism.L2.G.Model
