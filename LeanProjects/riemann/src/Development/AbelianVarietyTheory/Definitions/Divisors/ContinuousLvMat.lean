import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEisModel

open GlobalTheory.SphEis
open Formalism.UG (cT_mul cT_one)

section Ring

variable {A : Type} [CommRing A] {s : A →+* A} {n j m : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {C D C' D' : Matrix (Fin n) (Fin j) A} {Z Z' : Matrix (Fin n) (Fin m) A} {J₀ Ji : Matrix (Fin m) (Fin m) A}

theorem cT_add {p q : Type} (X Y : Matrix p q A) : cT s (X + Y) = cT s X + cT s Y := by ext; simp [cT]
theorem cT_sub {p q : Type} (X Y : Matrix p q A) : cT s (X - Y) = cT s X - cT s Y := by ext; simp [cT]
theorem cT_cT (h : ∀ x, s (s x) = x) {p q : Type} (X : Matrix p q A) : cT s (cT s X) = X := by ext; simp [cT, h]

variable (s J) in

def Gram (C D : Matrix (Fin n) (Fin j) A) (Z : Matrix (Fin n) (Fin m) A) (J₀ : Matrix (Fin m) (Fin m) A) : Prop :=
  cT s C * (J * C) = 0 ∧ cT s C * (J * Z) = 0 ∧ cT s C * (J * D) = 1 ∧
  cT s Z * (J * C) = 0 ∧ cT s Z * (J * Z) = J₀ ∧ cT s Z * (J * D) = 0 ∧
  cT s D * (J * C) = 1 ∧ cT s D * (J * Z) = 0 ∧ cT s D * (J * D) = 0

variable (s J C D Z Ji) in

def carry (C' D' : Matrix (Fin n) (Fin j) A) (Z' : Matrix (Fin n) (Fin m) A) : Matrix (Fin n) (Fin n) A :=
  C' * (cT s D * J) + Z' * (Ji * (cT s Z * J)) + D' * (cT s C * J)

theorem carry_frame (g : Gram s J C D Z J₀) (hi : Ji * J₀ = 1) :
    carry s J C D Z Ji C' D' Z' * C = C' ∧ carry s J C D Z Ji C' D' Z' * Z = Z' ∧ carry s J C D Z Ji C' D' Z' * D = D' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := g
  simp [carry, Matrix.add_mul, Matrix.mul_assoc, *]

theorem rext (hs : carry s J C D Z Ji C D Z = 1) {p : ℕ} {X Y : Matrix (Fin p) (Fin n) A} (h1 : X * C = Y * C)
    (h2 : X * Z = Y * Z) (h3 : X * D = Y * D) : X = Y := by
  rw [← Matrix.mul_one X, ← Matrix.mul_one Y, ← hs]
  simp only [carry, Matrix.mul_add, ← Matrix.mul_assoc, h1, h2, h3]

theorem lext (hs : carry s J C D Z Ji C D Z = 1) {p : ℕ} {X Y : Matrix (Fin n) (Fin p) A} (h1 : cT s C * X = cT s C * Y)
    (h2 : cT s Z * X = cT s Z * Y) (h3 : cT s D * X = cT s D * Y) : X = Y := by
  rw [← Matrix.one_mul X, ← Matrix.one_mul Y, ← cT_one s, ← hs]
  simp only [carry, cT_add, cT_mul s C, cT_mul s Z, cT_mul s D, Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]

theorem unitary (g : Gram s J C D Z J₀) (g' : Gram s J C' D' Z' J₀) (hs : carry s J C D Z Ji C D Z = 1)
    {M : Matrix (Fin n) (Fin n) A} (e1 : M * C = C') (e2 : M * Z = Z') (e3 : M * D = D') : cT s M * J * M = J := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := g
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := g'
  have a : ∀ {p q : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A),
      cT s U * (cT s M * J * M * V) = cT s (M * U) * (J * (M * V)) := fun U V => by
    simp only [cT_mul, Matrix.mul_assoc]
  refine rext hs (lext hs ?_ ?_ ?_) (lext hs ?_ ?_ ?_) (lext hs ?_ ?_ ?_) <;> rw [a] <;> simp only [*]

theorem gram_of_unitary (g : Gram s J C D Z J₀) {M : Matrix (Fin n) (Fin n) A} (hM : cT s M * J * M = J) :
    Gram s J (M * C) (M * D) (M * Z) J₀ := by
  have a : ∀ {p q : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A),
      cT s (M * U) * (J * (M * V)) = cT s U * (J * V) := fun U V => by
    conv_rhs => rw [← hM]
    simp only [cT_mul, Matrix.mul_assoc]
  simpa only [Gram, a] using g

theorem gram_levi (hs : ∀ x, s (s x) = x) (g : Gram s J C D Z J₀) (α : GL (Fin j) A) :
    Gram s J (C * α.1) (D * cT s (α⁻¹).1) Z J₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := g
  have a : ∀ {p q p' q' : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A) (x : Matrix (Fin p) (Fin p') A)
      (y : Matrix (Fin q) (Fin q') A), cT s (U * x) * (J * (V * y)) = cT s x * (cT s U * (J * V)) * y := fun U V x y => by
    simp only [cT_mul, Matrix.mul_assoc]
  have b : ∀ {p q q' : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A)
      (y : Matrix (Fin q) (Fin q') A), cT s U * (J * (V * y)) = (cT s U * (J * V)) * y := fun U V y => by
    simp only [Matrix.mul_assoc]
  have c : ∀ {p q p' : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A) (x : Matrix (Fin p) (Fin p') A),
      cT s (U * x) * (J * V) = cT s x * (cT s U * (J * V)) := fun U V x => by
    simp only [cT_mul, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, h5, ?_, ?_, ?_, ?_⟩
  · rw [a, h1]; simp
  · rw [c, h2]; simp
  · rw [a, h3, Matrix.mul_one, ← cT_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, cT_one]
  · rw [b, h4]; simp
  · rw [b, h6]; simp
  · rw [a, h7, Matrix.mul_one, cT_cT hs, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rw [c, h8]; simp
  · rw [a, h9]; simp

theorem gram_unip_iff (hs : ∀ x, s (s x) = x) (g : Gram s J C D Z J₀) (h₀ : cT s Ji * J₀ = 1) (hi : J₀ * Ji = 1)
    (b : Matrix (Fin j) (Fin m) A) (c : Matrix (Fin j) (Fin j) A) :
    Gram s J C (D - Z * (Ji * cT s b) + C * c) (Z + C * b) J₀ ↔ c + cT s c + b * (Ji * cT s b) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := g
  have b' : ∀ {p q q' : ℕ} (U : Matrix (Fin n) (Fin p) A) (V : Matrix (Fin n) (Fin q) A)
      (y : Matrix (Fin q) (Fin q') A), cT s U * (J * (V * y)) = (cT s U * (J * V)) * y := fun U V y => by
    simp only [Matrix.mul_assoc]
  have i1 : ∀ x : Matrix (Fin m) (Fin j) A, J₀ * (Ji * x) = x := fun x => by rw [← Matrix.mul_assoc, hi, Matrix.one_mul]
  have i2 : ∀ x : Matrix (Fin m) (Fin j) A, cT s Ji * (J₀ * x) = x := fun x => by
    rw [← Matrix.mul_assoc, h₀, Matrix.one_mul]
  have i3 : cT s Ji = Ji := by
    rw [← Matrix.mul_one (cT s Ji), ← hi, ← Matrix.mul_assoc, h₀, Matrix.one_mul]
  have i4 : Ji * J₀ = 1 := by rw [← h₀, i3]
  simp only [Gram, cT_add, cT_sub, cT_mul, cT_cT hs, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, b', h1, h2, h3, h4, h5, h6, h7, h8, h9, i1, i2, i3, i4, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add, sub_zero, zero_sub, true_and, neg_add_cancel, neg_neg, sub_neg_eq_add, sub_self]
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [← h]; abel

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n j m : ℕ} {J : Matrix (Fin n) (Fin n) E} {C D : Matrix (Fin n) (Fin j) E}
  {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

omit [NumberField E] in
theorem ad_cT {p q : Type} (X : Matrix p q E) : adMat F (cT (σ : E →+* E) X) = cT (sigR (AF F) σ) (adMat F X) := by
  ext a b; simp [cT, sigR, inclR]

theorem sig_sig (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : sigR (AF F) σ (sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, sigma_sigma h]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem gram_rat (f : Fr σ J C D Z J₀) : Gram (σ : E →+* E) J C D Z J₀ := by
  simp only [Gram, ← Matrix.mul_assoc]
  exact ⟨f.cc, f.cz, f.cd, f.zc, f.zz, f.zd, f.dc, f.dz, f.dd⟩

theorem gram_ad (f : Fr σ J C D Z J₀) :
    Gram (sigR (AF F) σ) (JR (AF F) J) (adMat F C) (adMat F D) (adMat F Z) (adMat F J₀) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := gram_rat f
  simp only [Gram, JR, ← ad_cT, ← Matrix.map_mul, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp

omit [NumberField E] in
theorem ad_carry (Ji : Matrix (Fin m) (Fin m) E) (C' D' : Matrix (Fin n) (Fin j) E) (Z' : Matrix (Fin n) (Fin m) E) :
    adMat F (carry (σ : E →+* E) J C D Z Ji C' D' Z') = carry (sigR (AF F) σ) (JR (AF F) J) (adMat F C) (adMat F D) (adMat F Z)
      (adMat F Ji) (adMat F C') (adMat F D') (adMat F Z') := by
  simp only [carry, JR, ← ad_cT, ← Matrix.map_mul]
  ext; simp only [Matrix.map_apply, Matrix.add_apply, map_add]

theorem sum_ad (f : Fr σ J C D Z J₀) : carry (sigR (AF F) σ) (JR (AF F) J) (adMat F C) (adMat F D) (adMat F Z)
      (adMat F J₀⁻¹) (adMat F C) (adMat F D) (adMat F Z) = 1 := by
  rw [← ad_carry, show carry (σ : E →+* E) J C D Z J₀⁻¹ C D Z = 1 from f.sum]
  simp

theorem inv_mul₀ (f : Fr σ J C D Z J₀) : J₀⁻¹ * J₀ = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit f.herm₀.2)
theorem mul_inv₀ (f : Fr σ J C D Z J₀) : J₀ * J₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit f.herm₀.2)
theorem inv_mul_ad (f : Fr σ J C D Z J₀) : adMat F J₀⁻¹ * adMat F J₀ = 1 := by rw [← Matrix.map_mul, inv_mul₀ f]; simp
theorem mul_inv_ad (f : Fr σ J C D Z J₀) : adMat F J₀ * adMat F J₀⁻¹ = 1 := by rw [← Matrix.map_mul, mul_inv₀ f]; simp
theorem cT_inv_ad (f : Fr σ J C D Z J₀) : cT (sigR (AF F) σ) (adMat F J₀⁻¹) * adMat F J₀ = 1 := by
  have : cT (σ : E →+* E) J₀ = J₀ := by ext a b; exact f.herm₀.1 a b
  conv_lhs => rw [← this, ad_cT (σ := σ) J₀, this]
  rw [← cT_mul, mul_inv_ad f, cT_one]

def lvMat (f : Fr σ J C D Z J₀) : GL (Fin j) (AF F ⊗[F] E) →* Matrix (Fin n) (Fin n) (AF F ⊗[F] E) where
  toFun α := carry (sigR (AF F) σ) (JR (AF F) J) (adMat F C) (adMat F D) (adMat F Z) (adMat F J₀⁻¹)
    (adMat F C * α.1) (adMat F D * cT (sigR (AF F) σ) (α⁻¹).1) (adMat F Z)
  map_one' := by simpa [cT_one] using sum_ad f
  map_mul' α β := by
    have h := fun C' D' Z' => carry_frame (C' := C') (D' := D') (Z' := Z') (gram_ad f) (inv_mul_ad f)
    refine rext (sum_ad f) ?_ ?_ ?_
    · rw [Matrix.mul_assoc, (h _ _ _).1, (h _ _ _).1, ← Matrix.mul_assoc, (h _ _ _).1, Units.val_mul, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, (h _ _ _).2.1, (h _ _ _).2.1, (h _ _ _).2.1]
    · rw [Matrix.mul_assoc, (h _ _ _).2.2, (h _ _ _).2.2, ← Matrix.mul_assoc, (h _ _ _).2.2, _root_.mul_inv_rev, Units.val_mul,
        cT_mul, Matrix.mul_assoc]

theorem lvMat_frame (f : Fr σ J C D Z J₀) (α : GL (Fin j) (AF F ⊗[F] E)) :
    lvMat f α * adMat F C = adMat F C * α.1 ∧ lvMat f α * adMat F Z = adMat F Z ∧
      lvMat f α * adMat F D = adMat F D * cT (sigR (AF F) σ) (α⁻¹).1 := carry_frame (gram_ad f) (inv_mul_ad f)

theorem continuous_lvMat (f : Fr σ J C D Z J₀) : Continuous (lvMat f) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (sigR (AF F) σ) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F)
      (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ).toLinearMap
  have h1 : Continuous fun α : GL (Fin j) (AF F ⊗[F] E) => cT (sigR (AF F) σ) (α⁻¹).1 :=
    (Units.continuous_coe_inv.matrix_map hs).matrix_transpose
  exact (((continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const).add continuous_const).add
    ((continuous_const.matrix_mul h1).matrix_mul continuous_const)

def lv (f : Fr σ J C D Z J₀) : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J :=
  (lvMat f).toHomUnits.codRestrict (HR (AF F) σ J) fun α =>
    unitary (gram_ad f) (gram_levi (sig_sig f.cm) (gram_ad f) α) (sum_ad f) (lvMat_frame f α).1 (lvMat_frame f α).2.1
      (lvMat_frame f α).2.2

theorem isLv_lv (f : Fr σ J C D Z J₀) : IsLv σ J C D Z (lv f) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine ⟨?_, fun α => (lvMat_frame f α).1, fun α => (lvMat_frame f α).2.2, fun α => (lvMat_frame f α).2.1, fun δ => ?_⟩
  · refine (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨continuous_lvMat f, ?_⟩)
    exact (continuous_lvMat f).comp continuous_inv
  · have h := fun C' D' Z' => carry_frame (C' := C') (D' := D') (Z' := Z') (gram_rat f) (inv_mul₀ f)
    set M := carry (σ : E →+* E) J C D Z J₀⁻¹ (C * δ.1) (D * cT (σ : E →+* E) (δ⁻¹).1) Z with hM
    have hu : cT (σ : E →+* E) M * J * M = J :=
      unitary (gram_rat f) (gram_levi (sigma_sigma f.cm) (gram_rat f) δ) f.sum (h _ _ _).1 (h _ _ _).2.1 (h _ _ _).2.2
    have hd : M.det ≠ 0 := fun e => f.herm.2 (by rw [← hu, Matrix.det_mul, e, mul_zero])
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hd, hu, Units.ext ?_⟩
    change adMat F M = carry _ _ _ _ _ _ (adMat F C * adMat F δ.1) (adMat F D * cT _ (adMat F (δ⁻¹).1)) _
    rw [hM, ad_carry, ← ad_cT, ← Matrix.map_mul, ← Matrix.map_mul]

theorem isLv_unique (f : Fr σ J C D Z J₀) {l l' : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J} (h : IsLv σ J C D Z l)
    (h' : IsLv σ J C D Z l') : l = l' := by
  ext α
  exact matHom_injective _ σ J (Units.ext (rext (sum_ad f) ((h.onC α).trans (h'.onC α).symm) ((h.onZ α).trans (h'.onZ α).symm)
    ((h.onD α).trans (h'.onD α).symm)))

theorem isLv_injective (f : Fr σ J C D Z J₀) {l : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J} (h : IsLv σ J C D Z l) :
    Function.Injective l := fun α β e => by
  have h7 := (gram_ad f).2.2.2.2.2.2.1
  have := congrArg (fun X : Matrix (Fin n) (Fin j) (AF F ⊗[F] E) => cT (sigR (AF F) σ) (adMat F D) * (JR (F := F) (AF F) J * X))
    ((h.onC α).symm.trans (e ▸ h.onC β))
  simp only [← Matrix.mul_assoc] at this h7
  rw [h7, Matrix.one_mul, Matrix.one_mul] at this
  exact Units.ext this

theorem exists_crd_iff (f : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E))
    (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :
    (∃ u, Crd σ J C D Z J₀ u b c) ↔ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  rw [plus, ← gram_unip_iff (sig_sig f.cm) (gram_ad f) (cT_inv_ad f) (mul_inv_ad f)]
  constructor
  · rintro ⟨u, h⟩
    have := gram_of_unitary (gram_ad f) (M := (matHom _ σ J u).1) u.2
    rwa [h.onC, h.onZ, h.onD] at this
  · intro g
    obtain ⟨e1, e2, e3⟩ := carry_frame (C' := adMat F C) (D' := adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c)
      (Z' := adMat F Z + adMat F C * b) (gram_ad f) (inv_mul_ad f)
    have hu := unitary (gram_ad f) g (sum_ad f) e1 e2 e3
    have hJ : IsUnit (JR (F := F) (AF F) J).det := by
      rw [JR, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (Ne.isUnit f.herm.2).map _
    rw [← hu, Matrix.det_mul] at hJ
    obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hJ)
    rw [← hU] at hu e1 e2 e3
    exact ⟨⟨U, hu⟩, e1, e2, e3⟩

theorem crd_unique (f : Fr σ J C D Z J₀) {u u' : GAd σ J} {b b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)}
    {c c' : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} (h : Crd σ J C D Z J₀ u b c) (h' : Crd σ J C D Z J₀ u' b' c') :
    u = u' ↔ b = b' ∧ c = c' := by
  constructor
  · rintro rfl
    have h7 := (gram_ad f).2.2.2.2.2.2.1
    have k : ∀ {p : ℕ} {x y : Matrix (Fin j) (Fin p) (AF F ⊗[F] E)}, adMat F C * x = adMat F C * y → x = y := fun {p x y} e => by
      have := congrArg (fun X : Matrix (Fin n) (Fin p) (AF F ⊗[F] E) =>
        cT (sigR (AF F) σ) (adMat F D) * (JR (F := F) (AF F) J * X)) e
      simp only [← Matrix.mul_assoc] at this h7
      rwa [h7, Matrix.one_mul, Matrix.one_mul] at this
    obtain rfl : b = b' := k (add_left_cancel (h.onZ.symm.trans h'.onZ))
    exact ⟨rfl, k (add_left_cancel (h.onD.symm.trans h'.onD))⟩
  · rintro ⟨rfl, rfl⟩
    exact matHom_injective _ σ J (Units.ext (rext (sum_ad f) (h.onC.trans h'.onC.symm) (h.onZ.trans h'.onZ.symm)
      (h.onD.trans h'.onD.symm)))

theorem bse_eq (h : IsCMExt F E σ) : (GlobalTheory.Doubling.absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) = (bse F)⁻¹ := by
  rw [GlobalTheory.Eis.Conv.absE_halfE F E σ h]; simp

theorem fr_three (h : IsCMExt F E σ) : Fr σ !![0, 0, 1; 0, 1, 0; 1, 0, 0] (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) E) !![0; 0; 1]
    (!![0; 1; 0] : Matrix (Fin 3) (Fin 1) E) 1 := by
  refine ⟨h, ⟨fun i j => ?_, by simp [Matrix.det_fin_three]⟩, ⟨fun i j => ?_, by simp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · fin_cases i <;> fin_cases j <;> simp
  · fin_cases i; fin_cases j; simp
  all_goals
    ext i j; fin_cases i <;> fin_cases j <;> simp [cT, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 3) (Fin 3) E) (C D Z : Matrix (Fin 3) (Fin 1) E) (J₀ : Matrix (Fin 1) (Fin 1) E)
    (l : GL (Fin 1) (AF F ⊗[F] E) →* GAd σ J) (u : GAd σ J) (c : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)),
    Fr σ J C D Z J₀ ∧ IsLv σ J C D Z l ∧ Function.Injective l ∧ Crd σ J C D Z J₀ u 1 c ∧ u ∈ fixG σ J C := by
  obtain ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, hc, -⟩ := GlobalTheory.EisLineModel.data_inhabited
  have f := fr_three hc
  obtain ⟨u, hu⟩ := (exists_crd_iff f 1 (adMat F ((-2⁻¹ : E) • 1))).2 (by
    have e : (-2⁻¹ : E) • (1 : Matrix (Fin 1) (Fin 1) E) + cT (σ : E →+* E) ((-2⁻¹ : E) • (1 : Matrix (Fin 1) (Fin 1) E)) + 1 = 0 := by
      ext i j; fin_cases i; fin_cases j; simp [cT, map_ofNat]; norm_num
    have := congrArg (adMat F) e
    rw [plus, cT_one, inv_one, ← ad_cT]
    simpa [Matrix.map_add] using this)
  exact ⟨F, E, _, _, _, _, _, σ, _, _, _, _, _, lv f, u, _, f, isLv_lv f, isLv_injective f (isLv_lv f), hu, hu.onC⟩

end GlobalTheory.SphEisModel

end
