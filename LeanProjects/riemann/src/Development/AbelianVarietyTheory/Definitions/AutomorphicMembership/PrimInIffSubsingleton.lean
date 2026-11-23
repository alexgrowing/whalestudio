import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MulVecMemLatMap

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Defs

def LieN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Y : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  cT σ Y * J + J * Y = 0 ∧ IsStrict A ∧ Y * P = P * A ∧ ∀ x ∈ perpX σ J P, Y *ᵥ x ∈ spanX P

def Relevant (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∀ Y A A', LieN σ J P Y A → LieN σ J P' Y A' →
    (simpleSum A - simpleSum A') + σ (simpleSum A - simpleSum A') = 0

def Unip {n r : ℕ} (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ a : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUp a ∧ P' = P * a

def SameFlag {n r : ℕ} (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ b : Matrix (Fin (r + 1)) (Fin (r + 1)) E, b.BlockTriangular id ∧ IsUnit b.det ∧ P' = P * b

def LiesAt {r : ℕ} (w : Formalism.MainNotions.S.Point E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ l u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsLo l ∧ IsUp u ∧ Z * eps E r = l * Formalism.MainNotions.S.ptMat w * u

def onePt (E : Type) [Field E] (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) := ⟨[(1, r + 1)], by simp, by simp⟩

open scoped Classical in

def ptOfMat {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Formalism.MainNotions.S.Point E (r + 1) :=
  if h : ∃ w, LiesAt w Z then h.choose else onePt E r

variable [NumberField E]

def IntFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IsFrame σ J T P ∧ PrimIn (frameLat P) Λ

def Cong {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  frameLat ((g : E)⁻¹ • (P' - P)) ≤ Λ

def admitted (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T' : E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IntFrame σ J T' Λ P' ∧ ∃ u ∈ UO E r, Cong g Λ (P * u) P'

def defLat {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Λ ⊓ (frameLat P ⊔ frameLat P').comap ((g : 𝓞 E) • LinearMap.id)

def satLat {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  latIn Λ (Submodule.span E (M : Set (Fin n → E)))

abbrev Defect {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Type :=
  satLat M Λ ⧸ M.submoduleOf (satLat M Λ)

def DefectAt (F : Type) [Field F] [Algebra F E] {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E))
    (p : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ x : Defect M Λ, ∀ a : 𝓞 F, a ∉ p.asIdeal → algebraMap (𝓞 F) (𝓞 E) a • x ≠ 0

def NO (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {s | InN σ J P s ∧ latMap s Λ = Λ}

def Move (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P A B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s ∈ NO σ J Λ P, ∃ u ∈ UO E r, B = s * A * u

def Transp (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin (r + 1)) E)
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s, InS σ J P s ∧ latMap s Λ = Λ' ∧ ∃ u ∈ UO E r, B = s * A * u

end Defs

section Field

variable {σ : E →+* E} {n r : ℕ} {J s Y : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v A Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem LieN.of_mul (hu : IsUp u) (h : LieN σ J (P * u) Y A) : LieN σ J P Y (u * A * u⁻¹) := by
  refine ⟨h.1, (strict_conj (up_inv hu) hu h.2.1).1, ?_, by simpa [perpX_mul hu, spanX_mul hu] using h.2.2.2⟩
  have := congrArg (· * u⁻¹) h.2.2.1
  simpa only [Matrix.mul_assoc, up_mul_inv hu, Matrix.mul_one] using this

theorem LieN.of_isom (hJ : IsUnit J.det) (hs : IsUn σ J s) (h : LieN σ J (s * P) Y A) :
    LieN σ J P (s⁻¹ * Y * s) A := by
  have hu := isUnit_det_of_isUn hJ hs
  have l := Matrix.nonsing_inv_mul s hu
  have e1 : J * s⁻¹ = cT σ s * J := by
    conv_lhs => rw [← hs, Matrix.mul_assoc, Matrix.mul_nonsing_inv s hu, Matrix.mul_one]
  have e2 : cT σ s⁻¹ * J = J * s := by
    conv_rhs => rw [← isUn_inv hJ hs, Matrix.mul_assoc, l, Matrix.mul_one]
  refine ⟨?_, h.2.1, ?_, fun x hx => ?_⟩
  · have := congrArg (fun W => cT σ s * W * s) h.1
    rw [cT_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, e2, ← Matrix.mul_assoc J, ← Matrix.mul_assoc J, e1]
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul] using this
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, h.2.2.1, Matrix.mul_assoc, ← Matrix.mul_assoc, l, Matrix.one_mul]
  · have := mulVec_mem_spanX (s := s⁻¹) (h.2.2.2 _ ((mulVec_mem_perpX hs P x).2 hx))
    rwa [← Matrix.mul_assoc, l, Matrix.one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this

theorem Relevant.mul (h : Relevant σ J P P') (hu : IsUp u) (hv : IsUp v) : Relevant σ J (P * u) (P' * v) := by
  intro Y A A' h1 h2
  have := h _ _ _ (h1.of_mul hu) (h2.of_mul hv)
  rwa [(strict_conj (up_inv hu) hu h1.2.1).2, (strict_conj (up_inv hv) hv h2.2.1).2] at this

theorem Relevant.isom (hJ : IsUnit J.det) (hs : IsUn σ J s) (h : Relevant σ J P P') :
    Relevant σ J (s * P) (s * P') := fun _ _ _ h1 h2 => h _ _ _ (h1.of_isom hJ hs) (h2.of_isom hJ hs)

theorem relevant_self (hP : Free P) : Relevant σ J P P := by
  intro Y A A' h1 h2
  obtain ⟨L, hL⟩ := hP
  have := congrArg (L * ·) (h1.2.2.1.symm.trans h2.2.2.1)
  simp only [← Matrix.mul_assoc, hL, Matrix.one_mul] at this
  simp [this]

theorem eps_mul_eps : eps E r * eps E r = 1 := by
  rw [eps, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext b
  rw [← mul_pow]; simp

theorem LiesAt.mul {w : Formalism.MainNotions.S.Point E (r + 1)} (h : LiesAt w Z) (hv : IsLo v) (hu : IsUp u) :
    LiesAt w (v * Z * u) := by
  obtain ⟨l, a, hl, ha, e⟩ := h
  refine ⟨v * l, a * (eps E r * u * eps E r), lo_mul hv hl, up_mul ha fun i j => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · simp [eps, (hu i j).1 h]
  · subst h; simp [eps, (hu i i).2 rfl, ← mul_pow]
  · calc v * Z * u * eps E r = v * (Z * eps E r) * (eps E r * u * eps E r) := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (eps E r) (eps E r), eps_mul_eps, Matrix.one_mul]
      _ = _ := by rw [e]; simp only [Matrix.mul_assoc]

theorem liesAt_ptOfMat (h : ∃ w, LiesAt w Z) : LiesAt (ptOfMat Z) Z := by
  rw [ptOfMat, dif_pos h]; exact h.choose_spec

theorem ptOfMat_congr {Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : ∀ w, LiesAt w Z ↔ LiesAt w Z') :
    ptOfMat Z = ptOfMat Z' := by
  have e : (fun w => LiesAt w Z) = fun w => LiesAt w Z' := funext fun w => propext (h w)
  have k (p q : Formalism.MainNotions.S.Point E (r + 1) → Prop) (e : p = q) [Decidable (∃ w, p w)] [Decidable (∃ w, q w)] :
      (if h : ∃ w, p w then h.choose else onePt E r) = if h : ∃ w, q w then h.choose else onePt E r := by
    subst e; congr
  exact @k _ _ e (Classical.propDecidable _) (Classical.propDecidable _)

theorem Gq_mul (T T' : E) (hv : IsLo v) (hu : IsUp u) : Gq σ T T' (v * Z * u) = Gq σ T T' Z := by
  simp only [Gq, Matrix.det_mul, lo_det hv, up_det hu, one_mul, mul_one, lead_mul_up _ hu, lead_lo_mul _ hv]

theorem map_Gq (hσ : ∀ x, σ (σ x) = x) {T T' : E} (hT : σ T = T) (hT' : σ T' = T') :
    σ (Gq σ T T' Z) = Gq σ T T' Z := by
  simp only [Gq, map_sub, map_mul, hσ, hT, hT']; ring

theorem Gq_TF {T : E} (hT : σ T = T) : Gq σ T T (TF r T) = 0 := by
  have h1 : (TF r T).det = 0 ^ r * -T := by
    simp [TF, Fin.prod_univ_castSucc, (Fin.castSucc_lt_last _).ne]
  have h2 : SgAlg.lead (TF r T) r (Nat.le_succ r) = 0 ^ r := by
    rw [SgAlg.lead, TF, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    refine (Finset.prod_congr rfl (g := fun _ => (0 : E)) fun i _ => ?_).trans (by simp)
    exact if_neg (Fin.castSucc_lt_last i).ne
  rw [Gq, h1, h2, map_mul, map_neg, hT]; ring

theorem Unip.norm_eq {T T' : E} (h : Unip P P') (hP : IsFrame σ J T P) (hP' : IsFrame σ J T' P') : T' = T := by
  obtain ⟨a, ha, rfl⟩ := h
  simpa [TF] using congrFun (congrFun (hP'.2.symm.trans (isFrame_mul hP ha).2) (Fin.last r)) (Fin.last r)

end Field

section Lattice

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' A B C : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ Λ' Λ'' M : Submodule (𝓞 E) (Fin n → E)} {T T' : E}

theorem mem_defLat (x : Fin n → E) :
    x ∈ defLat g Λ P P' ↔ x ∈ Λ ∧ (g : E) • x ∈ frameLat P ⊔ frameLat P' := by
  simp only [defLat, Submodule.mem_inf, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply,
    Nat.cast_smul_eq_nsmul]

theorem defLat_eq_pairLat (hg : g ≠ 0) (hP : PrimIn (frameLat P) Λ) (hu : u ∈ UO E r)
    (h : Cong g Λ (P * u) P') : defLat g Λ P P' = pairLat g (P * u) P' := by
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  rw [defLat, ← frameLat_mul (P := P) hu, ← defLat]
  rw [← frameLat_mul (P := P) hu] at hP
  generalize P * u = Q at *
  refine le_antisymm (fun x hx => ?_) (sup_le (fun x hx => ?_) fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := (mem_defLat x).1 hx
    obtain ⟨y, hy, y', hy', e⟩ := Submodule.mem_sup.1 h2
    obtain ⟨a, ha, rfl⟩ := (Iota.mem_frameLat _ _).1 hy
    obtain ⟨a', ha', rfl⟩ := (Iota.mem_frameLat _ _).1 hy'
    have k : ((g : E)⁻¹ • (P' - Q)) *ᵥ a' ∈ frameLat ((g : E)⁻¹ • (P' - Q)) :=
      (Iota.mem_frameLat _ _).2 ⟨a', ha', rfl⟩
    have e2 : x - ((g : E)⁻¹ • (P' - Q)) *ᵥ a' = Q *ᵥ ((g : E)⁻¹ • (a + a')) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.mulVec_add,
        ← inv_smul_smul₀ hg' x, ← e, ← smul_sub]
      congr 1; abel
    rw [← sub_add_cancel x (((g : E)⁻¹ • (P' - Q)) *ᵥ a')]
    exact add_mem (Submodule.mem_sup_left (hP.2 _ (sub_mem h1 (h k))
      ((Iota.mem_span_frameLat _ _).2 ⟨_, e2.symm⟩))) (Submodule.mem_sup_right k)
  · exact (mem_defLat x).2 ⟨hP.1 hx, Submodule.mem_sup_left (by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx g)⟩
  · refine (mem_defLat x).2 ⟨h hx, ?_⟩
    obtain ⟨a, ha, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
    rw [Matrix.smul_mulVec, smul_inv_smul₀ hg', Matrix.sub_mulVec]
    exact sub_mem (Submodule.mem_sup_right ((Iota.mem_frameLat _ _).2 ⟨a, ha, rfl⟩))
      (Submodule.mem_sup_left ((Iota.mem_frameLat _ _).2 ⟨a, ha, rfl⟩))

theorem defectAt_iff (F : Type) [Field F] [Algebra F E] (p : HeightOneSpectrum (𝓞 F)) :
    DefectAt F M Λ p ↔ ∃ x ∈ Λ, x ∈ Submodule.span E (M : Set (Fin n → E)) ∧
      ∀ a : 𝓞 F, a ∉ p.asIdeal → algebraMap (𝓞 F) (𝓞 E) a • x ∉ M := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨x, x.2.1, x.2.2, fun a ha h => hx a ha ((Submodule.Quotient.mk_eq_zero _).2 h)⟩
  · rintro ⟨x, h1, h2, h3⟩
    exact ⟨Submodule.Quotient.mk ⟨x, h1, h2⟩, fun a ha h => h3 a ha
      ((Submodule.Quotient.mk_eq_zero (M.submoduleOf (satLat M Λ))).1 h)⟩

theorem primIn_iff_subsingleton (h : M ≤ Λ) : PrimIn M Λ ↔ Subsingleton (Defect M Λ) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  exact ⟨fun k x _ => k.2 x x.2.1 x.2.2, fun k => ⟨h, fun x h1 h2 => k (x := ⟨x, h1, h2⟩) trivial⟩⟩

theorem primIn_iff_defectAt (F : Type) [Field F] [NumberField F] [Algebra F E] (h : M ≤ Λ) :
    PrimIn M Λ ↔ ∀ p, ¬ DefectAt F M Λ p := by
  simp only [defectAt_iff]
  refine ⟨fun k p ⟨x, h1, h2, h3⟩ => h3 1 ((Ideal.ne_top_iff_one _).1 p.isPrime.ne_top)
    (by simpa using k.2 x h1 h2), fun k => ⟨h, fun x h1 h2 => ?_⟩⟩
  by_contra hx
  let I : Ideal (𝓞 F) := (M.colon {x}).comap (algebraMap (𝓞 F) (𝓞 E))
  have hI (a : 𝓞 F) : a ∈ I ↔ algebraMap (𝓞 F) (𝓞 E) a • x ∈ M := by
    simp [I, Submodule.mem_colon_singleton]
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I fun e => hx (by simpa using (hI 1).1 (e ▸ trivial))
  exact k ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩
    ⟨x, h1, h2, fun a ha e => ha (hle ((hI a).2 e))⟩

theorem defectAt_latMap (F : Type) [Field F] [Algebra F E] (hs : IsUnit s.det) (p : HeightOneSpectrum (𝓞 F)) :
    DefectAt F (latMap s M) (latMap s Λ) p ↔ DefectAt F M Λ p := by
  have hsur := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hs)
  rw [defectAt_iff, defectAt_iff, hsur.exists]
  simp only [← Matrix.mulVec_smul, mulVec_mem_latMap hs, mulVec_mem_span hs]

theorem exists_UO (hP : Free P) (h : PrimIn (frameLat P) Λ) (h' : PrimIn (frameLat P) (latMap s Λ))
    (hs : InS σ J P s) : ∃ a ∈ UO E r, s * P = P * a := by
  obtain ⟨-, a, ha, e⟩ := inS_iff.1 hs
  refine ⟨a, mem_UO_of_le hP ha fun x hx => h'.2 x ?_ ?_, e⟩
  · rw [← e, frameLat_isom] at hx
    exact Submodule.map_mono h.1 hx
  · obtain ⟨c, -, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
    exact (Iota.mem_span_frameLat _ _).2 ⟨_, Matrix.mulVec_mulVec _ _ _⟩

theorem Unip.exists_UO (h : Unip P P') (hP : IntFrame σ J T Λ P) (hP' : frameLat P' ≤ Λ) :
    ∃ a ∈ UO E r, P' = P * a := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨a, mem_UO_of_le hP.1.1 ha fun x hx => hP.2.2 x (hP' hx) ?_, rfl⟩
  obtain ⟨c, -, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
  exact (Iota.mem_span_frameLat _ _).2 ⟨_, Matrix.mulVec_mulVec _ _ _⟩

theorem tower_admissible_self (h : IntFrame σ J T Λ P) : admitted σ J T g Λ P P :=
  ⟨h, 1, one_mem_UO, fun x hx => by
    obtain ⟨a, -, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
    simp⟩

theorem Transp.refl : Transp σ J P Λ A Λ A := ⟨1, inS_one, latMap_one _, 1, one_mem_UO, by simp⟩

theorem Transp.symm (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) : Transp σ J P Λ' B Λ A := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  have l := Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1)
  refine ⟨s⁻¹, inS_inv hJ hs, by rw [← latMap_mul, l, latMap_one], u⁻¹, UO_inv hu, ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, up_mul_inv hu.1, Matrix.mul_one, ← Matrix.mul_assoc, l, Matrix.one_mul]

theorem Transp.trans (h : Transp σ J P Λ A Λ' B) (k : Transp σ J P Λ' B Λ'' C) : Transp σ J P Λ A Λ'' C := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  obtain ⟨t, ht, rfl, v, hv, rfl⟩ := k
  exact ⟨t * s, inS_mul ht hs, latMap_mul _ _ _, u * v, UO_mul hu hv, by simp only [Matrix.mul_assoc]⟩

theorem move_equivalence (hJ : IsUnit J.det) : Equivalence (Move σ J Λ P) := by
  refine ⟨fun A => ⟨1, ⟨inN_one, latMap_one _⟩, 1, one_mem_UO, by simp⟩, ?_, ?_⟩
  · rintro A _ ⟨s, ⟨hs, e⟩, u, hu, rfl⟩
    have l := Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1)
    refine ⟨s⁻¹, ⟨inN_inv hJ hs, by conv_lhs => rw [← e, ← latMap_mul, l, latMap_one]⟩, u⁻¹, UO_inv hu, ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, up_mul_inv hu.1, Matrix.mul_one, ← Matrix.mul_assoc, l,
      Matrix.one_mul]
  · rintro A _ _ ⟨s, ⟨hs, e⟩, u, hu, rfl⟩ ⟨t, ⟨ht, f⟩, v, hv, rfl⟩
    exact ⟨t * s, ⟨inN_mul ht hs, by rw [latMap_mul, e, f]⟩, u * v, UO_mul hu hv, by
      simp only [Matrix.mul_assoc]⟩

theorem Move.transp (hP : IsFrame σ J T P) (h : Move σ J Λ P A B) : Transp σ J P Λ A Λ B := by
  obtain ⟨s, hs, u, hu, e⟩ := h
  exact ⟨s, inS_of_inN hP hs.1, hs.2, u, hu, e⟩

theorem Transp.pairM_eq (h : Transp σ J P Λ A Λ' B) :
    ∃ l u, IsLo l ∧ IsUp u ∧ pairM σ J B P = l * pairM σ J A P * u := by
  obtain ⟨s, hs, -, u, hu, rfl⟩ := h
  obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
  refine ⟨cT σ a⁻¹, u, lo_cT σ (up_inv ha), hu.1, ?_⟩
  rw [← pairM_isom (P' := A) h1, ← pairM_mul, e, Matrix.mul_assoc P, up_mul_inv ha, Matrix.mul_one]

theorem Transp.Gq_eq (h : Transp σ J P Λ A Λ' B) (T T' : E) :
    Gq σ T T' (pairM σ J B P) = Gq σ T T' (pairM σ J A P) := by
  obtain ⟨l, u, hl, hu, e⟩ := h.pairM_eq
  rw [e, Gq_mul T T' hl hu]

theorem Transp.lead_eq (h : Transp σ J P Λ A Λ' B) (l : ℕ) (hl : l ≤ r + 1) :
    SgAlg.lead (pairM σ J B P) l hl = SgAlg.lead (pairM σ J A P) l hl := by
  obtain ⟨a, u, ha, hu, e⟩ := h.pairM_eq
  rw [e, lead_mul_up _ hu, lead_lo_mul _ ha]

theorem Transp.liesAt_iff (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) (w : Formalism.MainNotions.S.Point E (r + 1)) :
    LiesAt w (pairM σ J B P) ↔ LiesAt w (pairM σ J A P) := by
  obtain ⟨a, u, ha, hu, e⟩ := h.pairM_eq
  obtain ⟨b, v, hb, hv, f⟩ := (h.symm hJ).pairM_eq
  exact ⟨fun k => f ▸ k.mul hb hv, fun k => e ▸ k.mul ha hu⟩

theorem Transp.relevant_iff (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) :
    Relevant σ J P B ↔ Relevant σ J P A := by
  have k {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {A B : Matrix (Fin n) (Fin (r + 1)) E}
      (h : Transp σ J P Λ A Λ' B) (hA : Relevant σ J P A) : Relevant σ J P B := by
    obtain ⟨s, hs, -, u, hu, rfl⟩ := h
    obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
    have := (hA.isom hJ h1).mul (up_inv ha) hu.1
    rwa [e, Matrix.mul_assoc P, up_mul_inv ha, Matrix.mul_one] at this
  exact ⟨k (h.symm hJ), k h⟩

theorem Transp.unip_iff (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) : Unip P B ↔ Unip P A := by
  have k {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {A B : Matrix (Fin n) (Fin (r + 1)) E}
      (h : Transp σ J P Λ A Λ' B) (hA : Unip P A) : Unip P B := by
    obtain ⟨s, hs, -, u, hu, rfl⟩ := h
    obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
    obtain ⟨b, hb, rfl⟩ := hA
    exact ⟨a * b * u, up_mul (up_mul ha hb) hu.1, by rw [← Matrix.mul_assoc s, e]; simp only [Matrix.mul_assoc]⟩
  exact ⟨k (h.symm hJ), k h⟩

theorem Transp.sameFlag_iff (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) : SameFlag P B ↔ SameFlag P A := by
  have k {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {A B : Matrix (Fin n) (Fin (r + 1)) E}
      (h : Transp σ J P Λ A Λ' B) (hA : SameFlag P A) : SameFlag P B := by
    obtain ⟨s, hs, -, u, hu, rfl⟩ := h
    obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
    obtain ⟨b, hb, hd, rfl⟩ := hA
    exact ⟨a * b * u, ((up_tri ha).mul hb).mul (up_tri hu.1), by simpa [up_det ha, up_det hu.1] using hd,
      by rw [← Matrix.mul_assoc s, e]; simp only [Matrix.mul_assoc]⟩
  exact ⟨k (h.symm hJ), k h⟩

theorem Transp.adm (hJ : IsUnit J.det) (hP : Free P) (h1 : PrimIn (frameLat P) Λ) (h2 : PrimIn (frameLat P) Λ')
    (h : Transp σ J P Λ A Λ' B) (hA : admitted σ J T' g Λ P A) : admitted σ J T' g Λ' P B := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  obtain ⟨a, ha, e⟩ := exists_UO hP h1 h2 hs
  obtain ⟨⟨k1, k2⟩, w, hw, k3⟩ := hA
  refine ⟨⟨isFrame_mul (isFrame_isom hJ k1 hs.1) hu.1, ?_⟩, a * w * u, UO_mul (UO_mul ha hw) hu, ?_⟩
  · rwa [frameLat_mul hu, frameLat_isom, primIn_latMap (isUnit_det_of_isUn hJ hs.1)]
  · have : (g : E)⁻¹ • (s * A * u - P * (a * w * u)) = s * ((g : E)⁻¹ • (A - P * w)) * u := by
      rw [← Matrix.mul_assoc P, ← Matrix.mul_assoc P, ← e]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [Cong, this, frameLat_mul hu, frameLat_isom]
    exact Submodule.map_mono k3

theorem Transp.defLat_eq (hJ : IsUnit J.det) (hP : Free P) (h1 : PrimIn (frameLat P) Λ)
    (h2 : PrimIn (frameLat P) Λ') (h : Transp σ J P Λ A Λ' B) :
    ∃ s, IsUnit s.det ∧ latMap s Λ = Λ' ∧ latMap s (defLat g Λ P A) = defLat g Λ' P B := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  obtain ⟨a, ha, e⟩ := exists_UO hP h1 h2 hs
  have hd := isUnit_det_of_isUn hJ hs.1
  have hsur := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hd)
  refine ⟨s, hd, rfl, Submodule.ext (hsur.forall.2 fun x => ?_)⟩
  have k : frameLat P ⊔ frameLat (s * A * u) = latMap s (frameLat P ⊔ frameLat A) := by
    rw [frameLat_mul hu, frameLat_isom, latMap, latMap, Submodule.map_sup, ← latMap, ← latMap,
      ← frameLat_isom (P := P), e, frameLat_mul ha]
  rw [mulVec_mem_latMap hd, mem_defLat, mem_defLat, k, ← Matrix.mulVec_smul, mulVec_mem_latMap hd,
    mulVec_mem_latMap hd]

end Lattice

end GlobalTheory.IntTerm
