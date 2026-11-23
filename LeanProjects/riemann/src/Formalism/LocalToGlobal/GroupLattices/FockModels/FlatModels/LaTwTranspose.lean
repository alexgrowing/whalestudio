import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.MemNablaLTwLetter
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.MatQTwDet
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.EdgeLatOfG

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det)

section Gen

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
  {S : Type} [Fintype S] [DecidableEq S]

def VS (Kf : Type) [Field Kf] (m : ℕ) (vec : S → Bool) (d : S → ℕ) :
    Submodule Kf (MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat Kf Kf fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (d s) (vec s)))

def thF (h : HidaSetting p n' W Qq O Kf ι σ j w) (m : ℕ) (vec : S → Bool)
    (hs : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (F : MvPolynomial (S × Fin (m + 1)) (KK O)) :
    MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf :=
  Th0 Kf m vec (Lin (fun x => Aa (vec x) (hs x)⁻¹) (map (kapR h) F))

theorem map_kap_smul (h : HidaSetting p n' W Qq O Kf ι σ j w) {τ : Type} (a : O) (F : MvPolynomial τ (KK O)) :
    map (kapR h) (a • F) = a • map (kapR h) F := by
  ext m
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_smul]
  exact map_smul (kap h) a (F.coeff m)

theorem thF_smul (h : HidaSetting p n' W Qq O Kf ι σ j w) (m : ℕ) (vec : S → Bool)
    (hs : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (a : O) (F : MvPolynomial (S × Fin (m + 1)) (KK O)) :
    thF h m vec hs (a • F) = a • thF h m vec hs F := by
  unfold thF
  rw [map_kap_smul, ← algebraMap_smul Kf a (map (kapR h) F), map_smul, map_smul, algebraMap_smul]

theorem gen_equiv (h : HidaSetting p n' W Qq O Kf ι σ j w) (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (hs : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hhs : ∀ x, IsUnit (hs x).det) :
    ∃ Θ : ↥((Pol (KK O) (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(VS Kf m vec d),
      ∀ F, ((Θ F : ↥(VS Kf m vec d)) : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF h m vec hs (F : MvPolynomial (S × Fin (m + 1)) (KK O)) := by
  let f : ↥((Pol (KK O) (m + 1) d).restrictScalars O) →ₗ[O] ↥(VS Kf m vec d) :=
    { toFun := fun F => ⟨thF h m vec hs F.1,
        (mem_tens_dw Kf m hm vec d _).2 ⟨_, Lin_Pol _ _ ((pol_iff h _ _ _).1 F.2), rfl⟩⟩
      map_add' := by
        intro F G
        apply Subtype.ext
        show thF h m vec hs (F.1 + G.1) = thF h m vec hs F.1 + thF h m vec hs G.1
        simp only [thF, map_add]
      map_smul' := by
        intro a F
        apply Subtype.ext
        exact thF_smul h m vec hs a F.1 }
  have hinj : Function.Injective f := by
    intro F G hFG
    have h1 : thF h m vec hs F.1 = thF h m vec hs G.1 := congrArg Subtype.val hFG
    have h2 := Th0_inj Kf m hm vec d _ _ (Lin_Pol _ _ ((pol_iff h _ _ _).1 F.2))
      (Lin_Pol _ _ ((pol_iff h _ _ _).1 G.2)) h1
    have h3 := congrArg (Lin (fun x => Aa (vec x) (hs x))) h2
    rw [Lin_comp, Lin_comp] at h3
    simp only [Aa_inv_mul _ _ (hhs _)] at h3
    rw [Lin_one, Lin_one] at h3
    exact Subtype.ext (map_injective _ (kapR_inj h) h3)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨F1, hF1, rfl⟩ := (mem_tens_dw Kf m hm vec d y).1 hy
    set F2 := Lin (fun x => Aa (vec x) (hs x)) F1 with hF2
    have hcomp : (kapR h).comp (((kap h).symm : Kf ≃ₐ[O] KK O) : Kf →+* KK O) = RingHom.id Kf := by
      ext x
      simp [kapR]
    have hmap : map (kapR h) (map (((kap h).symm : Kf ≃ₐ[O] KK O) : Kf →+* KK O) F2) = F2 := by
      rw [map_map, hcomp, MvPolynomial.map_id]
    refine ⟨⟨map (((kap h).symm : Kf ≃ₐ[O] KK O) : Kf →+* KK O) F2, ?_⟩, ?_⟩
    · show _ ∈ Pol (KK O) (m + 1) d
      rw [pol_iff h, hmap]
      exact Lin_Pol _ _ hF1
    · apply Subtype.ext
      show thF h m vec hs _ = _
      unfold thF
      rw [hmap, hF2, Lin_comp]
      simp only [Aa_mul_inv _ _ (hhs _)]
      rw [Lin_one]
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun F => rfl⟩

theorem pol_of_map (h : HidaSetting p n' W Qq O Kf ι σ j w) {k : ℕ} {d : S → ℕ} (P : MvPolynomial (S × Fin k) O)
    (hP : map (algebraMap O Kf) P ∈ Pol Kf k d) : P ∈ Pol O k d := by
  haveI := h.frac_O
  unfold Pol at hP ⊢
  rw [MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  rwa [MvPolynomial.support_map_of_injective _ (IsFractionRing.injective O Kf)] at hP

theorem gen_A (h : HidaSetting p n' W Qq O Kf ι σ j w) (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (hs : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hhs : ∀ x, IsUnit (hs x).det)
    (F : MvPolynomial (S × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) d) :
    InA (O := O) F ↔
      thF h m vec hs F ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (letterWt m (d s) (vec s)) (hs s)) := by
  have hF' := (pol_iff h _ _ _).1 hF
  have key := key_iff O Kf m hm vec d hs hs hhs 1 _ hF'
  simp only [Aa_inv_mul _ _ (hhs _), one_smul] at key
  rw [Lin_one] at key
  rw [inA_iff h]
  constructor
  · rintro ⟨P0, hP0⟩
    obtain ⟨y, hy, hxy⟩ := key.2 ⟨P0, pol_of_map h P0 (hP0 ▸ hF'), hP0⟩
    unfold thF
    rw [hxy]
    exact hy
  · intro hx
    obtain ⟨G, -, hG⟩ := key.1 ⟨_, hx, rfl⟩
    exact ⟨G, hG⟩

def Avec (vec : S → Bool) (d : S → ℕ) : ℕ := ∑ x, if vec x then d x else 0

variable [Fact p.Prime]

def Mx (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) (r : ℕ) {m : ℕ} (pos : S → Fin n')
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (x : S) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) Kf :=
  la_tw ι σ (pos x).val (hmat * ((matQ φ g)⁻¹).transpose) * lb_D (m + 1) r (algebraMap O Kf w)

theorem la_tw_mul {k : ℕ} (s : ℕ) (A B : Matrix (Fin k) (Fin k) Qq) :
    la_tw ι σ s (A * B) = la_tw ι σ s A * la_tw ι σ s B := by
  unfold la_tw
  exact map_mul _ A B

theorem la_tw_transpose {k : ℕ} (s : ℕ) (A : Matrix (Fin k) (Fin k) Qq) :
    la_tw ι σ s A.transpose = (la_tw ι σ s A).transpose := rfl

theorem la_tw_inv {k : ℕ} (s : ℕ) (A : Matrix (Fin k) (Fin k) Qq) (hA : IsUnit A.det) :
    la_tw ι σ s A⁻¹ = (la_tw ι σ s A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← la_tw_mul, Matrix.mul_nonsing_inv _ hA]
  unfold la_tw
  exact map_one _

theorem lb_D_inv {K : Type} [Field K] (k r : ℕ) (c : K) (hc : c ≠ 0) :
    (lb_D k r c)⁻¹ = Matrix.diagonal fun a : Fin k => if a.val < r then c else 1 := by
  unfold lb_D
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp [hc]

theorem Bm_eq (hw : algebraMap O Kf w ≠ 0) (φ : WF p n' ≃+* W) (r : ℕ) {m : ℕ} (vec : S → Bool) (pos : S → Fin n')
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g) (x : S) :
    Bm ι σ w φ r vec pos g x = (if vec x then algebraMap O Kf w else 1) •
      (Aa (vec x) (la_tw ι σ (pos x).val hmat)⁻¹ * Aa (vec x) (Mx ι σ w φ r pos hmat g x)) := by
  have hf : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq, (la_tw ι σ (pos x).val M).det =
      (ι.comp ((σ ^ (pos x).val : Qq ≃+* Qq) : Qq →+* Qq)) M.det := fun M => by
    unfold la_tw
    exact (RingHom.map_det _ M).symm
  have hA := la_tw_det ι σ (pos x).val hmat hh
  have hQ := matQ_tw_det (ι := ι) (σ := σ) φ g hg (pos x).val
  have hQq : IsUnit (matQ (Qq := Qq) φ g).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [hf, h0, map_zero] at hQ
    exact not_isUnit_zero hQ
  have hMx : Mx ι σ w φ r pos hmat g x = la_tw ι σ (pos x).val hmat *
      ((la_tw ι σ (pos x).val (matQ φ g))⁻¹).transpose * lb_D (m + 1) r (algebraMap O Kf w) := by
    unfold Mx
    rw [la_tw_mul, la_tw_transpose, la_tw_inv _ _ hQq]
  have key1 : ∀ A Q D : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit A.det → IsUnit Q.det →
      ((A⁻¹)⁻¹).transpose * ((A * (Q⁻¹).transpose * D)⁻¹).transpose = Q * (D⁻¹).transpose := by
    intro A Q D hA hQ
    rw [Matrix.nonsing_inv_nonsing_inv _ hA, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv,
      Matrix.nonsing_inv_nonsing_inv _ (by rwa [Matrix.det_transpose]), Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← mul_assoc, ← mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.transpose_one, one_mul]
  have key2 : ∀ A Q D : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit A.det →
      A⁻¹ * (A * (Q⁻¹).transpose * D) = (Q⁻¹).transpose * D := by
    intro A Q D hA
    rw [← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ hA, one_mul]
  have hDinv := lb_D_inv (m + 1) r (algebraMap O Kf w) hw
  rw [hMx]
  ext c b
  cases hv : vec x
  · simp only [Bm, hv, Aa, Bool.false_eq_true, ↓reduceIte, one_smul]
    rw [key1 _ _ _ hA hQ, hDinv, Matrix.diagonal_transpose, Matrix.mul_diagonal, mul_comm]
  · simp only [Bm, hv, Aa, ↓reduceIte]
    rw [key2 _ _ _ hA, Matrix.smul_apply, smul_eq_mul]
    unfold lb_D
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    by_cases hb : b.val < r
    · have hb' : ¬ r ≤ b.val := by omega
      simp only [hb, hb', ↓reduceIte]
      rw [mul_comm (algebraMap O Kf w), mul_assoc, inv_mul_cancel₀ hw, mul_one, one_mul]
    · have hb' : r ≤ b.val := by omega
      simp only [hb, hb', ↓reduceIte, mul_one]

theorem Mx_det (hw : algebraMap O Kf w ≠ 0) (φ : WF p n' ≃+* W) (r : ℕ) {m : ℕ} (pos : S → Fin n')
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g) (x : S) :
    IsUnit (Mx ι σ w φ r pos hmat g x).det := by
  have hf : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq, (la_tw ι σ (pos x).val M).det =
      (ι.comp ((σ ^ (pos x).val : Qq ≃+* Qq) : Qq →+* Qq)) M.det := fun M => by
    unfold la_tw
    exact (RingHom.map_det _ M).symm
  have hQ := matQ_tw_det (ι := ι) (σ := σ) φ g hg (pos x).val
  unfold Mx
  rw [Matrix.det_mul, isUnit_iff_ne_zero, mul_ne_zero_iff]
  refine ⟨?_, (lb_D_det _ _ _ hw).ne_zero⟩
  rw [hf, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, map_mul]
  refine mul_ne_zero ?_ ?_
  · rw [← hf]
    exact (la_tw_det ι σ _ hmat hh).ne_zero
  · rw [Ring.inverse_eq_inv, map_inv₀]
    apply inv_ne_zero
    rw [← hf]
    exact hQ.ne_zero

theorem gen_R (h : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ) (hm : 1 ≤ m)
    (r : ℕ) (LL : LiftLetters S) (pos : S → Fin n') (hpos : ∀ x, LL.pos x = ((pos x).val : ℤ)) (d : S → ℕ)
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial (S × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) d) (i : ℕ) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    InWjRg p n' O w r LL g F i ↔
      ∃ y ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (letterWt m (d s) (LL.vec s)) (Mx ι σ w φ r pos hmat g s)),
        thF h m LL.vec (fun x => la_tw ι σ (pos x).val hmat) F =
          (algebraMap O Kf w ^ ((i : ℤ) - (Avec LL.vec d : ℤ))) • y := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne h
  set c := algebraMap O Kf w with hc
  have hF' := (pol_iff h _ _ _).1 hF
  have key := key_iff O Kf m hm LL.vec d (fun x => la_tw ι σ (pos x).val hmat) (Mx ι σ w φ r pos hmat g)
    (Mx_det hw φ r pos hmat hh g hg) (c ^ ((i : ℤ) - (Avec LL.vec d : ℤ))) _ hF'
  unfold thF
  rw [key]
  unfold InWjRg
  rw [inWj_iff h, lift_eq h φ hφ r LL pos hpos g hg]
  have hB : Bm ι σ w φ r LL.vec pos g = fun x => (if LL.vec x then c else 1) •
      (Aa (LL.vec x) (la_tw ι σ (pos x).val hmat)⁻¹ * Aa (LL.vec x) (Mx ι σ w φ r pos hmat g x)) :=
    funext fun x => Bm_eq hw φ r LL.vec pos hmat hh g hg x
  rw [hB, Lin_smul _ _ _ hF']
  have hprod : ∏ x, (if LL.vec x then c else 1) ^ d x = c ^ Avec LL.vec d := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    split_ifs <;> simp
  rw [hprod]
  set Z := Lin (fun x => Aa (LL.vec x) (la_tw ι σ (pos x).val hmat)⁻¹ *
    Aa (LL.vec x) (Mx ι σ w φ r pos hmat g x)) (map (kapR h) F) with hZ
  have hZP : Z ∈ Pol Kf (m + 1) d := Lin_Pol _ _ hF'
  have hc0 : c ^ ((i : ℤ) - (Avec LL.vec d : ℤ)) ≠ 0 := zpow_ne_zero _ hw
  constructor
  · rintro ⟨P0, hP0⟩
    have h1 : Z = c ^ ((i : ℤ) - (Avec LL.vec d : ℤ)) • map (algebraMap O Kf) P0 := by
      have h2 := congrArg (fun t => (c ^ Avec LL.vec d)⁻¹ • t) hP0
      simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hw), one_smul] at h2
      rw [h2, zpow_sub₀ hw, zpow_natCast, zpow_natCast]
      congr 1
      field_simp
      rfl
    refine ⟨P0, pol_of_map h P0 ?_, h1⟩
    have h3 : map (algebraMap O Kf) P0 = (c ^ ((i : ℤ) - (Avec LL.vec d : ℤ)))⁻¹ • Z := by
      rw [h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ hZP
  · rintro ⟨G, -, hG⟩
    refine ⟨G, ?_⟩
    rw [hG, smul_smul, zpow_sub₀ hw, zpow_natCast, zpow_natCast]
    congr 1
    field_simp
    rfl

end Gen

end Formalism.L2.G.Model
