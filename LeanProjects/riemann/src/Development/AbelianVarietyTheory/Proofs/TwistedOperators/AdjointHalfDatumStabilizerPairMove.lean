import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjDatumMove

section Mat
variable {κ : Type} [CommRing κ] {n r : ℕ}

theorem topL_eq (hr : r ≤ n) (u : Matrix (Fin n) (Fin r) κ) : topL r u = u.submatrix (Fin.castLE hr) id := by
  ext i j
  simp only [topL, Matrix.submatrix_apply, id]
  rw [dif_pos ⟨lt_of_lt_of_le i.2 hr, j.2⟩]
  rfl

theorem lowZero_mul {G : GL (Fin n) κ} (hG : G ∈ blockTri (blk2 r)) (K : Matrix (Fin r) (Fin r) κ)
    {u : Matrix (Fin n) (Fin r) κ} (hu : LowZero r u) : LowZero r (G.val * u * K) := by
  intro i j hi _
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_eq_zero fun m _ => ?_, zero_mul]
  by_cases hm : r ≤ m.val
  · rw [hu m l hm l.2, mul_zero]
  · have hlt : blk2 r m < blk2 r i := by
      simp only [blk2, if_pos (not_le.mp hm), if_neg (not_lt.mpr hi)]
      exact Nat.zero_lt_one
    rw [(mem_blockTri.mp hG) i m hlt, zero_mul]

theorem lowZero_mul_iff {G : GL (Fin n) κ} (hG : G ∈ blockTri (blk2 r)) (K : GL (Fin r) κ)
    (u : Matrix (Fin n) (Fin r) κ) : LowZero r (G.val * u * K.val) ↔ LowZero r u := by
  constructor
  · intro h
    have h' := lowZero_mul ((blockTri (blk2 r)).inv_mem hG) (K⁻¹).val h
    have e : (G⁻¹).val * (G.val * u * K.val) * (K⁻¹).val = u := by
      simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rwa [e] at h'
  · exact lowZero_mul hG K.val

theorem topL_mul (hr : r ≤ n) {G : GL (Fin n) κ} (hG : G ∈ blockTri (blk2 r)) (K : Matrix (Fin r) (Fin r) κ)
    {u : Matrix (Fin n) (Fin r) κ} (hu : LowZero r u) :
    topL r (G.val * u * K) = (upperLeftBlock hr G).val * topL r u * K := by
  have key : ∀ (i : Fin r) (l : Fin r), ∑ m : Fin n, G.val (Fin.castLE hr i) m * u m l =
      ∑ m : Fin r, G.val (Fin.castLE hr i) (Fin.castLE hr m) * u (Fin.castLE hr m) l := by
    intro i l
    have hm := Finset.sum_map Finset.univ (Fin.castLEEmb hr) (fun m => G.val (Fin.castLE hr i) m * u m l)
    simp only [Fin.castLEEmb_apply] at hm
    rw [← hm]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro m _ hm
    have hrm : r ≤ m.val := by
      by_contra hc
      exact hm (Finset.mem_map.mpr ⟨⟨m.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [hu m l hrm l.2, mul_zero]
  rw [topL_eq hr, topL_eq hr, upper_block_val_submatrix hr hG]
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [key i l]

theorem restrictedBlock_self_apply (H : GL (Fin r) κ) : upperLeftBlock le_rfl H = H := by
  have hH : H ∈ blockTri (blk2 r) := mem_blockTri.mpr fun i j hij => by
    simp only [blk2, if_pos i.2, if_pos j.2] at hij
    exact absurd hij (lt_irrefl 0)
  apply Units.ext
  rw [upper_block_val_submatrix le_rfl hH]
  ext i j
  rfl

theorem adj_move {A : Type} [CommRing A] (c : A →+* A) {a b : ℕ} (G' g gi : Matrix (Fin a) (Fin a) A)
    (H h hi : Matrix (Fin b) (Fin b) A) (x : Matrix (Fin b) (Fin a) A)
    (h1 : G' * (gi.map c).transpose = g * G') (h2 : H * hi = (h.map c).transpose * H) :
    G' * ((h * x * gi).map c).transpose * H = g * (G' * (x.map c).transpose * H) * hi := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← h2, ← Matrix.mul_assoc G', h1]
  simp only [Matrix.mul_assoc]

theorem frame_move {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a b : ℕ} (g : Matrix (Fin a) (Fin a) A)
    (hi : Matrix (Fin b) (Fin b) A) (x : Matrix (Fin a) (Fin b) A) (β y : Matrix (Fin a) (Fin a) B)
    (γ z : Matrix (Fin b) (Fin b) B) (h1 : β * g.map f = y * β) (h2 : hi.map f * γ = γ * z) :
    β * (g * x * hi).map f * γ = y * (β * x.map f * γ) * z := by
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, ← Matrix.mul_assoc β, h1]
  simp only [Matrix.mul_assoc]

theorem adj_frame_move {A B : Type} [CommRing A] [CommRing B] (c : A →+* A) (f : A →+* B) {a b : ℕ}
    (G' g gi : Matrix (Fin a) (Fin a) A) (H h hi : Matrix (Fin b) (Fin b) A) (x : Matrix (Fin b) (Fin a) A)
    (β y : Matrix (Fin a) (Fin a) B) (γ z : Matrix (Fin b) (Fin b) B)
    (h1 : G' * (gi.map c).transpose = g * G') (h2 : H * hi = (h.map c).transpose * H)
    (h3 : β * g.map f = y * β) (h4 : hi.map f * γ = γ * z) :
    β * (G' * ((h * x * gi).map c).transpose * H).map f * γ =
      y * (β * (G' * (x.map c).transpose * H).map f * γ) * z := by
  rw [adj_move c G' g gi H h hi x h1 h2]
  exact frame_move f g hi _ β y γ z h3 h4

open Classical in
theorem red_mul {A : Type} [CommRing A] (R : Subring A) {a b : ℕ} (y : Matrix (Fin a) (Fin a) R)
    (z : Matrix (Fin b) (Fin b) R) {N N' : Matrix (Fin a) (Fin b) A} (hN : ∀ i j, N i j ∈ R)
    (e : N' = y.map R.subtype * N * z.map R.subtype) :
    (∀ i j, N' i j ∈ R) ∧ ∀ {κ : Type} [CommRing κ] (φ : R →+* κ),
      (Matrix.of fun i j => if h : N' i j ∈ R then φ ⟨N' i j, h⟩ else 0) =
        y.map φ * (Matrix.of fun i j => if h : N i j ∈ R then φ ⟨N i j, h⟩ else 0) * z.map φ := by
  set N₀ : Matrix (Fin a) (Fin b) R := Matrix.of fun i j => ⟨N i j, hN i j⟩ with hN₀
  have hN0 : N = N₀.map R.subtype := by ext i j; rfl
  have hN' : N' = (y * N₀ * z).map R.subtype := by rw [e, hN0, Matrix.map_mul, Matrix.map_mul]
  have mem : ∀ i j, N' i j ∈ R := fun i j => by rw [hN']; exact ((y * N₀ * z) i j).2
  refine ⟨mem, fun {κ} _ φ => ?_⟩
  have L1 : (Matrix.of fun i j => if h : N' i j ∈ R then φ ⟨N' i j, h⟩ else 0) = (y * N₀ * z).map φ := by
    ext i j
    rw [Matrix.of_apply, dif_pos (mem i j), Matrix.map_apply]
    congr 1
    exact Subtype.ext (by show N' i j = _; rw [hN']; rfl)
  have L2 : (Matrix.of fun i j => if h : N i j ∈ R then φ ⟨N i j, h⟩ else 0) = N₀.map φ := by
    ext i j
    rw [Matrix.of_apply, dif_pos (hN i j), Matrix.map_apply]
    rfl
  rw [L1, L2, Matrix.map_mul, Matrix.map_mul]

end Mat

variable {D : D7}

theorem omegaK_mul {n r : ℕ} (hr : r ≤ n) (Pg : Finset (Pl D.host.E)) (G : ∀ PP : Pl D.host.E, GL (Fin n) (kP PP))
    (H : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (hG : ∀ PP ∈ Pg, G PP ∈ blockTri (blk2 r))
    (hGH : ∀ PP ∈ Pg, upperLeftBlock hr (G PP) = H PP) (u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaK Pg (fun PP => (G PP).val * u PP * ((H PP)⁻¹).val) = omegaK Pg u := by
  have key : ∀ PP ∈ Pg, (LowZero r ((G PP).val * u PP * ((H PP)⁻¹).val) ∧
      topL r ((G PP).val * u PP * ((H PP)⁻¹).val) = 1) ↔ (LowZero r (u PP) ∧ topL r (u PP) = 1) := by
    intro PP hP
    rw [lowZero_mul_iff (hG PP hP) (H PP)⁻¹ (u PP)]
    refine and_congr_right fun hu => ?_
    rw [topL_mul hr (hG PP hP) _ hu, hGH PP hP]
    constructor
    · intro h1
      calc topL r (u PP) = ((H PP)⁻¹).val * ((H PP).val * topL r (u PP) * ((H PP)⁻¹).val) * (H PP).val := by
            simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
        _ = 1 := by rw [h1, Matrix.mul_one, Units.inv_mul]
    · intro h1
      rw [h1, Matrix.mul_one, Units.mul_inv]
  dsimp only [omegaK]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (fun PP hP => (key PP hP).mp (h1 PP hP)) h2
  · exact absurd (fun PP hP => (key PP hP).mpr (h2 PP hP)) h1
  · rfl

theorem omegaQ_mul {n r : ℕ} (hr : r ≤ n) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (G : ∀ PP : Pl D.host.E, GL (Fin n) (kP PP))
    (H : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (hG : ∀ PP ∈ Q, G PP ∈ blockTri (blk2 r))
    (u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaQ Q r ξ (-1) (fun PP => (G PP).val * u PP * ((H PP)⁻¹).val) =
      (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (G PP))))⁻¹ *
        ξ PP (Matrix.GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ)) * omegaQ Q r ξ (-1) u := by
  have hdet : ∀ PP ∈ Q, LowZero r (u PP) → (topL r ((G PP).val * u PP * ((H PP)⁻¹).val)).det =
      (upperLeftBlock hr (G PP)).val.det * (topL r (u PP)).det * ((H PP)⁻¹).val.det := fun PP hP hu => by
    rw [topL_mul hr (hG PP hP) _ hu, Matrix.det_mul, Matrix.det_mul]
  have key : ∀ PP ∈ Q, (LowZero r ((G PP).val * u PP * ((H PP)⁻¹).val) ∧
      IsUnit (topL r ((G PP).val * u PP * ((H PP)⁻¹).val)).det) ↔
      (LowZero r (u PP) ∧ IsUnit (topL r (u PP)).det) := by
    intro PP hP
    rw [lowZero_mul_iff (hG PP hP) (H PP)⁻¹ (u PP)]
    refine and_congr_right fun hu => ?_
    have uR : IsUnit (upperLeftBlock hr (G PP)).val.det := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
    have uH : IsUnit ((H PP)⁻¹).val.det := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
    rw [hdet PP hP hu, IsUnit.mul_iff, IsUnit.mul_iff]
    exact ⟨fun h => h.1.2, fun h => ⟨⟨uR, h⟩, uH⟩⟩
  dsimp only [omegaQ]
  split_ifs with h1 h2 h2
  · rw [← Finset.prod_attach Q, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have hu := (h2 PP.1 PP.2).1
    have e : (h1 PP.1 PP.2).2.unit = Matrix.GeneralLinearGroup.det (upperLeftBlock hr (G PP.1)) * (h2 PP.1 PP.2).2.unit *
        (Matrix.GeneralLinearGroup.det (H PP.1))⁻¹ := by
      apply Units.ext
      rw [IsUnit.unit_spec, Units.val_mul, Units.val_mul, IsUnit.unit_spec, hdet PP.1 PP.2 hu,
        ← map_inv Matrix.GeneralLinearGroup.det (H PP.1), Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.GeneralLinearGroup.val_det_apply]
    rw [e, map_mul, map_mul, map_inv]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, zpow_neg_one, mul_inv, inv_inv]
    ring
  · exact absurd (fun PP hP => (key PP hP).mp (h1 PP hP)) h2
  · exact absurd (fun PP hP => (key PP hP).mpr (h2 PP hP)) h1
  · rw [mul_zero]

theorem gram_inv_mul (S : HSp D) (g : GA D S) :
    (S.gram⁻¹).map (incA D) * ((Formalism.L2.Theta.mt S g⁻¹).map (cA D)).transpose =
      Formalism.L2.Theta.mt S g * (S.gram⁻¹).map (incA D) := by
  have hg := (g⁻¹).2
  simp only [HR, Formalism.UG.UJ, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq, Formalism.UG.cT] at hg
  have hg' : ((Formalism.L2.Theta.mt S g⁻¹).map (cA D)).transpose * S.gram.map (incA D) * Formalism.L2.Theta.mt S g⁻¹ =
      S.gram.map (incA D) := hg
  have m1 : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.inv_mul _
  by_cases hJ : IsUnit S.gram.det
  · have a1 : S.gram⁻¹.map (incA D) * S.gram.map (incA D) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ, Matrix.map_one _ (map_zero _) (map_one _)]
    have a2 : S.gram.map (incA D) * S.gram⁻¹.map (incA D) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ, Matrix.map_one _ (map_zero _) (map_one _)]
    calc S.gram⁻¹.map (incA D) * ((Formalism.L2.Theta.mt S g⁻¹).map (cA D)).transpose
        = S.gram⁻¹.map (incA D) * (((Formalism.L2.Theta.mt S g⁻¹).map (cA D)).transpose * S.gram.map (incA D) *
            S.gram⁻¹.map (incA D)) := by
          rw [Matrix.mul_assoc _ (S.gram.map (incA D)), a2, Matrix.mul_one]
      _ = S.gram⁻¹.map (incA D) * (((Formalism.L2.Theta.mt S g⁻¹).map (cA D)).transpose * S.gram.map (incA D) *
            Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g * S.gram⁻¹.map (incA D)) := by
          rw [Matrix.mul_assoc _ (Formalism.L2.Theta.mt S g⁻¹), m1, Matrix.mul_one]
      _ = S.gram⁻¹.map (incA D) * (S.gram.map (incA D) * Formalism.L2.Theta.mt S g * S.gram⁻¹.map (incA D)) := by
          rw [hg']
      _ = Formalism.L2.Theta.mt S g * S.gram⁻¹.map (incA D) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, a1, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hJ]
    simp

theorem frGL_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    β⁻¹ * frGL β y = intGL F E n y * β⁻¹ ∧ frGL β y * β = β * intGL F E n y := by
  have e : frGL β y = β * intGL F E n y * β⁻¹ := rfl
  exact ⟨by rw [e, mul_assoc, inv_mul_cancel_left], by rw [e, mul_assoc, inv_mul_cancel, mul_one]⟩

theorem frGL_inv (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {g : GA D V}
    {y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)} (hy : frGL β y = finE V g) :
    frGL β y⁻¹ = finE V g⁻¹ := by
  rw [map_inv, map_inv, hy]

theorem fin_move (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {g : GA D V}
    {y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)} (hy : frGL β y = finE V g) :
    (β⁻¹).val * (Formalism.L2.Theta.mt V g).map (toEAf D) = (intGL _ _ _ y).val * (β⁻¹).val ∧
      (Formalism.L2.Theta.mt V g).map (toEAf D) * β.val = β.val * (intGL _ _ _ y).val := by
  obtain ⟨h1, h2⟩ := frGL_move β y
  rw [hy] at h1 h2
  have e1 := congrArg Units.val h1
  have e2 := congrArg Units.val h2
  rw [Units.val_mul, Units.val_mul] at e1 e2
  have f := GlobalTheory.VecInv.finE_val V g
  exact ⟨(congrArg (fun M => (β⁻¹).val * M) f).symm.trans e1, (congrArg (fun M => M * β.val) f).symm.trans e2⟩

theorem frMapAdj_actO (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    {g : GA D S} {h : GA D T} {y : GL (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    {z : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)} (hy : frGL βS y = finE S g) (hz : frGL βT z = finE T h)
    (x : WO S T) :
    frMapAdj S T βS βT (actO S T g h x) =
      HMul.hMul (HMul.hMul (intGL _ _ _ y).val (frMapAdj S T βS βT x)) (intGL _ _ _ z⁻¹).val := by
  have hT2 : T.gram.map (incA D) * Formalism.L2.Theta.mt T h⁻¹ = ((Formalism.L2.Theta.mt T h).map (cA D)).transpose * T.gram.map (incA D) := by
    have hh := h.2
    simp only [HR, Formalism.UG.UJ, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
      Formalism.UG.cT] at hh
    have hh' : ((Formalism.L2.Theta.mt T h).map (cA D)).transpose * T.gram.map (incA D) * Formalism.L2.Theta.mt T h =
        T.gram.map (incA D) := hh
    have m2 : Formalism.L2.Theta.mt T h * Formalism.L2.Theta.mt T h⁻¹ = 1 := by
      unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.mul_inv _
    calc T.gram.map (incA D) * Formalism.L2.Theta.mt T h⁻¹
        = ((Formalism.L2.Theta.mt T h).map (cA D)).transpose * T.gram.map (incA D) * Formalism.L2.Theta.mt T h *
            Formalism.L2.Theta.mt T h⁻¹ := by rw [hh']
      _ = ((Formalism.L2.Theta.mt T h).map (cA D)).transpose * T.gram.map (incA D) := by
          rw [Matrix.mul_assoc _ (Formalism.L2.Theta.mt T h), m2, Matrix.mul_one]
  unfold actO frMapAdj
  exact adj_frame_move (cA D) (toEAf D) _ _ _ _ _ _ x _ _ _ _ (gram_inv_mul S g) hT2 (fin_move S βS hy).1
    (fin_move T βT (frGL_inv T βT hz)).2

theorem red_actO (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    {g : GA D S} {h : GA D T} (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) {x : WO S T}
    (hx : IsIntM (frMapAdj S T βS βT x)) :
    IsIntM (frMapAdj S T βS βT (actO S T g h x)) ∧ ∀ PP : Pl D.host.E,
      redM PP (frMapAdj S T βS βT (actO S T g h x)) =
        (redFn βS PP (finE S g)).val * redM PP (frMapAdj S T βS βT x) * ((redFn βT PP (finE T h))⁻¹).val := by
  obtain ⟨yy, hyy⟩ := hg
  obtain ⟨zz, hzz⟩ := hh
  have hA := frMapAdj_actO S T βS βT hyy hzz x
  obtain ⟨hint, hred⟩ := red_mul (Formalism.L2.Herm.intAf D.host.F D.host.E) yy.val (zz⁻¹).val hx hA
  refine ⟨hint, fun PP => ?_⟩
  rw [← hyy, ← hzz, redFn_frGL, redFn_frGL, ← map_inv (Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP)) zz]
  exact hred (Formalism.L2.DIV.resS D.host.F PP)

theorem isHalf_actO' {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  unfold IsHalf at hu ⊢
  unfold actO
  intro i j
  have hu' : (e • (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) = u := Matrix.ext fun i j => hu i j
  conv_rhs => rw [← hu']
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem adjDatum_actO : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (Pg Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (r : ℕ) (hS : r ≤ S.rank) (hT : r ≤ T.rank), T.rank = r → ∀ g h, finE S g ∈ St βS → finE T h ∈ St βT → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → redFn βS PP (finE S g) ∈ blockTri (blk2 r)) → (∀ PP ∈ Pg, upperLeftBlock hS (redFn βS PP (finE S g)) = upperLeftBlock hT (redFn βT PP (finE T h))) → ∀ x, adjDatum S T βS βT Pg Q ξ a (actO S T g h x) = (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hS (redFn βS PP (finE S g)))))⁻¹ * ξ PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)) * adjDatum S T βS βT Pg Q ξ a x := by
  intro D S T βS βT Pg Q ξ a r hS hT hr g h hg hh hblk hPg x
  subst hr
  have mtc : ∀ (V : HSp D) (k : GA D V), Formalism.L2.Theta.mt V k⁻¹ * Formalism.L2.Theta.mt V k = 1 := fun V k => by
    unfold Formalism.L2.Theta.mt
    rw [map_inv]
    exact Units.inv_mul _
  have back : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
    unfold actO
    rw [inv_inv]
    simp only [Matrix.mul_assoc, mtc S g, Matrix.mul_one]
    rw [← Matrix.mul_assoc, mtc T h, Matrix.one_mul]
  have hgi : finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact (St βS).inv_mem hg
  have hhi : finE T h⁻¹ ∈ St βT := by rw [map_inv]; exact (St βT).inv_mem hh
  have hiff : (IsHalf a (actO S T g h x) ∧ IsIntM (frMapAdj S T βS βT (actO S T g h x))) ↔
      (IsHalf a x ∧ IsIntM (frMapAdj S T βS βT x)) := by
    constructor
    · rintro ⟨h1, h2⟩
      have k1 := isHalf_actO' g⁻¹ h⁻¹ h1
      have k2 := (red_actO S T βS βT hgi hhi h2).1
      rw [back] at k1 k2
      exact ⟨k1, k2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨isHalf_actO' g h h1, (red_actO S T βS βT hg hh h2).1⟩
  unfold adjDatum
  by_cases hx : IsHalf a x ∧ IsIntM (frMapAdj S T βS βT x)
  · rw [if_pos hx, if_pos (hiff.mpr hx)]
    have e : (fun PP => redM PP (frMapAdj S T βS βT (actO S T g h x))) = fun PP =>
        (redFn βS PP (finE S g)).val * redM PP (frMapAdj S T βS βT x) * ((redFn βT PP (finE T h))⁻¹).val :=
      funext (red_actO S T βS βT hg hh hx.2).2
    rw [e, omegaK_mul hS Pg (fun PP => redFn βS PP (finE S g)) (fun PP => redFn βT PP (finE T h))
      (fun PP hP => hblk PP (Or.inl hP)) (fun PP hP => by rw [hPg PP hP]; exact restrictedBlock_self_apply _) _,
      omegaQ_mul hS Q ξ (fun PP => redFn βS PP (finE S g)) (fun PP => redFn βT PP (finE T h))
      (fun PP hP => hblk PP (Or.inr hP)) _]
    ring
  · rw [if_neg hx, if_neg (fun h' => hx (hiff.mp h')), mul_zero]

end GlobalTheory.AdjDatumMove

end
