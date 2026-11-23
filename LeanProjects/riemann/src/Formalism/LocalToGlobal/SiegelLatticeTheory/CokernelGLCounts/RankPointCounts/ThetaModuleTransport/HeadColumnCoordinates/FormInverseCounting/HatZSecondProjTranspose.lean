import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.StepLiftG

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def rh1 (g : SplitG M.L) : M.R →+* F := (ph1 g).comp M.R.subtype

def rh2 (g : SplitG M.L) : M.R →+* F := (ph2 g).comp M.R.subtype

theorem ringFirstProj_apply (x : M.R) : rh1 g x = ph1 g (x : E) := rfl

theorem ringSecondProj_apply (x : M.R) : rh2 g x = ph2 g (x : E) := rfl

def crn (r : ℕ) (c : F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

theorem uV_add (x y : Fin (r + 1) → M.R) : uV g (x + y) = uV g x + uV g y := by
  funext i
  rcases i with a | a <;> simp [uV, map_add]

theorem uV_mulVec (N : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (v : Fin (r + 1) → M.R) :
    uV g (N.mulVec v) = (Matrix.fromBlocks (N.map (rh1 g)) 0 0 (N.map (rh2 g))).mulVec (uV g v) := by
  funext i
  rcases i with a | a <;>
    simp [uV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, firstProj_ring_sum, secondProj_ring_sum, ringFirstProj_apply, ringSecondProj_apply]

theorem mul_crn (N : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (hN : ∀ i, N i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (c : F) : N * crn r c = crn r c := by
  ext i j
  simp only [Matrix.mul_apply, crn, Matrix.of_apply]
  by_cases hj : j = Fin.last r
  · subst hj
    simp [hN]
  · simp [hj]

theorem crn_mul (N : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (hN : ∀ j, N (Fin.last r) j = if j = Fin.last r then 1 else 0)
    (c : F) : crn r c * N = crn r c := by
  ext i j
  simp only [Matrix.mul_apply, crn, Matrix.of_apply]
  by_cases hi : i = Fin.last r
  · subst hi
    simp [hN]
  · simp [hi]

theorem hatZ_firstProj_smul (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') :
    Zh.map (ph1 g) = (g.q : F) • Z.Z.map (rh1 g) - crn r T := by
  have hq := q_ne g
  ext a b
  have he : ((Z.Z a b : M.R) : E) = HermSp.ZZplusOf M Zh T T' a b := by rw [← hZ]; rfl
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ringFirstProj_apply, he, zzPlus_firstProj_corner hs, crn,
    Matrix.of_apply]
  split_ifs <;> field_simp <;> ring

theorem hatZ_secondProj_transpose (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') :
    (Zh.map (ph2 g)).transpose = -((g.q : F) • Z.Z.map (rh2 g)) - crn r T' := by
  have hq := q_ne g
  ext a b
  have he : ((Z.Z a b : M.R) : E) = HermSp.ZZplusOf M Zh T T' a b := by rw [← hZ]; rfl
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul, ringSecondProj_apply, he, zzPlus_secondProj_corner hs, crn, Matrix.of_apply]
  split_ifs <;> field_simp <;> ring

theorem transpose_gHat_eq_fromBlocks (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') :
    (gHat g Zh T T').transpose = Matrix.fromBlocks (crn r (-T)) ((g.q : F) • Z.Z.map (rh1 g) - crn r T)
      (-((g.q : F) • Z.Z.map (rh2 g)) - crn r T') (crn r (-T')) := by
  rw [gHat, Matrix.fromBlocks_transpose, Matrix.transpose_transpose, hatZ_firstProj_smul hs Zh T T' Z hZ, hatZ_secondProj_transpose hs Zh T T' Z hZ]
  congr 1
  · ext a b; simp only [Matrix.transpose_apply, crn, Matrix.of_apply]; by_cases ha : a = Fin.last r <;> simp [ha, and_comm]
  · ext a b; simp only [Matrix.transpose_apply, crn, Matrix.of_apply]; by_cases ha : a = Fin.last r <;> simp [ha, and_comm]

theorem stepA_mat (hs : M.split = some g) (T T' : F) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (Z₁ Z₂ : M.Mat (r + 1)) (hZ₁ : Z₁.Z.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T')
    (hZ₂ : Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T') (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R)
    (hPQ : P * Z₁.Z = Z₂.Z * Q) (hPe : ∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hQe : ∀ j, Q (Fin.last r) j = if j = Fin.last r then 1 else 0) :
    Matrix.fromBlocks (P.map (rh1 g)) 0 0 (P.map (rh2 g)) * (gHat g Zh₁ T T').transpose =
      (gHat g Zh₂ T T').transpose * Matrix.fromBlocks (Q.map (rh2 g)) 0 0 (Q.map (rh1 g)) := by
  have hP1 : ∀ i, P.map (rh1 g) i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
    intro i; simp only [Matrix.map_apply, hPe]; split_ifs <;> simp
  have hP2 : ∀ i, P.map (rh2 g) i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
    intro i; simp only [Matrix.map_apply, hPe]; split_ifs <;> simp
  have hQ1 : ∀ j, Q.map (rh1 g) (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
    intro j; simp only [Matrix.map_apply, hQe]; split_ifs <;> simp
  have hQ2 : ∀ j, Q.map (rh2 g) (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
    intro j; simp only [Matrix.map_apply, hQe]; split_ifs <;> simp
  have e1 : P.map (rh1 g) * Z₁.Z.map (rh1 g) = Z₂.Z.map (rh1 g) * Q.map (rh1 g) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPQ]
  have e2 : P.map (rh2 g) * Z₁.Z.map (rh2 g) = Z₂.Z.map (rh2 g) * Q.map (rh2 g) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPQ]
  rw [transpose_gHat_eq_fromBlocks hs Zh₁ T T' Z₁ hZ₁, transpose_gHat_eq_fromBlocks hs Zh₂ T T' Z₂ hZ₂, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1
  · rw [mul_crn _ hP1, crn_mul _ hQ2]
  · rw [Matrix.mul_sub, Matrix.mul_smul, e1, mul_crn _ hP1, Matrix.sub_mul, Matrix.smul_mul, crn_mul _ hQ1]
  · rw [Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, e2, mul_crn _ hP2, Matrix.sub_mul, Matrix.neg_mul,
      Matrix.smul_mul, crn_mul _ hQ2]
  · rw [mul_crn _ hP2, crn_mul _ hQ1]

theorem dot_adj {n : Type} [Fintype n] [DecidableEq n] (A D G₁ G₂ : Matrix n n F) (h₁ : IsUnit G₁.det)
    (h₂ : IsUnit G₂.det) (h : A * G₁.transpose = G₂.transpose * D) (x y : n → F) :
    dotProduct (A.mulVec x) (G₂⁻¹.mulVec y) = dotProduct x (G₁⁻¹.mulVec (D.transpose.mulVec y)) := by
  have ht : G₁ * A.transpose = D.transpose * G₂ := by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose] at this
  have h2 : A.transpose * G₂⁻¹ = G₁⁻¹ * D.transpose := by
    calc A.transpose * G₂⁻¹ = G₁⁻¹ * (G₁ * A.transpose) * G₂⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h₁, Matrix.one_mul]
      _ = G₁⁻¹ * D.transpose * (G₂ * G₂⁻¹) := by rw [ht]; simp only [Matrix.mul_assoc]
      _ = G₁⁻¹ * D.transpose := by rw [Matrix.mul_nonsing_inv _ h₂, Matrix.mul_one]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec,
    h2, ← Matrix.mulVec_mulVec]

theorem gHat_unit (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (h : GHyp M g T T' TT Zh Z Zσ) : IsUnit (gHat g Zh T T').det := by
  have hq := q_ne g
  have hU := gramUnit_split_holds F E M g r T T' TT Zh Z Zσ h
  obtain ⟨h1, -⟩ := (isUnit_iff_ph (g := g) _).1 hU
  rw [det_ph, map_gramG, Matrix.det_mul, Matrix.det_mul] at h1
  exact isUnit_iff_ne_zero.2 (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 h1).1).2

theorem llMap_zero_last (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (m : Fin (r + 1) → M.R)
    (hm : m (Fin.last r) = 0) : llMap hs Z TT m = Z.Z.mulVec m := by
  have h0 : trO hs (0 : M.R) = 0 := map_zero _
  simp [llMap, hm, h0]

theorem stepDuF_of (hL : StepLiftG) : StepDuF := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk γ
  obtain ⟨P, Q, P', γ', hP, hP', hPQ, hPe, hQe, hstar⟩ := hL F E M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ γ
  have hZ₁ := h₁.2.2.2.1
  have hZ₂ := h₂.2.2.2.1
  have hS₁ := h₁.2.2.2.2.1
  have hS₂ := h₂.2.2.2.2.1
  have hTT := h₁.2.2.1
  have hG₁ := gHat_unit hs h₁
  have hG₂ := gHat_unit hs h₂

  have wl : ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : M.Mat (r + 1)),
      Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' → IsUnit (gHat g Zh T T').det →
      ∀ m y, dotProduct (uV g (llMap hs Z TT m)) ((gHat g Zh T T')⁻¹.mulVec (uV g y)) ∈ 𝒪[F] := by
    intro Zh Z hZ hG m y
    rw [uV_llMap hs Zh T T' Z TT hZ hTT m, dot_inv_vecMul _ hG]
    exact lamV_dot_mem hs m y
  have wr : ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Zσ : M.Mat (r + 1)),
      Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' → IsUnit (gHat g Zh T T').det →
      ∀ x m, dotProduct (uV g x) ((gHat g Zh T T')⁻¹.mulVec (uV g (llMap hs Zσ TT m))) ∈ 𝒪[F] := by
    intro Zh Zσ hZ hG x m
    rw [uV_llMap hs (Zh.map M.L.cj) T T' Zσ TT hZ hTT m, gHat_cj, Matrix.vecMul_transpose, dot_inv_mulVec _ hG,
      dotProduct_comm]
    exact lamV_dot_mem hs m x
  refine ⟨γ', fun θ₁ θ₂ i₁ i₂ l l₂ w w₂ e1 e2 => ?_⟩
  have t1 : θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT (P.mulVec l) := i₁ l _ (hP l)
  have t2 : θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT (P'.mulVec w) := i₂ w _ (hP' w)
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, l₂ = P.mulVec l + llMap hs Z₂ TT m₁ := by
    have : mk1 hs Z₂ TT (P.mulVec l) = mk1 hs Z₂ TT l₂ := t1.symm.trans e1
    obtain ⟨m₁, hm⟩ := (QuotientAddGroup.eq.1 this : -(P.mulVec l) + l₂ ∈ LL hs Z₂ TT)
    exact ⟨m₁, by rw [hm]; abel⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m₂, w₂ = P'.mulVec w + llMap hs Zσ₂ TT m₂ := by
    have : mk1 hs Zσ₂ TT (P'.mulVec w) = mk1 hs Zσ₂ TT w₂ := t2.symm.trans e2
    obtain ⟨m₂, hm⟩ := (QuotientAddGroup.eq.1 this : -(P'.mulVec w) + w₂ ∈ LL hs Zσ₂ TT)
    exact ⟨m₂, by rw [hm]; abel⟩
  obtain ⟨m, hml, hm⟩ := hstar w

  have hD : (Matrix.fromBlocks (Q.map (rh2 g)) 0 0 (Q.map (rh1 g))).transpose.mulVec (uV g (P'.mulVec w)) =
      uV g (w + llMap hs Zσ₁ TT m) := by
    rw [llMap_zero_last hs Zσ₁ TT m hml]
    funext i
    rcases i with a | a
    · have := congrArg (ph1 g) (hm a)
      simp only [map_sum, map_mul, map_add, splitFirstProj_conj] at this
      simpa [uV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_transpose, ringSecondProj_apply,
        map_add] using this
    · have := congrArg (ph2 g) (hm a)
      simp only [map_sum, map_mul, map_add, ph2_cj_eq_ph1] at this
      simpa [uV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_transpose, ringFirstProj_apply,
        map_add] using this
  have hA := stepA_mat hs T T' Zh₁ Zh₂ Z₁ Z₂ hZ₁ hZ₂ P Q hPQ hPe hQe
  have key : dotProduct (uV g (P.mulVec l)) ((gHat g Zh₂ T T')⁻¹.mulVec (uV g (P'.mulVec w))) =
      dotProduct (uV g l) ((gHat g Zh₁ T T')⁻¹.mulVec (uV g w)) +
        dotProduct (uV g l) ((gHat g Zh₁ T T')⁻¹.mulVec (uV g (llMap hs Zσ₁ TT m))) := by
    rw [uV_mulVec P l, dot_adj _ _ _ _ hG₁ hG₂ hA, hD, uV_add, Matrix.mulVec_add, dotProduct_add]
  rw [hm₁, hm₂, uV_add, uV_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, key]
  have a1 := wl Zh₂ Z₂ hZ₂ hG₂ m₁ (P'.mulVec w)
  have a2 := wl Zh₂ Z₂ hZ₂ hG₂ m₁ (llMap hs Zσ₂ TT m₂)
  have a3 := wr Zh₂ Zσ₂ hS₂ hG₂ (P.mulVec l) m₂
  have a4 := wr Zh₁ Zσ₁ hS₁ hG₁ l m
  have : ∀ a b c d e : F, a + b + (c + e) - a = b + c + e := fun a b c d e => by ring
  convert add_mem (add_mem (add_mem a4 a3) a1) a2 using 1
  ring

theorem stepDu_of_lift (hL : StepLiftG) : StepDu := stepDu_of gramUnit_split_holds (stepDuF_of hL)

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
