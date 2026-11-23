import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewGood
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.SwapShear

open GlobalTheory.LeviPlane

variable {R : Type} [CommRing R] (c : R →+* R) {n : ℕ}

def swapM (J : Matrix (Fin n) (Fin n) R) (a b : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  1 - Matrix.vecMulVec a (J *ᵥ fun i => c (b i)) + Matrix.vecMulVec b (J *ᵥ fun i => c (a i))

def shM (J : Matrix (Fin n) (Fin n) R) (P Q : Fin n → R) (t : R) : Matrix (Fin n) (Fin n) R :=
  1 + t • Matrix.vecMulVec P (J *ᵥ fun i => c (Q i)) + c t • Matrix.vecMulVec Q (J *ᵥ fun i => c (P i))

theorem swapM_mulVec (J : Matrix (Fin n) (Fin n) R) (a b u : Fin n → R) :
    swapM c J a b *ᵥ u = u - fm c J u b • a + fm c J u a • b := by
  ext i
  simp only [swapM, fm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct_comm u]
  ring

theorem shM_mulVec (J : Matrix (Fin n) (Fin n) R) (P Q : Fin n → R) (t : R) (u : Fin n → R) :
    shM c J P Q t *ᵥ u = u + (t * fm c J u Q) • P + (c t * fm c J u P) • Q := by
  ext i
  simp only [shM, fm, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct_comm u]
  ring

variable {c}

theorem unitary_of_fm {J M : Matrix (Fin n) (Fin n) R}
    (key : ∀ u v, fm c J (M *ᵥ u) (M *ᵥ v) = fm c J u v) : Mᵀ * J * M.map c = J := by
  ext i j
  rw [entry, key]
  have h1 := entry (c := c) J 1 i j
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one,
    Matrix.one_mulVec] at h1
  exact h1.symm

theorem eq_one_of_mulVec {M : Matrix (Fin n) (Fin n) R} (h : ∀ u, M *ᵥ u = u) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [Matrix.one_apply]
  simpa [Matrix.mulVec_single_one, Pi.single_apply] using this

theorem mul_eq_self {M : Matrix (Fin n) (Fin n) R} {k : ℕ} (K : Matrix (Fin n) (Fin k) R)
    (h : ∀ j, M *ᵥ (K *ᵥ Pi.single j 1) = K *ᵥ Pi.single j 1) : M * K = K := by
  ext i j
  have := congrFun (h j) i
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this

theorem fm_mulVec_mulVec {m : ℕ} (J : Matrix (Fin n) (Fin n) R) (ι : Matrix (Fin n) (Fin m) R) (u v : Fin m → R) :
    fm c J (ι *ᵥ u) (ι *ᵥ v) = fm c (ιᵀ * J * ι.map c) u v := by
  have e : (fun i => c ((ι *ᵥ v) i)) = ι.map c *ᵥ fun i => c (v i) := by
    ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [fm, e]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

section Forms
variable (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j)
include hc hJ

theorem swapM_invol {a b : Fin n → R} (haa : fm c J a a = 0) (hbb : fm c J b b = 0) (hab : fm c J a b = 2)
    (hba : fm c J b a = -2) : swapM c J a b * swapM c J a b = 1 := by
  apply eq_one_of_mulVec
  intro u
  rw [← Matrix.mulVec_mulVec, swapM_mulVec, swapM_mulVec]
  simp only [fm_add_left, fm_sub_left, fm_smul_left, haa, hbb, hab, hba]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem swapM_unitary {a b : Fin n → R} (haa : fm c J a a = 0) (hbb : fm c J b b = 0) (hab : fm c J a b = 2)
    (hba : fm c J b a = -2) : (swapM c J a b)ᵀ * J * (swapM c J a b).map c = J := by
  apply unitary_of_fm
  intro u v
  rw [swapM_mulVec, swapM_mulVec]
  simp only [fm_add_left, fm_sub_left, fm_smul_left, fm_add_right, fm_sub_right, fm_smul_right, haa, hbb, hab, hba]
  rw [fm_skew c hc J hJ a v, fm_skew c hc J hJ b v]
  ring

theorem shM_mul {P Q : Fin n → R} (hPP : fm c J P P = 0) (hQQ : fm c J Q Q = 0) (hPQ : fm c J P Q = 0)
    (t : R) : shM c J P Q t * shM c J P Q (-t) = 1 := by
  have hQP : fm c J Q P = 0 := by rw [fm_skew c hc J hJ, hPQ, map_zero, neg_zero]
  apply eq_one_of_mulVec
  intro u
  rw [← Matrix.mulVec_mulVec, shM_mulVec, shM_mulVec]
  simp only [fm_add_left, fm_smul_left, hPP, hQQ, hPQ, hQP, map_neg]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem shM_unitary {P Q : Fin n → R} (hPP : fm c J P P = 0) (hQQ : fm c J Q Q = 0) (hPQ : fm c J P Q = 0)
    (t : R) : (shM c J P Q t)ᵀ * J * (shM c J P Q t).map c = J := by
  have hQP : fm c J Q P = 0 := by rw [fm_skew c hc J hJ, hPQ, map_zero, neg_zero]
  apply unitary_of_fm
  intro u v
  rw [shM_mulVec, shM_mulVec]
  simp only [fm_add_left, fm_smul_left, fm_add_right, fm_smul_right, hPP, hQQ, hPQ, hQP, map_mul, hc]
  rw [fm_skew c hc J hJ P v, fm_skew c hc J hJ Q v]
  ring

end Forms

end GlobalTheory.SwapShear

namespace GlobalTheory.SwapShear
open GlobalTheory.LeviPlane

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_inc_mulVec {m k : ℕ} (S : Matrix (Fin m) (Fin k) E) (v : Fin k → E) :
    S.map (inclR (F := F) (AF F)) *ᵥ incV F v = incV F (S *ᵥ v) := by
  ext l; simp [incV, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem incM_mulVec_single {m k : ℕ} (K : Matrix (Fin m) (Fin k) E) (j : Fin k) :
    incM F K *ᵥ Pi.single j 1 = incV F (K *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]; rfl

end GlobalTheory.SwapShear

open GlobalTheory.LeviPlane GlobalTheory.SwapShear in

theorem GlobalTheory.ConeSmallMidJB.exists_levi_swap_shear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∃ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) ∧ (∃ w : UA σ G.W.J, IsSwap H' H₂ w) ∧
      ∃ nn : AE F E → UA σ G.W.J, IsShear H' H₂ nn := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V V' W₁' hT' e W₂ H₂ i₀ i₁ hH₂
  have hσ : ∀ x, σ (σ x) = x := sigma_invol hT.base.cm
  have hH' := hC.hH'
  let c : E →+* E := σ.toRingHom
  have hc : ∀ x, c (c x) = x := hσ
  have hJ : ∀ i j, c (G.W.J j i) = -G.W.J i j := fun i j => hT.geo.hW.skew i j
  have gram : ∀ u v, fm c G.W.J (H'.ι *ᵥ u) (H'.ι *ᵥ v) = fm c G₁.W.J u v := by
    intro u v; rw [fm_mulVec_mulVec]; congr 1; exact hH'.gram
  have hxx : fm c G.W.J H'.x H'.x = 0 := hH'.xx
  have hyy : fm c G.W.J H'.y H'.y = 0 := hH'.yy
  have hxy : fm c G.W.J H'.x H'.y = 1 := hH'.xy
  have hyx : fm c G.W.J H'.y H'.x = -1 := fm_yx hc hJ hxx hyy hxy
  have oX : ∀ u, fm c G.W.J (H'.ι *ᵥ u) H'.x = 0 := fun u => (hH'.orth u).1
  have oY : ∀ u, fm c G.W.J (H'.ι *ᵥ u) H'.y = 0 := fun u => (hH'.orth u).2
  have skew0 : ∀ p q, fm c G.W.J p q = 0 → fm c G.W.J q p = 0 := by
    intro p q h; rw [fm_skew c hc G.W.J hJ, h, map_zero, neg_zero]
  have h2xx : fm c G₁.W.J H₂.x H₂.x = 0 := hH₂.xx
  have h2yy : fm c G₁.W.J H₂.y H₂.y = 0 := hH₂.yy
  have h2xy : fm c G₁.W.J H₂.x H₂.y = 1 := hH₂.xy
  have h2oX : ∀ u, fm c G₁.W.J (H₂.ι *ᵥ u) H₂.x = 0 := fun u => (hH₂.orth u).1
  have h2oY : ∀ u, fm c G₁.W.J (H₂.ι *ᵥ u) H₂.y = 0 := fun u => (hH₂.orth u).2
  have hx'x' : fm c G.W.J (H'.ι *ᵥ H₂.x) (H'.ι *ᵥ H₂.x) = 0 := by rw [gram, h2xx]
  have hy'y' : fm c G.W.J (H'.ι *ᵥ H₂.y) (H'.ι *ᵥ H₂.y) = 0 := by rw [gram, h2yy]
  have hx'y' : fm c G.W.J (H'.ι *ᵥ H₂.x) (H'.ι *ᵥ H₂.y) = 1 := by rw [gram, h2xy]
  have hy'x' : fm c G.W.J (H'.ι *ᵥ H₂.y) (H'.ι *ᵥ H₂.x) = -1 := fm_yx hc hJ hx'x' hy'y' hx'y'
  have hx'x : fm c G.W.J (H'.ι *ᵥ H₂.x) H'.x = 0 := oX _
  have hx'y : fm c G.W.J (H'.ι *ᵥ H₂.x) H'.y = 0 := oY _
  have hy'x : fm c G.W.J (H'.ι *ᵥ H₂.y) H'.x = 0 := oX _
  have hy'y : fm c G.W.J (H'.ι *ᵥ H₂.y) H'.y = 0 := oY _
  have hxx' := skew0 _ _ hx'x
  have hyx' := skew0 _ _ hx'y
  have hxy' := skew0 _ _ hy'x
  have hyy' := skew0 _ _ hy'y

  have cX : ∀ j, fm c G.W.J (H'.ι *ᵥ (H₂.ι *ᵥ Pi.single j 1)) H'.x = 0 := fun j => oX _
  have cY : ∀ j, fm c G.W.J (H'.ι *ᵥ (H₂.ι *ᵥ Pi.single j 1)) H'.y = 0 := fun j => oY _
  have cX' : ∀ j, fm c G.W.J (H'.ι *ᵥ (H₂.ι *ᵥ Pi.single j 1)) (H'.ι *ᵥ H₂.x) = 0 := fun j => by
    rw [gram, h2oX]
  have cY' : ∀ j, fm c G.W.J (H'.ι *ᵥ (H₂.ι *ᵥ Pi.single j 1)) (H'.ι *ᵥ H₂.y) = 0 := fun j => by
    rw [gram, h2oY]
  refine ⟨fun h₁ => (exists_isLevi_unitary_smaller F E σ B (a + (b + 2)) (a + b) G.W G₁.W H' a (a + b + 1) _ _ _ _
      hT.base hT.geo.hW hT₁.geo.hW hH' h₁).choose,
    fun h₁ => (exists_isLevi_unitary_smaller F E σ B (a + (b + 2)) (a + b) G.W G₁.W H' a (a + b + 1) _ _ _ _
      hT.base hT.geo.hW hT₁.geo.hW hH' h₁).choose_spec, ?_, ?_⟩
  ·
    let S := swapM c G.W.J (H'.ι *ᵥ H₂.x - H'.x) (H'.ι *ᵥ H₂.y - H'.y)
    have haa : fm c G.W.J (H'.ι *ᵥ H₂.x - H'.x) (H'.ι *ᵥ H₂.x - H'.x) = 0 := by
      simp only [fm_sub_left, fm_sub_right, hxx, hx'x', hxx', hx'x]; ring
    have hbb : fm c G.W.J (H'.ι *ᵥ H₂.y - H'.y) (H'.ι *ᵥ H₂.y - H'.y) = 0 := by
      simp only [fm_sub_left, fm_sub_right, hyy, hy'y', hyy', hy'y]; ring
    have hab : fm c G.W.J (H'.ι *ᵥ H₂.x - H'.x) (H'.ι *ᵥ H₂.y - H'.y) = 2 := by
      simp only [fm_sub_left, fm_sub_right, hxy, hx'y', hxy', hx'y]; ring
    have hba : fm c G.W.J (H'.ι *ᵥ H₂.y - H'.y) (H'.ι *ᵥ H₂.x - H'.x) = -2 := by
      simp only [fm_sub_left, fm_sub_right, hyx, hy'x', hyx', hy'x]; ring
    have hSS : S * S = 1 := swapM_invol hc hJ haa hbb hab hba
    have hSU : Sᵀ * G.W.J * S.map c = G.W.J := swapM_unitary hc hJ haa hbb hab hba
    have sx : S *ᵥ H'.x = H'.ι *ᵥ H₂.x := by
      rw [swapM_mulVec]; simp only [fm_sub_right, hxx, hxy, hxx', hxy']; ext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have sy : S *ᵥ H'.y = H'.ι *ᵥ H₂.y := by
      rw [swapM_mulVec]; simp only [fm_sub_right, hyx, hyy, hyx', hyy']; ext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have sx' : S *ᵥ (H'.ι *ᵥ H₂.x) = H'.x := by
      rw [swapM_mulVec]; simp only [fm_sub_right, hx'x, hx'y, hx'x', hx'y']; ext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have sy' : S *ᵥ (H'.ι *ᵥ H₂.y) = H'.y := by
      rw [swapM_mulVec]; simp only [fm_sub_right, hy'x, hy'y, hy'x', hy'y']; ext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have scol : S * (H'.ι * H₂.ι) = H'.ι * H₂.ι := by
      apply mul_eq_self
      intro j
      rw [← Matrix.mulVec_mulVec, swapM_mulVec]
      simp only [fm_sub_right, cX j, cY j, cX' j, cY' j, sub_zero, zero_smul, add_zero]
    let gE : GL (Fin (a + (b + 2))) E := ⟨S, S, hSS, hSS⟩
    have hU : Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) gE ∈ GlobalTheory.WeilM.UG (cA σ) (incM F G.W.J) := by
      show (S.map (inclR (F := F) (AF F)))ᵀ * incM F G.W.J * (S.map (inclR (F := F) (AF F))).map (cA σ) = incM F G.W.J
      have e1 : (S.map (inclR (F := F) (AF F))).map (cA σ) = (S.map c).map (inclR (F := F) (AF F)) := by
        ext k l; simp only [Matrix.map_apply]; exact cA_inclR σ _
      rw [e1]
      show (S.map (inclR (F := F) (AF F)))ᵀ * G.W.J.map (inclR (F := F) (AF F)) * (S.map c).map (inclR (F := F) (AF F)) =
        G.W.J.map (inclR (F := F) (AF F))
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hSU]
    let w : UA σ G.W.J := ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) gE, hU⟩
    have hmat : mat w = S.map (inclR (F := F) (AF F)) := rfl
    refine ⟨w, Subgroup.mem_subgroupOf.2 ⟨gE, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmat, map_inc_mulVec, sx]
    · rw [hmat, map_inc_mulVec, sy]
    · rw [hmat, map_inc_mulVec, sx']
    · rw [hmat, map_inc_mulVec, sy']
    · rw [hmat]
      show S.map (inclR (F := F) (AF F)) * (H'.ι * H₂.ι).map (inclR (F := F) (AF F)) = (H'.ι * H₂.ι).map (inclR (F := F) (AF F))
      rw [← Matrix.map_mul, scol]
  ·
    let ca : AE F E →+* AE F E := (cA σ).toRingHom
    have hca : ∀ z, ca (ca z) = z := fun z => cA_invol hσ z
    have hJA : ∀ i j, ca (incM F G.W.J j i) = -incM F G.W.J i j := by
      intro i j
      simp only [ca, incM, Matrix.map_apply, cAr_inclR, hT.geo.hW.skew, map_neg]
    have inc : ∀ p q r, fm c G.W.J p q = r →
        fm ca (incM F G.W.J) (incV F p) (incV F q) = inclR (F := F) (AF F) r := by
      intro p q r h
      rw [fm_inc]
      have h' : form σ G.W.J p q = r := h
      rw [h']
    have hPP : fm ca (incM F G.W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [inc _ _ _ hxx, map_zero]
    have hQQ : fm ca (incM F G.W.J) (incV F (H'.ι *ᵥ H₂.y)) (incV F (H'.ι *ᵥ H₂.y)) = 0 := by
      rw [inc _ _ _ hy'y', map_zero]
    have hPQ : fm ca (incM F G.W.J) (incV F H'.x) (incV F (H'.ι *ᵥ H₂.y)) = 0 := by rw [inc _ _ _ hxy', map_zero]
    let N : AE F E → Matrix _ _ (AE F E) := fun t => shM ca (incM F G.W.J) (incV F H'.x) (incV F (H'.ι *ᵥ H₂.y)) t
    have hN : ∀ t, N t * N (-t) = 1 := fun t => shM_mul hca hJA hPP hQQ hPQ t
    have hN' : ∀ t, N (-t) * N t = 1 := fun t => by simpa using hN (-t)
    have hNU : ∀ t, ⟨N t, N (-t), hN t, hN' t⟩ ∈ GlobalTheory.WeilM.UG (cA σ) (incM F G.W.J) := fun t =>
      shM_unitary hca hJA hPP hQQ hPQ t
    refine ⟨fun t => ⟨⟨N t, N (-t), hN t, hN' t⟩, hNU t⟩, fun t => ?_⟩
    have hm : mat (⟨⟨N t, N (-t), hN t, hN' t⟩, hNU t⟩ : UA σ G.W.J) = N t := rfl
    simp only [hm]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show shM ca _ _ _ t *ᵥ _ = _
      rw [shM_mulVec, hPQ, hPP]; simp
    · show shM ca _ _ _ t *ᵥ _ = _
      rw [shM_mulVec, inc _ _ _ hx'y', inc _ _ _ hx'x, map_one, map_zero]; simp
    · show shM ca _ _ _ t *ᵥ _ = _
      rw [shM_mulVec, hQQ, inc _ _ _ hy'x, map_zero]; simp
    · show shM ca _ _ _ t *ᵥ _ = _
      rw [shM_mulVec, inc _ _ _ hyy', inc _ _ _ hyx, map_zero, map_neg, map_one]
      ext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero, zero_mul, add_zero]
      rw [show ca t = cA σ t from rfl]; ring
    · apply mul_eq_self
      intro j
      rw [incM_mulVec_single, ← Matrix.mulVec_mulVec]
      show shM ca _ _ _ t *ᵥ _ = _
      rw [shM_mulVec, inc _ _ _ (cY' j), inc _ _ _ (cX j), map_zero]; simp
