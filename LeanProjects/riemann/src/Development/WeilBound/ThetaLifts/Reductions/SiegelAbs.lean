import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd rId_inf)

namespace PositivityTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

variable (F E) in

def rIdU [IsTotallyReal F] (c : ℝ) : (AF F ⊗[F] E)ˣ where
  val := algebraMap (AF F) (AF F ⊗[F] E) (rId F c)
  inv := algebraMap (AF F) (AF F ⊗[F] E) (rId F (-c))
  val_inv := by rw [← map_mul, ← rId_add, add_neg_cancel, rId_zero', map_one]
  inv_val := by rw [← map_mul, ← rId_add, neg_add_cancel, rId_zero', map_one]

theorem val_rIdU [IsTotallyReal F] (c : ℝ) :
    (rIdU F E c : AF F ⊗[F] E) = algebraMap (AF F) (AF F ⊗[F] E) (rId F c) := rfl

theorem inv_rIdU [IsTotallyReal F] (c : ℝ) :
    (↑(rIdU F E c)⁻¹ : AF F ⊗[F] E) = algebraMap (AF F) (AF F ⊗[F] E) (rId F (-c)) := rfl

theorem card_infinitePlace [IsTotallyReal F] : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
  have h2 := IsTotallyReal.nrComplexPlaces_eq_zero (K := F)
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

theorem norm_evInf_rId [IsTotallyReal F] (w : InfinitePlace F) (c : ℝ) : ‖evInf F w (rId F c)‖ = Real.exp c := by
  have e := rId_inf (F := F) w c
  have e2 : evInf F w (rId F c) = (rId F c).1 w := rfl
  rw [e2, ← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) ((rId F c).1 w), e]
  simp [Real.abs_exp]

theorem absE_rIdU [IsTotallyReal F] (h2 : Module.finrank F E = 2) (c : ℝ) :
    (GlobalTheory.Doubling.absE F E (rIdU F E c) : ℝ) = Real.exp (2 * Module.finrank ℚ F * c) := by
  haveI : Nontrivial (AF F) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (evInf F w).toRingHom.domain_nontrivial
  have hn : Algebra.norm (AF F) (rIdU F E c : AF F ⊗[F] E) = rId F c ^ 2 := by
    rw [val_rIdU, Algebra.norm_algebraMap, Module.finrank_baseChange, h2]
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v (rIdU F E c)) = 1 := fun v => by
    rw [GlobalTheory.Doubling.absEv_unitFin, hn, map_pow]
    have e : evFin F v (rId F c) = 1 := by
      rw [evFin, AlgHom.comp_apply, show sndA F (rId F c) = 1 from rId_snd c, map_one]
    rw [e, one_pow, nnnorm_one]
  have hm : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]
  have hw : ∀ w : InfinitePlace F,
      (GlobalTheory.Doubling.absEw F E w (GlobalTheory.Doubling.unitInf F E w (rIdU F E c)) : ℝ) = Real.exp (2 * c) := fun w => by
    rw [GlobalTheory.Doubling.absEw_unitInf, hn, map_pow, hm, pow_one, coe_nnnorm, norm_pow, norm_evInf_rId, ← Real.exp_nat_mul]
    norm_num
  rw [GlobalTheory.Doubling.absE_apply, finprod_eq_one_of_forall_eq_one hfin, mul_one, NNReal.coe_prod,
    Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, card_infinitePlace,
    ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem pos_hom' {H : Type} [Group H] (δ : H →* ℝ≥0) (p : H) : 0 < δ p := by
  have e : δ p * δ p⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at e; exact zero_ne_one e

variable (σ) in
theorem sigRA_sigRA (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, sigma_sigma h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigRA_inclR (e : E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR {a b : Type} (P : Matrix a b E) :
    (Formalism.UG.cT (σ : E →+* E) P).map (inclR (F := F) (AF F)) = Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (P.map (inclR (F := F) (AF F))) :=
  Matrix.ext fun i j => by simp [cT, sigRA_inclR]

structure PFr {R : Type} [CommRing R] (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R) (Xm Ym : Matrix (Fin n) (Fin r) R) :
    Prop where
  ss : ∀ x, s (s x) = x
  herm : cT s Jm = Jm
  xx : cT s Xm * Jm * Xm = 0
  yy : cT s Ym * Jm * Ym = 0
  xy : cT s Xm * Jm * Ym = 1

section PFr

variable {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R} {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem PFr.cc (hF : PFr s Jm Xm Ym) {a b : Type} (P : Matrix a b R) : cT s (cT s P) = P :=
  Matrix.ext fun _ _ => hF.ss _

theorem PFr.yx (hF : PFr s Jm Xm Ym) : cT s Ym * Jm * Xm = 1 := by
  have := congrArg (cT s) hF.xy
  rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hF.cc, hF.herm, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this

theorem pgram_unitary {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm) {a b : Type}
    (P : Matrix (Fin n) a R) (Q : Matrix (Fin n) b R) : cT s (g * P) * Jm * (g * Q) = cT s P * Jm * Q := by
  conv_rhs => rw [← hg]
  simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]

theorem PFr.inv_coef (hF : PFr s Jm Xm Ym) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm)
    {B : Matrix (Fin r) (Fin r) R} (hB : g * Xm = Xm * B) : cT s (cT s Xm * Jm * (g * Ym)) * B = 1 := by
  have h2 : cT s B * (cT s Xm * Jm * (g * Ym)) = 1 := by
    rw [← hF.xy, ← pgram_unitary hg Xm Ym, hB, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  have := congrArg (cT s) h2
  rwa [Formalism.UG.cT_mul, hF.cc, Formalism.UG.cT_one] at this

def coefM (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R) (Xm Ym : Matrix (Fin n) (Fin r) R) (g : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin r) (Fin r) R :=
  cT s Ym * Jm * (g * Xm)

end PFr

theorem pfrA (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y) := by
  refine ⟨sigRA_sigRA σ h, ?_, ?_, ?_, ?_⟩
  · have e : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
    unfold JR
    rw [← cT_map_inclR, e]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

theorem unitaryA_matHom (p : GAd σ J) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (matHom _ σ J p).1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J * (matHom _ σ J p).1 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J :=
  (show ↥(HR (AF F) σ J) from p).2

variable (σ J X Y) in

def Bm (p : GAd σ J) : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
  coefM (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y)
    (matHom _ σ J p).1

section Bm

variable (hF : PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y))
include hF

theorem Bm_eq {p : GAd σ J} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (e : (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X = GlobalTheory.SiegelSet.adMat F X * B) : Bm σ J X Y p = B := by
  rw [Bm, coefM, e, ← Matrix.mul_assoc, hF.yx, Matrix.one_mul]

theorem mem_minPar_iff {p : GAd σ J} : p ∈ minPar σ J X ↔
    (Bm σ J X Y p).BlockTriangular id ∧ (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X = GlobalTheory.SiegelSet.adMat F X * Bm σ J X Y p := by
  constructor
  · rintro ⟨B, hB, e⟩
    rw [Bm_eq hF e]
    exact ⟨hB, e⟩
  · rintro ⟨hB, e⟩
    exact ⟨_, hB, e⟩

theorem Bm_mul {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) :
    Bm σ J X Y (p * q) = Bm σ J X Y p * Bm σ J X Y q := by
  have ep := ((mem_minPar_iff hF).1 hp).2
  have eq := ((mem_minPar_iff hF).1 hq).2
  apply Bm_eq hF
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, eq, ← Matrix.mul_assoc, ep, Matrix.mul_assoc]

theorem Bm_one : Bm σ J X Y (1 : GAd σ J) = 1 :=
  Bm_eq hF (by rw [map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])

end Bm

theorem diag_mul_bt {R : Type} [CommRing R] {B C : Matrix (Fin r) (Fin r) R} (hB : B.BlockTriangular id)
    (hC : C.BlockTriangular id) (i : Fin r) : (B * C) i i = B i i * C i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hl | hl
    · rw [hB hl, zero_mul]
    · rw [hC hl, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem mul_mem_minimal_parabolic {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) :
    p * q ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  obtain ⟨C, hC, e'⟩ := hq
  refine ⟨B * C, hB.mul hC, ?_⟩
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Matrix.mul_assoc]

theorem inv_mem_minimal_parabolic (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) : p⁻¹ ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  obtain ⟨Q, h3⟩ : ∃ Q, Q * B = 1 := ⟨_, (pfrA h hJ hW).inv_coef (unitaryA_matHom p) e⟩
  have h4 : B * Q = 1 := mul_eq_one_comm.1 h3
  haveI : Invertible B := ⟨Q, h3, h4⟩
  have hinv : B⁻¹ = Q := Matrix.inv_eq_left_inv h3
  refine ⟨Q, by rw [← hinv]; exact Matrix.blockTriangular_inv_of_blockTriangular hB, ?_⟩
  have e2 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  calc (matHom _ σ J p⁻¹).1 * GlobalTheory.SiegelSet.adMat F X = (matHom _ σ J p⁻¹).1 * (GlobalTheory.SiegelSet.adMat F X * (B * Q)) := by
        rw [h4, Matrix.mul_one]
    _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X * Q := by
        rw [← Matrix.mul_assoc (GlobalTheory.SiegelSet.adMat F X), ← e]
        simp only [Matrix.mul_assoc]
    _ = GlobalTheory.SiegelSet.adMat F X * Q := by rw [e2, Matrix.one_mul]

theorem continuous_matHom_val : Continuous fun p : GAd σ J => (matHom _ σ J p).1 :=
  Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous

theorem continuous_Bm : Continuous (Bm σ J X Y) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  unfold Bm coefM
  exact continuous_const.matrix_mul ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const)

theorem isClosed_minimal_parabolic (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (minPar σ J X) := by
  have hF := pfrA h hJ hW
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hBc : Continuous (Bm σ J X Y) := continuous_Bm
  have e : minPar σ J X = {p | (Bm σ J X Y p).BlockTriangular id} ∩
      {p | (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X = GlobalTheory.SiegelSet.adMat F X * Bm σ J X Y p} := by
    ext p
    exact mem_minPar_iff hF
  have e' : {p : GAd σ J | (Bm σ J X Y p).BlockTriangular id} =
      ⋂ i : Fin r, ⋂ j : Fin r, ⋂ (_ : j < i), {p | Bm σ J X Y p i j = 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.BlockTriangular, id]
  rw [e, e']
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (hBc.matrix_elem i j) continuous_const) ?_
  exact isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) (continuous_const.matrix_mul hBc)

variable (σ J X Y) in

def uU (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J} (hp : p ∈ minPar σ J X)
    (hp' : p⁻¹ ∈ minPar σ J X) (i : Fin r) : (AF F ⊗[F] E)ˣ where
  val := Bm σ J X Y p i i
  inv := Bm σ J X Y p⁻¹ i i
  val_inv := by
    have hF := pfrA h hJ hW
    rw [← diag_mul_bt ((mem_minPar_iff hF).1 hp).1 ((mem_minPar_iff hF).1 hp').1, ← Bm_mul hF hp hp',
      mul_inv_cancel, Bm_one hF, Matrix.one_apply_eq]
  inv_val := by
    have hF := pfrA h hJ hW
    rw [← diag_mul_bt ((mem_minPar_iff hF).1 hp').1 ((mem_minPar_iff hF).1 hp).1, ← Bm_mul hF hp' hp,
      inv_mul_cancel, Bm_one hF, Matrix.one_apply_eq]

theorem val_uU (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) (hp' : p⁻¹ ∈ minPar σ J X) (i : Fin r) :
    (uU σ J X Y h hJ hW hp hp' i : AF F ⊗[F] E) = Bm σ J X Y p i i := rfl

theorem minParOne_sub {p : GAd σ J} (hp : p ∈ minParOne σ J X) : p ∈ minPar σ J X :=
  let ⟨B, hB, e, _⟩ := hp
  ⟨B, hB, e⟩

variable (σ J X Y) in

def uP (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (P : Subgroup (GAd σ J))
    (hP : ∀ p, p ∈ P ↔ p ∈ minPar σ J X) (p : P) (i : Fin r) : (AF F ⊗[F] E)ˣ :=
  uU σ J X Y h hJ hW ((hP _).1 p.2) ((hP _).1 (P.inv_mem p.2)) i

theorem val_uP (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (P : Subgroup (GAd σ J))
    (hP : ∀ p, p ∈ P ↔ p ∈ minPar σ J X) (p : P) (i : Fin r) :
    (uP σ J X Y h hJ hW P hP p i : AF F ⊗[F] E) = Bm σ J X Y p.1 i i := rfl

theorem exists_torus_section (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (P : Subgroup (GAd σ J))
    (hP : ∀ p, p ∈ P ↔ p ∈ minPar σ J X) {a : (Fin r → ℝ) → GAd σ J} (hadd : ∀ s t, a (s + t) = a s * a t)
    (honX : ∀ t, (matHom _ σ J (a t)).1 * GlobalTheory.SiegelSet.adMat F X =
      GlobalTheory.SiegelSet.adMat F X * Matrix.diagonal (fun i => algebraMap (AF F) (AF F ⊗[F] E) (rId F (t i))))
    (ta : (Fin r → ℝ) → P) (hta : ∀ t, (ta t : GAd σ J) = a t) :
    ∃ τ : P → Fin r → ℝ, Continuous τ ∧ (∀ p q, τ (p * q) = τ p + τ q) ∧ (∀ t, τ (ta t) = t) ∧
      (∀ p (hp : p ∈ minParOne σ J X), τ ⟨p, (hP p).2 (minParOne_sub hp)⟩ = 0) ∧
      ∀ p : P, p.1 * (a (τ p))⁻¹ ∈ minParOne σ J X := by
  haveI := h.1
  have hF := pfrA h hJ hW
  have m1 : ∀ p : P, p.1 ∈ minPar σ J X := fun p => (hP _).1 p.2
  have hpos : ∀ x : (AF F ⊗[F] E)ˣ, (0 : ℝ) < GlobalTheory.Doubling.absE F E x := fun x => NNReal.coe_pos.2 (pos_hom' _ x)
  have h0 : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hd : (0 : ℝ) < 2 * (Module.finrank ℚ F : ℝ) := mul_pos two_pos (Nat.cast_pos.2 h0)
  have hu_mul : ∀ p q : P, ∀ i, uP σ J X Y h hJ hW P hP (p * q) i = uP σ J X Y h hJ hW P hP p i * uP σ J X Y h hJ hW P hP q i :=
    fun p q i => Units.ext (by
      rw [Units.val_mul, val_uP, val_uP, val_uP, Subgroup.coe_mul, Bm_mul hF (m1 p) (m1 q),
        diag_mul_bt ((mem_minPar_iff hF).1 (m1 p)).1 ((mem_minPar_iff hF).1 (m1 q)).1])
  have hcont : ∀ i, Continuous fun p : P => uP σ J X Y h hJ hW P hP p i := fun i => by
    have hBc : Continuous (Bm σ J X Y) := continuous_Bm
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (hBc.comp continuous_subtype_val).matrix_elem i i
    · exact (hBc.comp (continuous_subtype_val.comp continuous_inv)).matrix_elem i i
  have key : ∀ (p : P) (s : Fin r → ℝ), (∀ i, 2 * (Module.finrank ℚ F : ℝ) * s i =
      Real.log (GlobalTheory.Doubling.absE F E (uP σ J X Y h hJ hW P hP p i))) → p.1 * (a s)⁻¹ ∈ minParOne σ J X := by
    intro p s hs
    have ha0 : a 0 = 1 := by
      have e := hadd 0 0
      rw [add_zero] at e
      exact mul_left_cancel (e.symm.trans (mul_one _).symm)
    have hainv : (a s)⁻¹ = a (-s) := inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, ha0])
    have ep := ((mem_minPar_iff hF).1 (m1 p)).2
    have hBt := ((mem_minPar_iff hF).1 (m1 p)).1
    refine ⟨Bm σ J X Y p.1 * Matrix.diagonal (fun i => algebraMap (AF F) (AF F ⊗[F] E) (rId F ((-s) i))),
      hBt.mul (Matrix.blockTriangular_diagonal _), ?_, fun i => ⟨uP σ J X Y h hJ hW P hP p i * rIdU F E ((-s) i), ?_, ?_⟩⟩
    · rw [hainv, map_mul, Units.val_mul, Matrix.mul_assoc, honX, ← Matrix.mul_assoc, ep, Matrix.mul_assoc]
    · rw [Matrix.mul_diagonal, Units.val_mul, val_uP, val_rIdU]
    · apply NNReal.eq
      rw [map_mul, NNReal.coe_mul, absE_rIdU h.2.2.1, NNReal.coe_one, Pi.neg_apply, mul_neg, hs i, Real.exp_neg,
        Real.exp_log (hpos _), mul_inv_cancel₀ (hpos _).ne']
  refine ⟨fun p i => Real.log (GlobalTheory.Doubling.absE F E (uP σ J X Y h hJ hW P hP p i)) / (2 * (Module.finrank ℚ F : ℝ)),
    ?_, ?_, ?_, ?_, fun p => key p _ fun i => by dsimp only; field_simp⟩
  · exact continuous_pi fun i => (Continuous.log (NNReal.continuous_coe.comp
      (GlobalTheory.Doubling.continuous_absE.comp (hcont i))) fun p => (hpos _).ne').div_const _
  · intro p q
    funext i
    simp only [Pi.add_apply, hu_mul, map_mul, NNReal.coe_mul]
    rw [Real.log_mul (hpos _).ne' (hpos _).ne', add_div]
  · intro t
    funext i
    have e : uP σ J X Y h hJ hW P hP (ta t) i = rIdU F E (t i) := Units.ext (by
      rw [val_uP, val_rIdU, hta, Bm_eq hF (honX t), Matrix.diagonal_apply_eq])
    simp only [e]
    rw [absE_rIdU h.2.2.1, Real.log_exp, mul_div_cancel_left₀ _ hd.ne']
  · intro p hp
    funext i
    obtain ⟨B, -, e, hu⟩ := id hp
    obtain ⟨v, hv1, hv2⟩ := hu i
    have e2 : uP σ J X Y h hJ hW P hP ⟨p, (hP p).2 (minParOne_sub hp)⟩ i = v := Units.ext (by
      rw [val_uP, Bm_eq hF e, hv1])
    simp only [e2, hv2, NNReal.coe_one, Real.log_one, zero_div, Pi.zero_apply]

end PositivityTheory.ThKR

end
