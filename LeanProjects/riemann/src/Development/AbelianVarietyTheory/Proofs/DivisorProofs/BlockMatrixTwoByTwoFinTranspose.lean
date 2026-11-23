import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicWitt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {m n : ℕ}

abbrev cAl (D : D7) : AE D →ₐ[AF D.host.F] AE D := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig

abbrev UD (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) : Type := UA D.sp.cm.sig J

abbrev umat {k : ℕ} {J : Matrix (Fin k) (Fin k) D.host.E} (g : UD D J) : Mx D k k := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g

abbrev uinc (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) : UD D J →* GL (Fin k) (AE D) :=
  (UG (cAl D) (incM D.host.F J)).subtype

def cat {R : Type} (p y : Matrix (Fin m) (Fin n) R) : Matrix (Fin m) (Fin (n + n)) R :=
  (Matrix.fromCols p y).submatrix id finSumFinEquiv.symm

def cj (x : Mx D m n) : Mx D m n := x.map (cA D)

def pt (T : GL (Fin (n + n)) D.host.E) (q x : Mx D m n) : Mx D m (n + n) :=
  cat (cj q) (cj x) ⬝ (rat T.1 : Mx D (n + n) (n + n))ᵀ

def IsChartW {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} (T : GL (Fin (n + n)) D.host.E)
    (κ : UD D J₂ ≃* StdUnn.G D n) : Prop :=
  ∀ g, StdUnn.mat (κ g) = inBasis D.sp.cm.sig T g

def IsConjV (V : HSp D) (ι : UD D (-V.gram) ≃ₜ* GA D V) : Prop := ∀ h, mt V (ι h) = cj (umat h)

abbrev Dbx (V : HSp D) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (d : ℕ) : Type :=
  Darboux (symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂)) (Fin V.rank × Fin n × Fin d)

def IsCoord (V : HSp D) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} (T : GL (Fin (n + n)) D.host.E) {d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (co : Dbx V J₂ d) : Prop :=
  ∀ q x : Mx D V.rank n, (co.e (pt T q x)).1 = coord ε x ∧
    ∀ x' : Mx D V.rank n, coord ε x' ⬝ᵥ (co.e (pt T q x)).2 = -StdUnn.trA (Matrix.trace (StdUnn.inner V x' q))

def IsTrans {θ : InfFam D} {V : HSp D} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (ι : UD D (-V.gram) ≃ₜ* GA D V) (κ : UD D J₂ ≃* StdUnn.G D n)
    (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (om : UD D (-V.gram) × UD D J₂ →* Module.End ℂ ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ)) : Prop :=
  (∀ p, ∀ φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d), om p φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) ∧
  ∀ h g, ∀ φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d), ∀ Φ : schwartzA θ V.rank n, φ ∘ coord ε = Φ.1 →
    ∀ x : Mx D V.rank n, om (h, g) φ (coord ε x) = (ω (κ g) Φ).1 (mt V (ι h)⁻¹ ⬝ x)

theorem cAl_eq (z : AE D) : cAl D z = cA D z := GlobalTheory.IwLine.cA_eq_sigR _ z

theorem map_cAl {k l : ℕ} (x : Mx D k l) : x.map (cAl D) = cj x := by
  funext i j; exact cAl_eq _

theorem incM_eq {k l : ℕ} (J : Matrix (Fin k) (Fin l) D.host.E) : incM D.host.F J = rat J := rfl

theorem blk_eq {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : blk a b c d = StdUnn.blk4 a b c d := rfl

theorem adj_eq (x : Mx D m n) : adj x = (cj x)ᵀ := rfl

@[simp] theorem cj_cj (x : Mx D m n) : cj (cj x) = x := by
  funext i j; exact congrFun (congrFun (adj_adj x) i) j

@[simp] theorem cj_zero : cj (0 : Mx D m n) = 0 := by funext i j; exact map_zero (cA D)

@[simp] theorem cj_neg (x : Mx D m n) : cj (-x) = -cj x := by funext i j; exact map_neg (cA D) _

@[simp] theorem cj_add (x y : Mx D m n) : cj (x + y) = cj x + cj y := by funext i j; exact map_add (cA D) _ _

@[simp] theorem cj_one : cj (1 : Mx D n n) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cj_mul {l : ℕ} (x : Mx D l m) (y : Mx D m n) : cj (x ⬝ y) = cj x ⬝ cj y := Matrix.map_mul

theorem cj_transpose (x : Mx D m n) : cj xᵀ = (cj x)ᵀ := rfl

theorem cj_rat (M : Matrix (Fin m) (Fin n) D.host.E) : cj (rat M : Mx D m n) = rat (M.map D.sp.cm.sig) := rfl

theorem cat_mul_blk {R : Type} [CommRing R] (p y : Matrix (Fin m) (Fin n) R) (a b c d : Matrix (Fin n) (Fin n) R) :
    cat p y * StdUnn.blk4 a b c d = cat (p * a + y * c) (p * b + y * d) := by
  unfold cat StdUnn.blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]

theorem mul_cat {R : Type} [CommRing R] {l : ℕ} (h : Matrix (Fin l) (Fin m) R) (p y : Matrix (Fin m) (Fin n) R) :
    h * cat p y = cat (h * p) (h * y) := by
  unfold cat
  rw [← Matrix.mul_fromCols]
  rfl

theorem blockMatrixTwoByTwoFin_transpose {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) :
    (StdUnn.blk4 a b c d)ᵀ = StdUnn.blk4 aᵀ cᵀ bᵀ dᵀ := by
  unfold StdUnn.blk4
  rw [Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem exists_cat {R : Type} (u : Matrix (Fin m) (Fin (n + n)) R) : ∃ p y, u = cat p y := by
  refine ⟨(u.submatrix id finSumFinEquiv).toCols₁, (u.submatrix id finSumFinEquiv).toCols₂, ?_⟩
  unfold cat
  rw [Matrix.fromCols_toCols]
  simp

theorem cat_inj {R : Type} {p y p' y' : Matrix (Fin m) (Fin n) R} (h : cat p y = cat p' y') : p = p' ∧ y = y' := by
  have : Matrix.fromCols p y = Matrix.fromCols p' y' := by
    have := congrArg (fun u => u.submatrix id finSumFinEquiv) h
    simpa [cat] using this
  exact Matrix.fromCols_inj this

theorem rat_mul_inv (T : GL (Fin (n + n)) D.host.E) :
    (rat T.1 : Mx D (n + n) (n + n)) * rat (T⁻¹).1 = 1 := by
  rw [← rat_mul, T.mul_inv, rat_one]

theorem rat_inv_mul (T : GL (Fin (n + n)) D.host.E) :
    (rat (T⁻¹).1 : Mx D (n + n) (n + n)) * rat T.1 = 1 := by
  rw [← rat_mul, T.inv_mul, rat_one]

theorem exists_pt (T : GL (Fin (n + n)) D.host.E) (u : Mx D m (n + n)) : ∃ q x, u = pt T q x := by
  obtain ⟨p, y, h⟩ := exists_cat (u * (rat (T⁻¹).1 : Mx D (n + n) (n + n))ᵀ)
  refine ⟨cj p, cj y, ?_⟩
  rw [pt, cj_cj, cj_cj, ← h, Matrix.mul_assoc, ← Matrix.transpose_mul, rat_mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem pt_inj {T : GL (Fin (n + n)) D.host.E} {q x q' x' : Mx D m n} (h : pt T q x = pt T q' x') : q = q' ∧ x = x' := by
  have h1 := congrArg (fun u : Mx D m (n + n) => (u ⬝ (rat (T⁻¹).1 : Mx D (n + n) (n + n))ᵀ : Mx D m (n + n))) h
  simp only [pt, Matrix.mul_assoc, ← Matrix.transpose_mul, rat_inv_mul, Matrix.transpose_one, Matrix.mul_one] at h1
  obtain ⟨h2, h3⟩ := cat_inj h1
  exact ⟨by simpa using congrArg cj h2, by simpa using congrArg cj h3⟩

theorem mul_pt (T : GL (Fin (n + n)) D.host.E) (h : Mx D m m) (q x : Mx D m n) :
    (h ⬝ pt T q x : Mx D m (n + n)) = pt T (cj h ⬝ q) (cj h ⬝ x) := by
  rw [pt, pt, ← Matrix.mul_assoc, mul_cat, cj_mul, cj_mul, cj_cj]

variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n}

theorem IsChartW.mul_eq (hκ : IsChartW T κ) (g : UD D J₂) :
    umat g * rat T.1 = (rat T.1 : Mx D (n + n) (n + n)) * StdUnn.mat (κ g) := by
  rw [hκ g, inBasis, incM_eq, incM_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, rat_mul_inv, Matrix.one_mul]

theorem IsChartW.pt_mul (hκ : IsChartW T κ) {g : UD D J₂} {a b c d : Mx D n n}
    (hg : StdUnn.mat (κ g) = StdUnn.blk4 a b c d) (q x : Mx D m n) :
    (pt T q x ⬝ (umat g)ᵀ : Mx D m (n + n)) = pt T (q ⬝ adj a + x ⬝ adj b) (q ⬝ adj c + x ⬝ adj d) := by
  rw [pt, pt, Matrix.mul_assoc, ← Matrix.transpose_mul, hκ.mul_eq, Matrix.transpose_mul, ← Matrix.mul_assoc, hg,
    blockMatrixTwoByTwoFin_transpose, cat_mul_blk]
  simp only [cj_add, cj_mul, adj_eq, cj_transpose, cj_cj]

section Witt

theorem block_matrix_map {R S : Type} (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (StdUnn.blk4 a b c d).map f = StdUnn.blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold StdUnn.blk4
  rw [← Matrix.fromBlocks_map]; rfl

theorem rat_fromBlocks_map (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (rat (StdUnn.blk4 a b c d) : Mx D (n + n) (n + n)) = StdUnn.blk4 (rat a) (rat b) (rat c) (rat d) := block_matrix_map _ _ _ _ _

theorem rat_Jst : (rat (StdUnn.Jst D n) : Mx D (n + n) (n + n)) = StdUnn.blk4 0 1 (-1) 0 := by
  rw [StdUnn.Jst, rat_fromBlocks_map, rat_zero, rat_neg, rat_one]

variable {J : Matrix (Fin n) (Fin n) D.host.E}

theorem sig_sig (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := star_star x

theorem dblGram_eq (J : Matrix (Fin n) (Fin n) D.host.E) : dblGram finSumFinEquiv J = StdUnn.blk4 J 0 0 (-J) := rfl

theorem gram_witt (hJ : ∀ i j, D.sp.cm.sig (J j i) = -J i j) (hT : IsWittBasis D.sp.cm.sig J 1 T) :
    T.1ᵀ * dblGram finSumFinEquiv J * T.1.map D.sp.cm.sig = StdUnn.Jst D n := by
  obtain ⟨Z, hZ, hT⟩ := hT
  rw [one_smul] at hZ
  have hJ' : Jᴴ = -J := by funext i j; exact hJ i j
  have hs : Z.map D.sp.cm.sig = Zᴴᵀ := rfl
  have h2 : (2 : D.host.E) • (Zᵀ * J) = -1 := by
    have := congrArg Matrix.conjTranspose hZ
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hJ', hs, Matrix.conjTranspose_one, star_ofNat] at this
    have e : Zᴴᵀᴴ = Zᵀ := by funext i j; exact star_star _
    rw [e, Matrix.mul_neg, smul_neg] at this
    exact neg_eq_iff_eq_neg.1 this
  have hm : (StdUnn.blk4 1 Z 1 (-Z)).map D.sp.cm.sig = StdUnn.blk4 1 (Z.map D.sp.cm.sig) 1 (-Z.map D.sp.cm.sig) := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [StdUnn.blk4, Matrix.one_apply, apply_ite, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  rw [hT, blk_eq, hm, dblGram_eq, blockMatrixTwoByTwoFin_transpose, StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Jst]
  rw [two_smul] at hZ h2
  congr 1 <;> simp [hZ, h2, Matrix.transpose_neg]

theorem pt_witt (hT : IsWittBasis D.sp.cm.sig J 1 T) : ∃ Z Z' : Mx D n n, Z * Z' = 1 ∧ ∀ (m : ℕ) (q x : Mx D m n),
    pt T q x = cat (cj q + cj x ⬝ Z) (cj q - cj x ⬝ Z) := by
  obtain ⟨Z, hZ, hT⟩ := hT
  rw [one_smul, ← Matrix.smul_mul] at hZ
  have h1 : (rat ((2 : D.host.E) • J) : Mx D n n) * cj (rat Z) = 1 := by rw [cj_rat, ← rat_mul, hZ, rat_one]
  have h2 : (cj (rat ((2 : D.host.E) • J)) : Mx D n n) * rat Z = 1 := by
    have := congrArg cj h1
    rwa [cj_mul, cj_cj, cj_one] at this
  refine ⟨(rat Z)ᵀ, (cj (rat ((2 : D.host.E) • J)))ᵀ, by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one], fun m q x => ?_⟩
  have hm : (rat (StdUnn.blk4 1 Z 1 (-Z)) : Mx D (n + n) (n + n)) = StdUnn.blk4 1 (rat Z) 1 (-rat Z) := by
    rw [rat_fromBlocks_map, rat_one, rat_neg]
  rw [pt, hT, blk_eq, hm, blockMatrixTwoByTwoFin_transpose, cat_mul_blk]
  simp [sub_eq_add_neg, Matrix.transpose_neg]

theorem cat_row {R : Type} (p y : Matrix (Fin m) (Fin n) R) (i : Fin m) :
    cat p y i = pairVec finSumFinEquiv (p i) (y i) := by
  funext j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem eq_zero_of_add_self {z : Mx D m n} (h : z + z = 0) : z = 0 := by
  rw [← half_smul_add z, ← smul_add, h, smul_zero]

theorem pt_anti_iff (hT : IsWittBasis D.sp.cm.sig J 1 T) (q x : Mx D m n) :
    (∀ i, pt T q x i ∈ antiSub (AE D) finSumFinEquiv) ↔ q = 0 := by
  obtain ⟨Z, Z', -, h⟩ := pt_witt hT
  simp only [h, cat_row, pairVec_mem_antiSub]
  constructor
  · intro h1
    have h2 : cj q + cj x ⬝ Z = -(cj q - cj x ⬝ Z) := funext h1
    have h3 : cj q + cj q = 0 := by
      have := eq_neg_iff_add_eq_zero.1 h2
      rw [← this]; abel
    simpa using congrArg cj (eq_zero_of_add_self h3)
  · rintro rfl i
    rw [cj_zero, zero_add, zero_sub]
    exact (neg_neg _).symm

theorem pt_diag_iff (hT : IsWittBasis D.sp.cm.sig J 1 T) (q x : Mx D m n) :
    (∀ i, pt T q x i ∈ diagSub (AE D) finSumFinEquiv) ↔ x = 0 := by
  obtain ⟨Z, Z', hZ, h⟩ := pt_witt hT
  simp only [h, cat_row, pairVec_mem_diagSub]
  constructor
  · intro h1
    have h2 : cj q + cj x ⬝ Z = cj q - cj x ⬝ Z := funext h1
    have h3 : (cj x ⬝ Z + cj x ⬝ Z : Mx D m n) = 0 := by
      have := sub_eq_zero.2 h2
      rw [← this]; abel
    have h4 := congrArg (fun u : Mx D m n => (u ⬝ Z' : Mx D m n)) (eq_zero_of_add_self h3)
    simp only [Matrix.mul_assoc, hZ, Matrix.mul_one, Matrix.zero_mul] at h4
    simpa using congrArg cj h4
  · rintro rfl i
    simp

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {k l : ℕ}
    (JA : Matrix (Fin k) (Fin k) A) (JB : Matrix (Fin l) (Fin l) A) (x y : Matrix (Fin k) (Fin l) A) :
    GlobalTheory.WeilM.hTens c JA JB x y = Matrix.trace (xᵀ * (JA * (y.map c * JBᵀ))) := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem trace_cat {R : Type} [CommRing R] (p y p' y' : Matrix (Fin m) (Fin n) R) :
    Matrix.trace ((cat p y)ᵀ * cat p' y') = Matrix.trace (pᵀ * p') + Matrix.trace (yᵀ * y') := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem trace_pair {R : Type} [CommRing R] (Q : Matrix (Fin m) (Fin m) R) (p y q x : Matrix (Fin m) (Fin n) R)
    (S S' L : Matrix (Fin (n + n)) (Fin (n + n)) R) (h : S'ᵀ * (Lᵀ * S) = (StdUnn.blk4 0 1 (-1) 0)ᵀ) :
    -1 * Matrix.trace ((cat p y * Sᵀ)ᵀ * (-Q * (cat q x * S'ᵀ * Lᵀ))) =
      Matrix.trace (pᵀ * (Q * x)) - Matrix.trace (yᵀ * (Q * q)) := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc S, Matrix.trace_mul_comm S]
  simp only [Matrix.mul_assoc]
  rw [h, blockMatrixTwoByTwoFin_transpose, cat_mul_blk, mul_cat, trace_cat]
  simp [Matrix.transpose_neg, sub_eq_add_neg, add_comm]

theorem symp_pt (V : HSp D) (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = StdUnn.Jst D n) (q x q' x' : Mx D V.rank n) :
    symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂) (pt T q x) (pt T q' x') =
      StdUnn.trA (Matrix.trace (StdUnn.inner V q x')) - StdUnn.trA (Matrix.trace (StdUnn.inner V x q')) := by
  have h1 : (cj (rat T.1))ᵀ * ((rat J₂ : Mx D (n + n) (n + n))ᵀ * rat T.1) = (StdUnn.blk4 0 1 (-1) 0)ᵀ := by
    rw [← rat_Jst, ← hG, rat_mul, rat_mul, Matrix.transpose_mul, Matrix.transpose_mul, cj_rat]; rfl
  have h2 : cj (cat (cj q') (cj x')) = cat q' x' := by
    have : cj (cat (cj q') (cj x')) = cat (cj (cj q')) (cj (cj x')) := by
      funext i j
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp [cat, cj, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
    rw [this, cj_cj, cj_cj]
  have h3 : cj (pt T q' x') = cat q' x' ⬝ (cj (rat T.1 : Mx D (n + n) (n + n)))ᵀ := by
    rw [pt, cj_mul, h2, cj_transpose]
  rw [symp, hTens_eq_trace, map_cAl, h3, incM_eq, incM_eq, pt, rat_neg]
  exact (congrArg StdUnn.trA (trace_pair _ _ _ _ _ _ _ _ h1)).trans (map_sub (Algebra.trace _ _) _ _)

theorem trA_cA (z : AE D) : StdUnn.trA (cA D z) = StdUnn.trA z := by
  let e : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom (cAl D) (cAl D)
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
  rw [← cAl_eq]
  exact Algebra.trace_eq_of_algEquiv e z

theorem trA_inner_comm (V : HSp D) (x y : Mx D V.rank n) :
    StdUnn.trA (Matrix.trace (StdUnn.inner V x y)) = StdUnn.trA (Matrix.trace (StdUnn.inner V y x)) := by
  rw [← trA_cA, ← trace_adj, StdUnn.inner, StdUnn.inner, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

end Witt

def coordL {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (m n : ℕ) :
    Mx D m n ≃ₗ[AF D.host.F] (Fin m × Fin n × Fin d → AF D.host.F) where
  toFun := coord ε
  map_add' x y := by funext p; simp [coord]
  map_smul' a x := by funext p; simp [coord]
  invFun c := Matrix.of fun i j => (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.symm fun k => c (i, j, k)
  left_inv y := by
    funext i j
    exact (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.symm_apply_apply (y i j)
  right_inv c := by
    funext p
    exact congrFun ((Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.apply_symm_apply fun k => c (p.1, p.2.1, k)) p.2.2

theorem coordL_apply {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) : coordL ε m n x = coord ε x := rfl

theorem coord_bijective {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Function.Bijective (coord ε : Mx D m n → _) := (coordL ε m n).bijective

theorem coord_zero {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) : coord ε (0 : Mx D m n) = 0 :=
  (coordL ε m n).map_zero

end GlobalTheory.SWLink

end
