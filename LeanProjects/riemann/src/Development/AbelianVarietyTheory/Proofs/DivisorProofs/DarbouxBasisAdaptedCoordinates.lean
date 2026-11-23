import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

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
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.Darb

section General

variable {F E A ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [FiniteDimensional F E]

theorem trace_one_tmul (z : E) :
    Algebra.trace A (A ⊗[F] E) (1 ⊗ₜ z) = algebraMap F A (Algebra.trace F E z) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext y
  simp

theorem sum_repr_dual [Algebra.IsSeparable F E] [Fintype ι] [DecidableEq ι] (ε : Module.Basis ι F E) (a b : A ⊗[F] E) :
    ∑ k, (Algebra.TensorProduct.basis A ε).repr a k * (Algebra.TensorProduct.basis A ε.traceDual).repr b k =
      Algebra.trace A (A ⊗[F] E) (a * b) := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis A ε).sum_repr a, ← (Algebra.TensorProduct.basis A ε.traceDual).sum_repr b,
    Finset.sum_mul_sum]
  simp only [map_sum, smul_mul_smul_comm, map_smul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, trace_one_tmul, Module.Basis.trace_mul_traceDual, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]

end General

variable {D : D7} {m n d : ℕ}

theorem cj_smul (a : AF D.host.F) (x : Mx D m n) : cj (a • x) = a • cj x := by
  rw [← map_cAl, ← map_cAl]
  funext i j
  exact map_smul (cAl D) a (x i j)

theorem cat_add {R : Type} [Add R] (p y p' y' : Matrix (Fin m) (Fin n) R) :
    cat (p + p') (y + y') = cat p y + cat p' y' := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem cat_smul {S R : Type} [SMul S R] (a : S) (p y : Matrix (Fin m) (Fin n) R) :
    cat (a • p) (a • y) = a • cat p y := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem cat_map {S R : Type} (f : R → S) (p y : Matrix (Fin m) (Fin n) R) :
    (cat p y).map f = cat (p.map f) (y.map f) := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

def ptLin (T : GL (Fin (n + n)) D.host.E) (m : ℕ) : (Mx D m n × Mx D m n) →ₗ[AF D.host.F] Mx D m (n + n) where
  toFun p := pt T p.1 p.2
  map_add' p p' := by
    rw [Prod.fst_add, Prod.snd_add, pt, pt, pt, cj_add, cj_add, cat_add, Matrix.add_mul]
  map_smul' a p := by
    rw [Prod.smul_fst, Prod.smul_snd, pt, pt, cj_smul, cj_smul, cat_smul, Matrix.smul_mul, RingHom.id_apply]

def ptEquiv (T : GL (Fin (n + n)) D.host.E) (m : ℕ) : (Mx D m n × Mx D m n) ≃ₗ[AF D.host.F] Mx D m (n + n) :=
  LinearEquiv.ofBijective (ptLin T m)
    ⟨fun _ _ h => Prod.ext (pt_inj h).1 (pt_inj h).2, fun u => by
      obtain ⟨q, x, h⟩ := exists_pt T u
      exact ⟨(q, x), h.symm⟩⟩

theorem ptEquiv_symm (T : GL (Fin (n + n)) D.host.E) (q x : Mx D m n) : (ptEquiv T m).symm (pt T q x) = (q, x) :=
  (ptEquiv T m).symm_apply_eq.2 rfl

def gramEquiv (V : HSp D) (n : ℕ) : Mx D V.rank n ≃ₗ[AF D.host.F] Mx D V.rank n where
  toFun q := cj (-(gA V ⬝ q))
  map_add' q q' := by rw [Matrix.mul_add, neg_add, cj_add]
  map_smul' a q := by rw [Matrix.mul_smul, ← smul_neg, cj_smul, RingHom.id_apply]
  invFun y := -(giA V ⬝ cj y)
  left_inv q := by
    show -(giA V ⬝ cj (cj (-(gA V ⬝ q))) : Mx D V.rank n) = q
    rw [cj_cj, Matrix.mul_neg, neg_neg, giA_gA_cancel]
  right_inv y := by
    show cj (-(gA V ⬝ (-(giA V ⬝ cj y) : Mx D V.rank n))) = y
    rw [Matrix.mul_neg, neg_neg, gA_giA_cancel, cj_cj]

def coEquiv (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Mx D V.rank (n + n) ≃ₗ[AF D.host.F]
      (Fin V.rank × Fin n × Fin d → AF D.host.F) × (Fin V.rank × Fin n × Fin d → AF D.host.F) :=
  (ptEquiv T V.rank).symm ≪≫ₗ LinearEquiv.prodComm _ _ _ ≪≫ₗ
    (coordL ε V.rank n).prodCongr (gramEquiv V n ≪≫ₗ coordL ε.traceDual V.rank n)

theorem coEquiv_pt (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (q x : Mx D V.rank n) : coEquiv V T ε (pt T q x) = (coord ε x, coord ε.traceDual (cj (-(gA V ⬝ q)))) := by
  rw [coEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, ptEquiv_symm]
  rfl

theorem coord_dot (ε : Module.Basis (Fin d) D.host.F D.host.E) (x y : Mx D m n) :
    coord ε x ⬝ᵥ coord ε.traceDual (cj y) = StdUnn.trA (Matrix.trace (adj x ⬝ y : Mx D n n)) := by
  have h : Matrix.trace (adj x ⬝ y : Mx D n n) = ∑ i, ∑ j, cA D (x i j) * y i j := by
    rw [Finset.sum_comm]; rfl
  rw [h, StdUnn.trA, map_sum, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (sum_repr_dual ε (x i j) (cA D (y i j))).trans ?_
  refine Eq.trans ?_ (trA_cA _)
  rw [map_mul (cA D), cA_cA]

theorem coord_dot_gram (V : HSp D) (ε : Module.Basis (Fin d) D.host.F D.host.E) (x q : Mx D V.rank n) :
    coord ε x ⬝ᵥ coord ε.traceDual (cj (-(gA V ⬝ q))) = -StdUnn.trA (Matrix.trace (StdUnn.inner V x q)) := by
  rw [coord_dot, Matrix.mul_neg, Matrix.trace_neg, StdUnn.trA, map_neg]
  rfl

theorem coord_rat (ε : Module.Basis (Fin d) D.host.F D.host.E) (γ : Matrix (Fin m) (Fin n) D.host.E) :
    coord ε (rat γ : Mx D m n) = fun p => algebraMap D.host.F (AF D.host.F) (ε.repr (γ p.1 p.2.1) p.2.2) := by
  funext p
  show (Algebra.TensorProduct.basis (AF D.host.F) ε).repr (1 ⊗ₜ γ p.1 p.2.1) p.2.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem exists_pt_rat (T : GL (Fin (n + n)) D.host.E) (u : Matrix (Fin m) (Fin (n + n)) D.host.E) :
    ∃ q x : Matrix (Fin m) (Fin n) D.host.E, (rat u : Mx D m (n + n)) = pt T (rat q) (rat x) := by
  obtain ⟨p, y, h⟩ := exists_cat (u * (T⁻¹).1ᵀ)
  refine ⟨p.map D.sp.cm.sig, y.map D.sp.cm.sig, ?_⟩
  have h1 : u = cat p y * T.1ᵀ := by
    rw [← h, Matrix.mul_assoc, ← Matrix.transpose_mul, T.mul_inv, Matrix.transpose_one, Matrix.mul_one]
  rw [pt, ← cj_rat, ← cj_rat, cj_cj, cj_cj, h1, rat_mul, rat, cat_map]
  rfl

theorem coEquiv_form (V : HSp D) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (w w' : Mx D V.rank (n + n)) :
    symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂) w w' =
      (coEquiv V T ε w).1 ⬝ᵥ (coEquiv V T ε w').2 - (coEquiv V T ε w').1 ⬝ᵥ (coEquiv V T ε w).2 := by
  obtain ⟨q, x, rfl⟩ := exists_pt T w
  obtain ⟨q', x', rfl⟩ := exists_pt T w'
  rw [symp_pt V hG, coEquiv_pt, coEquiv_pt]
  dsimp only
  rw [coord_dot_gram, coord_dot_gram, trA_inner_comm V q x', neg_sub_neg]

def co (V : HSp D) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Dbx V J₂ d := ⟨coEquiv V T ε, coEquiv_form V hG ε⟩

theorem coEquiv_rat (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (u : Matrix (Fin V.rank) (Fin (n + n)) D.host.E) : ∃ y z : Fin V.rank × Fin n × Fin d → D.host.F,
    coEquiv V T ε (rat u) =
      (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  obtain ⟨q, x, h⟩ := exists_pt_rat T u
  have h1 : coEquiv V T ε (rat u) =
      (coord ε (rat x), coord ε.traceDual (rat ((-(V.gram * q)).map D.sp.cm.sig))) := by
    rw [h, coEquiv_pt, gA, ← rat_mul, ← rat_neg, cj_rat]
  rw [coord_rat, coord_rat] at h1
  exact ⟨_, _, h1⟩

theorem exists_adapted (D : D7) (n : ℕ) (V : HSp D) (J : Matrix (Fin n) (Fin n) D.host.E)
    (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E)
    (hT : IsWittBasis D.sp.cm.sig J 1 T) (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n)
    (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    ∃ co : Dbx V J₂ d, IsAdapted D.sp.cm.sig co ∧ IsCoord V T ε co := by
  refine ⟨co V hG ε, ⟨coEquiv_rat V T ε, fun u hu => ?_, fun u hu => ?_⟩, fun q x => ?_⟩
  · obtain ⟨q, x, rfl⟩ := exists_pt T u
    obtain rfl := (pt_diag_iff hT q x).1 hu
    exact (congrArg Prod.fst (coEquiv_pt V T ε q 0)).trans (coord_zero ε)
  · obtain ⟨q, x, rfl⟩ := exists_pt T u
    obtain rfl := (pt_anti_iff hT q x).1 hu
    refine (congrArg Prod.snd (coEquiv_pt V T ε 0 x)).trans ?_
    rw [Matrix.mul_zero, neg_zero, cj_zero]
    exact coord_zero _
  · refine ⟨congrArg Prod.fst (coEquiv_pt V T ε q x), fun x' => ?_⟩
    exact (congrArg (fun p => coord ε x' ⬝ᵥ Prod.snd p) (coEquiv_pt V T ε q x)).trans (coord_dot_gram V ε x' q)

end GlobalTheory.SWLink.Darb

end
