import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicQuaternionNormOneCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceNormOneCompactSupportStatement

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.TwoQ

section Gen

variable {F : Type} [Field F] {d β : F} {R T : Type} [CommRing R] [Algebra F R] [CommRing T]
  (ι : R →+* T) (h : T)

def th (x : Q d β R) : Matrix (Fin 2) (Fin 2) T :=
  !![ι x.re + ι x.imI * h, ι (algebraMap F R β) * (ι x.imJ + ι x.imK * h);
     ι x.imJ - ι x.imK * h, ι x.re - ι x.imI * h]

variable {ι h}

theorem th_mul (hh : h * h = ι (algebraMap F R d)) (x y : Q d β R) :
    th ι h (x * y) = th ι h x * th ι h y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [th, Matrix.mul_apply, Fin.sum_univ_two, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
  · linear_combination (-(ι x.imI * ι y.imI) + ι (algebraMap F R β) * ι x.imK * ι y.imK) * hh
  · linear_combination (-ι (algebraMap F R β)) * (ι x.imI * ι y.imK - ι x.imK * ι y.imI) * hh
  · linear_combination (-(ι x.imI * ι y.imK - ι x.imK * ι y.imI)) * hh
  · linear_combination (-(ι x.imI * ι y.imI) + ι (algebraMap F R β) * ι x.imK * ι y.imK) * hh

theorem th_one : th ι h (1 : Q d β R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [th]

theorem th_det (hh : h * h = ι (algebraMap F R d)) (x : Q d β R) : (th ι h x).det = ι (qn x) := by
  simp only [th, Matrix.det_fin_two_of, qn, map_add, map_sub, map_mul, map_pow]
  linear_combination (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh

theorem th_mul_star (hh : h * h = ι (algebraMap F R d)) {x : Q d β R} (hx : qn x = 1) :
    th ι h x * th ι h (star x) = 1 := by
  rw [← th_mul hh, mul_star_eq, hx, map_one, th_one]

theorem th_star_mul (hh : h * h = ι (algebraMap F R d)) {x : Q d β R} (hx : qn x = 1) :
    th ι h (star x) * th ι h x = 1 := by
  rw [← th_mul hh, star_mul_eq, hx, map_one, th_one]

theorem th_unitary (hh : h * h = ι (algebraMap F R d)) (c : T →+* T) (hc : ∀ a, c (ι a) = ι a) (hch : c h = -h)
    {x : Q d β R} (hx : qn x = 1) :
    Formalism.UG.cT c (th ι h x) * !![1, 0; 0, -ι (algebraMap F R β)] * th ι h x =
      !![1, 0; 0, -ι (algebraMap F R β)] := by
  have hq : ι x.re ^ 2 - ι (algebraMap F R d) * ι x.imI ^ 2 - ι (algebraMap F R β) * ι x.imJ ^ 2 +
      ι (algebraMap F R d) * ι (algebraMap F R β) * ι x.imK ^ 2 = 1 := by
    have := congrArg ι hx
    simpa [qn] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [th, Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, hc, hch]
  · linear_combination hq + (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh
  · ring
  · ring
  · linear_combination (-ι (algebraMap F R β)) * hq +
      (-ι (algebraMap F R β)) * (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh

end Gen

section Coef

variable {T : Type} [CommRing T]

theorem entries_of_unitary (c : T →+* T) {B : T} {M : Matrix (Fin 2) (Fin 2) T} (hdet : M.det = 1)
    (hM : Formalism.UG.cT c M * !![1, 0; 0, -B] * M = !![1, 0; 0, -B]) :
    M 1 1 = c (M 0 0) ∧ M 0 1 = B * c (M 1 0) := by
  have hA : M * M.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have key : Formalism.UG.cT c M * !![1, 0; 0, -B] = !![1, 0; 0, -B] * M.adjugate := by
    calc Formalism.UG.cT c M * !![1, 0; 0, -B] = Formalism.UG.cT c M * !![1, 0; 0, -B] * (M * M.adjugate) := by
          rw [hA, Matrix.mul_one]
      _ = !![1, 0; 0, -B] * M.adjugate := by rw [← Matrix.mul_assoc, hM]
  have e00 := congrFun (congrFun key 0) 0
  have e01 := congrFun (congrFun key 0) 1
  simp [Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] at e00 e01
  exact ⟨e00.symm, by linear_combination -e01⟩

end Coef

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d β : F} {R : Type} [CommRing R] [Algebra F R]

theorem incl_alg (t : F) :
    inclR R (algebraMap F E t) = algebraMap R (R ⊗[F] E) (algebraMap F R t) := by
  simp only [inclR]
  rw [← IsScalarTower.algebraMap_apply F R (R ⊗[F] E) t]
  exact Algebra.TensorProduct.includeRight.commutes t

theorem xh_sq {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) :
    inclR (F := F) R ξ * inclR (F := F) R ξ = algebraMap R (R ⊗[F] E) (algebraMap F R d) := by
  rw [← map_mul, ← pow_two, hξ, incl_alg]

theorem sig_alg (σ : E →ₐ[F] E) (a : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sig_xh {σ : E →ₐ[F] E} {ξ : E} (hσ : σ ξ = -ξ) :
    sigR R σ (inclR (F := F) R ξ) = -inclR (F := F) R ξ := by
  simp [sigR, inclR, hσ, TensorProduct.tmul_neg]

theorem hermitian_plane_matrix :
    JR R (J2 E β) = !![1, 0; 0, -algebraMap R (R ⊗[F] E) (algebraMap F R β)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [JR, J2, incl_alg]

abbrev thR (R : Type) [CommRing R] [Algebra F R] (E : Type) [Field E] [Algebra F E] (ξ : E) (x : Q d β R) :
    Matrix (Fin 2) (Fin 2) (R ⊗[F] E) :=
  th (algebraMap R (R ⊗[F] E)) (inclR (F := F) R ξ) x

def toHA (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) (x : Q d β R) (hx : qn x = 1) :
    HA R σ (J2 E β) :=
  (⟨⟨thR R E ξ x, thR R E ξ (star x), th_mul_star (xh_sq hξ) hx, th_star_mul (xh_sq hξ) hx⟩, by
    change Formalism.UG.cT (sigR R σ) (thR R E ξ x) * JR R (J2 E β) * thR R E ξ x = JR R (J2 E β)
    rw [hermitian_plane_matrix]
    exact th_unitary (xh_sq hξ) _ (sig_alg σ) (sig_xh hσ) hx⟩ : HR R σ (J2 E β))

theorem toHA_mat (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) (x : Q d β R)
    (hx : qn x = 1) :
    ((HA.mat R σ (J2 E β) (toHA σ hξ hσ x hx)).1 : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) = thR R E ξ x := rfl

section Basis

variable (b : Module.Basis (Fin 2) F E) {ξ : E}

def co (R : Type) [CommRing R] [Algebra F R] (i : Fin 2) (t : R ⊗[F] E) : R :=
  (Algebra.TensorProduct.basis R b).repr t i

variable {b}

theorem decomp (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (t : R ⊗[F] E) :
    t = algebraMap R (R ⊗[F] E) (co b R 0 t) + algebraMap R (R ⊗[F] E) (co b R 1 t) * inclR (F := F) R ξ := by
  have h := (Algebra.TensorProduct.basis R b).sum_repr t
  rw [Fin.sum_univ_two] at h
  conv_lhs => rw [← h]
  simp only [Algebra.TensorProduct.basis_apply, hb0, hb1, co, inclR, Algebra.smul_def]
  simp [Algebra.TensorProduct.one_def]

theorem co_emb (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (x y : R) :
    co b R 0 (algebraMap R (R ⊗[F] E) x + algebraMap R (R ⊗[F] E) y * inclR (F := F) R ξ) = x ∧
    co b R 1 (algebraMap R (R ⊗[F] E) x + algebraMap R (R ⊗[F] E) y * inclR (F := F) R ξ) = y := by
  have h : algebraMap R (R ⊗[F] E) x + algebraMap R (R ⊗[F] E) y * inclR (F := F) R ξ =
      x • Algebra.TensorProduct.basis R b 0 + y • Algebra.TensorProduct.basis R b 1 := by
    simp only [Algebra.TensorProduct.basis_apply, hb0, hb1, inclR, Algebra.smul_def]
    simp [Algebra.TensorProduct.one_def]
  simp only [co, h, map_add, map_smul, Module.Basis.repr_self]
  simp

theorem alg_inj (hb0 : b 0 = 1) (hb1 : b 1 = ξ) {x y : R}
    (h : algebraMap R (R ⊗[F] E) x = algebraMap R (R ⊗[F] E) y) : x = y := by
  have h1 := (co_emb (R := R) hb0 hb1 x 0).1
  have h2 := (co_emb (R := R) hb0 hb1 y 0).1
  simp only [map_zero, zero_mul, add_zero] at h1 h2
  rw [← h1, ← h2, h]

theorem exists_of_mem (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E) (hξ : ξ ^ 2 = algebraMap F E d)
    (hσ : σ ξ = -ξ) (g : HA R σ (J2 E β))
    (hdet : ((HA.mat R σ (J2 E β) g).1 : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)).det = 1) :
    ∃ (x : Q d β R) (hx : qn x = 1), g = toHA σ hξ hσ x hx := by
  set M : Matrix (Fin 2) (Fin 2) (R ⊗[F] E) := (HA.mat R σ (J2 E β) g).1 with hMdef
  have hU : Formalism.UG.cT (sigR R σ) M * JR R (J2 E β) * M = JR R (J2 E β) := (show (g : HR R σ (J2 E β)).1 ∈ HR R σ (J2 E β) from g.2)
  rw [hermitian_plane_matrix] at hU
  obtain ⟨h11, h01⟩ := entries_of_unitary _ hdet hU
  set ι := algebraMap R (R ⊗[F] E) with hι
  set h := inclR (F := F) R ξ with hh
  have hA := decomp (R := R) hb0 hb1 (M 0 0)
  have hC := decomp (R := R) hb0 hb1 (M 1 0)
  have hsa : ∀ u v : R, sigR R σ (ι u + ι v * h) = ι u - ι v * h := by
    intro u v
    rw [map_add, map_mul, sig_alg, sig_alg, sig_xh hσ]; ring
  let x : Q d β R := ⟨co b R 0 (M 0 0), co b R 1 (M 0 0), co b R 0 (M 1 0), -co b R 1 (M 1 0)⟩
  have hthx : thR R E ξ x = M := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [th, x] using hA.symm
    · show ι (algebraMap F R β) * (ι (co b R 0 (M 1 0)) + ι (-co b R 1 (M 1 0)) * h) = M 0 1
      rw [h01]
      conv_rhs => rw [hC, hsa]
      rw [map_neg]; ring
    · show ι (co b R 0 (M 1 0)) - ι (-co b R 1 (M 1 0)) * h = M 1 0
      conv_rhs => rw [hC]
      rw [map_neg]; ring
    · show ι (co b R 0 (M 0 0)) - ι (co b R 1 (M 0 0)) * h = M 1 1
      rw [h11]
      conv_rhs => rw [hA, hsa]
  have hq : qn x = 1 := by
    apply alg_inj (E := E) hb0 hb1
    rw [map_one, ← th_det (xh_sq hξ), show th _ _ x = M from hthx, hdet]
  refine ⟨x, hq, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hthx.symm

end Basis

end Tens

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d β : F}

theorem cont_th (ξ : E) : Continuous fun x : Q d β (AF F) => thR (AF F) E ξ x := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hι : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  have a0 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.re := hι.comp continuous_re
  have a1 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imI := hι.comp continuous_imI
  have a2 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imJ := hι.comp continuous_imJ
  have a3 : Continuous fun x : Q d β (AF F) => algebraMap (AF F) (AF F ⊗[F] E) x.imK := hι.comp continuous_imK
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact a0.add (a1.mul continuous_const)
  · exact continuous_const.mul (a2.add (a3.mul continuous_const))
  · exact a2.sub (a3.mul continuous_const)
  · exact a0.sub (a1.mul continuous_const)

theorem cont_star : Continuous fun x : Q d β (AF F) => star x := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star, zero_mul, add_zero]
  exact ⟨continuous_re, continuous_imI.neg, continuous_imJ.neg, continuous_imK.neg⟩

theorem cont_toHA (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) :
    Continuous fun x : {x : Q d β (AF F) // qn x = 1} => toHA σ hξ hσ x.1 x.2 := by
  have h : Continuous fun x : {x : Q d β (AF F) // qn x = 1} =>
      HA.mat (AF F) σ (J2 E β) (toHA σ hξ hσ x.1 x.2) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (cont_th ξ).comp continuous_subtype_val
    · exact (cont_th ξ).comp (cont_star.comp continuous_subtype_val)
  exact Continuous.subtype_mk (p := fun g => g ∈ HR (AF F) σ (J2 E β)) h (fun x => (toHA σ hξ hσ x.1 x.2).2)

theorem toHA_mul {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d)
    (hσ : σ ξ = -ξ) {x y z : Q d β R} (hx : qn x = 1) (hy : qn y = 1) (hz : qn z = 1) (e : z = x * y) :
    toHA σ hξ hσ z hz = toHA σ hξ hσ x hx * toHA σ hξ hσ y hy := by
  subst e
  apply Subtype.ext
  apply Units.ext
  exact th_mul (xh_sq hξ) x y

theorem idem_proj {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) (u : Pl F) :
    (u ∈ S₁.disjSum S₂ → proj u ε = 1) ∧ (u ∉ S₁.disjSum S₂ → proj u ε = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases u with
  | inl w =>
    simp only [Finset.inl_mem_disjSum]
    exact ⟨h1 w, h2 w⟩
  | inr v =>
    simp only [Finset.inr_mem_disjSum]
    exact ⟨h3 v, h4 v⟩

theorem mul_idem {T : Set (Pl F)} {ε a : AF F} (hε : ∀ u ∈ T, proj u ε = 1) (ha : ∀ u, u ∉ T → proj u a = 0) :
    ε * a = a := by
  refine adele_ext fun u => ?_
  by_cases hu : u ∈ T
  · rw [map_mul, hε u hu, one_mul]
  · rw [map_mul, ha u hu, mul_zero]

theorem toHA_mem_SUAdelic (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    (x : Q d β (AF F)) (hx : qn x = 1) : toHA σ hξ hσ x hx ∈ SUAdelic σ (J2 E β) := by
  refine StrongApprox.mem_SUAdelic.2 ?_
  rw [toHA_mat, th_det (xh_sq hξ), hx, map_one]

theorem toHA_mem_supp (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {T : Set (Pl F)} {ε : AF F} (hε : ∀ u ∈ T, proj u ε = 1) {x : Q d β (AF F)} (hT : x ∈ SuppAt d β T)
    (hx : qn x = 1) : toHA σ hξ hσ x hx ∈ SUSupp σ (J2 E β) ε := by
  refine ⟨toHA_mem_SUAdelic σ hξ hσ x hx, ?_⟩
  have c0 : ∀ u, u ∉ T → proj u (x.re - 1) = 0 := fun u hu => by
    have := congrArg QuaternionAlgebra.re (hT.2 u hu)
    rw [map_sub, map_one, sub_eq_zero]; simpa [qmap] using this
  have c1 : ∀ u, u ∉ T → proj u x.imI = 0 := fun u hu => by
    have := congrArg QuaternionAlgebra.imI (hT.2 u hu); simpa [qmap] using this
  have c2 : ∀ u, u ∉ T → proj u x.imJ = 0 := fun u hu => by
    have := congrArg QuaternionAlgebra.imJ (hT.2 u hu); simpa [qmap] using this
  have c3 : ∀ u, u ∉ T → proj u x.imK = 0 := fun u hu => by
    have := congrArg QuaternionAlgebra.imK (hT.2 u hu); simpa [qmap] using this
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  have e0 : ι ε * (ι x.re - 1) = ι x.re - 1 := by
    have := congrArg ι (mul_idem hε c0); simpa using this
  have e1 : ι ε * ι x.imI = ι x.imI := by
    have := congrArg ι (mul_idem hε c1); simpa using this
  have e2 : ι ε * ι x.imJ = ι x.imJ := by
    have := congrArg ι (mul_idem hε c2); simpa using this
  have e3 : ι ε * ι x.imK = ι x.imK := by
    have := congrArg ι (mul_idem hε c3); simpa using this
  intro i j
  rw [toHA_mat]
  fin_cases i <;> fin_cases j <;> simp [th, ← hι]
  · linear_combination e0 + inclR (F := F) (AF F) ξ * e1
  · linear_combination ι (algebraMap F (AF F) β) * e2 + ι (algebraMap F (AF F) β) * inclR (F := F) (AF F) ξ * e3
  · linear_combination e2 - inclR (F := F) (AF F) ξ * e3
  · linear_combination e0 - inclR (F := F) (AF F) ξ * e1

theorem supp_of_toHA {b : Module.Basis (Fin 2) F E} {ξ : E} (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E)
    (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {T : Set (Pl F)} {δ : AF F} (hδ : ∀ u, u ∉ T → proj u δ = 0) {x : Q d β (AF F)} (hx : qn x = 1)
    (hm : toHA σ hξ hσ x hx ∈ SUSupp σ (J2 E β) δ) : x ∈ SuppAt d β T := by
  refine ⟨hx, fun u hu => ?_⟩
  have hm2 := hm.2
  simp only [toHA_mat] at hm2
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  set h := inclR (F := F) (AF F) ξ with hh
  have h00 : ι (δ * (x.re - 1)) + ι (δ * x.imI) * h = ι (x.re - 1) + ι x.imI * h := by
    have := hm2 0 0
    simp [th, ← hι, ← hh] at this
    simp only [map_mul, map_sub, map_one]
    linear_combination this
  have h10 : ι (δ * x.imJ) + ι (δ * -x.imK) * h = ι x.imJ + ι (-x.imK) * h := by
    have := hm2 1 0
    simp [th, ← hι, ← hh] at this
    simp only [map_mul, map_neg]
    linear_combination this
  have p0 : δ * (x.re - 1) = x.re - 1 := by
    have := congrArg (co b (AF F) 0) h00
    rwa [(co_emb hb0 hb1 _ _).1, (co_emb hb0 hb1 _ _).1] at this
  have p1 : δ * x.imI = x.imI := by
    have := congrArg (co b (AF F) 1) h00
    rwa [(co_emb hb0 hb1 _ _).2, (co_emb hb0 hb1 _ _).2] at this
  have p2 : δ * x.imJ = x.imJ := by
    have := congrArg (co b (AF F) 0) h10
    rwa [(co_emb hb0 hb1 _ _).1, (co_emb hb0 hb1 _ _).1] at this
  have p3 : δ * -x.imK = -x.imK := by
    have := congrArg (co b (AF F) 1) h10
    rwa [(co_emb hb0 hb1 _ _).2, (co_emb hb0 hb1 _ _).2] at this
  have q : ∀ a : AF F, δ * a = a → proj u a = 0 := fun a ha => by
    rw [← ha, map_mul, hδ u hu, zero_mul]
  have q0 := q _ p0
  have q1 := q _ p1
  have q2 := q _ p2
  have q3 := q _ p3
  rw [map_sub, map_one, sub_eq_zero] at q0
  rw [map_neg, neg_eq_zero] at q3
  ext
  · simpa [qmap] using q0
  · simpa [qmap] using q1
  · simpa [qmap] using q2
  · simpa [qmap] using q3

theorem toHA_rat (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) {γ : Q d β F}
    (hγ : qn γ = 1) (hq : qn (rat γ : Q d β (AF F)) = 1) :
    toHA σ hξ hσ (rat γ) hq ∈ SURat σ (J2 E β) := by
  have hh : ξ * ξ = algebraMap F E (algebraMap F F d) := by rw [← pow_two, hξ]; rfl
  refine ⟨toHA_mem_SUAdelic σ hξ hσ _ hq, ?_⟩
  refine Subgroup.mem_subgroupOf.2 ?_
  refine ⟨⟨th (algebraMap F E) ξ γ, th (algebraMap F E) ξ (star γ), th_mul_star hh hγ, th_star_mul hh hγ⟩, ?_, ?_⟩
  · exact th_unitary hh (σ : E →+* E) (fun a => σ.commutes a) hσ hγ
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.UG.bc, toHA, th, rat, qmap, Algebra.ofId_apply, incl_alg]

theorem exists_supp {b : Module.Basis (Fin 2) F E} {ξ : E} (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E)
    (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {T : Set (Pl F)} {δ : AF F} (hδ : ∀ u, u ∉ T → proj u δ = 0) {g : HA (AF F) σ (J2 E β)}
    (hg : g ∈ SUSupp σ (J2 E β) δ) :
    ∃ (x : Q d β (AF F)) (hx : qn x = 1), x ∈ SuppAt d β T ∧ g = toHA σ hξ hσ x hx := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem hb0 hb1 σ hξ hσ g (StrongApprox.mem_SUAdelic.1 hg.1)
  exact ⟨x, hx, supp_of_toHA hb0 hb1 σ hξ hσ hδ hx hg, rfl⟩

theorem image_val_eq {A : Set (Q d β (AF F))} (h : ∀ y ∈ A, qn y = 1) :
    Subtype.val '' (Subtype.val ⁻¹' A : Set {x : Q d β (AF F) // qn x = 1}) = A := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨⟨y, h y hy⟩, hy, rfl⟩

theorem compact_SUSupp {b : Module.Basis (Fin 2) F E} {ξ : E} (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E)
    (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {T : Set (Pl F)} {ε : AF F} (hε1 : ∀ u ∈ T, proj u ε = 1) (hε0 : ∀ u, u ∉ T → proj u ε = 0)
    (hC : IsCompact (SuppAt d β T)) : IsCompact (SUSupp σ (J2 E β) ε) := by
  have hK : IsCompact (Subtype.val ⁻¹' SuppAt d β T : Set {x : Q d β (AF F) // qn x = 1}) := by
    refine Subtype.isCompact_iff.2 ?_
    rw [image_val_eq fun y hy => hy.1]
    exact hC
  convert hK.image (cont_toHA σ hξ hσ) using 1
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, hT, rfl⟩ := exists_supp hb0 hb1 σ hξ hσ hε0 hg
    exact ⟨⟨x, hx⟩, hT, rfl⟩
  · rintro ⟨⟨x, hx⟩, hT, rfl⟩
    exact toHA_mem_supp σ hξ hσ hε1 hT hx

theorem exists_basis {d : F} {ξ : E} (hfin : Module.finrank F E = 2) (hd : ∀ r : F, r ^ 2 ≠ d)
    (hξ : ξ ^ 2 = algebraMap F E d) : ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = ξ := by
  have hli : LinearIndependent F ![(1 : E), ξ] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      have hx : ξ = algebraMap F E (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [map_div₀, map_neg]
        field_simp
        linear_combination hst
      apply hd (-s / t)
      apply (algebraMap F E).injective
      rw [map_pow, ← hx, hξ]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfin])
  exact ⟨b, by simp [b], by simp [b]⟩

theorem exists_split_place {ξ : E} {b : Module.Basis (Fin 2) F E} (hb0 : b 0 = 1) (hb1 : b 1 = ξ) (σ : E →ₐ[F] E)
    (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε)
    (hnc : ¬ IsCompact (SUSupp σ (J2 E β) ε)) :
    ∃ s ∈ (S₁.disjSum S₂ : Finset (Pl F)), ∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0 := by
  have hε1 : ∀ u ∈ ((S₁.disjSum S₂ : Finset (Pl F)) : Set (Pl F)), proj u ε = 1 := fun u hu =>
    (idem_proj hε u).1 (Finset.mem_coe.1 hu)
  have hε0 : ∀ u, u ∉ ((S₁.disjSum S₂ : Finset (Pl F)) : Set (Pl F)) → proj u ε = 0 := fun u hu =>
    (idem_proj hε u).2 (fun h => hu (Finset.mem_coe.2 h))
  by_contra hno
  push_neg at hno
  refine hnc (compact_SUSupp hb0 hb1 σ hξ hσ hε1 hε0 (GlobalTheory.T.finite_place_norm_one_compact_support d β _ fun s hs => ?_))
  exact GlobalTheory.T.anisotropic_quaternion_norm_one_compact d β s fun x hx => by_contra fun h => hno s hs x h hx

theorem qn_rat {γ : Q d β F} (hγ : qn γ = 1) : qn (rat γ : Q d β (AF F)) = 1 :=
  (qn_qmap _ γ).trans (by rw [hγ, map_one])

theorem toHA_mem_SASet (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε)
    {s : Pl F} (hsS : s ∈ (S₁.disjSum S₂ : Finset (Pl F))) {y : Q d β (AF F)} (hy : qn y = 1)
    (hyS : y ∈ SAQ d β s) : toHA σ hξ hσ y hy ∈ Sa2.SASet σ (J2 E β) ε := by
  obtain ⟨γ, hγ, h, hh, e⟩ := hyS
  have hq : qn (rat γ : Q d β (AF F)) = 1 := qn_rat hγ
  have h1 := toHA_rat σ hξ hσ hγ hq
  have h2 : toHA σ hξ hσ h hh.1 ∈ SUSupp σ (J2 E β) ε :=
    toHA_mem_supp σ hξ hσ (T := {s}) (fun u hu => by
      rw [Set.mem_singleton_iff.1 hu]; exact (idem_proj hε s).1 hsS) hh hh.1
  exact ⟨_, h1, _, h2, toHA_mul σ hξ hσ hq hh.1 hy e⟩

theorem closure_norm_one_subtype {s : Pl F} {x : Q d β (AF F)} (hx : qn x = 1) (hcl : x ∈ closure (SAQ d β s)) :
    (⟨x, hx⟩ : {x : Q d β (AF F) // qn x = 1}) ∈
      closure (Subtype.val ⁻¹' SAQ d β s : Set {x : Q d β (AF F) // qn x = 1}) := by
  have hsub : ∀ y ∈ SAQ d β s, qn y = 1 := by
    rintro _ ⟨γ, hγ, h, hh, rfl⟩
    rw [qn_mul, hh.1, mul_one]
    exact qn_rat hγ
  refine closure_subtype.2 ?_
  rw [image_val_eq hsub]
  exact hcl

theorem toHA_mem_closure (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ)
    {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε)
    {s : Pl F} (hsS : s ∈ (S₁.disjSum S₂ : Finset (Pl F))) {x : Q d β (AF F)} (hx : qn x = 1)
    (hcl : x ∈ closure (SAQ d β s)) :
    toHA σ hξ hσ x hx ∈ closure (Sa2.SASet σ (J2 E β) ε) := by
  have hm : Set.MapsTo (fun x : {x : Q d β (AF F) // qn x = 1} => toHA σ hξ hσ x.1 x.2)
      (Subtype.val ⁻¹' SAQ d β s) (Sa2.SASet σ (J2 E β) ε) :=
    fun y hy => toHA_mem_SASet σ hξ hσ hε hsS y.2 hy
  have h := map_mem_closure (cont_toHA σ hξ hσ) (closure_norm_one_subtype hx hcl) hm
  exact h

end Adelic

theorem plane_strong_approx_of_quaternion : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ β : F, β ≠ 0 → ∀ d : F, (∀ r : F, r ^ 2 ≠ d) → ∀ ξ : E, ξ ^ 2 = algebraMap F E d → σ ξ = -ξ →
    (∀ s : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → QSA d β s) → HermitianPlaneStrongApprox σ β := by
  intro F E _ _ _ _ _ σ hcm β _ d hd ξ hξ hσ hQ S₁ S₂ ε hε hnc T₁ T₂ δ hδ g hg
  obtain ⟨b, hb0, hb1⟩ := exists_basis hcm.2.2.1 hd hξ
  have hδ0 : ∀ u, u ∉ ((T₁.disjSum T₂ : Finset (Pl F)) : Set (Pl F)) → proj u δ = 0 := fun u hu =>
    (idem_proj hδ u).2 (fun h => hu (Finset.mem_coe.2 h))
  obtain ⟨s, hsS, hiso⟩ := exists_split_place hb0 hb1 σ hξ hσ hε hnc
  obtain ⟨x, hx, hT, rfl⟩ := exists_supp hb0 hb1 σ hξ hσ hδ0 hg
  exact toHA_mem_closure σ hξ hσ hε hsS hx (hQ s hiso (T₁.disjSum T₂) hT)

end GlobalTheory.CompanionTheory.PlaneSA.TwoQ
