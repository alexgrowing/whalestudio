import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrongApproxClosureMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportProductOverPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionNeighbourhood

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.Split

section Elementary

variable {K : Type*} [Field K]

def nP (D A C B : K) : ℍ[K, D, 0, B] := ⟨0, (2 * D)⁻¹, -C / (2 * B), -A / (2 * D * B)⟩

def nM (D A C B : K) : ℍ[K, D, 0, B] := ⟨0, 2⁻¹, D * C / (2 * B), A / (2 * B)⟩

def toM (D A C B : K) (x : ℍ[K, D, 0, B]) : Matrix (Fin 2) (Fin 2) K :=
  !![x.re + A * x.imJ - D * C * x.imK, D * x.imI + D * C * x.imJ - D * A * x.imK;
     x.imI - C * x.imJ + A * x.imK, x.re - A * x.imJ + D * C * x.imK]

variable {D A C B : K}

theorem toM_mul (hB : B = A ^ 2 - D * C ^ 2) (x y : ℍ[K, D, 0, B]) :
    toM D A C B (x * y) = toM D A C B x * toM D A C B y := by
  subst hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem toM_injective (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0)
    {x y : ℍ[K, D, 0, B]} (h : toM D A C B x = toM D A C B y) : x = y := by
  have h11 : _ = _ := congrFun (congrFun h 0) 0
  have h12 : _ = _ := congrFun (congrFun h 0) 1
  have h21 : _ = _ := congrFun (congrFun h 1) 0
  have h22 : _ = _ := congrFun (congrFun h 1) 1
  simp only [toM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h11 h12 h21 h22
  have hne : 2 * D * B ≠ 0 := mul_ne_zero (mul_ne_zero h2 hD) hB0
  subst hB
  have e1 : x.re = y.re := by
    apply mul_left_cancel₀ h2
    linear_combination h11 + h22
  have e2 : x.imI = y.imI := by
    apply mul_left_cancel₀ (mul_ne_zero h2 hD)
    linear_combination h12 + D * h21
  have e3 : x.imJ = y.imJ := by
    apply mul_left_cancel₀ hne
    linear_combination D * A * (h11 - h22) - D * C * (h12 - D * h21)
  have e4 : x.imK = y.imK := by
    apply mul_left_cancel₀ hne
    linear_combination D * C * (h11 - h22) - A * (h12 - D * h21)
  exact QuaternionAlgebra.ext e1 e2 e3 e4

theorem det_toM (hB : B = A ^ 2 - D * C ^ 2) (x : ℍ[K, D, 0, B]) :
    (toM D A C B x).det = x.re ^ 2 - D * x.imI ^ 2 - B * x.imJ ^ 2 + D * B * x.imK ^ 2 := by
  subst hB
  simp [toM, Matrix.det_fin_two]
  ring

theorem toM_one : toM D A C B (1 : ℍ[K, D, 0, B]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM]

theorem toM_zero : toM D A C B (0 : ℍ[K, D, 0, B]) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM]

theorem toM_nP (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    toM D A C B (nP D A C B) = !![0, 1; 0, 0] := by
  subst hB
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM, nP] <;> field_simp <;> ring

theorem toM_nM (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    toM D A C B (nM D A C B) = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM, nM] <;> field_simp <;> rw [hB] <;> ring

theorem toM_add (x y : ℍ[K, D, 0, B]) : toM D A C B (x + y) = toM D A C B x + toM D A C B y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM] <;> ring

theorem toM_smul (c : K) (x : ℍ[K, D, 0, B]) : toM D A C B (c • x) = c • toM D A C B x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM] <;> ring

theorem toM_uP (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) (c : K) :
    toM D A C B (1 + c • nP D A C B) = !![1, c; 0, 1] := by
  rw [toM_add, toM_smul, toM_nP hB hD hB0 h2, toM_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem toM_uM (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) (c : K) :
    toM D A C B (1 + c • nM D A C B) = !![1, 0; c, 1] := by
  rw [toM_add, toM_smul, toM_nM hB hD hB0 h2, toM_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem nP_mul_self_eq_zero (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    nP D A C B * nP D A C B = 0 := by
  apply toM_injective hB hD hB0 h2
  rw [toM_mul hB, toM_nP hB hD hB0 h2, toM_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem nM_mul_self (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    nM D A C B * nM D A C B = 0 := by
  apply toM_injective hB hD hB0 h2
  rw [toM_mul hB, toM_nM hB hD hB0 h2, toM_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem normSq_nP_eq_zero (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    (nP D A C B).re ^ 2 - D * (nP D A C B).imI ^ 2 - B * (nP D A C B).imJ ^ 2 +
      D * B * (nP D A C B).imK ^ 2 = 0 := by
  rw [← det_toM hB, toM_nP hB hD hB0 h2, Matrix.det_fin_two_of]
  ring

theorem nM_norm (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    (nM D A C B).re ^ 2 - D * (nM D A C B).imI ^ 2 - B * (nM D A C B).imJ ^ 2 +
      D * B * (nM D A C B).imK ^ 2 = 0 := by
  rw [← det_toM hB, toM_nM hB hD hB0 h2, Matrix.det_fin_two_of]
  ring

theorem matrix_det_one_eq_three_elementary (p q r t : K) (hM : p * t - q * r = 1) (h : r ≠ 0) :
    !![p, q; r, t] = !![1, (p - 1) / r; 0, 1] * !![1, 0; r, 1] * !![1, (t - 1) / r; 0, 1] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
    first | ring1 | linear_combination hM | linear_combination (-1 : K) * hM

theorem mem_of_unipotent (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0)
    (P : Set ℍ[K, D, 0, B]) (hmul : ∀ x ∈ P, ∀ y ∈ P, x * y ∈ P)
    (hP : ∀ c : K, 1 + c • nP D A C B ∈ P) (hM : ∀ c : K, 1 + c • nM D A C B ∈ P)
    {g : ℍ[K, D, 0, B]} (hg : g.re ^ 2 - D * g.imI ^ 2 - B * g.imJ ^ 2 + D * B * g.imK ^ 2 = 1) :
    g ∈ P := by
  have key : ∀ g : ℍ[K, D, 0, B], (toM D A C B g).det = 1 → toM D A C B g 1 0 ≠ 0 → g ∈ P := by
    intro g h1 hr
    have e : g = (1 + ((toM D A C B g 0 0 - 1) / toM D A C B g 1 0) • nP D A C B) *
        (1 + (toM D A C B g 1 0) • nM D A C B) *
        (1 + ((toM D A C B g 1 1 - 1) / toM D A C B g 1 0) • nP D A C B) := by
      apply toM_injective hB hD hB0 h2
      rw [toM_mul hB, toM_mul hB, toM_uP hB hD hB0 h2, toM_uM hB hD hB0 h2, toM_uP hB hD hB0 h2,
        ← matrix_det_one_eq_three_elementary _ (toM D A C B g 0 1) _ _ (by rw [← Matrix.det_fin_two]; exact h1) hr]
      exact Matrix.eta_fin_two _
    rw [e]
    exact hmul _ (hmul _ (hP _) _ (hM _)) _ (hP _)
  have hdet : (toM D A C B g).det = 1 := by rw [det_toM hB, hg]
  by_cases h : toM D A C B g 1 0 = 0
  · have hp : toM D A C B g 0 0 ≠ 0 := by
      intro h0
      rw [Matrix.det_fin_two, h, h0] at hdet
      simp at hdet
    have hu : toM D A C B (1 + (1 : K) • nM D A C B) = !![1, 0; 1, 1] := toM_uM hB hD hB0 h2 1
    have hg' : (1 + (1 : K) • nM D A C B) * g ∈ P := by
      apply key
      · rw [toM_mul hB, Matrix.det_mul, hdet, hu, Matrix.det_fin_two_of]
        ring
      · rw [toM_mul hB, hu]
        simpa [Matrix.mul_apply, Fin.sum_univ_two, h] using hp
    have e : g = (1 + (-1 : K) • nM D A C B) * ((1 + (1 : K) • nM D A C B) * g) := by
      rw [← mul_assoc]
      have : (1 + (-1 : K) • nM D A C B) * (1 + (1 : K) • nM D A C B) = 1 := by
        apply toM_injective hB hD hB0 h2
        rw [toM_mul hB, toM_uM hB hD hB0 h2, hu, toM_one, Matrix.mul_fin_two,
          Matrix.one_fin_two]
        simp
      rw [this, one_mul]
    rw [e]
    exact hmul _ (hM _) _ hg'
  · exact key g hdet h

end Elementary

section Adelic

variable {F : Type} [Field F] {d β : F} {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
  [Algebra F R']

def un (n : Q d β F) (c : R) : Q d β R := 1 + c • rat n

theorem qmap_un (f : R →ₐ[F] R') (n : Q d β F) (c : R) : qmap f (un n c) = un n (f c) := by
  ext <;> simp [un, rat, qmap]

theorem un_zero (n : Q d β F) : un n (0 : R) = 1 := by simp [un]

theorem qn_un (n : Q d β F) (h0 : n.re = 0) (hn : qn n = 0) (c : R) : qn (un n c) = 1 := by
  have h := congrArg (algebraMap F R) hn
  simp only [qn, h0, map_add, map_sub, map_mul, map_pow, map_zero, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  have h0' : algebraMap F R n.re = 0 := by rw [h0, map_zero]
  simp only [qn, un, rat, qmap]
  simp [h0']
  linear_combination c ^ 2 * h

theorem un_add (n : Q d β F) (hn : n * n = 0) (c c' : R) : un n (c + c') = un n c * un n c' := by
  have h : (rat n : Q d β R) * rat n = 0 := by rw [← map_mul, hn, map_zero]
  simp only [un, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, h, smul_zero, add_smul,
    add_zero]
  abel

theorem continuous_un [TopologicalSpace R] [IsTopologicalRing R] (n : Q d β F) :
    Continuous (fun c : R => (un n c : Q d β R)) := by
  rw [continuous_q_iff]
  simp only [un, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
    QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> fun_prop

theorem rat_nP {K : Type} [Field K] [Algebra F K] (a b : F) :
    (rat (nP (algebraMap F F d) (algebraMap F F a) (algebraMap F F b) (algebraMap F F β)) : Q d β K) =
      nP (algebraMap F K d) (algebraMap F K a) (algebraMap F K b) (algebraMap F K β) := by
  have h2 : algebraMap F K 2 = 2 := map_ofNat _ 2
  ext <;> simp [rat, qmap, nP, h2]

theorem rat_nM {K : Type} [Field K] [Algebra F K] (a b : F) :
    (rat (nM (algebraMap F F d) (algebraMap F F a) (algebraMap F F b) (algebraMap F F β)) : Q d β K) =
      nM (algebraMap F K d) (algebraMap F K a) (algebraMap F K b) (algebraMap F K β) := by
  have h2 : algebraMap F K 2 = 2 := map_ofNat _ 2
  ext <;> simp [rat, qmap, nM, h2]

theorem exists_norm_form (hd : ∀ r : F, r ^ 2 ≠ d) {x : Q d β F} (hx : x ≠ 0) (hq : qn x = 0) :
    ∃ a b : F, β = a ^ 2 - d * b ^ 2 := by
  have hm : ∀ u v : F, u ^ 2 - d * v ^ 2 = 0 → u = 0 ∧ v = 0 := by
    intro u v h
    have hv : v = 0 := by
      by_contra hv
      apply hd (u / v)
      field_simp
      linear_combination h
    subst hv
    refine ⟨?_, rfl⟩
    simpa using h
  simp only [qn, Algebra.algebraMap_self, RingHom.id_apply] at hq
  by_cases m0 : x.imJ ^ 2 - d * x.imK ^ 2 = 0
  · obtain ⟨hj, hk⟩ := hm _ _ m0
    rw [hj, hk] at hq
    obtain ⟨hr, hi⟩ := hm x.re x.imI (by linear_combination hq)
    exact absurd (QuaternionAlgebra.ext hr hi hj hk) hx
  · refine ⟨(x.re * x.imJ - d * x.imI * x.imK) / (x.imJ ^ 2 - d * x.imK ^ 2),
      (x.imI * x.imJ - x.re * x.imK) / (x.imJ ^ 2 - d * x.imK ^ 2), ?_⟩
    rw [div_pow, div_pow, mul_div_assoc', div_sub_div_same, eq_div_iff (pow_ne_zero 2 m0)]
    linear_combination (-(x.imJ ^ 2 - d * x.imK ^ 2)) * hq

end Adelic

section Lift

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem q_ext {x y : Q d β (AF F)} (h : ∀ u : Pl F, qmap (proj u) x = qmap (proj u) y) : x = y := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> refine adele_ext fun u => ?_
  · exact congrArg (fun z : Q d β (Kp u) => z.re) (h u)
  · exact congrArg (fun z : Q d β (Kp u) => z.imI) (h u)
  · exact congrArg (fun z : Q d β (Kp u) => z.imJ) (h u)
  · exact congrArg (fun z : Q d β (Kp u) => z.imK) (h u)

def lift (u : Pl F) (x : Q d β (Kp u)) : Q d β (AF F) :=
  ⟨1 + inc u (x.re - 1), inc u x.imI, inc u x.imJ, inc u x.imK⟩

theorem qmap_lift_same (u : Pl F) (x : Q d β (Kp u)) : qmap (proj u) (lift u x) = x := by
  ext <;> simp [lift, qmap, proj_inc_same]

theorem qmap_lift_ne {u u' : Pl F} (h : u' ≠ u) (x : Q d β (Kp u)) :
    qmap (proj u') (lift u x) = 1 := by
  ext <;> simp [lift, qmap, proj_inc_ne h]

theorem lift_mul (u : Pl F) (x y : Q d β (Kp u)) : lift u (x * y) = lift u x * lift u y := by
  refine q_ext fun u' => ?_
  rw [map_mul]
  by_cases h : u' = u
  · subst h
    simp only [qmap_lift_same]
  · simp only [qmap_lift_ne h, mul_one]

theorem lift_qmap {u : Pl F} {g : Q d β (AF F)} (hg : g ∈ SuppAt d β {u}) :
    lift u (qmap (proj u) g) = g := by
  refine q_ext fun u' => ?_
  by_cases h : u' = u
  · subst h
    exact qmap_lift_same _ _
  · rw [qmap_lift_ne h, hg.2 u' (by simpa using h)]

theorem lift_un (u : Pl F) (n : Q d β F) (c : Kp u) : lift u (un n c) = un n (inc u c) := by
  refine q_ext fun u' => ?_
  rw [qmap_un]
  by_cases h : u' = u
  · subst h
    rw [qmap_lift_same, proj_inc_same]
  · rw [qmap_lift_ne h, proj_inc_ne h, un_zero]

theorem dense_add (s : Pl F) :
    Dense {c : AF F | ∃ (t : F) (y : Kp s), c = algebraMap F (AF F) t + inc s y} := by
  classical
  intro c
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨T, U, hU, -, hO, hy⟩ := Box.adele_box c W hW
  obtain ⟨t, ht, hint⟩ := additive_strong_approx_away s (T.erase s) (by simp) (fun u => interior (U u))
    (fun u _ => ⟨isOpen_interior, ⟨proj u c, mem_interior_iff_mem_nhds.2 (hU u)⟩⟩)
  have hproj : ∀ u, u ≠ s → proj u (algebraMap F (AF F) t + inc s (proj s c - algebraMap F (Kp s) t)) =
      algebraMap F (Kp u) t := fun u hu => by
    rw [map_add, proj_inc_ne hu, add_zero, AlgHom.commutes]
  have hs : proj s (algebraMap F (AF F) t + inc s (proj s c - algebraMap F (Kp s) t)) = proj s c := by
    rw [map_add, proj_inc_same, AlgHom.commutes]
    ring
  refine ⟨algebraMap F (AF F) t + inc s (proj s c - algebraMap F (Kp s) t),
    hy _ (fun u hu => ?_) (fun v hv => ?_), ⟨t, _, rfl⟩⟩
  · by_cases h : u = s
    · subst h
      rw [hs]
      exact mem_of_mem_nhds (hU u)
    · rw [hproj u h]
      exact interior_subset (ht u (Finset.mem_erase.2 ⟨h, hu⟩))
  · by_cases h : (Sum.inr v : Pl F) = s
    · subst h
      rw [hs]
      exact hO v hv (mem_of_mem_nhds (hU _))
    · rw [hproj _ h]
      exact hint v (fun h' => hv (Finset.mem_of_mem_erase h')) h

theorem un_mem_closure (s : Pl F) (n : Q d β F) (h0 : n.re = 0) (hn : qn n = 0) (hnn : n * n = 0)
    (c : AF F) : un n c ∈ closure (SAQ d β s) := by
  refine map_mem_closure (continuous_un n) (dense_add s c) ?_
  rintro _ ⟨t, y, rfl⟩
  refine ⟨un n t, qn_un n h0 hn t, un n (inc s y), ⟨qn_un n h0 hn _, fun u hu => ?_⟩, ?_⟩
  · rw [qmap_un, proj_inc_ne (by simpa using hu), un_zero]
  · rw [un_add n hnn]
    congr 1
    exact (qmap_un (Algebra.ofId F (AF F)) n t).symm

theorem one_mem_SAQ (s : Pl F) : (1 : Q d β (AF F)) ∈ SAQ d β s :=
  ⟨1, qn_one, 1, ⟨qn_one, fun _ _ => map_one _⟩, by rw [map_one, one_mul]⟩

theorem supp_mem {a b : F} (hab : β = a ^ 2 - d * b ^ 2) (hd : d ≠ 0) (hβ : β ≠ 0) (s u : Pl F)
    {g : Q d β (AF F)} (hg : g ∈ SuppAt d β {u}) : g ∈ closure (SAQ d β s) := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have hBF : algebraMap F F β = algebraMap F F a ^ 2 - algebraMap F F d * algebraMap F F b ^ 2 := by
    simpa using hab
  have hdF : algebraMap F F d ≠ 0 := by simpa using hd
  have hβF : algebraMap F F β ≠ 0 := by simpa using hβ
  have hB : algebraMap F (Kp u) β =
      algebraMap F (Kp u) a ^ 2 - algebraMap F (Kp u) d * algebraMap F (Kp u) b ^ 2 := by
    rw [hab, map_sub, map_pow, map_mul, map_pow]
  have hD : algebraMap F (Kp u) d ≠ 0 := fun h => hd ((map_eq_zero _).1 h)
  have hB0 : algebraMap F (Kp u) β ≠ 0 := fun h => hβ ((map_eq_zero _).1 h)
  have h2 : (2 : Kp u) ≠ 0 := fun h => h2F ((map_eq_zero (algebraMap F (Kp u))).1 ((map_ofNat _ 2).trans h))
  have hnP : ∀ c : AF F, un (nP (algebraMap F F d) (algebraMap F F a) (algebraMap F F b)
      (algebraMap F F β) : Q d β F) c ∈ closure (SAQ d β s) :=
    un_mem_closure s _ rfl (normSq_nP_eq_zero hBF hdF hβF h2F) (nP_mul_self_eq_zero hBF hdF hβF h2F)
  have hnM : ∀ c : AF F, un (nM (algebraMap F F d) (algebraMap F F a) (algebraMap F F b)
      (algebraMap F F β) : Q d β F) c ∈ closure (SAQ d β s) :=
    un_mem_closure s _ rfl (nM_norm hBF hdF hβF h2F) (nM_mul_self hBF hdF hβF h2F)
  have key : qmap (proj u) g ∈ {x : Q d β (Kp u) | lift u x ∈ closure (SAQ d β s)} := by
    refine mem_of_unipotent hB hD hB0 h2 _ (fun x hx y hy => ?_) (fun c => ?_) (fun c => ?_) ?_
    · rw [Set.mem_setOf_eq, lift_mul]
      exact closure_SAQ_mul d β s _ hx _ hy
    · rw [Set.mem_setOf_eq, ← rat_nP a b]
      exact (lift_un u _ c).symm ▸ hnP _
    · rw [Set.mem_setOf_eq, ← rat_nM a b]
      exact (lift_un u _ c).symm ▸ hnM _
    · have h := qn_qmap (proj u) g
      rw [hg.1, map_one] at h
      exact h
  rw [Set.mem_setOf_eq, lift_qmap hg] at key
  exact key

end Lift

theorem strong_approx_split : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ r : F, r ^ 2 ≠ d) → β ≠ 0 →
    (∃ x : Q d β F, x ≠ 0 ∧ qn x = 0) → ∀ s : Pl F, QSA d β s := by
  intro F _ _ d β hd hβ ⟨x, hx0, hq⟩ s T
  obtain ⟨a, b, hab⟩ := exists_norm_form hd hx0 hq
  have hd0 : d ≠ 0 := fun h => hd 0 (by simp [h])
  exact ProdSupp.suppAt_subset_of_places d β (closure (SAQ d β s)) (subset_closure (one_mem_SAQ s))
    (closure_SAQ_mul d β s) (fun u g hg => supp_mem hab hd0 hβ s u hg) T

end GlobalTheory.CompanionTheory.PlaneSA.Split
