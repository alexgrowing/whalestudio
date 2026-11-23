import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AutFunCounterexample

open Matrix Formalism.UG

theorem borel_NI (D : D7) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    BorelSpace (NI V C) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  infer_instance

theorem topGroup_GA (D : D7) (V : HSp D) : IsTopologicalGroup (GA D V) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

variable {D : D7}

theorem GA_ext (V : HSp D) {g h : GA D V} (e : (matHom V g).1 = (matHom V h).1) : g = h :=
  Subtype.ext (Units.ext e)

theorem hT_coord (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.repr x i) * V.gram i j * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, starRingEnd_apply, mul_comm]

theorem gram_pull (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram * frameMat A B ι = B.gram := by
  ext a b
  have := hι (B.frame a) (B.frame b)
  rw [hT_coord] at this
  rw [HSpace.gram, ← this, Finset.sum_comm]
  simp only [Matrix.mul_apply, cT, frameMat, LinearMap.toMatrix_apply, transpose_apply, map_apply,
    Finset.sum_mul]
  rfl

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    rw [hT_coord]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : ∀ j, V.frame.repr (V.frame.equivFun.symm v) j = v j := fun j =>
      congr_fun (V.frame.equivFun.apply_symm_apply v) j
    simp only [h2, mul_assoc, ← Finset.mul_sum, h1, mul_zero]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 this

theorem split_gen {E R : Type} [CommRing E] [CommRing R] (φ : E →+* R) {n r : ℕ}
    (P : Matrix (Fin n) (Fin r) E) (Q : Matrix (Fin r) (Fin n) E) (g₁ g₂ : Matrix (Fin n) (Fin n) R)
    (h₁ : g₁ * (1 - P * Q).map φ = g₂ * (1 - P * Q).map φ) (h₂ : g₁ * P.map φ = g₂ * P.map φ) : g₁ = g₂ := by
  have s : ∀ g : Matrix (Fin n) (Fin n) R, g = g * (1 - P * Q).map φ + (g * P.map φ) * Q.map φ := by
    intro g
    rw [Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _),
      sub_add_cancel, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  rw [s g₁, s g₂, h₁, h₂]

theorem tens_inj {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {n : ℕ} (m : Matrix (Fin n) (Fin n) ((A × B) ⊗[F] E))
    (a : m.map (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E)) = 1)
    (b : m.map (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E)) = 1) : m = 1 := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  ext i j
  have a' := congr_fun (congr_fun a i) j
  have b' := congr_fun (congr_fun b i) j
  rw [Matrix.map_apply] at a' b'
  rw [hz (m i j), a', b']
  by_cases h : i = j
  · subst h
    simp only [Matrix.one_apply_eq]
    have := hz 1
    simp only [map_one] at this
    exact this.symm
  · simp [Matrix.one_apply_ne h]

theorem embRel_unique (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι)
    {g₁ g₂ : GA D A} {g' : GA D B} (h₁ : EmbRel A B ι g₁ g') (h₂ : EmbRel A B ι g₂ g') : g₁ = g₂ := by
  set P := frameMat A B ι with hP
  set T := cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * A.gram with hT
  have hG : T * P = B.gram := gram_pull A B ι hι
  have hu : IsUnit B.gram.det := (gram_det_ne B).isUnit
  set N : Matrix (Fin A.rank) (Fin A.rank) D.host.E := 1 - P * (B.gram⁻¹ * T) with hN
  have hTN : T * N = 0 := by
    rw [hN, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hG, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, sub_self]
  have key : ∀ g : GA D A, EmbRel A B ι g g' → (matHom A g).1 * N.map (incA D) = N.map (incA D) := by
    intro g hg
    ext i j
    have := hg.2 (fun k => N k j) (by funext k; exact congr_fun (congr_fun hTN k) j)
    exact congr_fun this i
  apply GA_ext
  exact split_gen (incA D) P (B.gram⁻¹ * T) _ _ ((key g₁ h₁).trans (key g₂ h₂).symm) (h₁.1.trans h₂.1.symm)

theorem one_mem_KsphC (V : HSp D) (S) : (1 : GA D V) ∈ KsphC V S := by
  have : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨one_mem _, fun y => by rw [this, Matrix.one_mulVec], fun v _ => ?_⟩
  rw [this]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem GfC_inf_GinfC (V : HSp D) {g : GA D V} (h₁ : g ∈ GfC V) (h₂ : g ∈ GinfC V) : g = 1 := by
  apply GA_ext
  have a := congrArg Units.val (MonoidHom.mem_ker.1 h₁)
  have b := congrArg Units.val (MonoidHom.mem_ker.1 h₂)
  exact tens_inj (F := D.host.F) (E := D.host.E) (A := Ainf D.host.F) (B := Af D.host.F) _ a b

theorem ext_unitary {R : Type} [CommRing R] (σ : R →+* R) {n r : ℕ} (J : Matrix (Fin n) (Fin n) R)
    (G : Matrix (Fin r) (Fin r) R) (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (h1 : J * P = cT σ Q * G) (h2 : cT σ P * J = G * Q) (h3 : Q * P = 1) (h : Matrix (Fin r) (Fin r) R)
    (hh : cT σ h * G * h = G) :
    cT σ (1 + P * (h - 1) * Q) * J * (1 + P * (h - 1) * Q) = J := by
  have e : cT σ (1 + P * (h - 1) * Q) = 1 + cT σ Q * (cT σ h - 1) * cT σ P := by
    rw [Matrix.mul_assoc (cT σ Q), ← cT_one σ (n := Fin r), ← cT_one σ (n := Fin n)]
    have : cT σ h - cT σ 1 = cT σ (h - 1) := by simp [cT, Matrix.map_sub _ (map_sub σ)]
    rw [this, ← cT_mul, ← cT_mul]
    simp [cT, Matrix.map_add _ (map_add σ)]
  have e1 : (1 + cT σ Q * (cT σ h - 1) * cT σ P) * J = J + cT σ Q * (cT σ h - 1) * G * Q := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc _ (cT σ P), h2, ← Matrix.mul_assoc]
  have e2 : J * (P * (h - 1) * Q) = cT σ Q * (G * (h - 1)) * Q := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc _ G]
  have e3 : cT σ Q * (cT σ h - 1) * G * Q * (P * (h - 1) * Q) =
      cT σ Q * ((cT σ h - 1) * G * (h - 1)) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, h3, Matrix.one_mul]
  have e4 : G * (h - 1) + (cT σ h - 1) * G + (cT σ h - 1) * G * (h - 1) = 0 := by
    have : G * (h - 1) + (cT σ h - 1) * G + (cT σ h - 1) * G * (h - 1) = cT σ h * G * h - G := by
      noncomm_ring
    rw [this, hh, sub_self]
  rw [e, e1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, e2, e3, Matrix.mul_assoc (cT σ Q) _ G]
  have : cT σ Q * (G * (h - 1) + (cT σ h - 1) * G + (cT σ h - 1) * G * (h - 1)) * Q = 0 := by
    rw [e4]; simp
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul] at this
  rw [add_assoc, add_eq_left, ← this]
  abel

theorem gram_herm (V : HSp D) : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
  funext i j
  exact V.herm.eq (V.frame j) (V.frame i)

theorem cT_cT {m p : ℕ} (M : Matrix (Fin m) (Fin p) D.host.E) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M) = M := by
  funext i j
  exact star_star (M i j)

theorem cT_map_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {m p : ℕ} (M : Matrix (Fin m) (Fin p) E) :
    cT (sigR R σ) (M.map (inclR (F := F) R)) = (cT (σ : E →+* E) M).map (inclR (F := F) R) := by
  funext i j
  simp [cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]

theorem ext_mul {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (h3 : Q * P = 1) (a b : Matrix (Fin r) (Fin r) R) (hab : a * b = 1) :
    (1 + P * (a - 1) * Q) * (1 + P * (b - 1) * Q) = 1 := by
  have e3 : P * (a - 1) * Q * (P * (b - 1) * Q) = P * ((a - 1) * (b - 1)) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, h3, Matrix.one_mul]
  have e4 : (a - 1) + (b - 1) + (a - 1) * (b - 1) = 0 := by
    have : (a - 1) + (b - 1) + (a - 1) * (b - 1) = a * b - 1 := by noncomm_ring
    rw [this, hab, sub_self]
  have : P * ((a - 1) + (b - 1) + (a - 1) * (b - 1)) * Q = 0 := by rw [e4]; simp
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul] at this
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, e3, add_assoc, add_eq_left, ← this]
  abel

theorem exists_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin n) (Fin r) E)
    (Gi : Matrix (Fin r) (Fin r) E) (hGi : G * Gi = 1) (hGi' : Gi * G = 1)
    (hG : cT (σ : E →+* E) P * J * P = G) (hJ : cT (σ : E →+* E) J = J) (hGh : cT (σ : E →+* E) G = G)
    (hP : cT (σ : E →+* E) (cT (σ : E →+* E) P) = P) (h : HR R σ G) :
    ∃ g : HR R σ J, g.1.1 * P.map (inclR (F := F) R) = P.map (inclR (F := F) R) * h.1.1 ∧
      ∀ x : Fin n → E, (cT (σ : E →+* E) P * J).mulVec x = 0 →
        g.1.1.mulVec (fun i => inclR (F := F) R (x i)) = fun i => inclR (F := F) R (x i) := by
  set φ : E →+* R ⊗[F] E := inclR (F := F) R
  set Q := Gi * (cT (σ : E →+* E) P * J) with hQ
  have q3 : Q * P = 1 := by rw [hQ, Matrix.mul_assoc, hG, hGi']
  have q2 : cT (σ : E →+* E) P * J = G * Q := by rw [hQ, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have q1 : J * P = cT (σ : E →+* E) Q * G := by
    have := congrArg (cT (σ : E →+* E)) q2
    rwa [cT_mul, cT_mul, hJ, hP, hGh] at this
  have m3 : Q.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, q3, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨⟨1 + P.map φ * (h.1.1 - 1) * Q.map φ, 1 + P.map φ * (h.1.inv - 1) * Q.map φ,
    ext_mul _ _ m3 _ _ h.1.val_inv, ext_mul _ _ m3 _ _ h.1.inv_val⟩, ?_⟩, ?_, ?_⟩
  · refine ext_unitary (sigR R σ) (J.map φ) (G.map φ) _ _ ?_ ?_ m3 _ h.2
    · rw [cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, q1]
    · rw [cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, q2]
  · show (1 + P.map φ * (h.1.1 - 1) * Q.map φ) * P.map φ = _
    rw [Matrix.add_mul, Matrix.mul_assoc, m3, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, add_sub_cancel]
  · intro x hx
    show (1 + P.map φ * (h.1.1 - 1) * Q.map φ).mulVec _ = _
    have : (Q.map φ).mulVec (fun i => φ (x i)) = 0 := by
      funext i
      have h0 : Q.mulVec x = 0 := by rw [hQ, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      have := RingHom.map_mulVec φ Q x i
      rw [h0] at this
      simpa [Function.comp_def] using this.symm
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero, add_zero]

theorem embRel_existsUnique (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι)
    (g' : GA D B) : ∃! g : GA D A, EmbRel A B ι g g' := by
  have hu : IsUnit B.gram.det := (gram_det_ne B).isUnit
  obtain ⟨g, hg⟩ := exists_gen (R := AF D.host.F) D.sp.cm.sig A.gram B.gram (frameMat A B ι) B.gram⁻¹
    (Matrix.mul_nonsing_inv _ hu) (Matrix.nonsing_inv_mul _ hu) (gram_pull A B ι hι) (gram_herm A)
    (gram_herm B) (cT_cT _) g'
  exact ⟨g, hg, fun y hy => embRel_unique A B ι hι hy hg⟩

end GlobalTheory.AutFunCounterexample
end
