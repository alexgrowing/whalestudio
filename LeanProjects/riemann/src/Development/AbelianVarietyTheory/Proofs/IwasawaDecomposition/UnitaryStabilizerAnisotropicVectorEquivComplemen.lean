import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.FrameStep

open Formalism.UG (cT cT_mul cT_one UJ)

section Abstract

variable {A : Type} [CommRing A] (s : A →+* A) {m n : Type} [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

theorem cT_add {p q : Type} (U V : Matrix p q A) : cT s (U + V) = cT s U + cT s V := by
  ext i j; simp [cT]

theorem exists_equiv (J : Matrix m m A) (J' : Matrix n n A) (X : Matrix m (Fin 1) A)
    (B : Matrix m n A) (L₁ : Matrix (Fin 1) m A) (L : Matrix n m A) (c : Matrix (Fin 1) (Fin 1) A)
    (hL : L₁ = c * (cT s X * J)) (h11 : L₁ * X = 1) (h21 : L * X = 0) (h22 : L * B = 1)
    (hsum : X * L₁ + B * L = 1) (hXB : cT s X * J * B = 0) (hBX : cT s B * J * X = 0)
    (hBB : cT s B * J * B = J') (S : Subgroup (UJ s J))
    (hS : ∀ g : UJ s J, g ∈ S ↔ ((g : GL m A) : Matrix m m A) * X = X) :
    ∃ e : S ≃* UJ s J', ∀ g : S, (((g : UJ s J) : GL m A) : Matrix m m A) * B =
      B * (((e g : UJ s J') : GL n A) : Matrix n n A) := by
  have h12 : L₁ * B = 0 := by rw [hL, Matrix.mul_assoc, hXB, Matrix.mul_zero]
  let mt : S → Matrix m m A := fun g => (((g : UJ s J) : GL m A) : Matrix m m A)
  have mt_mul : ∀ g h, mt (g * h) = mt g * mt h := fun g h => rfl
  have mt_one : mt 1 = 1 := rfl
  have hU : ∀ g, cT s (mt g) * J * mt g = J := fun g => (g : UJ s J).2
  have hX : ∀ g, mt g * X = X := fun g => (hS _).1 g.2
  have key : ∀ g, mt g * B = B * (L * mt g * B) := by
    intro g
    have h1 : cT s X * J * (mt g * B) = 0 := by
      calc cT s X * J * (mt g * B) = cT s (mt g * X) * J * (mt g * B) := by rw [hX]
        _ = cT s X * (cT s (mt g) * J * mt g) * B := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hU, hXB]
    have h2 : L₁ * (mt g * B) = 0 := by rw [hL, Matrix.mul_assoc, h1, Matrix.mul_zero]
    calc mt g * B = (X * L₁ + B * L) * (mt g * B) := by rw [hsum, Matrix.one_mul]
      _ = _ := by
        rw [Matrix.add_mul, Matrix.mul_assoc X, h2, Matrix.mul_zero, zero_add]
        simp only [Matrix.mul_assoc]
  have φmul : ∀ g h, L * mt (g * h) * B = (L * mt g * B) * (L * mt h * B) := by
    intro g h
    rw [mt_mul, Matrix.mul_assoc L, Matrix.mul_assoc (mt g), key h]
    simp only [Matrix.mul_assoc]
  have φone : L * mt 1 * B = 1 := by rw [mt_one, Matrix.mul_one, h22]
  let φu : S → GL n A := fun g =>
    ⟨L * mt g * B, L * mt g⁻¹ * B, by rw [← φmul, mul_inv_cancel, φone],
      by rw [← φmul, inv_mul_cancel, φone]⟩
  have φmem : ∀ g, φu g ∈ UJ s J' := by
    intro g
    show cT s (L * mt g * B) * J' * (L * mt g * B) = J'
    calc cT s (L * mt g * B) * J' * (L * mt g * B)
        = cT s (B * (L * mt g * B)) * J * (B * (L * mt g * B)) := by
          rw [← hBB, cT_mul s B]; simp only [Matrix.mul_assoc]
      _ = cT s B * (cT s (mt g) * J * mt g) * B := by
          rw [← key, cT_mul]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [hU, hBB]
  let φ : S →* UJ s J' := MonoidHom.mk' (fun g => ⟨φu g, φmem g⟩)
    (fun g h => Subtype.ext (Units.ext (φmul g h)))
  have ψX : ∀ k : Matrix n n A, (X * L₁ + B * k * L) * X = X := by
    intro k
    rw [Matrix.add_mul, Matrix.mul_assoc X, h11, Matrix.mul_assoc _ L, h21]; simp
  have ψB : ∀ k : Matrix n n A, (X * L₁ + B * k * L) * B = B * k := by
    intro k
    rw [Matrix.add_mul, Matrix.mul_assoc X, h12, Matrix.mul_assoc _ L, h22]; simp
  have ψmul : ∀ k k' : Matrix n n A, k * k' = 1 →
      (X * L₁ + B * k * L) * (X * L₁ + B * k' * L) = 1 := by
    intro k k' hk
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ψX, Matrix.mul_assoc B k', ← Matrix.mul_assoc _ B, ψB,
      Matrix.mul_assoc B, ← Matrix.mul_assoc k, hk, Matrix.one_mul, hsum]
  have hinj : Function.Injective φ := by
    intro g h hgh
    have h1 : L * mt g * B = L * mt h * B := congrArg (fun u : UJ s J' => ((u : GL n A) : Matrix n n A)) hgh
    have h2 : mt g * B = mt h * B := by rw [key g, key h, h1]
    have h3 : mt g = mt h := by
      rw [← Matrix.mul_one (mt g), ← Matrix.mul_one (mt h), ← hsum, Matrix.mul_add, Matrix.mul_add]
      simp only [← Matrix.mul_assoc]
      rw [hX, hX, h2]
    exact Subtype.ext (Subtype.ext (Units.ext h3))
  have hsurj : Function.Surjective φ := by
    intro u
    set k : Matrix n n A := ((u : GL n A) : Matrix n n A) with hk
    have hku : cT s k * J' * k = J' := u.2
    let ψ : GL m A := ⟨X * L₁ + B * k * L, X * L₁ + B * (((u : GL n A)⁻¹ : GL n A) : Matrix n n A) * L,
      ψmul _ _ (Units.mul_inv _), ψmul _ _ (Units.inv_mul _)⟩
    have hψ : ψ ∈ UJ s J := by
      show cT s (X * L₁ + B * k * L) * J * (X * L₁ + B * k * L) = J
      have gen : ∀ k₁ : Matrix n n A, cT s (X * L₁ + B * k₁ * L) * J * (X * L₁ + B * k₁ * L) =
          cT s L₁ * (cT s X * J * X) * L₁ + cT s L * (cT s k₁ * J' * k₁) * L := by
        intro k₁
        have : cT s (X * L₁ + B * k₁ * L) * J * (X * L₁ + B * k₁ * L) =
            cT s L₁ * (cT s X * J * X) * L₁ + cT s L₁ * (cT s X * J * B) * k₁ * L +
            (cT s L * cT s k₁ * (cT s B * J * X) * L₁ +
              cT s L * (cT s k₁ * (cT s B * J * B) * k₁) * L) := by
          simp only [cT_add, cT_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
          abel
        rw [this, hXB, hBX, hBB]; simp
      have g1 := gen 1
      rw [Matrix.mul_one B, hsum, cT_one, cT_one] at g1
      simp only [Matrix.one_mul, Matrix.mul_one] at g1
      rw [gen, hku, ← g1]
    refine ⟨⟨⟨ψ, hψ⟩, (hS _).2 (ψX k)⟩, Subtype.ext (Units.ext ?_)⟩
    show L * (X * L₁ + B * k * L) * B = k
    rw [Matrix.mul_assoc, ψB, ← Matrix.mul_assoc, h22, Matrix.one_mul]
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun g => key g⟩

end Abstract

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem exists_dual (hσ : ∀ y, σ (σ y) = y) {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    {x : Fin 1 → Fin (M + 1) → E} {a : F} {B : Matrix (Fin (M + 1)) (Fin M) E}
    {J' : Matrix (Fin M) (Fin M) E} (h : StepData σ J x a B J') :
    (consCol x B).det ≠ 0 ∧ ∃ (L₁ : Matrix (Fin 1) (Fin (M + 1)) E) (L : Matrix (Fin M) (Fin (M + 1)) E)
      (c : Matrix (Fin 1) (Fin 1) E),
      L₁ = c * (cT (σ : E →+* E) (Matrix.of x).transpose * J) ∧ L₁ * (Matrix.of x).transpose = 1 ∧
      L * (Matrix.of x).transpose = 0 ∧ L * B = 1 ∧ (Matrix.of x).transpose * L₁ + B * L = 1 ∧
      cT (σ : E →+* E) (Matrix.of x).transpose * J * B = 0 ∧
      cT (σ : E →+* E) B * J * (Matrix.of x).transpose = 0 := by
  obtain ⟨⟨hJ, -⟩, ha, hxx, hxB, hJ', -, hdet⟩ := h
  set X : Matrix (Fin (M + 1)) (Fin 1) E := (Matrix.of x).transpose with hXdef
  have ha' : algebraMap F E a ≠ 0 := by simpa using ha
  have hXB : cT (σ : E →+* E) X * J * B = 0 := by
    ext i j
    have := hxB j
    rw [Subsingleton.elim i 0]
    simp only [hE, Formalism.UG.hform] at this
    simp only [Matrix.mul_apply, cT, Finset.sum_mul, Matrix.zero_apply]
    rw [Finset.sum_comm, ← this]
    rfl
  have hXX : cT (σ : E →+* E) X * J * X = Matrix.of fun _ _ => algebraMap F E a := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp only [hE, Formalism.UG.hform] at hxx
    simp only [Matrix.mul_apply, cT, Finset.sum_mul, Matrix.of_apply]
    rw [Finset.sum_comm, ← hxx]
    rfl
  have hcJ : cT (σ : E →+* E) J = J := by
    ext i j; exact hJ i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j; exact hσ _
  have hBX : cT (σ : E →+* E) B * J * X = 0 := by
    have := congrArg (cT (σ : E →+* E)) hXB
    rw [cT_mul, cT_mul, hcc, hcJ, ← Matrix.mul_assoc] at this
    rw [this]
    ext i j; simp [cT]
  let c : Matrix (Fin 1) (Fin 1) E := Matrix.of fun _ _ => (algebraMap F E a)⁻¹
  set L₁ := c * (cT (σ : E →+* E) X * J) with hL₁
  set L := J'⁻¹ * (cT (σ : E →+* E) B * J) with hL
  have h11 : L₁ * X = 1 := by
    rw [hL₁, Matrix.mul_assoc, hXX]
    ext i j
    rw [Subsingleton.elim i j]
    simp [Matrix.mul_apply, c, ha']
  have h12 : L₁ * B = 0 := by rw [hL₁, Matrix.mul_assoc, hXB, Matrix.mul_zero]
  have h21 : L * X = 0 := by rw [hL, Matrix.mul_assoc, hBX, Matrix.mul_zero]
  have h22 : L * B = 1 := by
    rw [hL, Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  let Q : Matrix (Fin (M + 1)) (Fin (M + 1)) E :=
    Matrix.of (Fin.cons (α := fun _ => Fin (M + 1) → E) (L₁ 0) L)
  have hQP : Q * consCol x B = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact (congrFun (congrFun h11 0) 0).trans (by simp)
    · exact (congrFun (congrFun h12 0) j).trans (by simp [Matrix.one_apply, (Fin.succ_ne_zero j).symm])
    · exact (congrFun (congrFun h21 i) 0).trans (by simp [Matrix.one_apply])
    · exact (congrFun (congrFun h22 i) j).trans (by simp [Matrix.one_apply])
  have hPQ : consCol x B * Q = 1 := mul_eq_one_comm.1 hQP
  refine ⟨?_, L₁, L, c, rfl, h11, h21, h22, ?_, hXB, hBX⟩
  · intro h0
    have := congrArg Matrix.det hQP
    rw [Matrix.det_mul, h0] at this
    simp at this
  · rw [← hPQ]
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero]
    rfl

theorem cT_map (R : Type) [CommRing R] [Algebra F R] {p q : Type} (U : Matrix p q E) :
    cT (sigR R σ) (U.map (inclR R)) = (cT (σ : E →+* E) U).map (inclR (F := F) R) := by
  ext i j
  simp [cT, sigR, inclR]

end Field

theorem continuous_into {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) {T : Type} [TopologicalSpace T] (f : T → HA R σ J)
    (h1 : Continuous fun t => ((HA.mat R σ J (f t) : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)))
    (h2 : Continuous fun t => ((HA.mat R σ J (f t)⁻¹ : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E))) : Continuous f :=
  continuous_induced_rng.2 (Units.continuous_iff.2 ⟨h1, h2⟩)

theorem frameStep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → (consCol x B).det ≠ 0 ∧ (∃! e : Hstab R σ J x ≃* HA R σ J', ∀ g : Hstab R σ J x, FrameRelR R σ J J' B (g : HA R σ J) (e g)) ∧ ∀ e : Hstab R σ J x ≃* HA R σ J', (∀ g : Hstab R σ J x, FrameRelR R σ J J' B (g : HA R σ J) (e g)) → Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ M J x a B J' h
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨hdet, L₁, L, c, hL, h11, h21, h22, hsum, hXB, hBX⟩ := exists_dual σ hσ h
  have hBB := h.2.2.2.2.1
  set X : Matrix (Fin (M + 1)) (Fin 1) E := (Matrix.of x).transpose with hXdef
  set ι : E →+* R ⊗[F] E := inclR R with hι
  have hone : ∀ k : ℕ, (1 : Matrix (Fin k) (Fin k) E).map ι = 1 := fun k =>
    Matrix.map_one _ (map_zero ι) (map_one ι)
  have hzero : ∀ k l : ℕ, (0 : Matrix (Fin k) (Fin l) E).map ι = 0 := fun k l =>
    Matrix.map_zero _ (map_zero ι)
  have h22' : L.map ι * B.map ι = 1 := by rw [← Matrix.map_mul, h22, hone]
  have hsum' : X.map ι * L₁.map ι + B.map ι * L.map ι = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), hsum, hone]
  have hS : ∀ g : HA R σ J, g ∈ Hstab R σ J x ↔
      ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * X.map ι = X.map ι := by
    intro g
    refine MulAction.mem_stabilizer_iff.trans ⟨fun hg => ?_, fun hg => ?_⟩
    · ext i j
      exact congrFun (congrFun hg j) i
    · funext j i
      exact congrFun (congrFun hg i) j
  have hfor : ∀ (g : HA R σ J) (g' : HA R σ J'), FrameRelR R σ J J' B g g' →
      ((HA.mat R σ J' g' : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        L.map ι * ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * B.map ι := by
    intro g g' hr
    rw [FrameRelR, ← hι] at hr
    rw [Matrix.mul_assoc]
    erw [hr, ← Matrix.mul_assoc, h22', Matrix.one_mul]
  have hback : ∀ (g : Hstab R σ J x) (g' : HA R σ J'), FrameRelR R σ J J' B (g : HA R σ J) g' →
      ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
        X.map ι * L₁.map ι +
          B.map ι * ((HA.mat R σ J' g' : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * L.map ι := by
    intro g g' hr
    rw [FrameRelR, ← hι] at hr
    have h3 := congrArg (((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * ·) hsum'
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_one] at h3
    rw [(hS g).1 g.2] at h3
    erw [hr] at h3
    exact h3.symm
  refine ⟨hdet, ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_equiv (sigR R σ) (JR R J) (JR R J') (X.map ι) (B.map ι) (L₁.map ι)
      (L.map ι) (c.map ι)
      (by rw [hL, Matrix.map_mul, Matrix.map_mul, cT_map]; rfl)
      (by rw [← Matrix.map_mul, h11, hone]) (by rw [← Matrix.map_mul, h21, hzero]) h22' hsum'
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hXB, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBX, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, ← hBB]; rfl)
      (Hstab R σ J x) hS
    refine ⟨e, he, fun e' he' => MulEquiv.ext fun g => Subtype.ext (Units.ext ?_)⟩
    exact (hfor _ _ (he' g)).trans (hfor _ _ (he g)).symm
  · intro e he
    have c1 : Continuous fun g : Hstab R σ J x =>
        ((HA.mat R σ J' (e g) : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
      simp only [fun g => hfor _ _ (he g)]
      exact (continuous_const.matrix_mul
        ((continuous_mat R σ J).comp continuous_subtype_val)).matrix_mul continuous_const
    have c2 : Continuous fun g : HA R σ J' =>
        ((HA.mat R σ J (e.symm g) : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := by
      simp only [fun g => hback _ _ (he g), MulEquiv.apply_symm_apply]
      exact continuous_const.add
        ((continuous_const.matrix_mul (continuous_mat R σ J')).matrix_mul continuous_const)
    refine ⟨continuous_into R σ J' _ c1 ?_, continuous_induced_rng.2 (continuous_into R σ J _ c2 ?_)⟩
    · simp only [← map_inv]
      exact c1.comp continuous_inv
    · have := c2.comp (continuous_inv (G := HA R σ J'))
      refine this.congr fun g => ?_
      simp only [Function.comp, map_inv]
      rfl

end GlobalTheory.FrameStep
