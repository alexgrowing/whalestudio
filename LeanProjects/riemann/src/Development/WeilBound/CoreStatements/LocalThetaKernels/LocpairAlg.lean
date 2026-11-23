import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

noncomputable section

namespace PositivityTheory.ThKH.Locpair

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt tensAt_tmul compFin_tensAt tensAt_mul_right)

section Base

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem repr_map (f : R →ₐ[F] R') (y : R ⊗[F] E) (i) : (Algebra.TensorProduct.basis R' (Module.finBasis F E)).repr
    (Algebra.TensorProduct.map f (AlgHom.id F E) y) i =
      f ((Algebra.TensorProduct.basis R (Module.finBasis F E)).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem lmm_map (f : R →ₐ[F] R') (y : R ⊗[F] E) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis R' (Module.finBasis F E))
      (Algebra.TensorProduct.map f (AlgHom.id F E) y) =
    (Algebra.leftMulMatrix (Algebra.TensorProduct.basis R (Module.finBasis F E)) y).map f := by
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, ← repr_map,
    map_mul (Algebra.TensorProduct.map f (AlgHom.id F E))]
  simp [Algebra.TensorProduct.basis_apply]

theorem norm_map' (f : R →ₐ[F] R') (y : R ⊗[F] E) :
    Algebra.norm R' (Algebra.TensorProduct.map f (AlgHom.id F E) y) = f (Algebra.norm R y) := by
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R' (Module.finBasis F E)),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R (Module.finBasis F E)), AlgHom.map_det, lmm_map]
  rfl

theorem trace_map' (f : R →ₐ[F] R') (y : R ⊗[F] E) :
    Algebra.trace R' _ (Algebra.TensorProduct.map f (AlgHom.id F E) y) = f (Algebra.trace R _ y) := by
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R' (Module.finBasis F E)),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R (Module.finBasis F E)), lmm_map]
  simp [Matrix.trace]

end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (v : Pl F)

abbrev Qv : Type := AF F ⧸ Ideal.span {atPlace v (1 : Fv F v)}

def awF : AF F →ₐ[F] Qv v := Ideal.Quotient.mkₐ F _

variable (E) in

def aw : AE F E →+* Qv v ⊗[F] E := (Algebra.TensorProduct.map (awF v) (AlgHom.id F E)).toRingHom

theorem awF_at (a : Fv F v) : awF v (atPlace v a) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨_, (idem_at v a).symm⟩)

theorem extF {a b : AF F} (h1 : evFin F v a = evFin F v b) (h2 : awF v a = awF v b) : a = b := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h2)
  have h3 := congrArg (evFin F v) hc
  rw [map_sub, h1, sub_self, map_mul, evFin_atPlace, one_mul] at h3
  rw [atPlace_mul_right, ← h3, mul_zero, map_zero, sub_eq_zero] at hc
  exact hc

theorem extE {a b : AE F E} (h1 : compFin F E v a = compFin F E v b) (h2 : aw E v a = aw E v b) : a = b := by
  refine (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr.injective (Finsupp.ext fun i => extF v ?_ ?_)
  · rw [← repr_map, ← repr_map]
    exact congrArg (fun y => (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)).repr y i) h1
  · rw [← repr_map, ← repr_map]
    exact congrArg (fun y => (Algebra.TensorProduct.basis (Qv v) (Module.finBasis F E)).repr y i) h2

omit [NumberField E] in
theorem aw_tensAt (y : Ev E v) : aw E v (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul a x =>
    change awF v (atPlace v a) ⊗ₜ[F] x = 0
    rw [awF_at, TensorProduct.zero_tmul]

omit [NumberField E] in
theorem smul_tensAt (a : Fv F v) (y : Ev E v) : tensAt E v (a • y) = atPlace v a • tensAt E v y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul b x =>
    rw [TensorProduct.smul_tmul', tensAt_tmul, tensAt_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
      atPlace_mul_right, evFin_atPlace]

omit [NumberField E] in
theorem tensAt_comp (z : AE F E) : tensAt E v (compFin F E v z) = atPlace v (1 : Fv F v) • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul b x =>
    change atPlace v (evFin F v b) ⊗ₜ[F] x = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, atPlace_mul_right, one_mul]

omit [NumberField E] in
theorem aw_of_at {z : AE F E} (h : At (evFin F v) z) : aw E v z = 0 := by
  rw [← idem_smul h, ← tensAt_comp, aw_tensAt]

theorem at_smul_idem {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) :
    At (evFin F v) (atPlace v (1 : Fv F v) • z) := fun u hu => by
  rw [smul_smul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero, zero_smul]

omit [NumberField E] in
theorem at_tensAt (y : Ev E v) : At (evFin F v) (tensAt E v y) := by
  rw [← compFin_tensAt v y, tensAt_comp]; exact at_smul_idem v _

omit [NumberField E] in
theorem comp_cA (z : AE F E) : compFin F E v (cA σ z) = cV σ v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x => rfl

variable (σ) in

def cQ : Qv v ⊗[F] E →ₐ[Qv v] Qv v ⊗[F] E := Algebra.TensorProduct.map (AlgHom.id _ _) σ

omit [NumberField E] in
theorem aw_cA (z : AE F E) : aw E v (cA σ z) = cQ σ v (aw E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x => rfl

variable (E) in

def liftE : Ev E v →* AE F E where
  toFun y := 1 + tensAt E v (y - 1)
  map_one' := by simp
  map_mul' a b := extE v (by simp [compFin_tensAt, -map_sub]) (by simp [aw_tensAt, -map_sub])

theorem comp_liftE (y : Ev E v) : compFin F E v (liftE E v y) = y := by
  change compFin F E v (1 + _) = y
  simp [compFin_tensAt, -map_sub]

theorem aw_liftE (y : Ev E v) : aw E v (liftE E v y) = 1 := by
  change aw E v (1 + _) = 1
  simp [aw_tensAt, -map_sub]

theorem norm_liftE (y : Ev E v) :
    Algebra.norm (AF F) (liftE E v y) = 1 - atPlace v 1 + atPlace v (Algebra.norm (Fv F v) y) := by
  refine extF v ?_ ?_
  · rw [← norm_map']
    change Algebra.norm _ (compFin F E v _) = _
    simp [comp_liftE, evFin_atPlace]
  · rw [← norm_map']
    change Algebra.norm _ (aw E v _) = _
    simp [aw_liftE, awF_at]

def locChr (χ : Chr F E) : (Ev E v)ˣ →* Circle := χ.comp (Units.map (liftE E v))

theorem isLocChar (χ : Chr F E) : IsLocChar χ v (locChr v χ) := fun z hz => by
  refine congrArg χ (Units.ext (extE v (comp_liftE v _) ?_))
  have := aw_of_at v hz
  rw [map_sub, map_one (aw E v), sub_eq_zero] at this
  exact (aw_liftE v _).trans this.symm

section Mat

variable {α β ν κ : Type}

theorem extM {a b : Matrix α β (AE F E)} (h1 : a.map (compFin F E v) = b.map (compFin F E v))
    (h2 : a.map (aw E v) = b.map (aw E v)) : a = b :=
  Matrix.ext fun i j => extE v (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

omit [NumberField E] in
theorem comp_up (w : Matrix α β (Ev E v)) : (w.map (tensAt E v)).map (compFin F E v) = w :=
  Matrix.ext fun _ _ => compFin_tensAt v _

omit [NumberField E] in
theorem aw_up (w : Matrix α β (Ev E v)) : (w.map (tensAt E v)).map (aw E v) = 0 :=
  Matrix.ext fun _ _ => aw_tensAt v _

omit [NumberField E] in
theorem up_comp (u : Matrix α β (AE F E)) : (u.map (compFin F E v)).map (tensAt E v) = atPlace v (1 : Fv F v) • u :=
  Matrix.ext fun _ _ => tensAt_comp v _

omit [NumberField E] in
theorem at_up (w : Matrix α β (Ev E v)) : At (evFin F v) (w.map (tensAt E v)) := fun u hu =>
  Matrix.ext fun _ _ => at_tensAt v _ u hu

omit [NumberField E] in
theorem awM_of_at {u : Matrix α β (AE F E)} (h : At (evFin F v) u) : u.map (aw E v) = 0 := by
  rw [← idem_smul h, ← up_comp, aw_up]

omit [NumberField E] in
theorem compM_of_away {u : Matrix α β (AE F E)} (h : atPlace v (1 : Fv F v) • u = 0) : u.map (compFin F E v) = 0 := by
  rw [← comp_up v (u.map _), up_comp, h, Matrix.map_zero _ (map_zero _)]

omit [NumberField E] in
theorem compM_cA (u : Matrix α β (AE F E)) :
    (u.map (cA σ)).map (compFin F E v) = (u.map (compFin F E v)).map (cV σ v) := Matrix.ext fun _ _ => comp_cA v _

omit [NumberField E] in
theorem awM_cA (u : Matrix α β (AE F E)) : (u.map (cA σ)).map (aw E v) = (u.map (aw E v)).map (cQ σ v) :=
  Matrix.ext fun _ _ => aw_cA v _

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

omit [NumberField E] [Fintype β] in
theorem comp_lift' (m : Matrix β β (Ev E v)) : (1 + (m - 1).map (tensAt E v)).map (compFin F E v) = m := by
  rw [Matrix.map_add _ (map_add _), comp_up, Matrix.map_one _ (map_zero _) (map_one _), add_sub_cancel]

omit [NumberField E] [Fintype β] in
theorem aw_lift' (m : Matrix β β (Ev E v)) : (1 + (m - 1).map (tensAt E v)).map (aw E v) = 1 := by
  rw [Matrix.map_add _ (map_add _), aw_up, Matrix.map_one _ (map_zero _) (map_one _), add_zero]

variable (E β) in

def liftM : Matrix β β (Ev E v) →* Matrix β β (AE F E) where
  toFun m := 1 + (m - 1).map (tensAt E v)
  map_one' := by rw [sub_self, Matrix.map_zero _ (map_zero _), add_zero]
  map_mul' a b := extM v (by simp only [Matrix.map_mul, comp_lift']) (by simp only [Matrix.map_mul, aw_lift', one_mul])

theorem comp_liftM (m : Matrix β β (Ev E v)) : (liftM E v β m).map (compFin F E v) = m := comp_lift' v m

theorem aw_liftM (m : Matrix β β (Ev E v)) : (liftM E v β m).map (aw E v) = 1 := aw_lift' v m

theorem at_liftM (m : Matrix β β (Ev E v)) : At (evFin F v) (liftM E v β m - 1) := by
  change At (evFin F v) (1 + (m - 1).map (tensAt E v) - 1)
  rw [add_sub_cancel_left]
  exact at_up v _

theorem det_liftM (m : Matrix β β (Ev E v)) : (liftM E v β m).det = liftE E v m.det :=
  extE v (by rw [RingHom.map_det, RingHom.mapMatrix_apply, comp_liftM, comp_liftE])
    (by rw [RingHom.map_det, RingHom.mapMatrix_apply, aw_liftM, aw_liftE, Matrix.det_one])

variable {v}

def liftU {J : Matrix β β (AE F E)} {Jv : Matrix β β (Ev E v)} (h : J.map (compFin F E v) = Jv) :
    UG (cV σ v) Jv →* UG (cA σ) J :=
  ((Units.map (liftM E v β)).comp (UG (cV σ v) Jv).subtype).codRestrict _ fun g => by
    change (liftM E v β g.1.1)ᵀ * J * (liftM E v β g.1.1).map (cA σ) = J
    refine extM v ?_ ?_
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, compM_cA, comp_liftM, h]
      exact g.2
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, awM_cA, aw_liftM, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]

theorem liftU_val {J : Matrix β β (AE F E)} {Jv : Matrix β β (Ev E v)} (h : J.map (compFin F E v) = Jv)
    (g : UG (cV σ v) Jv) : ((liftU h g).1 : Matrix β β (AE F E)) = liftM E v β g.1.1 := rfl

theorem exists_liftU {J : Matrix β β (AE F E)} {Jv : Matrix β β (Ev E v)} (h : J.map (compFin F E v) = Jv)
    (g : UG (cA σ) J) (hg : At (evFin F v) ((g.1 : Matrix β β (AE F E)) - 1)) : ∃ gv, liftU h gv = g := by
  refine ⟨⟨Matrix.GeneralLinearGroup.map (compFin F E v) g.1, ?_⟩, Subtype.ext (Units.ext (extM v (comp_liftM v _) ?_))⟩
  · change (g.1.1.map (compFin F E v))ᵀ * Jv * (g.1.1.map (compFin F E v)).map (cV σ v) = Jv
    rw [← h, ← compM_cA, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (·.map (compFin F E v)) g.2
  · have := awM_of_at v hg
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), sub_eq_zero] at this
    exact (aw_liftM v _).trans this.symm

variable (v) in

def locW (w : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) := (evA κ v w.1, evA κ v w.2)

omit [Fintype κ] in
theorem locW_smul (a : Fv F v) (w : (κ → AF F) × (κ → AF F)) : locW v (atPlace v a • w) = a • locW v w := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change evFin F v (atPlace v a * w.1 i) = a * evFin F v (w.1 i)
    rw [map_mul, evFin_atPlace]
  · change evFin F v (atPlace v a * w.2 i) = a * evFin F v (w.2 i)
    rw [map_mul, evFin_atPlace]

omit [Fintype κ] in
theorem in_locW (w : (κ → AF F) × (κ → AF F)) :
    (inA κ v (locW v w).1, inA κ v (locW v w).2) = atPlace v (1 : Fv F v) • w := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change atPlace v (evFin F v (w.1 i)) = atPlace v 1 * w.1 i
    rw [atPlace_mul_right, one_mul]
  · change atPlace v (evFin F v (w.2 i)) = atPlace v 1 * w.2 i
    rw [atPlace_mul_right, one_mul]

theorem ev_dot (a b : κ → AF F) : evFin F v (a ⬝ᵥ b) = evA κ v a ⬝ᵥ evA κ v b := by
  simp only [dotProduct, map_sum, map_mul]; rfl

variable {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {JAv : Matrix α α (Ev E v)} {JBv : Matrix β β (Ev E v)}

def IsLocD (co : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) JAv JBv) κ) : Prop :=
  ∀ u, dv.e (u.map (compFin F E v)) = locW v (co.e u)

omit [DecidableEq α] [DecidableEq β] in
theorem ev_symp (hA : JA.map (compFin F E v) = JAv) (hB : JB.map (compFin F E v) = JBv) (u u' : Matrix α β (AE F E)) :
    symp (R := Fv F v) (cV σ v) (-1) JAv JBv (u.map (compFin F E v)) (u'.map (compFin F E v)) =
      evFin F v (symp (R := AF F) (cA σ) (-1) JA JB u u') := by
  subst hA hB
  rw [symp, symp, ← trace_map']
  change _ = Algebra.trace _ _ (compFin F E v _)
  simp only [hTens, map_mul, map_sum, map_neg, map_one, comp_cA, Matrix.map_apply]

omit [DecidableEq α] [DecidableEq β] in
theorem exists_locD (hA : JA.map (compFin F E v) = JAv) (hB : JB.map (compFin F E v) = JBv)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) :
    ∃ dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) JAv JBv) κ, IsLocD co dv := by
  have key : ∀ u, locW v (co.e ((u.map (compFin F E v)).map (tensAt E v))) = locW v (co.e u) := fun u => by
    rw [up_comp, map_smul, locW_smul, one_smul]
  refine ⟨⟨{ toFun := fun w => locW v (co.e (w.map (tensAt E v)))
             map_add' := fun a b => ?_
             map_smul' := fun a w => ?_
             invFun := fun p => (co.e.symm (inA κ v p.1, inA κ v p.2)).map (compFin F E v)
             left_inv := fun w => ?_
             right_inv := fun p => ?_ }, fun w w' => ?_⟩, key⟩
  · rw [Matrix.map_add _ (map_add _), map_add]
    exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  · rw [show (a • w).map (tensAt E v) = atPlace v a • w.map (tensAt E v) from Matrix.ext fun _ _ => smul_tensAt v _ _,
      map_smul, locW_smul]
    rfl
  · simp only
    rw [in_locW, ← map_smul, LinearEquiv.symm_apply_apply, idem_smul (at_up v w), comp_up]
  · simp only
    rw [key, LinearEquiv.apply_symm_apply]
    exact Prod.ext (evA_inA v _) (evA_inA v _)
  · conv_lhs => rw [← comp_up v w, ← comp_up v w', ev_symp hA hB, co.form, map_sub, ev_dot, ev_dot]
    rfl

end Mat

end PositivityTheory.ThKH.Locpair
