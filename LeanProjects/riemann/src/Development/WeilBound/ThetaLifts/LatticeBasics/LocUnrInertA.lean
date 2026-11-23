import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersAgreeInertUnramified

noncomputable section

namespace GlobalTheory.ThK.Dbl.Inert

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.LFun.InertChart PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt)
open GlobalTheory.Doubling (absE)

section Alg

variable {L : Type} [CommRing L] {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def conjM {A : Matrix β γ L} {A' : Matrix γ β L} (h1 : A * A' = 1) (h2 : A' * A = 1) : Matrix γ γ L →* Matrix β β L where
  toFun m := A * m * A'
  map_one' := by rw [Matrix.mul_one, h1]
  map_mul' a b := by
    rw [show A * a * A' * (A * b * A') = A * (a * (A' * A) * b) * A' by simp only [Matrix.mul_assoc], h2, Matrix.mul_one]

theorem iso_iff (c : L →+* L) {A : Matrix β γ L} {A' : Matrix γ β L} (h1 : A * A' = 1) {J : Matrix β β L} {H : Matrix γ γ L}
    (hH : cT c A * Jᵀ * A = H) (M : Matrix β β L) :
    Mᵀ * J * M.map c = J ↔ cT c (A' * M * A) * H * (A' * M * A) = H := by
  have e : cT c (A' * M * A) * H * (A' * M * A) = cT c A * (Mᵀ * J * M.map c)ᵀ * A := by
    have : A * (A' * M * A) = M * A := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    calc _ = cT c (A * (A' * M * A)) * Jᵀ * (A * (A' * M * A)) := by rw [← hH, cT_mul c A]; simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [this, cT_mul]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, cT]
  have k : ∀ X : Matrix β β L, cT c A' * (cT c A * X * A) * A' = X := fun X => by
    calc _ = cT c (A * A') * X * (A * A') := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, cT_one, Matrix.one_mul, Matrix.mul_one]
  rw [e, ← hH]
  exact ⟨fun h => by rw [h], fun h => Matrix.transpose_injective ((k _).symm.trans ((congrArg (cT c A' * · * A') h).trans (k _)))⟩

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} {Y : Spc F E n}

omit [NumberField E] in
theorem latW_le : latW Y v ≤ latHat Y := AddSubgroup.closure_mono (by
  rintro _ ⟨a, ha, hi, x, hx, rfl⟩
  have e : a = atPlace v (evFin F v a) := by simpa [atPlace_mul_right] using (idem_smul ha).symm
  refine ⟨a, by rw [e]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun u => ?_, x, hx, rfl⟩
  by_cases hu : u = v
  · exact hu ▸ hi
  · rw [e, show evFin F u (atPlace v (evFin F v a)) = 0 from evalV_singleFin_ne hu _]; exact zero_mem _)

omit [NumberField E] in
theorem idem_mem {z : Fin n → AE F E} (hz : z ∈ latHat Y) : atPlace v (1 : Fv F v) • z ∈ latW Y v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hi, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨atPlace v 1 • a, at_smul_idem v a, by
      rw [smul_eq_mul, map_mul, evFin_atPlace, one_mul]; exact hi v, x, hx, by rw [smul_smul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

omit [NumberField E] in
theorem stab_latW {g : Matrix (Fin n) (Fin n) (AE F E)} (hat : ∀ z ∈ latW Y v, At (evFin F v) z) :
    (∀ z ∈ latHat Y, At (evFin F v) z → g *ᵥ z ∈ latHat Y) ↔ ∀ z ∈ latW Y v, g *ᵥ z ∈ latW Y v :=
  ⟨fun h z hz => idem_smul (at_mulVec_right g (hat z hz)) ▸ idem_mem (h z (latW_le hz) (hat z hz)),
    fun h z hz ha => latW_le (h z (idem_smul ha ▸ idem_mem hz))⟩

omit [NumberField E] in
theorem mulVec_latHat {N : Matrix (Fin n) (Fin n) (AE F E)} (hN : At (evFin F v) N) (h : ∀ z ∈ latW Y v, N *ᵥ z ∈ latW Y v)
    {z : Fin n → AE F E} (hz : z ∈ latHat Y) : N *ᵥ z ∈ latHat Y := by
  have := latW_le (h _ (idem_mem hz))
  rwa [Matrix.mulVec_smul, idem_smul (at_mulVec_left hN z)] at this

omit [NumberField E] in
theorem piInf_at {u : InfinitePlace F} (τ : EmbOver E u) {z : AE F E} (hz : At (evFin F v) z) : piInf τ z = 0 := by
  have h0 : compInf F E u (algebraMap (AF F) (AE F E) (atPlace v 1)) = 0 :=
    (congrArg (· ⊗ₜ[F] _) (show evInf F u (atPlace v 1) = 0 from rfl)).trans (TensorProduct.zero_tmul _ _)
  rw [← idem_smul hz, Algebra.smul_def, piInf, RingHom.comp_apply, map_mul, h0, zero_mul, map_zero]

theorem mem_K {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {k : G2 σ Y}
    (h : ∀ x ∈ ({k, k⁻¹} : Set (G2 σ Y)), At (evFin F v) (mat2 x - 1) ∧ ∀ i j : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) →
      j ∈ ({.inl, .inr} : Set _) → ∀ z ∈ latW Y v, (mat2 x - 1).submatrix i j *ᵥ z ∈ latW Y v) : k ∈ K := by
  refine (hK k).2 ⟨fun u => ?_, fun z z' hz hz' x hx => ?_⟩
  · have : (mat2 k).map (piInf (B.emb u)) = 1 := Matrix.ext fun i j => by
      have := piInf_at (B.emb u) (z := (mat2 k - 1) i j) fun a ha => congrFun (congrFun ((h k (by simp)).1 a ha) i) j
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      simpa [Matrix.one_apply, apply_ite] using this
    rw [this]; exact Commute.one_left _
  · obtain ⟨h1, h2⟩ := h x hx
    have key : ∀ i : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) → Sum.elim z z' ∘ i ∈ latHat Y →
        (mat2 x *ᵥ Sum.elim z z') ∘ i ∈ latHat Y := fun i hi h3 => by
      have b : ∀ j : Fin n → Fin n ⊕ Fin n, At (evFin F v) ((mat2 x - 1).submatrix i j) := fun j a ha =>
        Matrix.ext fun _ _ => congrFun (congrFun (h1 a ha) _) _
      convert add_mem h3 (add_mem (mulVec_latHat (b .inl) (h2 i _ hi (by simp)) hz) (mulVec_latHat (b .inr) (h2 i _ hi (by simp)) hz'))
      have : mat2 x *ᵥ Sum.elim z z' = Sum.elim z z' + (mat2 x - 1) *ᵥ Sum.elim z z' := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      rw [this]
      ext l
      simp [Matrix.mulVec, dotProduct]
    exact ⟨key _ (by simp) hz, key _ (by simp) hz'⟩

variable (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

variable (β) in

def up : Matrix β β (w.adicCompletion E) →* Matrix β β (AE F E) :=
  (liftM E v β).comp (RingHom.mapMatrix (complEquiv hw h).symm.toRingHom).toMonoidHom

theorem up_pi (m : Matrix β β (w.adicCompletion E)) : (up hw h β m).map (piE h) = m := Matrix.ext fun i j =>
  (congrArg (toCompl h) (congrFun (congrFun (comp_liftM v _) i) j)).trans ((complEquiv hw h).apply_symm_apply _)

theorem up_aw (m : Matrix β β (w.adicCompletion E)) : (up hw h β m).map (aw E v) = 1 := aw_liftM v _

theorem up_at (m : Matrix β β (w.adicCompletion E)) : At (evFin F v) (up hw h β m - 1) := at_liftM v _

include hw in
theorem extW {ι κ : Type} {a b : Matrix ι κ (AE F E)} (h1 : a.map (piE h) = b.map (piE h)) (h2 : a.map (aw E v) = b.map (aw E v)) :
    a = b := extM v (Matrix.ext fun i j => (toCompl_bijective hw h).1 (congrFun (congrFun h1 i) j)) h2

theorem continuous_tensAt : Continuous (tensAt E v : Ev E v → AE F E) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  let b := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
  have e : (tensAt E v : Ev E v → AE F E) = fun y => ∑ i, atPlace v (b.coord i y) • tensAt E v (b i) := by
    funext y
    conv_lhs => rw [← b.sum_repr y, map_sum]
    exact Finset.sum_congr rfl fun i _ => smul_tensAt v _ _
  rw [e]
  exact continuous_finset_sum _ fun i _ => ((GlobalTheory.VacAny.continuous_atPlace v).comp
    (IsModuleTopology.continuous_of_linearMap (b.coord i))).smul continuous_const

theorem continuous_up : Continuous (up hw h β) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : IsTopologicalAddGroup (Ev E v) := IsModuleTopology.topologicalAddGroup (Fv F v) _
  have c1 : Continuous (liftM E v β) :=
    continuous_const.add ((continuous_id.sub continuous_const).matrix_map continuous_tensAt)
  exact c1.comp (continuous_id.matrix_map (continuous_complEquiv hw h).2)

include hw in
theorem continuous_piE : Continuous (piE h) := (continuous_complEquiv hw h).1.comp
  (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd))

variable {h} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {J : Matrix β β (AE F E)}
  {A : Matrix β γ (w.adicCompletion E)} {A' : Matrix γ β (w.adicCompletion E)} (h1 : A * A' = 1) (h2 : A' * A = 1)
  {H : Matrix γ γ (w.adicCompletion E)} (hH : cT c A * (J.map (piE h))ᵀ * A = H)

omit [DecidableEq β] in
include hc in
theorem pi_gram (M : Matrix β β (AE F E)) :
    (Mᵀ * J * M.map (cA σ)).map (piE h) = (M.map (piE h))ᵀ * J.map (piE h) * (M.map (piE h)).map c := by
  rw [Matrix.map_mul, Matrix.map_mul]
  exact congrArg _ (Matrix.ext fun i j => piE_cA hc _)

def liftW : UJ c H →* UG (cA σ) J :=
  ((Units.map ((up hw h β).comp (conjM h1 h2))).comp (UJ c H).subtype).codRestrict _ fun g => by
    change (up hw h β (A * g.1.1 * A'))ᵀ * J * (up hw h β (A * g.1.1 * A')).map (cA σ) = J
    refine extW hw h ?_ ?_
    · rw [pi_gram hc, up_pi, iso_iff c h1 hH, show A' * (A * g.1.1 * A') * A = A' * A * g.1.1 * (A' * A) by
        simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
      exact g.2
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, awM_cA, up_aw, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]

def downW : UG (cA σ) J →* UJ c H :=
  ((Units.map ((conjM h2 h1).comp (piE h).mapMatrix.toMonoidHom)).comp (UG (cA σ) J).subtype).codRestrict _ fun g =>
    (iso_iff c h1 hH _).1 ((pi_gram hc g.1.1).symm.trans (congrArg (·.map (piE h)) g.2))

theorem continuous_liftW : Continuous (liftW hw hc h1 h2 hH) :=
  ((Units.continuous_map ((continuous_up hw h).comp ((continuous_const.matrix_mul continuous_id).matrix_mul
    continuous_const))).comp continuous_subtype_val).subtype_mk _

include hw in
theorem continuous_downW : Continuous (downW hc h1 h2 hH) :=
  ((Units.continuous_map ((continuous_const.matrix_mul (continuous_id.matrix_map (continuous_piE hw h))).matrix_mul
    continuous_const)).comp continuous_subtype_val).subtype_mk _

theorem down_lift (x : UJ c H) : downW hc h1 h2 hH (liftW hw hc h1 h2 hH x) = x := Subtype.ext (Units.ext (by
  change A' * (up hw h β (A * x.1.1 * A')).map (piE h) * A = x.1.1
  rw [up_pi, show A' * (A * x.1.1 * A') * A = A' * A * x.1.1 * (A' * A) by simp only [Matrix.mul_assoc], h2, Matrix.one_mul,
    Matrix.mul_one]))

theorem lift_down {g : UG (cA σ) J} (hg : At (evFin F v) (g.1.1 - 1)) : liftW hw hc h1 h2 hH (downW hc h1 h2 hH g) = g :=
  Subtype.ext (Units.ext (mat_inj hw h (sub_sub_sub_cancel_right _ _ (1 : Matrix β β (AE F E)) ▸ at_sub (up_at hw h _) hg) (by
    refine (up_pi hw h _).trans ?_
    change A * (A' * g.1.1.map (piE h) * A) * A' = _
    rw [show ∀ M, A * (A' * M * A) * A' = A * A' * M * (A * A') from fun M => by simp only [Matrix.mul_assoc], h1, Matrix.one_mul,
      Matrix.mul_one])))

end GlobalTheory.ThK.Dbl.Inert

end
