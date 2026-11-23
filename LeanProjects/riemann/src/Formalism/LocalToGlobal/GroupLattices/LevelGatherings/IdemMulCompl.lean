import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.FiniteClassSetOfLe

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

section Glue

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (ε : A)

theorem idem_mul_compl (hε : ε * ε = ε) : ε * (1 - ε) = 0 := by
  rw [mul_sub, mul_one, hε, sub_self]

theorem compl_mul_idem (hε : ε * ε = ε) : (1 - ε) * ε = 0 := by
  rw [sub_mul, one_mul, hε, sub_self]

theorem compl_idem (hε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [sub_mul, one_mul, idem_mul_compl ε hε, sub_zero]

def glueM (hε : ε * ε = ε) : Matrix n n A × Matrix n n A →* Matrix n n A where
  toFun x := (1 - ε) • x.1 + ε • x.2
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one]
    rw [← add_smul, sub_add_cancel, one_smul]
  map_mul' := by
    intro x y
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
      compl_idem ε hε, hε, idem_mul_compl ε hε, compl_mul_idem ε hε, zero_smul, add_zero, zero_add]

def glue (hε : ε * ε = ε) : GL n A × GL n A →* GL n A :=
  (Units.map (glueM (n := n) ε hε)).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem glue_val (hε : ε * ε = ε) (g h : GL n A) :
    (glue ε hε (g, h) : Matrix n n A) = (1 - ε) • (g : Matrix n n A) + ε • (h : Matrix n n A) := rfl

theorem bc_glue_zero (hε : ε * ε = ε) {B : Type} [CommRing B] (φ : A →+* B) (h0 : φ ε = 0) (g h : GL n A) :
    bc φ (glue ε hε (g, h)) = bc φ g := by
  apply Units.ext
  ext i j
  simp [bc, glue_val, h0]

theorem bc_glue_one (hε : ε * ε = ε) {B : Type} [CommRing B] (φ : A →+* B) (h1 : φ ε = 1) (g h : GL n A) :
    bc φ (glue ε hε (g, h)) = bc φ h := by
  apply Units.ext
  ext i j
  simp [bc, glue_val, h1]

theorem glue_mem_UJ (hε : ε * ε = ε) (σ : A →+* A) (hσ : σ ε = ε) (J : Matrix n n A) {g h : GL n A} (hg : g ∈ UJ σ J) (hh : h ∈ UJ σ J) :
    glue ε hε (g, h) ∈ UJ σ J := by

  have hσ1 : σ (1 - ε) = 1 - ε := by rw [map_sub, map_one, hσ]
  have hc : ∀ (c : A) (M : Matrix n n A), cT σ (c • M) = σ c • cT σ M := by
    intro c M; ext i j; simp [cT]
  have hadd : ∀ M N : Matrix n n A, cT σ (M + N) = cT σ M + cT σ N := by
    intro M N; ext i j; simp [cT]
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have hh' : cT σ (h : Matrix n n A) * J * (h : Matrix n n A) = J := hh
  show cT σ ((glue ε hε (g, h) : GL n A) : Matrix n n A) * J * ((glue ε hε (g, h) : GL n A) : Matrix n n A) = J
  rw [glue_val, hadd, hc, hc, hσ1, hσ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
    compl_idem ε hε, hε, idem_mul_compl ε hε, compl_mul_idem ε hε, zero_smul, add_zero, zero_add, hg', hh']
  rw [← add_smul, sub_add_cancel, one_smul]

end Glue

section Adele

variable (F : Type) [Field F] [NumberField F] (p : ℕ)

open Classical in

def eP : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if ((p : ℕ) : 𝓞 F) ∈ v.asIdeal then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem idempotentOver_eval_eq_one (v : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) : evalV F v (eP F p) = 1 := by
  show (eP F p) v = 1
  first
  | exact if_pos h
  | simp [eP, h]

theorem idempotentOver_eval_eq_zero (v : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) : evalV F v (eP F p) = 0 := by
  show (eP F p) v = 0
  first
  | exact if_neg h
  | simp [eP, h]

theorem projection_idem : eP F p * eP F p = eP F p := by
  have key : ∀ v, (eP F p * eP F p) v = (eP F p) v := fun v => by
    show (eP F p) v * (eP F p) v = (eP F p) v
    by_cases h : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
    · rw [show (eP F p) v = 1 from idempotentOver_eval_eq_one F p v h, one_mul]
    · rw [show (eP F p) v = 0 from idempotentOver_eval_eq_zero F p v h, zero_mul]
  first
  | exact RestrictedProduct.ext key
  | exact Subtype.ext (funext key)
  | (ext1 v; exact key v)

variable (E : Type) [Field E] [Algebra F E]

def epsP : E ⊗[F] FiniteAdeleRing (𝓞 F) F := (1 : E) ⊗ₜ[F] eP F p

theorem isIdempotentElem_placeIdempotent : epsP F p E * epsP F p E = epsP F p E := by
  rw [epsP, Algebra.TensorProduct.tmul_mul_tmul, one_mul, projection_idem]

theorem epsP_sig (σE : E →ₐ[F] E) : sigR σE (FiniteAdeleRing (𝓞 F) F) (epsP F p E) = epsP F p E := by
  simp [sigR, epsP]

theorem epsP_over (v : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    prV (E := E) v (epsP F p E) = 1 := by
  rw [Algebra.TensorProduct.one_def]
  simp [prV, epsP, idempotentOver_eval_eq_one F p v h]

theorem epsP_off (v : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    prV (E := E) v (epsP F p E) = 0 := by
  simp [prV, epsP, idempotentOver_eval_eq_zero F p v h]

end Adele

section Rep

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

def trivP (sp : Spaces R F E) (p : ℕ) (y : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) :
    UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) :=
  ⟨glue (epsP F p E) (isIdempotentElem_placeIdempotent F p E) ((y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), 1),
    glue_mem_UJ (epsP F p E) (isIdempotentElem_placeIdempotent F p E) _ (epsP_sig F p E sp.cm.sig) _ y.2 (Subgroup.one_mem _)⟩

theorem trivializeAt_component_eq_one_of_mem (p : ℕ) (y : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (h : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    bc (prV (E := E) v) (trivP sp p y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 := by
  exact (bc_glue_one (epsP F p E) (isIdempotentElem_placeIdempotent F p E) (prV (E := E) v) (epsP_over F p E v h)
    (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) 1).trans (map_one _)

theorem trivializeAt_component_of_notMem (p : ℕ) (y : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (h : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    bc (prV (E := E) v) (trivP sp p y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      bc (prV (E := E) v) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
  exact bc_glue_zero (epsP F p E) (isIdempotentElem_placeIdempotent F p E) (prV (E := E) v) (epsP_off F p E v h)
    (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) 1

theorem inv_mul_trivializeAt_mem_away (L : ColLevel R F E sp gp C A clsLat) (p : ℕ)
    (y : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) :
    ((y⁻¹ * trivP sp p y : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ Formalism.L2.Herm.awayFrom₂ L p := by
  unfold Formalism.L2.Herm.awayFrom₂
  refine Subgroup.mem_inf.mpr ⟨(y⁻¹ * trivP sp p y).2, ?_⟩
  refine Subgroup.mem_iInf.mpr fun v => Subgroup.mem_iInf.mpr fun hv => ?_
  rw [Subgroup.mem_comap, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, trivializeAt_component_of_notMem p y v hv,
    inv_mul_cancel]
  exact Subgroup.one_mem _

theorem mk_trivP (L : ColLevel R F E sp gp C A clsLat) (p : ℕ)
    (y : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) :
    (Quotient.mk'' (trivP sp p y) : compL L p) = Quotient.mk'' y := by
  refine ((DoubleCoset.eq _ _ _ _).mpr ⟨1, Subgroup.one_mem _, y⁻¹ * trivP sp p y, ?_, ?_⟩).symm
  · exact Subgroup.mem_subgroupOf.mpr (inv_mul_trivializeAt_mem_away L p y)
  · rw [one_mul, mul_inv_cancel_left]

def repP (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (i : compL L p) :
    UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F) :=
  trivP sp p (Quotient.out i)

theorem repP_mk (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (i : compL L p) :
    (Quotient.mk'' (repP L p i) : compL L p) = i := by
  exact (mk_trivP L p (Quotient.out i)).trans (Quotient.out_eq' i)

theorem repP_over (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (i : compL L p) (v : HeightOneSpectrum (𝓞 F))
    (h : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    bc (prV (E := E) v) (repP L p i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by
  exact trivializeAt_component_eq_one_of_mem p (Quotient.out i) v h

end Rep

end Formalism.L2.G
