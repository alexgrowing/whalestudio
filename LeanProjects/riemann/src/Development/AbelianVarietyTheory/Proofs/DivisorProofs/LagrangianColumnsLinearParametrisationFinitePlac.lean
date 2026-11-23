import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLagParam

open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev lift (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := (liftV v).rTensor E

theorem compFin_lift (v : Pl F) (t : Fv F v ⊗[F] E) : compFin F E v (lift v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftV_one_smul_eq (v : Pl F) (a : AE F E) : liftV v (1 : Fv F v) • a = lift v (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin]
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]

theorem compFin_smul (v : Pl F) (r : AF F) (a : AE F E) : compFin F E v (r • a) = evFin F v r • compFin F E v a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem at_map_lift {α β : Type} (v : Pl F) (A : Matrix α β (Fv F v ⊗[F] E)) : At (evFin F v) (A.map (lift v)) := by
  intro u hu
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  induction A i k using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    rw [← smul_eq_mul, at_liftV v x u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

theorem eq_map_lift {α β : Type} (v : Pl F) (z : Matrix α β (AE F E)) (hz : At (evFin F v) z) :
    z = (z.map (compFin F E v)).map (lift v) := by
  conv_lhs => rw [← liftV_one_smul v z hz]
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, liftV_one_smul_eq]

theorem map_lift_compFin {α β : Type} (v : Pl F) (A : Matrix α β (Fv F v ⊗[F] E)) :
    (A.map (lift v)).map (compFin F E v) = A := by
  ext i k; simp [compFin_lift]

end GlobalTheory.InertLagParam
end

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem card_eq_of_inv {R : Type} [CommRing R] [Nontrivial R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (A : Matrix α β R) (B : Matrix β α R) (h1 : A * B = 1) (h2 : B * A = 1) :
    Fintype.card α = Fintype.card β := by
  let f : (β → R) ≃ₗ[R] (α → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := f.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

theorem eq_zero_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (v : Pl F) (u : W) (hu : At (evFin F v) u) (h0 : locCo co v u = 0) : u = 0 := by
  have h1 : co.e u = liftV v (1 : Fv F v) • co.e u := by rw [← LinearEquiv.map_smul, liftV_one_smul v u hu]
  have h2 : co.e u = 0 := by
    rw [h1]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have := congrArg (fun p => p.1 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
    · have := congrArg (fun p => p.2 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
  exact co.e.map_eq_zero_iff.1 h2

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam

def mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin m) R →ₗ[R] Matrix (Fin n) (Fin m) R where
  toFun x := A * x
  map_add' x y := Matrix.mul_add A x y
  map_smul' c x := Matrix.mul_smul A c x

theorem det_mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.det (mulLeft n m A) = A.det ^ m := by
  let τ : Matrix (Fin n) (Fin m) R ≃ₗ[R] (Fin m → Fin n → R) :=
    { toFun := fun x k i => x i k
      invFun := fun y => Matrix.of fun i k => y k i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : (τ : _ →ₗ[R] _) ∘ₗ mulLeft n m A ∘ₗ (τ.symm : (Fin m → Fin n → R) →ₗ[R] _) =
      LinearMap.pi fun k : Fin m => Matrix.toLin' A ∘ₗ LinearMap.proj k := by
    refine LinearMap.ext fun y => ?_
    funext k i
    rfl
  rw [← LinearMap.det_conj (mulLeft n m A) τ, h, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

theorem param : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl F)
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E)), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (AE F E), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  intro F E _ _ _ _ _ σ n d X W M v m C hC
  obtain ⟨h0, Cx, P, hx, h1, h2⟩ := hC
  have hP1 : P.toRows₁ * C.map (compFin F E v) = 1 := by
    have h2' := h2
    rw [← Matrix.fromRows_toRows P, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at h2'
    exact h2'.1
  refine ⟨?_, ?_⟩
  · have := card_eq_of_inv _ _ h1 h2
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  let Z := Matrix (Fin n) (Fin m) (Fv F v ⊗[F] E)
  let N := Module.finrank (Fv F v) Z
  let e : (Fin N → Fv F v) ≃ₗ[Fv F v] Z := (Module.finBasis (Fv F v) Z).equivFun.symm
  let ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E) := fun y => (e y).map (lift v)
  have hζat : ∀ y, At (evFin F v) (ζ y) := fun y => at_map_lift v _
  have hζc : ∀ y, (ζ y).map (compFin F E v) = e y := fun y => map_lift_compFin v _
  have hζadd : ∀ y y', ζ (y + y') = ζ y + ζ y' := fun y y' => by
    simp only [ζ, map_add]
    exact Matrix.map_add _ (map_add _) _ _
  have hζsmul : ∀ (a : Fv F v) y, ζ (a • y) = liftV v a • ζ y := fun a y => by
    have hat : At (evFin F v) (liftV v a • ζ y) := fun u hu => by rw [smul_comm, hζat y u hu, smul_zero]
    rw [eq_map_lift v _ hat]
    congr 1
    ext i k
    simp [ζ, compFin_smul, evFin_liftV, compFin_lift] <;> rfl
  let j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun y => locCo M.co v (ζ y * Cᵀ)
      map_add' := fun y y' => by rw [hζadd, Matrix.add_mul, map_add]
      map_smul' := fun a y => by
        rw [hζsmul, Matrix.smul_mul]
        ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul] }
  refine ⟨N, j, ζ, ?_, fun y => ⟨hζat y, rfl⟩, fun z hz => ?_, fun s => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hu := eq_zero_of_locCo M.co v _ (at_mul v _ (hζat y) _) hy
    have h3 : e y * (C.map (compFin F E v))ᵀ = 0 := by
      have := congrArg (fun x => Matrix.map x (compFin F E v)) hu
      simp only [Matrix.map_mul, Matrix.transpose_map, hζc, Matrix.map_zero _ (map_zero _)] at this
      exact this
    have h4 : e y = 0 := by
      have h5 : e y = e y * (P.toRows₁ * C.map (compFin F E v))ᵀ := by
        rw [hP1, Matrix.transpose_one, Matrix.mul_one]
      rw [h5, Matrix.transpose_mul, ← Matrix.mul_assoc, h3, Matrix.zero_mul]
    exact e.map_eq_zero_iff.1 h4
  · exact ⟨e.symm (z.map (compFin F E v)), by simp only [ζ, LinearEquiv.apply_symm_apply]; exact (eq_map_lift v z hz).symm⟩
  · let sv := s.val.map (compFin F E v)
    let L : Z →ₗ[Fv F v] Z := (mulLeft n m sv).restrictScalars (Fv F v)
    let f := e.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap
    have hdet : (LinearMap.toMatrix' f).det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
      rw [LinearMap.det_toMatrix']
      have hf : f = e.symm.toLinearMap ∘ₗ L ∘ₗ e.symm.symm.toLinearMap := rfl
      rw [hf, LinearMap.det_conj, LinearMap.det_restrictScalars, det_mulLeft, map_pow, RingHom.map_det]
      rfl
    have hs : IsUnit s.val.det := by simpa using (Matrix.GeneralLinearGroup.det s).isUnit
    have hne : (LinearMap.toMatrix' f).det ≠ 0 := by
      rw [hdet]
      exact (((hs.map (compFin F E v)).map (Algebra.norm (Fv F v))).pow m).ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, fun y => ?_, hdet⟩
    show ζ (LinearMap.toMatrix' f *ᵥ y) = s.val * ζ y
    rw [LinearMap.toMatrix'_mulVec]
    have hat : At (evFin F v) (s.val * ζ y) := fun u hu => by rw [← Matrix.mul_smul, hζat y u hu, Matrix.mul_zero]
    rw [eq_map_lift v _ hat, Matrix.map_mul, hζc]
    simp [ζ, f, L, mulLeft, sv]

end GlobalTheory.InertLagParam
