import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.BaseChg

section Gen

variable {F : Type} [Field F] {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k']
  (ψ : k →ₐ[F] k')

theorem sigR_map {A : Type} [Field A] [Algebra F A] (τ : A →ₐ[F] A) (z : k ⊗[F] A) :
    sigR k' τ (Algebra.TensorProduct.map ψ (AlgHom.id F A) z) =
      Algebra.TensorProduct.map ψ (AlgHom.id F A) (sigR k τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => simp [sigR]

theorem mapH_diagH' {A : Type} [Field A] [Algebra F A] (τ : A →ₐ[F] A) {m : ℕ} (G : Matrix (Fin m) (Fin m) A)
    (g : Formalism.UG.UJ (τ : A →+* A) G) : mapH τ G ψ (diagH τ G k g) = diagH τ G k' g := by
  apply Subtype.ext; apply Units.ext; ext i j
  show Algebra.TensorProduct.map ψ (AlgHom.id F A) (inclR k _) = inclR k' _
  simp [inclR]

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] (s : A →+* A) (G : Matrix ι ι A)

theorem hform_add_left (u u' v : ι → A) :
    Formalism.UG.hform s G (u + u') v = Formalism.UG.hform s G u v + Formalism.UG.hform s G u' v := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (u v v' : ι → A) :
    Formalism.UG.hform s G u (v + v') = Formalism.UG.hform s G u v + Formalism.UG.hform s G u v' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_zero_left (v : ι → A) : Formalism.UG.hform s G 0 v = 0 := by simp [Formalism.UG.hform]

theorem hform_zero_right (u : ι → A) : Formalism.UG.hform s G u 0 = 0 := by simp [Formalism.UG.hform]

theorem hform_smul_left (c : A) (u v : ι → A) : Formalism.UG.hform s G (c • u) v = s c * Formalism.UG.hform s G u v := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_right (c : A) (u v : ι → A) : Formalism.UG.hform s G u (c • v) = c * Formalism.UG.hform s G u v := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

abbrev mapL {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') :
    k ⊗[F] Fld P →ₐ[F] k' ⊗[F] Fld P := Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P))

abbrev mapE {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') :
    k ⊗[F] E →ₐ[F] k' ⊗[F] E := Algebra.TensorProduct.map ψ (AlgHom.id F E)

abbrev dimL : ℕ := Module.finrank E (Fld P)

section Coord

variable (k : Type) [CommRing k] [Algebra F k]

def coordF : (k ⊗[F] Fld P) ≃ₗ[F] (Fin (dimL P) → k ⊗[F] E) :=
  LinearEquiv.lTensor k ((Module.finBasis E (Fld P)).equivFun.restrictScalars F) ≪≫ₗ
    TensorProduct.piRight F F k (fun _ : Fin (dimL P) => E)

theorem coordF_tmul (a : k) (l : Fld P) (i : Fin (dimL P)) :
    coordF P k (a ⊗ₜ l) i = a ⊗ₜ (Module.finBasis E (Fld P)).repr l i := by
  simp [coordF]

theorem coordF_smul (c : k ⊗[F] E) (y : k ⊗[F] Fld P) : coordF P k (c • y) = c • coordF P k y := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' hc hc' => simp [add_smul, hc, hc']
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp [smul_add, hy, hy']
    | tmul b l =>
      funext i
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.tmul_mul_tmul, coordF_tmul, Pi.smul_apply, smul_eq_mul]
      rw [← Algebra.smul_def, map_smul]
      simp

def coordE : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin (dimL P) → k ⊗[F] E) :=
  { coordF P k with map_smul' := fun c y => coordF_smul P k c y }

theorem coordE_apply (y : k ⊗[F] Fld P) : coordE P k y = coordF P k y := rfl

end Coord

variable {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k')

theorem coordF_map (y : k ⊗[F] Fld P) : coordF P k' (mapL P ψ y) = fun i => mapE ψ (coordF P k y i) := by
  induction y using TensorProduct.induction_on with
  | zero => funext i; simp
  | add y y' hy hy' => funext i; simp only [map_add, hy, hy', Pi.add_apply]
  | tmul a l => funext i; simp [coordF_tmul]

end GlobalTheory.TrEll.BaseChg

namespace GlobalTheory.TrEll.BaseChg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
variable {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') {n : ℕ}

theorem exists_natural (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) :
    ∃ φ' : (k' ⊗[F] Fld P) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E),
      ∀ y, φ' (mapL P ψ y) = fun i => mapE ψ (φ y i) := by
  classical
  let ρ := (coordE P k).symm ≪≫ₗ φ
  let A := LinearMap.toMatrix' ρ.toLinearMap
  let B := LinearMap.toMatrix' ρ.symm.toLinearMap
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1; ext v; simp
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1; ext v; simp
  let f : k ⊗[F] E →+* k' ⊗[F] E := (mapE ψ).toRingHom
  have hAB' : A.map f * B.map f = 1 := by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero f) (map_one f)]
  have hBA' : B.map f * A.map f = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero f) (map_one f)]
  let ρ' : (Fin (dimL P) → k' ⊗[F] E) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E) :=
    LinearEquiv.ofLinear (Matrix.toLin' (A.map f)) (Matrix.toLin' (B.map f))
      (by rw [← Matrix.toLin'_mul, hAB', Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hBA', Matrix.toLin'_one])
  have hA : ∀ v, A *ᵥ v = ρ v := fun v => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  refine ⟨coordE P k' ≪≫ₗ ρ', fun y => ?_⟩
  funext i
  show (A.map f *ᵥ coordE P k' (mapL P ψ y)) i = _
  rw [coordE_apply, coordF_map]
  have := RingHom.map_mulVec f A (coordF P k y) i
  rw [hA] at this
  refine this.symm.trans ?_
  show f (φ ((coordE P k).symm (coordE P k y)) i) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

theorem trBase_map (z : k ⊗[F] Fld P) : trBase P k' (mapL P ψ z) = mapE ψ (trBase P k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a l => simp [trBase]

theorem trBase_tmul_one_mul (a : k') (z : k' ⊗[F] Fld P) :
    trBase P k' ((a ⊗ₜ 1) * z) = (a ⊗ₜ 1) * trBase P k' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | tmul b l => simp [trBase, Algebra.TensorProduct.tmul_mul_tmul]

theorem hx_map (x y y' : k ⊗[F] Fld P) :
    hx P k' (mapL P ψ x) (mapL P ψ y) (mapL P ψ y') = mapE ψ (hx P k x y y') := by
  simp only [hx, ← trBase_map, map_mul]
  rw [sigR_map]

theorem map_hform (J : Matrix (Fin n) (Fin n) E) (u v : Fin n → k ⊗[F] E) :
    mapE ψ (Formalism.UG.hform (sigR k σ) (JR k J) u v) =
      Formalism.UG.hform (sigR k' σ) (JR k' J) (fun i => mapE ψ (u i)) (fun i => mapE ψ (v i)) := by
  simp only [Formalism.UG.hform, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← sigR_map]
  congr 2
  simp [JR, inclR]

end GlobalTheory.TrEll.BaseChg

namespace GlobalTheory.TrEll.BaseChg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
variable {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') {n : ℕ}

theorem tmul_eq_smul (a : k') (l : Fld P) :
    (a ⊗ₜ[F] l : k' ⊗[F] Fld P) = ((a ⊗ₜ[F] (1 : E) : k' ⊗[F] E)) • ((1 : k') ⊗ₜ[F] l) := by
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  simp

theorem isIsom_map {J : Matrix (Fin n) (Fin n) E} {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ)
    {φ' : (k' ⊗[F] Fld P) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E)}
    (hφ' : ∀ y, φ' (mapL P ψ y) = fun i => mapE ψ (φ y i)) : IsIsom P k' J (mapL P ψ x) φ' := by
  have base : ∀ l l' : Fld P, Formalism.UG.hform (sigR k' σ) (JR k' J) (φ' ((1 : k') ⊗ₜ l')) (φ' ((1 : k') ⊗ₜ l)) =
      hx P k' (mapL P ψ x) ((1 : k') ⊗ₜ l) ((1 : k') ⊗ₜ l') := by
    intro l l'
    have e : ∀ m : Fld P, ((1 : k') ⊗ₜ[F] m : k' ⊗[F] Fld P) = mapL P ψ ((1 : k) ⊗ₜ m) := fun m => by simp
    rw [e l, e l', hφ', hφ', ← map_hform, h, hx_map]
  intro y y'
  induction y using TensorProduct.induction_on with
  | zero => simp [hx, hform_zero_right]
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, hform_add_right, h₁, h₂]; simp only [hx, add_mul, mul_add, map_add]
  | tmul a l =>
    induction y' using TensorProduct.induction_on with
    | zero => simp [hx, hform_zero_left]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, hform_add_left, h₁, h₂]; simp only [hx, add_mul, mul_add, map_add]
    | tmul a' l' =>
      rw [tmul_eq_smul P a l, tmul_eq_smul P a' l', map_smul, map_smul, hform_smul_left, hform_smul_right, base]
      simp only [hx, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have s1 : sigR k' σ (a' ⊗ₜ[F] (1 : E)) = a' ⊗ₜ 1 := by simp [sigR]
      rw [s1]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        map_one]
      have s2 : sigR k' (star' P) (a' ⊗ₜ[F] (1 : Fld P)) = a' ⊗ₜ 1 := by simp [sigR]
      rw [RingHom.map_mul (sigR k' (star' P)), s2]
      have e3 : mapL P ψ x * (a ⊗ₜ[F] 1 * 1 ⊗ₜ[F] l) * (a' ⊗ₜ[F] 1 * sigR k' (star' P) (1 ⊗ₜ[F] l')) =
          (a' ⊗ₜ[F] 1) * ((a ⊗ₜ[F] 1) * (mapL P ψ x * 1 ⊗ₜ[F] l * sigR k' (star' P) (1 ⊗ₜ[F] l'))) := by ring
      rw [e3, trBase_tmul_one_mul, trBase_tmul_one_mul]

theorem torEmb_map {J : Matrix (Fin n) (Fin n) E} {x : k ⊗[F] Fld P} {x' : k' ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ)
    {φ' : (k' ⊗[F] Fld P) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E)} (h' : IsIsom P k' J x' φ')
    (hφ' : ∀ y, φ' (mapL P ψ y) = fun i => mapE ψ (φ y i)) (t : Tor P k) :
    torEmb h' (mapH (star' P) (one₁ P) ψ t) = mapH σ J ψ (torEmb h t) := by
  classical
  have ht : (torUnit (mapH (star' P) (one₁ P) ψ t)).1 = mapL P ψ (torUnit t).1 := by
    change Matrix.det ((mapH (star' P) (one₁ P) ψ t).1 : Matrix (Fin 1) (Fin 1) (k' ⊗[F] Fld P)) =
      (mapL P ψ : k ⊗[F] Fld P →+* k' ⊗[F] Fld P) (Matrix.det (t.1 : Matrix (Fin 1) (Fin 1) (k ⊗[F] Fld P)))
    rw [RingHom.map_det]; rfl
  apply Subtype.ext; apply Units.ext
  show mulMat φ' (torUnit (mapH (star' P) (one₁ P) ψ t)).1 = (mulMat φ (torUnit t).1).map (mapE ψ).toRingHom
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have hs : (Pi.single j 1 : Fin n → k' ⊗[F] E) = fun i => mapE ψ (φ (φ.symm (Pi.single j 1)) i) := by
    funext i
    rw [LinearEquiv.apply_symm_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_apply, hij]
  rw [hs, ← hφ', mulMat_mulVec, ht, ← map_mul, hφ']
  funext i
  rw [← mulMat_mulVec φ, LinearEquiv.apply_symm_apply]
  rw [hφ', LinearEquiv.apply_symm_apply]
  exact RingHom.map_mulVec (mapE (E := E) ψ).toRingHom (mulMat φ (torUnit t).1) (Pi.single j 1) i

end GlobalTheory.TrEll.BaseChg

namespace GlobalTheory.TrEll.BaseChg

theorem exists_isom_baseChange : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k k' : Type) [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ (x' : plusUnits P k') (φ' : (k' ⊗[F] Fld P) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E)) (h' : IsIsom P k' J x'.1.1 φ'), x'.1.1 = Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P)) x.1.1 ∧ gam h' = mapH σ J ψ (gam h) ∧ ∀ t, torEmb h' (mapH (star' P) (one₁ P) ψ t) = mapH σ J ψ (torEmb h t) := by
  intro F E _ _ _ _ _ σ _ r n P J _ k k' _ _ _ _ ψ x φ h
  obtain ⟨φ', hφ'⟩ := exists_natural P ψ φ
  have hx : sigR k (star' P) x.1.1 = x.1.1 := congrArg Units.val x.2
  let x' : plusUnits P k' := ⟨Units.map (mapL P ψ).toMonoidHom x.1, by
    show Units.map (sigR k' (star' P)).toMonoidHom (Units.map (mapL P ψ).toMonoidHom x.1) = Units.map (mapL P ψ).toMonoidHom x.1
    apply Units.ext
    show sigR k' (star' P) (mapL P ψ x.1.1) = mapL P ψ x.1.1
    rw [sigR_map, hx]⟩
  have h' : IsIsom P k' J x'.1.1 φ' := isIsom_map P ψ h hφ'
  have ht : ∀ t, torEmb h' (mapH (star' P) (one₁ P) ψ t) = mapH σ J ψ (torEmb h t) := torEmb_map P ψ h h' hφ'
  refine ⟨x', φ', h', rfl, ?_, ht⟩
  show torEmb h' (diagH (star' P) (one₁ P) k' (alphaRat P)) = mapH σ J ψ (torEmb h (diagH (star' P) (one₁ P) k (alphaRat P)))
  rw [← mapH_diagH' ψ, ht]

end GlobalTheory.TrEll.BaseChg
