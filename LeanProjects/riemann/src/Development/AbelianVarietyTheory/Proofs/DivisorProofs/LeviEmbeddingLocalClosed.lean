import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
noncomputable section

namespace GlobalTheory.LeviSectionH

open Matrix

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

theorem vmv_mulVec (a b u : Fin n → R) : vecMulVec a b *ᵥ u = (b ⬝ᵥ u) • a := by
  ext i; simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

theorem vmv_mul_vmv (a b u w : Fin n → R) : vecMulVec a b * vecMulVec u w = (b ⬝ᵥ u) • vecMulVec a w := by
  ext i j; simp only [mul_apply, vecMulVec_apply, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem vmv_mul (a b : Fin n → R) (M : Matrix (Fin n) (Fin n) R) : vecMulVec a b * M = vecMulVec a (b ᵥ* M) :=
  Matrix.vecMulVec_mul a b M

theorem mul_vmv (M : Matrix (Fin n) (Fin n) R) (a b : Fin n → R) : M * vecMulVec a b = vecMulVec (M *ᵥ a) b :=
  Matrix.mul_vecMulVec M a b

variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

def cv (u : Fin n → R) : Fin n → R := fun i => c (u i)

def levH (x y : Fin n → R) (s r : R) : Matrix (Fin n) (Fin n) R :=
  1 + (s - 1) • vecMulVec x (J *ᵥ cv c y) + (r - 1) • vecMulVec y (J *ᵥ cv c x)

variable {c J}

theorem form_swap (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) (u w : Fin n → R) :
    c (u ⬝ᵥ J *ᵥ cv c w) = w ⬝ᵥ J *ᵥ cv c u := by
  simp only [dotProduct, mulVec, cv, map_sum, map_mul, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem vecMul_J (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) (u : Fin n → R) :
    u ᵥ* J = cv c (J *ᵥ cv c u) := by
  ext j
  simp only [vecMul, mulVec, dotProduct, cv, map_sum, map_mul, hc, hJ]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cv_dot (a b : Fin n → R) : cv c a ⬝ᵥ cv c b = c (a ⬝ᵥ b) := by
  simp [dotProduct, cv, map_sum]

variable {x y : Fin n → R}

section Rel
variable (hxx : x ⬝ᵥ J *ᵥ cv c x = 0) (hyy : y ⬝ᵥ J *ᵥ cv c y = 0) (hxy : x ⬝ᵥ J *ᵥ cv c y = 1)
  (hyx : y ⬝ᵥ J *ᵥ cv c x = 1)
include hxx hyy hxy hyx

theorem levH_mulVec_x (s r : R) : levH c J x y s r *ᵥ x = s • x := by
  rw [levH, add_mulVec, add_mulVec, one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vmv_mulVec, vmv_mulVec,
    dotProduct_comm, hxy, dotProduct_comm, hxx]
  module

theorem levH_y (s r : R) : levH c J x y s r *ᵥ y = r • y := by
  rw [levH, add_mulVec, add_mulVec, one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vmv_mulVec, vmv_mulVec,
    dotProduct_comm, hyy, dotProduct_comm, hyx]
  module

theorem levH_mul (s r s' r' : R) : levH c J x y s r * levH c J x y s' r' = levH c J x y (s * s') (r * r') := by
  simp only [levH, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    vmv_mul_vmv]
  rw [dotProduct_comm (J *ᵥ cv c y) x, hxy, dotProduct_comm (J *ᵥ cv c y) y, hyy,
    dotProduct_comm (J *ᵥ cv c x) x, hxx, dotProduct_comm (J *ᵥ cv c x) y, hyx]
  module

end Rel

theorem levH_one (x y : Fin n → R) : levH c J x y 1 1 = 1 := by simp [levH]

theorem levH_fix {m : ℕ} (ι : Matrix (Fin n) (Fin m) R)
    (h : ∀ j, (fun i => ι i j) ⬝ᵥ J *ᵥ cv c x = 0 ∧ (fun i => ι i j) ⬝ᵥ J *ᵥ cv c y = 0) (s r : R) :
    levH c J x y s r * ι = ι := by
  have h1 : (J *ᵥ cv c y) ᵥ* ι = 0 := by
    ext j; rw [Pi.zero_apply, ← (h j).2, dotProduct_comm]; rfl
  have h2 : (J *ᵥ cv c x) ᵥ* ι = 0 := by
    ext j; rw [Pi.zero_apply, ← (h j).1, dotProduct_comm]; rfl
  rw [levH, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, h1, h2]
  ext i j; simp [vecMulVec_apply]

theorem levH_unitary (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = J i j) (hxx : x ⬝ᵥ J *ᵥ cv c x = 0)
    (hyy : y ⬝ᵥ J *ᵥ cv c y = 0) (hxy : x ⬝ᵥ J *ᵥ cv c y = 1) (hyx : y ⬝ᵥ J *ᵥ cv c x = 1) (s r : R)
    (h1 : s * c r = 1) (h2 : c s * r = 1) :
    (levH c J x y s r)ᵀ * J * (levH c J x y s r).map c = J := by
  have hm : (levH c J x y s r).map c = 1 + (c s - 1) • vecMulVec (cv c x) (cv c (J *ᵥ cv c y)) +
      (c r - 1) • vecMulVec (cv c y) (cv c (J *ᵥ cv c x)) := by
    ext i j; by_cases h : i = j <;> simp [levH, cv, one_apply, h, vecMulVec_apply]
  have ht : (levH c J x y s r)ᵀ = 1 + (s - 1) • vecMulVec (J *ᵥ cv c y) x + (r - 1) • vecMulVec (J *ᵥ cv c x) y := by
    simp [levH, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  have hA : vecMulVec (J *ᵥ cv c y) x * J = vecMulVec (J *ᵥ cv c y) (cv c (J *ᵥ cv c x)) := by
    rw [vmv_mul, vecMul_J hc hJ]
  have hB : vecMulVec (J *ᵥ cv c x) y * J = vecMulVec (J *ᵥ cv c x) (cv c (J *ᵥ cv c y)) := by
    rw [vmv_mul, vecMul_J hc hJ]
  have hC : J * vecMulVec (cv c x) (cv c (J *ᵥ cv c y)) = vecMulVec (J *ᵥ cv c x) (cv c (J *ᵥ cv c y)) := mul_vmv _ _ _
  have hD : J * vecMulVec (cv c y) (cv c (J *ᵥ cv c x)) = vecMulVec (J *ᵥ cv c y) (cv c (J *ᵥ cv c x)) := mul_vmv _ _ _
  have d1 : cv c (J *ᵥ cv c x) ⬝ᵥ cv c x = 0 := by rw [cv_dot, dotProduct_comm, hxx, map_zero]
  have d2 : cv c (J *ᵥ cv c x) ⬝ᵥ cv c y = 1 := by rw [cv_dot, dotProduct_comm, hyx, map_one]
  have d3 : cv c (J *ᵥ cv c y) ⬝ᵥ cv c x = 1 := by rw [cv_dot, dotProduct_comm, hxy, map_one]
  have d4 : cv c (J *ᵥ cv c y) ⬝ᵥ cv c y = 0 := by rw [cv_dot, dotProduct_comm, hyy, map_zero]
  rw [hm, ht]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hA, hB,
    hC, hD, vmv_mul_vmv, d1, d2, d3, d4, zero_smul, one_smul, smul_zero]
  linear_combination (norm := module) h1 • vecMulVec (J *ᵥ cv c y) (cv c (J *ᵥ cv c x)) +
    h2 • vecMulVec (J *ᵥ cv c x) (cv c (J *ᵥ cv c y))

end Alg

section Adelic

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem sig_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_inclR (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_cA_of (hσ : ∀ x, σ (σ x) = x) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cv_incV (w : Fin n → E) : cv (cA σ).toRingHom (incV F w) = incV F (fun i => σ (w i)) := by
  ext i; exact cA_inclR (w i)

theorem dot_incV (J : Matrix (Fin n) (Fin n) E) (u w : Fin n → E) :
    incV F u ⬝ᵥ incM F J *ᵥ cv (cA σ).toRingHom (incV F w) = inclR (AF F) (form σ J u w) := by
  rw [cv_incV]
  simp [dotProduct, mulVec, incV, incM, form, map_sum, map_mul]

end Adelic

section Hom

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
variable (σ) in

def levU (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (t : (AE F E)ˣ) : Matrix (Fin n) (Fin n) (AE F E) :=
  levH (cA σ).toRingHom (incM F J) (incV F x) (incV F y) t (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E))

section Rels
variable {J : Matrix (Fin n) (Fin n) E} {x y : Fin n → E} (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j)
  (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
include hσ hJ hxx hyy hxy

theorem rels : (∀ i j, (cA σ).toRingHom (incM F J j i) = incM F J i j) ∧
    incV F x ⬝ᵥ incM F J *ᵥ cv (cA σ).toRingHom (incV F x) = 0 ∧
    incV F y ⬝ᵥ incM F J *ᵥ cv (cA σ).toRingHom (incV F y) = 0 ∧
    incV F x ⬝ᵥ incM F J *ᵥ cv (cA σ).toRingHom (incV F y) = 1 ∧
    incV F y ⬝ᵥ incM F J *ᵥ cv (cA σ).toRingHom (incV F x) = 1 := by
  have hJA : ∀ i j, (cA σ).toRingHom (incM F J j i) = incM F J i j := fun i j => by
    show cA σ (inclR (AF F) (J j i)) = inclR (AF F) (J i j)
    rw [cA_inclR, hJ]
  have hXY : incV F x ⬝ᵥ incM F J *ᵥ cv (cA σ).toRingHom (incV F y) = 1 := by rw [dot_incV, hxy, map_one]
  refine ⟨hJA, by rw [dot_incV, hxx, map_zero], by rw [dot_incV, hyy, map_zero], hXY, ?_⟩
  rw [← form_swap (cA_cA_of hσ) hJA, hXY, map_one]

theorem levU_mul (t s : (AE F E)ˣ) : levU σ J x y t * levU σ J x y s = levU σ J x y (t * s) := by
  obtain ⟨_, h1, h2, h3, h4⟩ := rels hσ hJ hxx hyy hxy
  rw [levU, levU, levU, levH_mul h1 h2 h3 h4, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  congr 1; rw [map_mul, mul_comm]

omit hσ hJ hxx hyy hxy in
theorem levU_one : levU σ J x y 1 = 1 := by
  rw [levU, inv_one, Units.val_one, map_one, levH_one]

variable (x y) in

def leviU : (AE F E)ˣ →* UA σ J where
  toFun t := ⟨⟨levU σ J x y t, levU σ J x y t⁻¹, by rw [levU_mul hσ hJ hxx hyy hxy, mul_inv_cancel, levU_one],
    by rw [levU_mul hσ hJ hxx hyy hxy, inv_mul_cancel, levU_one]⟩, by
    obtain ⟨h0, h1, h2, h3, h4⟩ := rels hσ hJ hxx hyy hxy
    show (levU σ J x y t)ᵀ * incM F J * (levU σ J x y t).map (cA σ) = incM F J
    exact levH_unitary (cA_cA_of hσ) h0 h1 h2 h3 h4 _ _
      (by show (t : AE F E) * cA σ (cA σ _) = 1; rw [cA_cA_of hσ, Units.mul_inv])
      (by show cA σ (t : AE F E) * cA σ _ = 1; rw [← map_mul, Units.mul_inv, map_one])⟩
  map_one' := Subtype.ext (Units.ext levU_one)
  map_mul' t s := Subtype.ext (Units.ext (levU_mul hσ hJ hxx hyy hxy t s).symm)

theorem mat_leviU (t : (AE F E)ˣ) : mat (leviU x y hσ hJ hxx hyy hxy t) = levU σ J x y t := rfl

end Rels
end Hom

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
variable {J : Matrix (Fin n) (Fin n) E} {x y : Fin n → E} (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j)
  (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
include hσ hJ hxx hyy hxy

theorem mat_leviU_mulVec_incV (t : (AE F E)ˣ) : mat (leviU x y hσ hJ hxx hyy hxy t) *ᵥ incV F x = (t : AE F E) • incV F x := by
  obtain ⟨_, h1, h2, h3, h4⟩ := rels hσ hJ hxx hyy hxy
  exact levH_mulVec_x h1 h2 h3 h4 _ _

theorem mat_leviU_y (t : (AE F E)ˣ) :
    mat (leviU x y hσ hJ hxx hyy hxy t) *ᵥ incV F y = cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) • incV F y := by
  obtain ⟨_, h1, h2, h3, h4⟩ := rels hσ hJ hxx hyy hxy
  exact levH_y h1 h2 h3 h4 _ _

theorem mat_leviU_ι {m : ℕ} (ι : Matrix (Fin n) (Fin m) E)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (t : (AE F E)ˣ) :
    mat (leviU x y hσ hJ hxx hyy hxy t) * incM F ι = incM F ι := by
  rw [mat_leviU, levU]
  apply levH_fix
  intro j
  have hcol : (fun i => incM F ι i j) = incV F (ι *ᵥ Pi.single j 1) := by ext i; simp [incV, incM]
  rw [hcol, dot_incV, dot_incV, (horth _).1, (horth _).2, map_zero]
  exact ⟨rfl, rfl⟩

theorem dot_leviUnipotent_x (t : (AE F E)ˣ) :
    (mat (leviU x y hσ hJ hxx hyy hxy t) *ᵥ incV F x) ⬝ᵥ (incM F J *ᵥ cv (cA σ).toRingHom (incV F y)) = t := by
  obtain ⟨_, _, _, h3, _⟩ := rels hσ hJ hxx hyy hxy
  rw [mat_leviU_mulVec_incV, smul_dotProduct, h3, smul_eq_mul, mul_one]

theorem continuous_leviU : Continuous (leviU x y hσ hJ hxx hyy hxy) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hcA : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hval : Continuous fun t : (AE F E)ˣ => levU σ J x y t := by
    simp only [levU, levH]
    fun_prop
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hval, ?_⟩)
  exact hval.comp continuous_inv

end Main

theorem exists_levi_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∃ m₀ : idelesAt E (evFin F v) →* UAtSub σ G.V (evFin F v), Topology.IsClosedEmbedding m₀ ∧
      (∀ t, IsLevi H t.1 (1 : UA σ G₁.V.J) (m₀ t).1) ∧ ∀ t, m₀ t ∈ stabAt σ G.V (evFin F v) H.x → t = 1 := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg X om om' om₁ om₁' hT _ v
  have hσ : ∀ e, σ (σ e) = e := sig_invol hT.base.cm
  have hJ := hT.geo.hV.herm
  have hH := hcfg.hH
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hcA : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  set ψ := leviU H.x H.y hσ hJ hH.xx hH.yy hH.xy with hψ
  have hmem : ∀ t : idelesAt E (evFin F v), (ψ.comp (idelesAt E (evFin F v)).subtype) t ∈ UAtSub σ G.V (evFin F v) := by
    intro t u hu
    have ht1 : u • ((t.1 : AE F E) - 1) = 0 := t.2 u hu
    have ht2 : u • (((t.1⁻¹ : (AE F E)ˣ) : AE F E) - 1) = 0 := (inv_mem t.2) u hu
    have hc2 : u • (cA σ ((t.1⁻¹ : (AE F E)ˣ) : AE F E) - 1) = 0 := by
      rw [← map_one (cA σ), ← map_sub, ← map_smul, ht2, map_zero]
    show u • (levU σ G.V.J H.x H.y t.1 - 1) = 0
    rw [levU, levH, add_assoc, add_sub_cancel_left, smul_add, ← smul_assoc, ← smul_assoc, ht1, hc2, zero_smul, zero_smul,
      add_zero]
  set m₀ := (ψ.comp (idelesAt E (evFin F v)).subtype).codRestrict (UAtSub σ G.V (evFin F v)) hmem with hm₀
  have hmat : ∀ t, mat (m₀ t).1 = mat (ψ t.1) := fun t => rfl
  set p := incM F G.V.J *ᵥ cv (cA σ).toRingHom (incV F H.y) with hp
  let a : UAtSub σ G.V (evFin F v) → AE F E := fun g => (mat g.1 *ᵥ incV F H.x) ⬝ᵥ p
  let a' : UAtSub σ G.V (evFin F v) → AE F E := fun g => (mat g.1⁻¹ *ᵥ incV F H.x) ⬝ᵥ p
  have ha : ∀ t, a (m₀ t) = (t.1 : AE F E) := fun t => dot_leviUnipotent_x hσ hJ hH.xx hH.yy hH.xy t.1
  have ha' : ∀ t, a' (m₀ t) = ((t.1⁻¹ : (AE F E)ˣ) : AE F E) := fun t => by
    show (mat (ψ t.1)⁻¹ *ᵥ incV F H.x) ⬝ᵥ p = _
    rw [← map_inv]
    exact dot_leviUnipotent_x hσ hJ hH.xx hH.yy hH.xy _
  have hm : Continuous fun g : UAtSub σ G.V (evFin F v) => mat g.1 :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hmi : Continuous fun g : UAtSub σ G.V (evFin F v) => mat g.1⁻¹ :=
    Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hac : Continuous a := (hm.matrix_mulVec continuous_const).dotProduct continuous_const
  have hac' : Continuous a' := (hmi.matrix_mulVec continuous_const).dotProduct continuous_const
  have hcont : Continuous m₀ :=
    ((continuous_leviU hσ hJ hH.xx hH.yy hH.xy).comp continuous_subtype_val).subtype_mk _
  have hemb : Topology.IsEmbedding m₀ := by
    refine Topology.IsEmbedding.of_comp hcont (g := fun g => (a g, MulOpposite.op (a' g)))
      (hac.prodMk (MulOpposite.continuous_op.comp hac')) ?_
    have e : ((fun g => (a g, MulOpposite.op (a' g))) ∘ m₀) =
        (Units.embedProduct (AE F E)) ∘ (Subtype.val : idelesAt E (evFin F v) → (AE F E)ˣ) := by
      funext t
      simp only [Function.comp_apply, ha, ha', Units.embedProduct_apply]
    rw [e]
    exact Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range m₀ = {g | a g * a' g = 1 ∧ a' g * a g = 1 ∧
      (∀ u, evFin F v u = 0 → u • (a g - 1) = 0) ∧
      mat g.1 = levH (cA σ).toRingHom (incM F G.V.J) (incV F H.x) (incV F H.y) (a g) (cA σ (a' g))} := by
    ext g
    constructor
    · rintro ⟨t, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [ha, ha']
      exact ⟨Units.mul_inv _, Units.inv_mul _, t.2, rfl⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨⟨a g, a' g, h1, h2⟩, h3⟩, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
      exact h4.symm
  have hclosed : IsClosed (Set.range m₀) := by
    rw [hrange]
    simp only [Set.setOf_and]
    refine (isClosed_eq (hac.mul hac') continuous_const).inter ((isClosed_eq (hac'.mul hac) continuous_const).inter
      (IsClosed.inter ?_ (isClosed_eq hm ?_)))
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun u => isClosed_iInter fun _ =>
        isClosed_eq ((hac.sub continuous_const).const_smul u) continuous_const
    · simp only [levH]
      fun_prop
  refine ⟨m₀, ⟨hemb, hclosed⟩, fun t => ⟨?_, ?_, ?_⟩, fun t ht => ?_⟩
  · exact mat_leviU_mulVec_incV hσ hJ hH.xx hH.yy hH.xy t.1
  · exact mat_leviU_y hσ hJ hH.xx hH.yy hH.xy t.1
  · show mat (ψ t.1) * incM F H.ι = incM F H.ι * mat (1 : UA σ G₁.V.J)
    rw [show mat (1 : UA σ G₁.V.J) = 1 from rfl, Matrix.mul_one]
    exact mat_leviU_ι hσ hJ hH.xx hH.yy hH.xy H.ι hH.orth t.1
  · have h1 : a (m₀ t) = 1 := by
      show (mat (m₀ t).1 *ᵥ incV F H.x) ⬝ᵥ p = 1
      rw [ht]
      exact (rels hσ hJ hH.xx hH.yy hH.xy).2.2.2.1
    rw [ha] at h1
    exact Subtype.ext (Units.ext h1)

end GlobalTheory.LeviSectionH
