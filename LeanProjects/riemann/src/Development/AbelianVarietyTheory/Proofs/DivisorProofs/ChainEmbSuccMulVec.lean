import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT
open GlobalTheory.LeviUnitary

noncomputable section

namespace GlobalTheory.ThK.FlagSemi

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_ext {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g h : UA σ J} (e : mat g = mat h) : g = h :=
  Subtype.ext (Units.ext e)

theorem ext_mulVec_single {R : Type} [CommRing R] {k n : ℕ} {A B : Matrix (Fin k) (Fin n) R}
    (h : ∀ j, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) : A = B := by
  ext i j
  have := congrFun (h j) i
  rwa [mulVec_single_one, mulVec_single_one] at this

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem incV_zero {n : ℕ} : incV F (0 : Fin n → E) = 0 := by funext i; exact map_zero _

theorem mem_ratU_iff {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : g ∈ ratU σ J ↔ ∃ A, incM F A = mat g := by
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  rw [ratU, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ.1, by ext a b; rw [incM, Matrix.map_apply, ← Matrix.GeneralLinearGroup.map_apply, hγ]; rfl⟩
  · rintro ⟨A, hA⟩
    have hd : A.det ≠ 0 := by
      intro h0
      have e := RingHom.map_det (inclR (F := F) (E := E) (AF F)) A
      rw [h0, map_zero] at e
      have h2 := congrArg Matrix.det (mat_inv_mul g)
      rw [det_mul, ← hA, show (incM F A).det = 0 from e.symm, mul_zero, det_one] at h2
      exact zero_ne_one h2
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hd, Units.ext hA⟩

variable (σ) in

def IsProj {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin m) (Fin m) E) (ι : Matrix (Fin n) (Fin m) E)
    (π : Matrix (Fin m) (Fin n) E) : Prop :=
  π * ι = 1 ∧ J * ι.map σ = πᵀ * J₁ ∧ ιᵀ * J = J₁ * π.map σ

section Proj

variable {n m k : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin k) (Fin k) E}
  {ι : Matrix (Fin n) (Fin m) E} {π : Matrix (Fin m) (Fin n) E} {ι' : Matrix (Fin m) (Fin k) E} {π' : Matrix (Fin k) (Fin m) E}

theorem IsProj.mul (h : IsProj σ J J₁ ι π) (h' : IsProj σ J₁ J₂ ι' π') : IsProj σ J J₂ (ι * ι') (π' * π) := by
  have mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E),
      (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc π, h.1, Matrix.one_mul, h'.1]
  · rw [mul, ← Matrix.mul_assoc, h.2.1, Matrix.mul_assoc, h'.2.1, transpose_mul, Matrix.mul_assoc]
  · rw [mul, transpose_mul, Matrix.mul_assoc, h.2.2, ← Matrix.mul_assoc, h'.2.2, Matrix.mul_assoc]

theorem IsProj.q1 (h : IsProj σ J J₁ ι π) : incM F π * incM F ι = 1 := by rw [← incM_mul, h.1, incM_one]

theorem IsProj.q2 (h : IsProj σ J J₁ ι π) : incM F J * (incM F ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F J₁ := by
  rw [incM_conj, ← incM_mul, h.2.1, incM_mul]; rfl

theorem IsProj.q3 (h : IsProj σ J J₁ ι π) : (incM F ι)ᵀ * incM F J = incM F J₁ * (incM F π).map (cA σ).toRingHom := by
  rw [incM_conj, ← incM_mul, ← h.2.2, incM_mul]; rfl

def IsProj.levi (h : IsProj σ J J₁ ι π) : UA σ J₁ →* UA σ J where
  toFun g := ⟨⟨1 + incM F ι * (mat g - 1) * incM F π, 1 + incM F ι * (mat g⁻¹ - 1) * incM F π,
    by rw [ext_mul h.q1, mat_mul_inv]; simp, by rw [ext_mul h.q1, mat_inv_mul]; simp⟩,
    ext_unitary (cA σ).toRingHom h.q1 h.q2 h.q3 g.2⟩
  map_one' := mat_ext (show 1 + incM F ι * (1 - 1) * incM F π = 1 by simp)
  map_mul' g g' := mat_ext (ext_mul h.q1 (mat g) (mat g')).symm

theorem IsProj.mat_levi (h : IsProj σ J J₁ ι π) (g : UA σ J₁) :
    mat (h.levi g) = 1 + incM F ι * (mat g - 1) * incM F π := rfl

theorem IsProj.levi_mul_ι (h : IsProj σ J J₁ ι π) (g : UA σ J₁) : mat (h.levi g) * incM F ι = incM F ι * mat g := by
  rw [h.mat_levi, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, h.q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
    add_sub_cancel]

theorem IsProj.levi_ι (h : IsProj σ J J₁ ι π) (g : UA σ J₁) (z : Fin m → AE F E) :
    mat (h.levi g) *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ (mat g *ᵥ z) := by
  rw [mulVec_mulVec, h.levi_mul_ι, mulVec_mulVec]

theorem IsProj.levi_fix (h : IsProj σ J J₁ ι π) (g : UA σ J₁) {v : Fin n → AE F E} (hv : incM F π *ᵥ v = 0) :
    mat (h.levi g) *ᵥ v = v := by
  rw [h.mat_levi, add_mulVec, one_mulVec, ← mulVec_mulVec, hv, mulVec_zero, add_zero]

theorem IsProj.π_ι (h : IsProj σ J J₁ ι π) (z : Fin m → AE F E) : incM F π *ᵥ (incM F ι *ᵥ z) = z := by
  rw [mulVec_mulVec, h.q1, one_mulVec]

theorem IsProj.continuous_levi (h : IsProj σ J J₁ ι π) : Continuous h.levi := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := (GlobalTheory.UnipCT.topFacts σ J₁).1
  have hm : Continuous fun g : UA σ J₁ => mat g := Units.continuous_val.comp continuous_subtype_val
  have hL : Continuous fun A : Matrix (Fin m) (Fin m) (AE F E) => 1 + incM F ι * (A - 1) * incM F π :=
    continuous_const.add ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const)
  apply Continuous.subtype_mk
  exact Units.continuous_iff.2 ⟨(hL.comp hm).congr fun _ => rfl, (hL.comp (hm.comp continuous_inv)).congr fun _ => rfl⟩

theorem IsProj.levi_rat (h : IsProj σ J J₁ ι π) {g : UA σ J₁} (hg : g ∈ ratU σ J₁) : h.levi g ∈ ratU σ J := by
  obtain ⟨A, hA⟩ := (mem_ratU_iff g).1 hg
  refine (mem_ratU_iff _).2 ⟨1 + ι * (A - 1) * π, ?_⟩
  rw [h.mat_levi, ← hA, incM, Matrix.map_add _ (map_add _), ← incM, ← incM, incM_mul, incM_mul, incM_one]
  congr 3
  rw [incM, Matrix.map_sub _ (map_sub _), ← incM, ← incM, incM_one]

end Proj

theorem unitary_of_act {R : Type} [CommRing R] {n m : ℕ} {κ : Type} [Fintype κ] (c : R →+* R) {J : Matrix (Fin n) (Fin n) R}
    {J₁ : Matrix (Fin m) (Fin m) R} {ι : Matrix (Fin n) (Fin m) R} {π : Matrix (Fin m) (Fin n) R} (hπ : π * ι = 1)
    (h1 : J * ι.map c = πᵀ * J₁) (h2 : ιᵀ * J = J₁ * π.map c) {g : Matrix (Fin n) (Fin n) R} (hg : gᵀ * J * g.map c = J)
    {X : Matrix (Fin n) κ R} (hX : π * X = 0) (hgX : g * X = X) {D : Matrix (Fin m) (Fin m) R} {B : Matrix κ (Fin m) R}
    (hD : ι * D = g * ι - X * B) : Dᵀ * J₁ * D.map c = J₁ := by
  have h3 : π.map c * ι.map c = 1 := by rw [← Matrix.map_mul, hπ, Matrix.map_one _ (map_zero c) (map_one c)]
  have h4 : π.map c * X.map c = 0 := by rw [← Matrix.map_mul, hX, Matrix.map_zero _ (map_zero c)]
  have h5 : ιᵀ * J * ι.map c = J₁ := by rw [h2, Matrix.mul_assoc, h3, Matrix.mul_one]
  have h6 : Xᵀ * (J * ι.map c) = 0 := by rw [h1, ← Matrix.mul_assoc, ← transpose_mul, hX, transpose_zero, Matrix.zero_mul]
  have h7 : ι.map c * D.map c = g.map c * (ι.map c - X.map c * B.map c) := by
    rw [← Matrix.map_mul, hD, Matrix.map_sub _ (map_sub c), Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub,
      ← Matrix.mul_assoc, ← Matrix.map_mul (L := g) (M := X), hgX]
  calc Dᵀ * J₁ * D.map c = (ι * D)ᵀ * (J * ι.map c) * D.map c := by
        rw [← h5, transpose_mul]; simp only [Matrix.mul_assoc]
    _ = ιᵀ * gᵀ * (J * ι.map c) * D.map c := by
        rw [hD, transpose_sub, Matrix.sub_mul, transpose_mul X, Matrix.mul_assoc Bᵀ, h6, Matrix.mul_zero, sub_zero,
          transpose_mul]
    _ = ιᵀ * (gᵀ * J * g.map c) * (ι.map c - X.map c * B.map c) := by
        simp only [Matrix.mul_assoc]; rw [h7]
    _ = J₁ := by
        rw [hg, Matrix.mul_sub, h5, h2, ← Matrix.mul_assoc, Matrix.mul_assoc J₁, h4, Matrix.mul_zero, Matrix.zero_mul, sub_zero]

variable (σ) in

def IsFrame {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin m) (Fin m) E) (H : Plane E n m)
    (π : Matrix (Fin m) (Fin n) E) : Prop :=
  IsProj σ J J₁ H.ι π ∧ π *ᵥ H.x = 0 ∧ π *ᵥ H.y = 0 ∧
    H.ι * π + vecMulVec H.x (J *ᵥ fun i => σ (H.y i)) - vecMulVec H.y (J *ᵥ fun i => σ (H.x i)) = 1

theorem exists_isFrame {n m : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin m) (Fin m) E} (H : Plane E n m)
    (hσ : ∀ x, σ (σ x) = x) (hsk : ∀ i j, σ (J j i) = -J i j) (hn : n = m + 2) (hxx : form σ J H.x H.x = 0)
    (hyy : form σ J H.y H.y = 0) (hxy : form σ J H.x H.y = 1)
    (horth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) (hg : H.ιᵀ * J * H.ι.map σ = J₁)
    (hd : J₁.det ≠ 0) : ∃ π, IsFrame σ J J₁ H π := by
  have hdet : IsUnit J₁.det := isUnit_iff_ne_zero.2 hd
  have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A := fun A => by
    ext a b; exact hσ _
  have mul : ∀ {k l q : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin q) E),
      (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
  have sk : J.map σ = -Jᵀ := by ext a b; exact hsk b a
  have sk₁ : J₁.map σ = -J₁ᵀ := by
    rw [← hg, mul, mul, mm, sk, transpose_mul, transpose_mul, transpose_transpose, ← transpose_map]
    simp [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  obtain ⟨P, hP⟩ : ∃ P, P = J₁⁻¹ * (H.ιᵀ * J) := ⟨_, rfl⟩
  have h2 : H.ιᵀ * J = J₁ * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have p1 : P.map σ * H.ι = 1 := by
    have : P * H.ι.map σ = 1 := by rw [hP, Matrix.mul_assoc, hg, Matrix.nonsing_inv_mul _ hdet]
    rw [← mm H.ι, ← mul, this]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have p3 : H.ιᵀ * J = J₁ * (P.map σ).map σ := by rw [mm, h2]
  have p2 : J * H.ι.map σ = (P.map σ)ᵀ * J₁ := by
    have := congrArg (fun A => (Matrix.map A σ)ᵀ) h2
    simp only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg,
      neg_inj] at this
    exact this
  have hz : ∀ z : Fin n → E, (∀ u, form σ J (H.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0 := by
    intro z hz
    have e1 : (H.ιᵀ * J) *ᵥ (fun i => σ (z i)) = 0 := by
      funext j
      have := hz (Pi.single j 1)
      rw [form, mulVec_single_one] at this
      rw [← mulVec_mulVec]
      exact this
    have e2 : P *ᵥ (fun i => σ (z i)) = 0 := by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]
    funext j
    have := congrArg σ (congrFun e2 j)
    simpa [mulVec, dotProduct, map_sum, map_mul, hσ] using this
  have px := hz _ fun u => (horth u).1
  have py := hz _ fun u => (horth u).2
  obtain ⟨π, hπ⟩ : ∃ π, π = P.map σ := ⟨_, rfl⟩
  rw [← hπ] at p1 p2 p3 px py
  refine ⟨π, ⟨p1, p2, p3⟩, px, py, ?_⟩
  have hyx : form σ J H.y H.x = -1 := by rw [GlobalTheory.LeviPlaneSection.form_skew hσ hsk, hxy, map_one]
  let Φ : ((Fin m → E) × E × E) →ₗ[E] (Fin n → E) :=
    H.ι.mulVecLin.coprod ((LinearMap.toSpanSingleton E _ H.x).coprod (LinearMap.toSpanSingleton E _ H.y))
  have hΦ : ∀ p, Φ p = H.ι *ᵥ p.1 + (p.2.1 • H.x + p.2.2 • H.y) := fun p => rfl
  have hlin : ∀ p w, form σ J (Φ p) w = form σ J (H.ι *ᵥ p.1) w + p.2.1 * form σ J H.x w + p.2.2 * form σ J H.y w := by
    intro p w
    simp only [hΦ, form, add_dotProduct, smul_dotProduct, smul_eq_mul]; ring
  have e0 : ∀ p, π *ᵥ Φ p = p.1 := fun p => by
    rw [hΦ, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, px, py, mulVec_mulVec, p1]; simp
  have e1 : ∀ p, (J *ᵥ fun i => σ (H.y i)) ⬝ᵥ Φ p = p.2.1 := fun p => by
    rw [dotProduct_comm, ← form, hlin, (horth _).2, hxy, hyy]; ring
  have e2 : ∀ p, (J *ᵥ fun i => σ (H.x i)) ⬝ᵥ Φ p = -p.2.2 := fun p => by
    rw [dotProduct_comm, ← form, hlin, (horth _).1, hxx, hyx]; ring
  have hinj : Function.Injective Φ := by
    intro p q hpq
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [← e0, hpq, e0]
    · rw [← e1, hpq, e1]
    · rw [← neg_inj, ← e2, hpq, e2]
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod, hn])).1 hinj
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun z => ?_
  obtain ⟨p, rfl⟩ := hsurj z
  rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply, sub_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec,
    ← mulVec_mulVec, e0, e1, e2, hΦ]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
  ring

section Frame

variable {n m : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin m) (Fin m) E} {H : Plane E n m}
  {π : Matrix (Fin m) (Fin n) E}

theorem IsFrame.πx (h : IsFrame σ J J₁ H π) : incM F π *ᵥ incV F H.x = 0 := by rw [incM_mulVec, h.2.1, incV_zero]

theorem IsFrame.πy (h : IsFrame σ J J₁ H π) : incM F π *ᵥ incV F H.y = 0 := by rw [incM_mulVec, h.2.2.1, incV_zero]

theorem IsFrame.decomp (h : IsFrame σ J J₁ H π) (v : Fin n → AE F E) :
    v = incM F H.ι *ᵥ (incM F π *ᵥ v) + (incV F (J *ᵥ fun i => σ (H.y i)) ⬝ᵥ v) • incV F H.x -
      (incV F (J *ᵥ fun i => σ (H.x i)) ⬝ᵥ v) • incV F H.y := by
  have e := congrArg (incM F) h.2.2.2
  have hv : ∀ a b : Fin n → E, incM F (vecMulVec a b) = vecMulVec (incV F a) (incV F b) := fun a b => by
    ext i j; simp [incM, incV, vecMulVec_apply]
  rw [incM_one, incM, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), ← incM, ← incM, ← incM, hv, hv,
    incM_mul] at e
  conv_lhs => rw [← one_mulVec v, ← e]
  rw [sub_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ← mulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
  ring

theorem IsFrame.ext (h : IsFrame σ J J₁ H π) {k : ℕ} {A A' : Matrix (Fin k) (Fin n) (AE F E)}
    (hx : A *ᵥ incV F H.x = A' *ᵥ incV F H.x) (hy : A *ᵥ incV F H.y = A' *ᵥ incV F H.y)
    (hι : A * incM F H.ι = A' * incM F H.ι) : A = A' := by
  refine ext_mulVec_single fun j => ?_
  rw [h.decomp (Pi.single j 1)]
  simp only [mulVec_sub, mulVec_add, mulVec_smul, hx, hy]
  rw [mulVec_mulVec _ A, hι, ← mulVec_mulVec]

theorem IsFrame.isLevi {Y : Spc F E n} {Y₁ : Spc F E m} (h : IsFrame σ Y.J Y₁.J H π) (g : UA σ Y₁.J) :
    IsLevi (W₁ := Y₁) H 1 g (h.1.levi g) :=
  ⟨by rw [Units.val_one, one_smul]; exact h.1.levi_fix g h.πx,
    by rw [inv_one, Units.val_one, map_one, one_smul]; exact h.1.levi_fix g h.πy, h.1.levi_mul_ι g⟩

theorem IsFrame.act (h : IsFrame σ J J₁ H π) (g : UA σ J) (hg : mat g *ᵥ incV F H.x = incV F H.x) :
    ∃ a : Fin m → AE F E, incM F H.ι * (incM F π * mat g * incM F H.ι) =
      mat g * incM F H.ι - replicateCol Unit (incV F H.x) * replicateRow Unit a := by
  set c := (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom with hc
  have hu : (mat g)ᵀ * incM F J * (mat g).map c = incM F J := g.2
  have hx : incV F (fun i => σ (H.x i)) = fun i => c (incV F H.x i) := by
    funext i; exact (GlobalTheory.LeviTorus.cA_incl σ (H.x i)).symm
  have hmv : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin n) (AE F E)) (v : Fin n → AE F E),
      A.map c *ᵥ (fun i => c (v i)) = fun i => c ((A *ᵥ v) i) := fun A v => by
    funext i; simp [mulVec, dotProduct, map_sum, map_mul]
  have h0 : ∀ z, incV F (J *ᵥ fun i => σ (H.x i)) ⬝ᵥ (mat g *ᵥ (incM F H.ι *ᵥ z)) = 0 := by
    intro z
    have e1 : (fun i => c (incV F H.x i)) = (mat g).map c *ᵥ fun i => c (incV F H.x i) := by rw [hmv, hg]
    rw [← incM_mulVec, hx, e1, dotProduct_comm, mulVec_mulVec, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec,
      mulVec_mulVec, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (mat g)ᵀ, hu, h.1.q3, ← mulVec_mulVec, hmv, h.πx]
    simp [mulVec, dotProduct]
  refine ⟨fun j => incV F (J *ᵥ fun i => σ (H.y i)) ⬝ᵥ (mat g *ᵥ (incM F H.ι *ᵥ Pi.single j 1)), ?_⟩
  refine ext_mulVec_single fun j => ?_
  have e := h.decomp (mat g *ᵥ (incM F H.ι *ᵥ Pi.single j 1))
  rw [h0, zero_smul, sub_zero] at e
  rw [sub_mulVec, eq_sub_iff_add_eq]
  simp only [← mulVec_mulVec]
  refine Eq.trans ?_ e.symm
  congr 1
  ext i
  simp [mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem IsFrame.exists_unip {Y : Spc F E n} (h : IsFrame σ Y.J J₁ H π) (g : UA σ Y.J)
    (hg : mat g *ᵥ incV F H.x = incV F H.x) : ∃ h₁ : UA σ J₁, g * (h.1.levi h₁)⁻¹ ∈ unip σ Y H := by
  have hgi : mat g⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hg]
    rw [mulVec_mulVec, mat_inv_mul, one_mulVec]
  have hX : ∀ g : UA σ Y.J, mat g *ᵥ incV F H.x = incV F H.x →
      mat g * replicateCol Unit (incV F H.x) = replicateCol Unit (incV F H.x) := fun g hg => by
    rw [← replicateCol_mulVec, hg]
  have hπX : incM F π * replicateCol Unit (incV F H.x) = 0 := by rw [← replicateCol_mulVec, h.πx, replicateCol_zero]
  have hinv : ∀ g : UA σ Y.J, mat g *ᵥ incV F H.x = incV F H.x → mat g⁻¹ *ᵥ incV F H.x = incV F H.x →
      (incM F π * mat g⁻¹ * incM F H.ι) * (incM F π * mat g * incM F H.ι) = 1 := fun g hg hgi => by
    obtain ⟨a, ha⟩ := h.act g hg
    rw [Matrix.mul_assoc (incM F π * mat g⁻¹), ha, Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (mat g⁻¹), ← Matrix.mul_assoc (mat g⁻¹), mat_inv_mul, Matrix.one_mul, h.1.q1, hX _ hgi,
      ← Matrix.mul_assoc, hπX, Matrix.zero_mul, sub_zero]
  obtain ⟨a, ha⟩ := h.act g hg
  let h₁ : UA σ J₁ := ⟨⟨incM F π * mat g * incM F H.ι, incM F π * mat g⁻¹ * incM F H.ι,
    by simpa only [inv_inv] using hinv g⁻¹ hgi (by rwa [inv_inv]), hinv g hg hgi⟩,
    unitary_of_act (cA σ).toRingHom h.1.q1 h.1.q2 h.1.q3 g.2 hπX (hX g hg) ha⟩
  refine ⟨h₁, ?_⟩
  rw [← map_inv]
  refine Subgroup.subset_closure ⟨?_, fun z => ⟨a ⬝ᵥ (mat h₁⁻¹ *ᵥ z), ?_⟩⟩
  · rw [mat_mul, ← mulVec_mulVec, h.1.levi_fix _ h.πx, hg]
  · have e : mat g * incM F H.ι = incM F H.ι * mat h₁ + replicateCol Unit (incV F H.x) * replicateRow Unit a :=
      (eq_sub_iff_add_eq.1 ha).symm
    rw [mat_mul, ← mulVec_mulVec, h.1.levi_ι, mulVec_mulVec, e, add_mulVec, ← mulVec_mulVec, mulVec_mulVec _ (mat h₁),
      mat_mul_inv, one_mulVec, ← mulVec_mulVec]
    congr 1
    ext i
    simp [mulVec, dotProduct, mul_comm]

end Frame

end GlobalTheory.ThK.FlagSemi

end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT
open GlobalTheory.LeviUnitary

noncomputable section

namespace GlobalTheory.ThK.FlagSemi

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def lam {R : Type} [CommRing R] {d : ℕ} (ξ : ℕ → Fin d → R) (r : ℕ) : Submodule R (Fin d → R) :=
  Submodule.span R (ξ '' Set.Iio r)

section abelian₂

variable {R : Type} [CommRing R] {d : ℕ} {ξ : ℕ → Fin d → R}

theorem lam_mono {r r' : ℕ} (h : r ≤ r') : lam ξ r ≤ lam ξ r' :=
  Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

theorem mem_lam {k r : ℕ} (h : k < r) : ξ k ∈ lam ξ r := Submodule.subset_span ⟨k, h, rfl⟩

theorem lam_zero {v : Fin d → R} (h : v ∈ lam ξ 0) : v = 0 := by
  simpa [lam] using h

theorem lam_map {e : ℕ} (A : Matrix (Fin e) (Fin d) R) (S : Submodule R (Fin e → R)) {r : ℕ} (h : ∀ k < r, A *ᵥ ξ k ∈ S) :
    ∀ v ∈ lam ξ r, A *ᵥ v ∈ S := by
  intro v hv
  have : lam ξ r ≤ S.comap A.mulVecLin := Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h k hk)
  exact this hv

theorem lam_pres {A : Matrix (Fin d) (Fin d) R} {i : ℕ} (h : ∀ k ≤ i, A *ᵥ ξ k - ξ k ∈ lam ξ k) :
    ∀ r ≤ i + 1, ∀ v ∈ lam ξ r, A *ᵥ v ∈ lam ξ r := fun r hr => lam_map A _ fun k hk => by
  have := add_mem (lam_mono hk.le (h k (by omega))) (mem_lam (ξ := ξ) hk)
  rwa [sub_add_cancel] at this

theorem lam_pres_inv {A A' : Matrix (Fin d) (Fin d) R} (hA : A' * A = 1) {i : ℕ}
    (h : ∀ k ≤ i, A *ᵥ ξ k - ξ k ∈ lam ξ k) : ∀ r ≤ i + 1, ∀ v ∈ lam ξ r, A' *ᵥ v ∈ lam ξ r := by
  intro r
  induction r with
  | zero => intro _ v hv; rw [lam_zero hv, mulVec_zero]; exact zero_mem _
  | succ r ih =>
    intro hr
    refine lam_map A' _ fun k hk => ?_
    have h1 := ih (by omega) _ (lam_mono (by omega) (h k (by omega)))
    rw [mulVec_sub, mulVec_mulVec, hA, one_mulVec] at h1
    have := sub_mem (mem_lam (ξ := ξ) hk) (lam_mono (Nat.le_succ r) h1)
    rwa [sub_sub_cancel] at this

end abelian₂

variable (σ) in

def radV {d m : ℕ} (J : Matrix (Fin d) (Fin d) E) (ξ : ℕ → Fin d → AE F E) (i : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)) :
    Subgroup (UA σ J) where
  carrier := {u | (∀ k ≤ i, mat u *ᵥ ξ k - ξ k ∈ lam ξ k) ∧ ∀ z, mat u *ᵥ (C *ᵥ z) - C *ᵥ z ∈ lam ξ (i + 1)}
  one_mem' := ⟨fun k _ => by simp [mat_one], fun z => by simp [mat_one]⟩
  mul_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨k1, k2⟩
    have e : ∀ w, mat (u * v) *ᵥ w - w = mat u *ᵥ (mat v *ᵥ w - w) + (mat u *ᵥ w - w) := fun w => by
      rw [mat_mul, ← mulVec_mulVec, mulVec_sub]; abel
    exact ⟨fun k hk => e _ ▸ add_mem (lam_pres h1 k (by omega) _ (k1 k hk)) (h1 k hk),
      fun z => e _ ▸ add_mem (lam_pres h1 _ le_rfl _ (k2 z)) (h2 z)⟩
  inv_mem' := by
    rintro u ⟨h1, h2⟩
    have e : ∀ w, mat u⁻¹ *ᵥ w - w = -(mat u⁻¹ *ᵥ (mat u *ᵥ w - w)) := fun w => by
      rw [mulVec_sub, mulVec_mulVec, mat_inv_mul, one_mulVec, neg_sub]
    exact ⟨fun k hk => e _ ▸ neg_mem (lam_pres_inv (mat_inv_mul u) h1 k (by omega) _ (h1 k hk)),
      fun z => e _ ▸ neg_mem (lam_pres_inv (mat_inv_mul u) h1 _ le_rfl _ (h2 z))⟩

variable (F) in

def fx {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) : ℕ → Fin d → AE F E
  | 0 => incV F H'.x
  | k + 1 => incM F (chainEmb H' pl k) *ᵥ incV F (pl k).x

variable (F) in

def fy {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) : ℕ → Fin d → AE F E
  | 0 => incV F H'.y
  | k + 1 => incM F (chainEmb H' pl k) *ᵥ incV F (pl k).y

def chainProj {d d₁ : ℕ} (π₀ : Matrix (Fin d₁) (Fin d) E) (πs : ∀ j : ℕ, Matrix (Fin (d₁ - 2 * (j + 1))) (Fin (d₁ - 2 * j)) E)
    (k : ℕ) : Matrix (Fin (d₁ - 2 * k)) (Fin d) E :=
  Nat.rec (motive := fun k => Matrix (Fin (d₁ - 2 * k)) (Fin d) E) π₀ (fun k M => πs k * M) k

section Chain

variable {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
  {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} {p : ℕ} {π₀ : Matrix (Fin d₁) (Fin d) E}
  {πs : ∀ j : ℕ, Matrix (Fin (d₁ - 2 * (j + 1))) (Fin (d₁ - 2 * j)) E}

theorem mem_unip {n m : ℕ} {Y : Spc F E n} {H : Plane E n m} {u : UA σ Y.J} : u ∈ unip σ Y H ↔
    mat u *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x := by
  rw [GlobalTheory.UnipCT.unip_eq]; rfl

variable (h0 : IsFrame σ W.J (sp 0).J H' π₀) (hs : ∀ j < p, IsFrame σ (sp j).J (sp (j + 1)).J (pl j) (πs j))
include h0 hs

theorem isProj_chain : ∀ k ≤ p, IsProj σ W.J (sp k).J (chainEmb H' pl k) (chainProj π₀ πs k)
  | 0, _ => h0.1
  | k + 1, hk => (isProj_chain k (by omega)).mul (hs k hk).1

def leviC (i : ℕ) (hi : i ≤ p) : UA σ (sp i).J →* UA σ W.J := (isProj_chain h0 hs i hi).levi

end Chain

end GlobalTheory.ThK.FlagSemi

end
