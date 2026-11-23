import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentHaarFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMultiplicativeStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenIntegralHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHaarStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarNonarchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ConeSmallBig
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Alg
open GlobalTheory.PlaneLevi GlobalTheory.LeviModulus.HCoord GlobalTheory.UnipMass

theorem nontrivial_AE : Nontrivial (AE F E) := by
  have h : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)
  exact h.nontrivial

theorem mat_mul_mulVec {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) (v : Fin n → AE F E) :
    mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v) := by
  rw [Matrix.mulVec_mulVec]; rfl

theorem mat_inv_mulVec {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {u v : Fin n → AE F E} (h : mat g *ᵥ u = v) :
    mat g⁻¹ *ᵥ v = u := by
  rw [← h, Matrix.mulVec_mulVec, GlobalTheory.UnipCT.mat_inv_mul', Matrix.one_mulVec]

theorem form_skew {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem incM_mulVec {n m : ℕ} (A : Matrix (Fin n) (Fin m) E) (z : Fin m → E) :
    incM F A *ᵥ incV F z = incV F (A *ᵥ z) := by
  ext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) A z i).symm

theorem exists_ratU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (U : Matrix (Fin n) (Fin n) E)
    (hU : ∀ u v, form σ J (U *ᵥ u) (U *ᵥ v) = form σ J u v) : ∃ g ∈ ratU σ J, mat g = incM F U := by
  have h : Uᵀ * J * U.map σ = J := by
    ext i j
    have := entry_eq_form (σ := σ) (J := J) 1 i j
    rw [Matrix.one_mulVec, Matrix.one_mulVec, Matrix.transpose_one, Matrix.one_mul,
      Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.mul_one] at this
    rw [entry_eq_form, hU, this]
  have hd : U.det ≠ 0 := by
    intro h0
    apply hJ
    rw [← h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
  exact ⟨toUA σ (Matrix.GeneralLinearGroup.mkOfDetNeZero U hd) h, Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩, rfl⟩

theorem two_mulVec {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (p q a b v : Fin n → E) :
    (1 + Matrix.vecMulVec p (J *ᵥ fun i => σ (a i)) + Matrix.vecMulVec q (J *ᵥ fun i => σ (b i))) *ᵥ v =
      v + form σ J v a • p + form σ J v b • q := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec', form, dotProduct_comm v]

theorem exists_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁),
    B.IsGood σ → X.IsSkew σ B r s → X₁.IsSkew σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∃ w ∈ ratU σ X.J, mat w *ᵥ incV F H.x = incV F H.y ∧ mat w *ᵥ incV F H.y = -incV F H.x ∧ mat w * incM F H.ι = incM F H.ι := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH
  have hσ := invol_of_good hB
  have hyx : form σ X.J H.y H.x = -1 := by rw [form_skew hσ hX.skew, hH.xy, map_one]
  obtain ⟨w, hw, hm⟩ := exists_ratU (σ := σ) (GlobalTheory.UnipComm.det_ne_of_skew B X.J hX.sig)
    (1 + Matrix.vecMulVec (H.y + (-1 : E) • H.x) (X.J *ᵥ fun i => σ (H.y i)) +
      Matrix.vecMulVec (H.x + H.y) (X.J *ᵥ fun i => σ (H.x i))) (fun u v => by
      rw [two_mulVec, two_mulVec]
      simp only [form_add_left, form_smul_left, form_add_right, form_smul_right, hH.xx, hH.yy, hH.xy, hyx, map_neg, map_one]
      rw [form_skew hσ hX.skew H.x v, form_skew hσ hX.skew H.y v]
      ring)
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · rw [hm, incM_mulVec, two_mulVec, hH.xx, hH.xy]
    congr 1
    module
  · rw [hm, incM_mulVec, two_mulVec, hH.yy, hyx]
    ext i
    simp [incV]
  · rw [hm, ← incM_mul]
    congr 1
    ext i j
    have := congrFun (two_mulVec (σ := σ) X.J (H.y + (-1 : E) • H.x) (H.x + H.y) H.y H.x (H.ι *ᵥ Pi.single j 1)) i
    rw [(hH.orth _).1, (hH.orth _).2, Matrix.mulVec_mulVec] at this
    simpa [Matrix.mulVec_single_one] using this

theorem exists_eichler : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁),
    B.IsGood σ → X.IsSkew σ B r s → X₁.IsSkew σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ t ∈ ratU σ X.J, ¬ GlobalTheory.ConeSmallSer.OrthLn H.x t →
      ∃ ν ∈ ratU σ X.J ⊓ unip σ X H, ∃ l : (AE F E)ˣ, mat (ν * t⁻¹) *ᵥ incV F H.x = l.1 • incV F H.y := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH t ht hno
  haveI := nontrivial_AE (F := F) (E := E)
  have hσ := invol_of_good hB
  have sk := form_skew hσ hX.skew
  have hyx : form σ X.J H.y H.x = -1 := by rw [sk, hH.xy, map_one]
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.1 (inv_mem ht)
  have hmt : mat t⁻¹ = incM F g₀.1 := (congrArg Units.val hg₀).symm
  set v : Fin n → E := g₀.1 *ᵥ H.x with hv
  have hiv : mat t⁻¹ *ᵥ incV F H.x = incV F v := by rw [hmt, incM_mulVec]
  have hvx : form σ X.J v H.x ≠ 0 := fun h0 => hno (by
    show hA σ X.J (mat t⁻¹ *ᵥ incV F H.x) (incV F H.x) = 0
    rw [hiv, hA_incV', h0, map_zero])
  have hvv : form σ X.J v v = 0 := by
    apply (inclR (F := F) (E := E) (AF F)).injective
    rw [← hA_incV', ← hiv, hA_mat, hA_incV', hH.xx]
  set c : E := -(form σ X.J v H.x)⁻¹ with hc
  have hc0 : c ≠ 0 := neg_ne_zero.2 (inv_ne_zero hvx)
  obtain ⟨p, hp⟩ : ∃ p, p = c • v := ⟨_, rfl⟩
  have hpx : form σ X.J p H.x = -1 := by rw [hp, form_smul_left, hc, neg_mul, inv_mul_cancel₀ hvx]
  have hxp : form σ X.J H.x p = 1 := by rw [sk, hpx]; simp
  have hpp : form σ X.J p p = 0 := by rw [hp, form_smul_left, form_smul_right, hvv, mul_zero, mul_zero]
  set k : E := form σ X.J H.y p with hk
  have hpy : form σ X.J p H.y = -σ k := sk _ _
  obtain ⟨u, hu, hm⟩ := exists_ratU (σ := σ) (GlobalTheory.UnipComm.det_ne_of_skew B X.J hX.sig)
    (1 + Matrix.vecMulVec ((-1 : E) • H.x) (X.J *ᵥ fun i => σ ((p + (-1 : E) • H.y) i)) +
      Matrix.vecMulVec ((-1 : E) • p + H.y + (-k) • H.x) (X.J *ᵥ fun i => σ (H.x i))) (fun a b => by
      rw [two_mulVec, two_mulVec]
      simp only [form_add_left, form_smul_left, form_add_right, form_smul_right, hH.xx, hH.yy, hH.xy, hyx, map_neg, map_one,
        hpx, hxp, hpp, hpy, ← hk, map_add, map_mul]
      rw [sk H.x b, sk H.y b, sk p b]
      ring)
  have hmem : u ∈ unip σ X H := by
    refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
    · rw [hm, incM_mulVec, two_mulVec, form_add_right, form_smul_right, hH.xx, hH.xy, hxp]
      simp
    · refine ⟨-hA σ X.J (incM F H.ι *ᵥ z) (incV F (p + (-1 : E) • H.y)), ?_⟩
      have h0 := hA_ι_incV σ X.J H.ι H.x (fun u => (hH.orth u).1) z
      have hvm : ∀ a b : Fin n → E, incM F (Matrix.vecMulVec a (X.J *ᵥ fun i => σ (b i))) *ᵥ (incM F H.ι *ᵥ z) =
          hA σ X.J (incM F H.ι *ᵥ z) (incV F b) • incV F a := by
        intro a b
        have e1 : incM F (Matrix.vecMulVec a (X.J *ᵥ fun i => σ (b i))) =
            Matrix.vecMulVec (incV F a) (incM F X.J *ᵥ fun i => cA σ (incV F b i)) := by
          have e2 : (fun i => cA σ (incV F b i)) = incV F fun i => σ (b i) := funext fun i => cA_inclR' σ _
          rw [e2, incM_mulVec]
          ext i j
          simp [incM, incV, Matrix.vecMulVec_apply]
        rw [e1, Matrix.vecMulVec_mulVec, hA, dotProduct_comm]
        ext i
        simp [mul_comm]
      have hadd : ∀ A A' : Matrix (Fin n) (Fin n) E, incM F (A + A') = incM F A + incM F A' := fun A A' =>
        Matrix.map_add _ (map_add _) _ _
      have hone : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [hm, hadd, hadd, hone, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hvm, hvm, h0, zero_smul, add_zero]
      ext i
      simp [incV]
  have huy : mat u *ᵥ incV F H.y = incV F p := by
    rw [hm, incM_mulVec, two_mulVec, form_add_right, form_smul_right, hH.yy, hyx, ← hk]
    congr 1
    module
  refine ⟨u⁻¹, inv_mem ⟨hu, hmem⟩, Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom (Units.mk0 c hc0)⁻¹, ?_⟩
  rw [mat_mul_mulVec, hiv, ← mat_inv_mulVec u huy, ← Matrix.mulVec_smul, hp]
  congr 1
  ext i
  simp [incV, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0]

end Alg

section Coords
open GlobalTheory.LeviModulus GlobalTheory.UnipMass GlobalTheory.LeviModulus.HCoord

theorem heis_coords_form {n n₁ : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (hσ : ∀ a, σ (σ a) = a)
    (hJ : ∀ i j, σ (X.J j i) = X.J i j) (hd : X₁.J.det ≠ 0)
    (hdec : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y)
    (hxx : form σ X.J H.x H.x = 0) (hyy : form σ X.J H.y H.y = 0) (hxy : form σ X.J H.x H.y = 1)
    (horth : ∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * X.J * H.ι.map σ = X₁.J) :
    ∃ (Ψ : (Fin n₁ → AE F E) × GlobalTheory.LeviModulus.imA σ ≃ₜ unip σ X H)
      (ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → GlobalTheory.LeviModulus.imA σ),
      Continuous (fun p : (Fin n₁ → AE F E) × (Fin n₁ → AE F E) => ω p.1 p.2) ∧
      (∀ a b a' b', Ψ (a, b) * Ψ (a', b') = Ψ (a + a', b + b' + ω a a')) ∧
      ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ X.J), IsLevi H l g₀ m → ∀ a b,
        ∃ p : (Fin n₁ → AE F E) × GlobalTheory.LeviModulus.imA σ, m * ((Ψ (a, b) : unip σ X H) : UA σ X.J) * m⁻¹ = ((Ψ p : unip σ X H) : UA σ X.J) ∧
          p.1 = cA σ l • (mat g₀ *ᵥ a) ∧ ((p.2 : GlobalTheory.LeviModulus.imA σ) : AE F E) = l * cA σ l * b := by
  haveI := (topAE F E).1
  have hXX : hA σ X.J (incV F H.x) (incV F H.x) = 0 := by rw [hA_incV', hxx, map_zero]
  have hXY : hA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [hA_incV', hxy, map_one]
  have hYX : hA σ X.J (incV F H.y) (incV F H.x) = 1 := by rw [hA_herm σ X.J hσ hJ, hXY, map_one]
  have hιX : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0 :=
    hA_ι_incV σ X.J H.ι H.x (fun u => (horth u).1)
  have hιY : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.y) = 0 :=
    hA_ι_incV σ X.J H.ι H.y (fun u => (horth u).2)
  have hXι : ∀ z, hA σ X.J (incV F H.x) (incM F H.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ X.J hσ hJ, hιX, map_zero]
  have hYι : ∀ z, hA σ X.J (incV F H.y) (incM F H.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ X.J hσ hJ, hιY, map_zero]
  have hιι : ∀ a w, hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ w) = hA σ X₁.J a w :=
    hA_ιι σ X.J X₁.J H.ι hgram
  have hself : ∀ v, cA σ (hA σ X.J v v) = hA σ X.J v v := fun v => (hA_herm σ X.J hσ hJ v v).symm
  set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def
  have hhalf : (2 : AE F E) * half = 1 := by
    rw [hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hσhalf : cA σ half = half := by rw [hhalf_def, cA_inclR', map_inv₀, map_ofNat]
  have hcf : ∀ (a : Fin n₁ → AE F E) (k : imA σ),
      ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) +
        cA σ ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) =
        -hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
    intro a k
    have hk : cA σ (k : AE F E) = -k := k.2
    rw [map_sub, map_mul, hk, hσhalf, hself]
    linear_combination (-hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * hhalf

  let Ψf : (Fin n₁ → AE F E) × imA σ → unip σ X H := fun p => elt hσ hJ hXX hιX p.1 _ (hcf p.1 p.2)
  have hmatΨ : ∀ p, mat ((Ψf p : unip σ X H) : UA σ X.J) = hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ p.1)
      ((p.2 : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1)) := fun p => rfl
  let A : Matrix (Fin n) (Fin n) (AE F E) → Fin n₁ → AE F E := fun M => Matrix.vecMul (rv σ X H M) (incM F X₁.J⁻¹)
  let K : Matrix (Fin n) (Fin n) (AE F E) → AE F E := fun M =>
    hA σ X.J (M *ᵥ incV F H.y - incV F H.y) (incV F H.y) + half * hA σ X.J (incM F H.ι *ᵥ A M) (incM F H.ι *ᵥ A M)
  have hdy : ∀ a c, hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c *ᵥ incV F H.y - incV F H.y =
      incM F H.ι *ᵥ a + c • incV F H.x := by
    intro a c; rw [hmat_mulVec, hYX, hYι, one_smul, zero_smul, sub_zero, add_sub_cancel_left]
  have hA_h : ∀ a c, A (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = a := by
    intro a c
    have e : rv σ X H (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = Matrix.vecMul a (incM F X₁.J) := by
      funext j; simp only [rv]; rw [hdy, hA_add_l, hA_smul_l, hXι, mul_zero, add_zero, hιι, hA_single]
    simp only [A]; rw [e, Matrix.vecMul_vecMul, incM_mul_inv _ hd, Matrix.vecMul_one]
  have hK_h : ∀ a c, K (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) =
      c + half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
    intro a c; simp only [K]; rw [hA_h, hdy, hA_add_l, hA_smul_l, hιY, hXY, mul_one, zero_add]
  have hmemK : ∀ g : unip σ X H, K (mat (g : UA σ X.J)) ∈ imA σ := by
    intro g
    obtain ⟨b, c, hc, hg⟩ := unip_eq_hmat σ hσ X H hJ hxx hyy hxy horth hdec _ g.2
    rw [hg, hK_h, mem_imA, map_add, map_mul, hσhalf, hself]
    linear_combination hc + hA σ X.J (incM F H.ι *ᵥ b) (incM F H.ι *ᵥ b) * hhalf
  let invf : unip σ X H → (Fin n₁ → AE F E) × imA σ := fun g =>
    (A (mat (g : UA σ X.J)), ⟨K (mat (g : UA σ X.J)), hmemK g⟩)
  have hmc : Continuous fun g : unip σ X H => mat (g : UA σ X.J) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hAc : Continuous A := continuous_rv.matrix_vecMul continuous_const
  have hKc : Continuous K :=
    (continuous_hA X.J ((continuous_id.matrix_mulVec continuous_const).sub continuous_const) continuous_const).add
      (continuous_const.mul (continuous_hA X.J (continuous_const.matrix_mulVec hAc)
        (continuous_const.matrix_mulVec hAc)))
  have hQc : Continuous fun p : (Fin n₁ → AE F E) × imA σ =>
      hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1) :=
    continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst) (continuous_const.matrix_mulVec continuous_fst)
  let Ψ : (Fin n₁ → AE F E) × imA σ ≃ₜ unip σ X H :=
    { toFun := Ψf
      invFun := invf
      left_inv := fun p => by
        refine Prod.ext (hA_h _ _) (Subtype.ext ?_)
        show K (mat ((Ψf p : unip σ X H) : UA σ X.J)) = p.2
        rw [hmatΨ, hK_h]; ring
      right_inv := fun g => by
        apply unip_ext'
        obtain ⟨b, c, hc, hg⟩ := unip_eq_hmat σ hσ X H hJ hxx hyy hxy horth hdec _ g.2
        rw [hmatΨ]
        show hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))
          (K (mat (g : UA σ X.J)) - half * hA σ X.J (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))
            (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))) = mat (g : UA σ X.J)
        rw [hg, hK_h, hA_h, add_sub_cancel_right]
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _) _
        · exact continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst)
            ((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc))
        · exact continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst).neg
            (((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc)).neg.sub hQc)
      continuous_invFun := by
        refine Continuous.prodMk (hAc.comp hmc) (Continuous.subtype_mk (hKc.comp hmc) _) }

  have hωmem : ∀ a a' : Fin n₁ → AE F E, half * (hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a') -
      hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) ∈ imA σ := by
    intro a a'
    rw [mem_imA, map_mul, map_sub, hσhalf, ← hA_herm σ X.J hσ hJ, ← hA_herm σ X.J hσ hJ]
    ring
  let ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → imA σ := fun a a' => ⟨_, hωmem a a'⟩
  refine ⟨Ψ, ω, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_const.mul
      ((continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst)
        (continuous_const.matrix_mulVec continuous_snd)).sub
      (continuous_hA X.J (continuous_const.matrix_mulVec continuous_snd)
        (continuous_const.matrix_mulVec continuous_fst)))) _
  · intro a b a' b'
    apply unip_ext'
    show mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) * mat ((Ψf (a', b') : unip σ X H) : UA σ X.J) =
      mat ((Ψf (a + a', b + b' + ω a a') : unip σ X H) : UA σ X.J)
    rw [hmatΨ, hmatΨ, hmatΨ, hmat_mul hσ hJ _ _ _ _ _ hXX (hιX a) (hιX a'), ← Matrix.mulVec_add]
    congr 1
    simp only [AddSubgroup.coe_add, ω, Matrix.mulVec_add, hA_add_l, hA_add_r]
    linear_combination (hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) * hhalf
  · intro l g₀ m hL a b
    have hpmem : l.1 * cA σ l.1 * (b : AE F E) ∈ imA σ := by
      have hb : cA σ (b : AE F E) = -b := b.2
      rw [mem_imA, map_mul, map_mul, cA_cA σ hσ, hb]; ring
    refine ⟨(cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩), ?_, rfl, rfl⟩
    set M := mat m with hM
    have hMx : M *ᵥ incV F H.x = l.1 • incV F H.x := hL.1
    have hMι : ∀ w, M *ᵥ (incM F H.ι *ᵥ w) = incM F H.ι *ᵥ (mat g₀ *ᵥ w) := fun w => by
      rw [Matrix.mulVec_mulVec, hL.2.2, ← Matrix.mulVec_mulVec]
    have hx' : M *ᵥ ((l⁻¹).1 • incV F H.x) = incV F H.x := by
      rw [Matrix.mulVec_smul, hMx, smul_smul, Units.inv_mul, one_smul]
    have hMvx : ∀ v, hA σ X.J (M *ᵥ v) (incV F H.x) = cA σ (l⁻¹).1 * hA σ X.J v (incV F H.x) := fun v => by
      have e := hA_mat m v ((l⁻¹).1 • incV F H.x)
      rw [← hM, hx', hA_smul_r] at e
      exact e
    have hιp : incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a)) = cA σ l.1 • (M *ᵥ (incM F H.ι *ᵥ a)) := by
      rw [Matrix.mulVec_smul, hMι]
    have hMvu : ∀ v, hA σ X.J (M *ᵥ v) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) =
        l.1 * hA σ X.J v (incM F H.ι *ᵥ a) := fun v => by
      rw [hιp, hA_smul_r, cA_cA σ hσ, hM, hA_mat]
    have hQp : hA σ X.J (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) =
        cA σ l.1 * l.1 * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
      rw [hιp, hA_smul_l, hA_smul_r, cA_cA σ hσ, hM, hA_mat]; ring
    have hinv : cA σ (l⁻¹).1 * cA σ l.1 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hMMi : M * mat m⁻¹ = 1 := by
      rw [hM, show mat m * mat m⁻¹ = mat (m * m⁻¹) from rfl, mul_inv_cancel]; rfl
    set T := mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) with hT
    set T' := mat ((Ψf (cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩) : unip σ X H) : UA σ X.J) with hT'
    have key : M * T = T' * M := by
      refine hmat_ext fun v => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT, hT', hmatΨ, hmatΨ, hmat_mulVec, hmat_mulVec,
        hMvx, hMvu, hQp]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hMx, hMι, hιp]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(hA σ X.J v (incV F H.x) * (incM F H.ι *ᵥ (mat g₀ *ᵥ a)) i +
        hA σ X.J v (incV F H.x) * incV F H.x i * ((b : AE F E) -
          half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * l.1)) * hinv
    apply Subtype.ext; apply Units.ext
    show M * T * mat m⁻¹ = T'
    rw [key, Matrix.mul_assoc, hMMi, Matrix.mul_one]

theorem mem_UG_smul {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0) (g : GL (Fin n) (AE F E)) :
    g ∈ UG (cA σ) (incM F (δ • J)) ↔ g ∈ UG (cA σ) (incM F J) := by
  have hs : incM F (δ • J) = inclR (F := F) (AF F) δ • incM F J := by
    ext i j; simp [incM]
  have hu : inclR (F := F) (AF F) δ⁻¹ * inclR (F := F) (AF F) δ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ, map_one]
  change g.1ᵀ * incM F (δ • J) * g.1.map (cA σ) = incM F (δ • J) ↔ g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J
  rw [hs, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun hg => ?_, fun hg => by rw [hg]⟩
  have := congrArg (inclR (F := F) (AF F) δ⁻¹ • ·) hg
  simpa only [smul_smul, hu, one_smul] using this

def scaleUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0) : UA σ J ≃ₜ* UA σ (δ • J) where
  toFun g := ⟨g.1, (mem_UG_smul J hδ g.1).2 g.2⟩
  invFun g := ⟨g.1, (mem_UG_smul J hδ g.1).1 g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem heis_coords_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁),
    B.IsGood σ → X.IsSkew σ B r s → X₁.IsSkew σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∃ (Ψ : (Fin n₁ → AE F E) × GlobalTheory.LeviModulus.imA σ ≃ₜ unip σ X H)
      (ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → GlobalTheory.LeviModulus.imA σ),
      Continuous (fun p : (Fin n₁ → AE F E) × (Fin n₁ → AE F E) => ω p.1 p.2) ∧
      (∀ a b a' b', Ψ (a, b) * Ψ (a', b') = Ψ (a + a', b + b' + ω a a')) ∧
      ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ X.J), IsLevi H l g₀ m → ∀ a b,
        ∃ p : (Fin n₁ → AE F E) × GlobalTheory.LeviModulus.imA σ, m * ((Ψ (a, b) : unip σ X H) : UA σ X.J) * m⁻¹ = ((Ψ p : unip σ X H) : UA σ X.J) ∧
          p.1 = cA σ l • (mat g₀ *ᵥ a) ∧ ((p.2 : GlobalTheory.LeviModulus.imA σ) : AE F E) = l * cA σ l * b := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH
  have hσ := GlobalTheory.PlaneLevi.invol_of_good hB
  obtain ⟨δ, hδ, hδs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hB.cm
  let Y : Spc F E n := { X with J := δ • X.J }
  let Y₁ : Spc F E n₁ := { X₁ with J := δ • X₁.J }
  let P : Plane E n n₁ := { H with y := (-δ⁻¹) • H.y }
  have hf : ∀ u v, form σ (δ • X.J) u v = δ * form σ X.J u v := fun u v => by
    simp only [form, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hσc : σ (-δ⁻¹) = δ⁻¹ := by rw [map_neg, map_inv₀, hδs, inv_neg, neg_neg]
  obtain ⟨Ψ, ω, hω, hlaw, hconj⟩ := heis_coords_form (σ := σ) Y Y₁ P hσ
    (fun i j => by
      show σ (δ * X.J j i) = δ * X.J i j
      rw [map_mul, hδs, hX.skew, neg_mul_neg])
    (by
      show (δ • X₁.J).det ≠ 0
      rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hδ) (GlobalTheory.UnipComm.det_ne_of_skew B X₁.J hX₁.sig))
    (fun v => by
      obtain ⟨a, b, u, hv⟩ := (GlobalTheory.LeviRatHerm.decomp hX.lat hH).1 v
      refine ⟨a, -(b * δ), u, ?_⟩
      show v = a • H.x + H.ι *ᵥ u + (-(b * δ)) • ((-δ⁻¹) • H.y)
      rw [smul_smul, neg_mul_neg, mul_assoc, mul_inv_cancel₀ hδ, mul_one]
      exact hv)
    (by
      show form σ (δ • X.J) H.x H.x = 0
      rw [hf, hH.xx, mul_zero])
    (by
      show form σ (δ • X.J) ((-δ⁻¹) • H.y) ((-δ⁻¹) • H.y) = 0
      rw [hf, GlobalTheory.PlaneLevi.form_smul_left, GlobalTheory.PlaneLevi.form_smul_right, hH.yy, mul_zero, mul_zero, mul_zero])
    (by
      show form σ (δ • X.J) H.x ((-δ⁻¹) • H.y) = 1
      rw [hf, GlobalTheory.PlaneLevi.form_smul_right, hH.xy, hσc, mul_one, mul_inv_cancel₀ hδ])
    (fun u => by
      show form σ (δ • X.J) (H.ι *ᵥ u) H.x = 0 ∧ form σ (δ • X.J) (H.ι *ᵥ u) ((-δ⁻¹) • H.y) = 0
      rw [hf, hf, GlobalTheory.PlaneLevi.form_smul_right, (hH.orth u).1, (hH.orth u).2]
      simp)
    (by
      show H.ιᵀ * (δ • X.J) * H.ι.map σ = δ • X₁.J
      rw [Matrix.mul_smul, Matrix.smul_mul, hH.gram])
  let e : UA σ X.J ≃ₜ* UA σ Y.J := scaleUA X.J hδ
  let e₁ : UA σ X₁.J ≃ₜ* UA σ Y₁.J := scaleUA X₁.J hδ
  have hmem : ∀ g : UA σ X.J, g ∈ unip σ X H ↔ e g ∈ unip σ Y P := fun g => by
    rw [GlobalTheory.UnipCT.unip_eq, GlobalTheory.UnipCT.unip_eq]
    rfl
  let η : unip σ Y P ≃ₜ unip σ X H :=
    { toFun := fun u => ⟨e.symm u.1, (hmem _).2 u.2⟩
      invFun := fun u => ⟨e u.1, (hmem _).1 u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨Ψ.trans η, ω, hω, fun a b a' b' => ?_, fun l g₀ m hm a b => ?_⟩
  · exact congrArg η (hlaw a b a' b')
  · have hm' : IsLevi (W₁ := Y₁) P l (e₁ g₀) (e m) := by
      refine ⟨hm.1, ?_, hm.2.2⟩
      show mat m *ᵥ incV F ((-δ⁻¹) • H.y) = cA σ (l⁻¹).1 • incV F ((-δ⁻¹) • H.y)
      rw [incV_smul', Matrix.mulVec_smul, hm.2.1, smul_comm]
    obtain ⟨p, hp, hp1, hp2⟩ := hconj l (e₁ g₀) (e m) hm' a b
    exact ⟨p, congrArg e.symm hp, hp1, hp2⟩

end Coords

open GlobalTheory.LeviModulus GlobalTheory.LeviModulusAdapted in

theorem integral_conj_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁),
    B.IsGood σ → X.IsSkew σ B r s → X₁.IsSkew σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ (μN : Measure (unip σ X H)), μN.IsHaarMeasure →
    ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ X.J), IsLevi H l g₀ m → ∀ f : UA σ X.J → ℂ,
      ∫ u, f (m * u.1 * m⁻¹) ∂μN = (((absE F E l : ℝ) : ℂ) ^ (n₁ + 1))⁻¹ * ∫ u, f u.1 ∂μN := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH μN hμ l g₀ m hm0 f
  obtain ⟨hR, hLC, hSC, hT2⟩ := topAE F E
  haveI := hR; haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTG, hLCU, hSCU, hT2U⟩ := topUA σ X.J
  haveI := hTG; haveI := hLCU; haveI := hSCU; haveI := hT2U
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hd : X₁.J.det ≠ 0 := GlobalTheory.UnipComm.det_ne_of_skew B X₁.J hX₁.sig
  have hcl := GlobalTheory.UnipCT.isClosed_unip σ X H
  haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  obtain ⟨Ψ, ω, hω, hlaw, hconj⟩ := heis_coords_skew F E σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH
  have hmem : ∀ (l' : (AE F E)ˣ) (g' : UA σ X₁.J) (m' : UA σ X.J), IsLevi H l' g' m' →
      ∀ u ∈ unip σ X H, m' * u * m'⁻¹ ∈ unip σ X H := by
    intro l' g' m' hl' u hu
    obtain ⟨p, hp, -, -⟩ := hconj l' g' m' hl' (Ψ.symm ⟨u, hu⟩).1 (Ψ.symm ⟨u, hu⟩).2
    rw [Prod.mk.eta, Homeomorph.apply_symm_apply] at hp
    rw [hp]
    exact (Ψ p).2
  have h₁ := hmem l g₀ m hm0
  have h₂ : ∀ u ∈ unip σ X H, m⁻¹ * u * m ∈ unip σ X H := fun u hu => by
    simpa using hmem _ _ _ (isLevi_inv H hm0) u hu
  let φ := conjOn (unip σ X H) m h₁ h₂
  have hσσ : ∀ a, σ (σ a) = a := GlobalTheory.PlaneLevi.invol_of_good hB
  have hcc : ∀ z : AE F E, cA σ (cA σ z) = z := cA_cA σ hσσ
  have hcu : ∀ u : (AE F E)ˣ, cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (u : AE F E) = 1 := fun u => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hcu' : ∀ u : (AE F E)ˣ, cA σ (u : AE F E) * cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) = 1 := fun u => by
    rw [← map_mul, Units.mul_inv, map_one]
  have hN : ∀ u : (AE F E)ˣ, cA σ ((u : AE F E) * cA σ u) = u * cA σ u := fun u => by
    rw [map_mul, hcc, mul_comm]
  have hmc : Continuous fun a : Fin n₁ → AE F E => a := continuous_id
  let L₁ : (Fin n₁ → AE F E) ≃ₜ+ (Fin n₁ → AE F E) :=
    { toFun := fun a => cA σ (l : AE F E) • (mat g₀ *ᵥ a)
      invFun := fun a => cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) • (mat g₀⁻¹ *ᵥ a)
      left_inv := fun a => by
        simp only
        rw [Matrix.mulVec_smul, smul_smul, hcu, one_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul,
          Matrix.one_mulVec]
      right_inv := fun a => by
        simp only
        rw [Matrix.mulVec_smul, smul_smul, hcu', one_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv,
          Matrix.one_mulVec]
      map_add' := fun a b => by simp only [Matrix.mulVec_add, smul_add]
      continuous_toFun := (continuous_const.matrix_mulVec continuous_id).const_smul (cA σ (l : AE F E))
      continuous_invFun :=
        (continuous_const.matrix_mulVec continuous_id).const_smul (cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E)) }
  let L₂ : imA σ ≃ₜ+ imA σ :=
    { toFun := fun b => ⟨(l : AE F E) * cA σ l * b, mul_mem_imA (hN l) b.2⟩
      invFun := fun b => ⟨((l⁻¹ : (AE F E)ˣ) : AE F E) * cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) * b, mul_mem_imA (hN l⁻¹) b.2⟩
      left_inv := fun b => Subtype.ext (by
        simp only
        rw [← mul_assoc, mul_mul_mul_comm, Units.inv_mul, hcu, one_mul, one_mul])
      right_inv := fun b => Subtype.ext (by
        simp only
        rw [← mul_assoc, mul_mul_mul_comm, Units.mul_inv, hcu', one_mul, one_mul])
      map_add' := fun a b => Subtype.ext (by simp only [AddSubgroup.coe_add, mul_add])
      continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _ }
  have hφΨ : ∀ a b, φ (Ψ (a, b)) = Ψ (L₁ a, L₂ b) := by
    intro a b
    obtain ⟨p, hp, hp1, hp2⟩ := hconj l g₀ m hm0 a b
    apply Subtype.ext
    rw [conjOn_apply, hp]
    congr 2
    exact Prod.ext hp1 (Subtype.ext hp2)
  letI : MeasurableSpace (Fin n₁ → AE F E) := borel _
  haveI : BorelSpace (Fin n₁ → AE F E) := ⟨rfl⟩
  letI : MeasurableSpace (imA σ) := borel _
  haveI : BorelSpace (imA σ) := ⟨rfl⟩
  haveI : LocallyCompactSpace (imA σ) := (isClosed_imA σ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (imA σ) :=
    (isClosed_imA σ).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have hchar : mulEquivHaarChar φ = absE F E l ^ n₁ * absE F E l := by
    rw [GlobalTheory.mulEquivHaarChar_heisenberg_chart _ _ _ Ψ ω hω hlaw φ L₁ L₂ hφΨ, haarChar_smul_mulVec F E σ B n₁ X₁ hB hd l g₀ L₁ (fun a => rfl),
      GlobalTheory.ImaginaryModulus.addEquivAddHaarChar_imA F E σ B hB l L₂ (fun b => rfl)]
  haveI : IsTopologicalGroup (unip σ X H) := inferInstance
  haveI : T2Space (unip σ X H) := inferInstance
  haveI : RegularSpace (unip σ X H) := by
    first
    | exact IsTopologicalGroup.regularSpace _
    | exact TopologicalGroup.regularSpace _
    | exact inferInstanceAs (RegularSpace (Subtype _))
  haveI : T1Space (unip σ X H) := T2Space.t1Space
  haveI : T0Space (unip σ X H) := T1Space.t0Space
  haveI : T3Space (unip σ X H) := T3Space.mk
  haveI : TopologicalSpace.MetrizableSpace (unip σ X H) := TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : μN.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hsm := mulEquivHaarChar_smul_map μN φ
  rw [hchar] at hsm
  have hpos : absE F E l ≠ 0 := ((Group.isUnit l).map (absE F E)).ne_zero
  set c : ℝ≥0 := absE F E l ^ n₁ * absE F E l with hc
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hpos) hpos
  have hmap : μN.map φ = c⁻¹ • μN := by
    conv_rhs => rw [← hsm]
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e1 : ∫ u, f (m * u.1 * m⁻¹) ∂μN = ∫ u, f u.1 ∂(μN.map φ) :=
    (integral_map_equiv φ.toHomeomorph.toMeasurableEquiv (fun v : unip σ X H => f v.1)).symm
  rw [e1, hmap, integral_smul_nnreal_measure, hc, NNReal.smul_def, Complex.real_smul]
  push_cast
  rw [pow_succ]

open GlobalTheory.LeviModulus.HCoord GlobalTheory.UnipMass in

theorem eq_one_of_stab_dual {B : Base F E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {r s i₀ i₁ : ℕ} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hX : X.IsSkew σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) {u : UA σ X.J} (hu : u ∈ unip σ X H)
    {l : AE F E} (hl : mat u *ᵥ incV F H.y = l • incV F H.y) : u = 1 := by
  rw [GlobalTheory.UnipCT.unip_eq] at hu
  obtain ⟨hx, hz⟩ := hu
  have hXY : hA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [hA_incV', hH.xy, map_one]
  have h1 : cA σ l = 1 := by
    have e := hA_mat u (incV F H.x) (incV F H.y)
    rwa [hx, hl, hA_smul_r, hXY, mul_one] at e
  have hl1 : l = 1 := by
    rw [← GlobalTheory.LeviModulus.cA_cA σ (GlobalTheory.PlaneLevi.invol_of_good hB) l, h1, map_one]
  rw [hl1, one_smul] at hl
  have hι : ∀ z, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
    intro z
    obtain ⟨a, ha⟩ := hz z
    have h0 := hA_ι_incV σ X.J H.ι H.y (fun u => (hH.orth u).2) z
    have e := hA_mat u (incM F H.ι *ᵥ z) (incV F H.y)
    rw [hl, ha, hA_add_l, hA_smul_l, hXY, h0, zero_add, mul_one] at e
    rw [ha, e, zero_smul, add_zero]
  have hone : mat (1 : UA σ X₁.J) = 1 := rfl
  have hone' : mat (1 : UA σ X.J) = 1 := rfl
  refine GlobalTheory.LeviUniq.levi_unique F E σ B n r s X hX n₁ X₁ H i₀ i₁ hH 1 u 1 ⟨by simpa using hx, by simpa using hl, ?_⟩
    ⟨by simp [hone'], by simp [hone'], by rw [hone, hone', Matrix.one_mul, Matrix.mul_one]⟩
  rw [hone, Matrix.mul_one]
  ext i j
  have := congrFun (hι (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec] at this
  simpa [Matrix.mulVec_single_one] using this

theorem integrable_of_fd {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
    [SecondCountableTopology N] (Γ : Subgroup N) [Countable Γ] (μ : Measure N) [μ.IsHaarMeasure] (𝓕 : Set N)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) {Φ : N → ℂ} (hΦ : Measurable Φ) {C : ENNReal} (hC : C < ⊤)
    (hb : ∀ u, ∑' γ : Γ, ‖Φ (γ.1 * u)‖ₑ ≤ C) : Integrable Φ μ := by
  refine ⟨hΦ.aestronglyMeasurable, ?_⟩
  have hl : ∫⁻ u, ‖Φ u‖ₑ ∂μ = ∑' γ : Γ, ∫⁻ u in 𝓕, ‖Φ (γ.1 * u)‖ₑ ∂μ := h𝓕.lintegral_eq_tsum'' (fun u => ‖Φ u‖ₑ)
  have hm : ∀ γ : Γ, AEMeasurable (fun u => ‖Φ (γ.1 * u)‖ₑ) (μ.restrict 𝓕) := fun γ =>
    (hΦ.comp (measurable_const_mul γ.1)).enorm.aemeasurable
  rw [HasFiniteIntegral, hl, ← lintegral_tsum hm]
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  rw [lintegral_const, Measure.restrict_apply_univ, h1, mul_one]
  exact hC

open GlobalTheory.ConeSmallSer GlobalTheory.ConeSmallCT GlobalTheory.ConeSmallSerInt GlobalTheory.LeviModulus.HCoord GlobalTheory.UnipMass

theorem exists_bigEquiv {B : Base F E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {r s r₁ s₁ i₀ i₁ : ℕ} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hX : X.IsSkew σ B r s) (hX₁ : X₁.IsSkew σ B r₁ s₁) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    {w : UA σ X.J} (hw : w ∈ ratU σ X.J) (hwx : mat w *ᵥ incV F H.x = incV F H.y) (hwy : mat w *ᵥ incV F H.y = -incV F H.x)
    {T : Set (UA σ X.J)} (hT : IsReps T H.x) :
    ∃ e : bigSet H.x T ≃ (ratU σ X.J).subgroupOf (unip σ X H), ∀ t, StabLn H.x (w * (e t).1.1 * t.1⁻¹) := by
  have hwi : mat w⁻¹ *ᵥ incV F H.x = -incV F H.y :=
    mat_inv_mulVec w (by rw [Matrix.mulVec_neg, hwy, neg_neg])
  have huq : ∀ (γ : UA σ X.J) (ν ν' : (ratU σ X.J).subgroupOf (unip σ X H)),
      StabLn H.x (w * ν.1.1 * γ⁻¹) → StabLn H.x (w * ν'.1.1 * γ⁻¹) → ν = ν' := by
    intro γ ν ν' h1 h2
    have h3 := stabLn_mul h1 (stabLn_inv h2)
    have h4 : w * ν.1.1 * γ⁻¹ * (w * ν'.1.1 * γ⁻¹)⁻¹ = w * (ν.1.1 * ν'.1.1⁻¹) * w⁻¹ := by group
    rw [h4] at h3
    obtain ⟨l, hl⟩ := h3
    rw [mat_mul_mulVec, mat_mul_mulVec, hwi] at hl
    have h5 := mat_inv_mulVec w hl
    rw [Matrix.mulVec_smul, hwi, Matrix.mulVec_neg, smul_neg, neg_inj] at h5
    have := eq_one_of_stab_dual hB hX hH (mul_mem ν.1.2 (inv_mem ν'.1.2)) h5.symm
    exact Subtype.ext (Subtype.ext (mul_inv_eq_one.1 this))
  have hex : ∀ t : bigSet H.x T, ∃ ν : (ratU σ X.J).subgroupOf (unip σ X H), StabLn H.x (w * ν.1.1 * t.1⁻¹) := by
    intro t
    obtain ⟨ν, hν, l, hl⟩ := exists_eichler F E σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH t.1 (hT.1 t.2.1) t.2.2.2
    refine ⟨⟨⟨ν, hν.2⟩, hν.1⟩, -l, ?_⟩
    rw [mul_assoc, mat_mul_mulVec, hl, Matrix.mulVec_smul, hwy, Units.val_neg, smul_neg, neg_smul]
  have hwν : ∀ ν : (ratU σ X.J).subgroupOf (unip σ X H), w * ν.1.1 ∈ ratU σ X.J := fun ν =>
    mul_mem hw (Subgroup.mem_subgroupOf.1 ν.2)
  have hrep : ∀ ν : (ratU σ X.J).subgroupOf (unip σ X H), ∃ t, t ∈ T ∧ StabLn H.x (w * ν.1.1 * t⁻¹) := fun ν =>
    (hT.2 _ (hwν ν)).exists
  have hXX : hA σ X.J (incV F H.x) (incV F H.x) = 0 := by rw [hA_incV', hH.xx, map_zero]
  have hXY : hA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [hA_incV', hH.xy, map_one]
  have hno : ∀ u ∈ unip σ X H, ∀ t, StabLn H.x (w * u * t⁻¹) → ¬ OrthLn H.x t := by
    intro u hu t ⟨l, hl⟩ ho
    rw [GlobalTheory.UnipCT.unip_eq] at hu
    have hux : mat u *ᵥ incV F H.x = incV F H.x := hu.1
    have e := hA_mat (w * u) (mat t⁻¹ *ᵥ incV F H.x) (incV F H.x)
    rw [← mat_mul_mulVec, hl, mat_mul_mulVec, hux, hwx, hA_smul_l, hXY, mul_one] at e
    haveI := nontrivial_AE (F := F) (E := E)
    exact l.ne_zero (e.trans ho)
  have hso : ∀ t : UA σ X.J, StabLn H.x t → OrthLn H.x t := by
    intro t ht
    obtain ⟨l, hl⟩ := stabLn_inv ht
    show hA σ X.J (mat t⁻¹ *ᵥ incV F H.x) (incV F H.x) = 0
    rw [hl, hA_smul_l, hXX, mul_zero]
  refine ⟨{ toFun := fun t => (hex t).choose
            invFun := fun ν => ⟨(hrep ν).choose, (hrep ν).choose_spec.1,
              fun h => hno _ ν.1.2 _ (hrep ν).choose_spec.2 (hso _ h), hno _ ν.1.2 _ (hrep ν).choose_spec.2⟩
            left_inv := fun t => by
              apply Subtype.ext
              exact (hT.2 _ (hwν _)).unique (hrep _).choose_spec ⟨t.2.1, (hex t).choose_spec⟩
            right_inv := fun ν => huq _ _ _ (hex _).choose_spec (hrep ν).choose_spec.2 }, fun t => (hex t).choose_spec⟩

theorem isLevi_conj {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} (hσ : ∀ a, σ (σ a) = a)
    {w : UA σ X.J} (hwx : mat w *ᵥ incV F H.x = incV F H.y) (hwy : mat w *ᵥ incV F H.y = -incV F H.x)
    (hwι : mat w * incM F H.ι = incM F H.ι) {t : (AE F E)ˣ} {m : UA σ X.J} (hm : IsLevi (W₁ := X₁) H t 1 m) :
    IsLevi (W₁ := X₁) H (Units.map (cA σ).toMonoidHom t)⁻¹ 1 (w * m * w⁻¹) := by
  have hwi : mat w⁻¹ *ᵥ incV F H.x = -incV F H.y :=
    mat_inv_mulVec w (by rw [Matrix.mulVec_neg, hwy, neg_neg])
  have hwi' : mat w⁻¹ *ᵥ incV F H.y = incV F H.x := mat_inv_mulVec w hwx
  have hone : mat (1 : UA σ X₁.J) = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_mul_mulVec, mat_mul_mulVec, hwi, Matrix.mulVec_neg, hm.2.1, Matrix.mulVec_neg, Matrix.mulVec_smul, hwy, smul_neg,
      neg_neg, ← map_inv]
    rfl
  · rw [mat_mul_mulVec, mat_mul_mulVec, hwi', hm.1, Matrix.mulVec_smul, hwx, inv_inv]
    congr 1
    exact (GlobalTheory.LeviModulus.cA_cA σ hσ _).symm
  · have h1 : mat w⁻¹ * incM F H.ι = incM F H.ι := by
      conv_lhs => rw [← hwι]
      rw [← Matrix.mul_assoc, GlobalTheory.UnipCT.mat_inv_mul', Matrix.one_mul]
    have h2 := hm.2.2
    rw [hone, Matrix.mul_one] at h2 ⊢
    rw [GlobalTheory.UnipCT.mat_mul', GlobalTheory.UnipCT.mat_mul', Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, hwι]

theorem exists_isCT_big {B : Base F E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {r s r₁ s₁ i₀ i₁ : ℕ} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hX : X.IsSkew σ B r s) (hX₁ : X₁.IsSkew σ B r₁ s₁) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    {T : Set (UA σ X.J)} (hT : IsReps T H.x) {f : UA σ X.J → ℂ} (hf : Measurable f)
    (hinv : ∀ p ∈ ratU σ X.J, StabLn H.x p → ∀ h, f (p * h) = f h) (hL : LocUnifSum f T)
    {χ : Chr F E} {z : ℂ} (hlaw : HasLawC X₁ H χ z f) (hχ : ∀ t, χ (Units.map (cA σ).toMonoidHom t) = (χ t)⁻¹) :
    ∃ T₂ : UA σ X.J → ℂ, IsCT H (partSum f (bigSet H.x T)) T₂ ∧ HasLawC X₁ H χ (-z + ((n₁ + 1 : ℕ) : ℂ)) T₂ := by
  obtain ⟨w, hw, hwx, hwy, hwι⟩ := exists_swap F E σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH
  obtain ⟨R, hR⟩ := GlobalTheory.UnipCompact.exists_bounded_translate F E σ B _ _ X X₁ H _ _ _ _ hB hX hH
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ X H) := (GlobalTheory.UnipCT.isClosed_unip σ X H).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) X.J
  let Γ := (ratU σ X.J).subgroupOf (unip σ X H)
  obtain ⟨e, he⟩ : ∃ e : bigSet H.x T ≃ Γ, ∀ t, StabLn H.x (w * (e t).1.1 * t.1⁻¹) :=
    exists_bigEquiv hB hX hX₁ hH hw hwx hwy hT
  haveI : Countable Γ :=
    Function.Injective.countable (f := fun g : Γ => (⟨g.1.1, g.2⟩ : ratU σ X.J))
      fun g h hgh => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hgh
  have hfe : ∀ (t : bigSet H.x T) (v : UA σ X.J), f (t.1 * v) = f (w * (e t).1.1 * v) := by
    intro t v
    have hp : w * (e t).1.1 * t.1⁻¹ ∈ ratU σ X.J :=
      mul_mem (mul_mem hw (Subgroup.mem_subgroupOf.1 (e t).2)) (inv_mem (hT.1 t.2.1))
    rw [← hinv _ hp (he t) (t.1 * v)]
    congr 1
    group
  let Φ : UA σ X.J → unip σ X H → ℂ := fun h u => f (w * u.1 * h)
  have key : ∀ h (u : unip σ X H), partSum f (bigSet H.x T) (u.1 * h) = ∑' ν : Γ, Φ h (ν.1 * u) := by
    intro h u
    unfold partSum
    rw [← e.symm.tsum_eq]
    refine tsum_congr fun ν => ?_
    rw [hfe, e.apply_symm_apply]
    show _ = f (w * (ν.1.1 * u.1) * h)
    simp only [mul_assoc]
  have hΦm : ∀ h, Measurable (Φ h) := fun h =>
    hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hint : ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure → IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 →
      ∀ h, Integrable (Φ h) μ := by
    intro μ 𝓕 hμ h𝓕 h1 h
    obtain ⟨b, hb, hbd⟩ := hL _ (isCompact_ht_le (σ := σ) (J := X.J) (R * ht h))
    have hbound : ∀ u : unip σ X H, ∑' γ : Γ, ‖Φ h (γ.1 * u)‖ₑ ≤ ∑' t : T, ENNReal.ofReal (b t) := by
      intro u
      obtain ⟨γ₀, hγ₀, hγR⟩ := hR u.1 u.2
      let γ₁ : Γ := ⟨⟨γ₀, hγ₀.2⟩, hγ₀.1⟩
      have hmem : γ₀ * u.1 * h ∈ {g : UA σ X.J | ht g ≤ R * ht h} :=
        (heightGL_mul_le F (γ₀ * u.1).1 h.1).trans (mul_le_mul_left hγR _)
      rw [← (e.trans (Equiv.mulRight γ₁)).tsum_eq]
      refine le_trans (ENNReal.tsum_le_tsum fun t => ?_) (ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun t : bigSet H.x T => (⟨t.1, t.2.1⟩ : T)) (fun t t' htt => Subtype.ext (congrArg (fun x : T => x.1) htt))
        (fun t => ENNReal.ofReal (b t)))
      have h2 := hbd ⟨t.1, t.2.1⟩ _ hmem
      have h3 : Φ h (((e.trans (Equiv.mulRight γ₁)) t).1 * u) = f (t.1 * (γ₀ * u.1 * h)) := by
        rw [hfe]
        show f (w * ((e t).1.1 * γ₀ * u.1) * h) = _
        simp only [mul_assoc]
      rw [h3, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal h2
    exact integrable_of_fd Γ μ 𝓕 h𝓕 h1 (hΦm h) hb.tsum_ofReal_lt_top hbound
  by_cases hex : ∃ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1
  swap
  · exact ⟨0, fun μ 𝓕 hμ h𝓕 h1 => (hex ⟨μ, 𝓕, hμ, h𝓕, h1⟩).elim, fun _ _ _ _ => by simp⟩
  obtain ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h₀⟩ := hex
  refine ⟨fun h => ∫ u, Φ h u ∂μ₀, fun μ 𝓕 hμ h𝓕 h1 h => ?_, fun t m hm h => ?_⟩
  · simp only [key]
    rw [← (GlobalTheory.EisBig.unfold_fd Γ μ₀ 𝓕₀ h𝓕₀ (Φ h) (hint μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ h)).2]
    refine GlobalTheory.UnipCT.setIntegral_fd_eq Γ (fun u => ∑' ν : Γ, Φ h (ν.1 * u)) (fun γ hγ x => ?_) μ₀ μ 𝓕₀ 𝓕 h𝓕₀ h𝓕 h₀ h1
    show ∑' ν : Γ, Φ h (ν.1 * (γ * x)) = ∑' ν : Γ, Φ h (ν.1 * x)
    rw [← (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq (fun ν : Γ => Φ h (ν.1 * x))]
    refine tsum_congr fun ν => ?_
    rw [← mul_assoc]
    rfl
  · have hm' := isLevi_conj (GlobalTheory.PlaneLevi.invol_of_good hB) hwx hwy hwι hm
    have hmi := GlobalTheory.LeviModulusAdapted.isLevi_inv H hm
    have h1 : ∀ u : unip σ X H, Φ (m * h) u = (χ (Units.map (cA σ).toMonoidHom t)⁻¹ : ℂ) *
        ((absE F E (Units.map (cA σ).toMonoidHom t)⁻¹ : ℝ) : ℂ) ^ z * f (w * (m⁻¹ * u.1 * m⁻¹⁻¹) * h) := by
      intro u
      rw [← hlaw _ _ hm']
      show f _ = f _
      congr 1
      group
    show ∫ u, Φ (m * h) u ∂μ₀ = _
    simp only [h1]
    rw [integral_const_mul, integral_conj_levi F E σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH μ₀ hμ₀ _ _ _ hmi
      (fun v => f (w * v * h)), map_inv χ, hχ, inv_inv, map_inv, map_inv, GlobalTheory.ConeSmallLaw.absE_cA]
    have hr := GlobalTheory.ConeSmallLaw.absE_pos t
    have hc0 : ((absE F E t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have ha : ((absE F E t : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]
      exact Real.pi_ne_zero.symm
    rw [NNReal.coe_inv, Complex.ofReal_inv, Complex.inv_cpow _ _ ha, inv_pow, inv_inv, Complex.cpow_add _ _ hc0,
      Complex.cpow_neg, Complex.cpow_natCast]
    ring

theorem ctBig : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T →
      GlobalTheory.ThK.CTAdd.CTInt H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.bigSet H'.x T)) ∧ ∃ T₂ : UA σ G.W.J → ℂ, IsCT H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.bigSet H'.x T)) T₂ ∧
        GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.β (-s + ((a + b + 1 : ℕ) : ℂ) / 2) T₂ := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ
  refine ⟨0, fun T hR s _ hL => ?_⟩
  obtain ⟨R, hR'⟩ := GlobalTheory.UnipCompact.exists_bounded_translate F E σ B _ _ G.W G₁.W H' _ _ _ _ hT.base hT.geo.hW hC.hH'
  have hm := measurable_coneI hK F E σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ
    (s + ((a : ℂ) + 1) / 2)
  have hinv := fun p hp hs h => GlobalTheory.T.seesaw_evaluation_haar_nonarchimedean hK F E σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ
    (s + ((a : ℂ) + 1) / 2) p hp hs h
  refine ⟨ctInt_partSum H' R hR' hR (fun t ht => ht.1) hm hinv hL, ?_⟩
  obtain ⟨T₂, h1, h2⟩ := exists_isCT_big hT.base hT.geo.hW hT₁.geo.hW hC.hH' hR hm hinv hL
    (GlobalTheory.T.eisenstein_haar_stabilizer_integral hK F E σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ _)
    (GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT))
  refine ⟨T₂, h1, ?_⟩
  convert h2 using 1
  push_cast
  ring

end GlobalTheory.ConeSmallBig

end
