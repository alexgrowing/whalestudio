import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapStarMul

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.IndLine.Iwasawa

open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealLift.OneParam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => simp [cA, sigma_sigma h]

theorem inclR_sigma (a : E) : inclR (F := F) (AF F) (σ a) = cA σ (inclR (F := F) (AF F) a) := by
  simp [cA, inclR]

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ r s : ℕ}

theorem exists_hyp (hcm : IsCMExt F E σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ ι', Hyp (σ : E →+* E) W.J H.x H.y H.ι ι' := by
  have cc : ∀ a, (σ : E →+* E) ((σ : E →+* E) a) = a := sigma_sigma hcm
  have skew : W.J.map (σ : E →+* E) = -W.Jᵀ := by
    ext i j
    exact hW.skew j i
  have xx : H.x ⬝ᵥ W.J *ᵥ ((σ : E →+* E) ∘ H.x) = 0 := hH.xx
  have yy : H.y ⬝ᵥ W.J *ᵥ ((σ : E →+* E) ∘ H.y) = 0 := hH.yy
  have xy : H.x ⬝ᵥ W.J *ᵥ ((σ : E →+* E) ∘ H.y) = 1 := hH.xy
  have ox : ∀ u, (H.ι *ᵥ u) ⬝ᵥ W.J *ᵥ ((σ : E →+* E) ∘ H.x) = 0 := fun u => (hH.orth u).1
  have oy : ∀ u, (H.ι *ᵥ u) ⬝ᵥ W.J *ᵥ ((σ : E →+* E) ∘ H.y) = 0 := fun u => (hH.orth u).2
  have yx : H.y ⬝ᵥ W.J *ᵥ ((σ : E →+* E) ∘ H.x) = -1 := by
    have e := congrArg (σ : E →+* E) xy
    rw [RingHom.map_dotProduct, c_mulVec cc skew, map_one, dotProduct_neg, dotProduct_comm,
      ← Matrix.dotProduct_mulVec] at e
    exact neg_eq_iff_eq_neg.1 e
  have vz : ∀ a : Fin d → E, (∀ u, (H.ι *ᵥ u) ⬝ᵥ a = 0) → a ᵥ* H.ι = 0 := fun a ha => by
    funext j
    have := ha (Pi.single j 1)
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    exact this
  let T : (E × (Fin d₁ → E) × E) →ₗ[E] (Fin d → E) :=
    (LinearMap.toSpanSingleton E _ H.x).coprod ((Matrix.mulVecLin H.ι).coprod (LinearMap.toSpanSingleton E _ H.y))
  have hT : ∀ a u b, T (a, u, b) = a • H.x + (H.ι *ᵥ u + b • H.y) := fun a u b => rfl
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, e⟩ := hH.split z hz
    exact ⟨(a, u, b), by rw [hT, e, add_assoc]⟩
  have hinj : Function.Injective T := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj
    simp [hH.rank]; ring
  have hι : ∀ u v, H.ι *ᵥ u = H.ι *ᵥ v → u = v := fun u v h => by
    have := @hinj (0, u, 0) (0, v, 0) (by rw [hT, hT, h])
    simpa using this
  have hu : ∀ v, ∃ u, H.ι *ᵥ u = (1 - prX (σ : E →+* E) W.J H.x H.y - prY (σ : E →+* E) W.J H.x H.y) *ᵥ v := fun v => by
    obtain ⟨⟨a, u, b⟩, rfl⟩ := hsurj v
    refine ⟨u, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, prX_mulVec, prY_mulVec, hT]
    simp only [add_dotProduct, smul_dotProduct, xx, yy, xy, yx, ox, oy, smul_eq_mul]
    simp
  choose u hu using hu
  let ι' : Matrix (Fin d₁) (Fin d) E := Matrix.of fun i j => u (Pi.single j 1) i
  have right : H.ι * ι' = 1 - prX (σ : E →+* E) W.J H.x H.y - prY (σ : E →+* E) W.J H.x H.y := by
    ext i j
    have := congrFun (hu (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  refine ⟨ι', cc, skew, xx, yy, xy, yx, vz _ ox, vz _ oy, ?_, right⟩
  refine Matrix.toLin'.injective (LinearMap.ext fun v => hι _ _ ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, right,
    ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, prX_mulVec, prY_mulVec, ox, oy]
  simp

variable {ι' : Matrix (Fin d₁) (Fin d) E}

theorem hyp_adelic (hcm : IsCMExt F E σ) (h : Hyp (σ : E →+* E) W.J H.x H.y H.ι ι') :
    Hyp (cA σ : AE F E →+* AE F E) (incM F W.J) (incV F H.x) (incV F H.y) (incM F H.ι) (incM F ι') :=
  h.map (inclR (F := F) (AF F)) inclR_sigma (cA_cA hcm)

theorem hyp_place (hcm : IsCMExt F E σ) (h : Hyp (σ : E →+* E) W.J H.x H.y H.ι ι') (τ : E →+* ℂ) :
    Hyp (starRingEnd ℂ) (W.J.map τ) (τ ∘ H.x) (τ ∘ H.y) (H.ι.map τ) (ι'.map τ) :=
  h.map τ (hcm.2.2.2 τ) star_star

theorem prX_piInf (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) :
    (prX (cA σ : AE F E →+* AE F E) (incM F W.J) (incV F H.x) (incV F H.y)).map (piInf τ) =
      prX (starRingEnd ℂ) (W.J.map τ.1) (τ.1 ∘ H.x) (τ.1 ∘ H.y) := by
  rw [← prX_map (c := (σ : E →+* E)) (c' := starRingEnd ℂ) τ.1 (hcm.2.2.2 τ.1), ← incM_piInf]
  exact congrArg (·.map (piInf τ)) (prX_map (c := (σ : E →+* E)) (J := W.J) (x := H.x) (y := H.y) (inclR (F := F) (AF F)) inclR_sigma).symm

theorem prY_piInf (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) :
    (prY (cA σ : AE F E →+* AE F E) (incM F W.J) (incV F H.x) (incV F H.y)).map (piInf τ) =
      prY (starRingEnd ℂ) (W.J.map τ.1) (τ.1 ∘ H.x) (τ.1 ∘ H.y) := by
  rw [← prY_map (c := (σ : E →+* E)) (c' := starRingEnd ℂ) τ.1 (hcm.2.2.2 τ.1), ← incM_piInf]
  exact congrArg (·.map (piInf τ)) (prY_map (c := (σ : E →+* E)) (J := W.J) (x := H.x) (y := H.y) (inclR (F := F) (AF F)) inclR_sigma).symm

theorem grading_place {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] {N θ : Matrix m m ℂ}
    {x y : m → ℂ} {ι : Matrix m n ℂ} {ι' : Matrix n m ℂ} (h : Hyp (starRingEnd ℂ) N x y ι ι') (hθ : θ * θ = 1)
    {θ₁ : Matrix n n ℂ} (hι : θ * ι = ι * θ₁) {c : ℂ} (hc : c ≠ 0) (hy : y = c • θ *ᵥ x) :
    Grading (prX (starRingEnd ℂ) N x y) (1 - prX (starRingEnd ℂ) N x y - prY (starRingEnd ℂ) N x y)
      (prY (starRingEnd ℂ) N x y) θ := by
  have e1 : θ *ᵥ x = c⁻¹ • y := by rw [hy, inv_smul_smul₀ hc]
  have e2 : θ *ᵥ y = c • x := by rw [hy, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hθ, Matrix.one_mulVec]
  refine ⟨h.pp, h.qq, h.pq, h.qp, rfl, hθ, h.ext' ?_ ?_ ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h.px, e1, Matrix.mulVec_smul, h.qy]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h.py, e2, Matrix.mulVec_smul, h.qx, Matrix.mulVec_zero, smul_zero]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, h.pι, hι, ← Matrix.mul_assoc, h.qι, Matrix.mul_zero, Matrix.zero_mul]

theorem adj_cartan {N θ : Matrix (Fin d) (Fin d) ℂ} (h : IsCartan (Complex.I • N) θ) : Adj N θ θ := by
  have e := h.2.1
  rw [Matrix.mul_smul, Matrix.smul_mul] at e
  have e' := smul_right_injective _ Complex.I_ne_zero e
  have e2 : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h.1, Matrix.map_one _ (star_zero _) (star_one _)]
  calc θᵀ * N = θᵀ * N * θ.map star * θ.map star := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
    _ = _ := by rw [e']

theorem upq_iff {N Z : Matrix (Fin d) (Fin d) ℂ} {C : Matrix (Fin d) (Ix r s) ℂ} {C' : Matrix (Ix r s) (Fin d) ℂ}
    (hF : Cᵀ * (Complex.I • N) * C.map star = Jm r s) (hR : C * C' = 1) {Y : Mat r s} (hZ : Z * C = C * Y) :
    Y ∈ upq r s ↔ Adj N Z (-Z) := by
  have key : (Yᴴ * Jm r s + Jm r s * Y)ᵀ = Cᵀ * (Complex.I • (Zᵀ * N - N * (-Z).map star)) * C.map star := by
    have e1 : Cᵀ * Zᵀ = Yᵀ * Cᵀ := by rw [← Matrix.transpose_mul, hZ, Matrix.transpose_mul]
    have e2 : Z.map star * C.map star = C.map star * Y.map star := by rw [← map_star_mul, hZ, map_star_mul]
    have e3 : Yᴴᵀ = Y.map star := rfl
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, jm_transpose, e3, Matrix.map_neg _ star_neg,
      Matrix.mul_neg, sub_neg_eq_add, smul_add, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_smul, ← Matrix.smul_mul,
      ← Matrix.mul_assoc, e1, Matrix.mul_assoc Cᵀ, Matrix.mul_assoc _ (Z.map star), e2, add_comm, ← hF]
    simp only [Matrix.mul_assoc]
  constructor
  · intro hY
    have hY' : Yᴴ * Jm r s + Jm r s * Y = 0 := hY
    rw [hY', Matrix.transpose_zero] at key
    have e1 : C'ᵀ * Cᵀ = 1 := by rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
    have e2 : C.map star * C'.map star = 1 := by
      rw [← map_star_mul, hR, Matrix.map_one _ (star_zero _) (star_one _)]
    have e := congrArg (fun A => C'ᵀ * A * C'.map star) key
    simp only [Matrix.mul_zero, Matrix.zero_mul] at e
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one, eq_comm,
      smul_eq_zero] at e
    exact sub_eq_zero.1 (e.resolve_left Complex.I_ne_zero)
  · intro hA
    rw [sub_eq_zero.2 hA, smul_zero, Matrix.mul_zero, Matrix.zero_mul] at key
    exact Matrix.transpose_eq_zero.1 key

theorem exists_line (hcm : IsCMExt F E σ) {C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ}
    {C' : InfinitePlace F → Matrix (Ix r s) (Fin d) ℂ} (hC : ∀ w, IsFrame (Complex.I • W.J.map (B.emb w).1) (C w))
    (hR : ∀ w, C w * C' w = 1) (Z : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ)
    (hZ : ∀ w, Adj (W.J.map (B.emb w).1) (Z w) (-Z w)) :
    ∃ γ ∈ Lines σ W, IsGen B.emb C γ (fun w => C' w * Z w * C w) ∧
      ∀ t w, (mat (γ t)).map (piInf (B.emb w)) = NormedSpace.exp (Multiplicative.toAdd t • Z w) := by
  have e : ∀ w, Z w * C w = C w * (C' w * Z w * C w) := fun w => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hR, Matrix.one_mul]
  obtain ⟨γ, hγ, hg⟩ := exists_line_of_upq F E σ (Fin d) r s B.emb (incM F W.J) Complex.I C hcm
    (fun w => by rw [incM_piInf]; exact hC w) (fun w => C' w * Z w * C w) fun w => (upq_iff (hC w).1 (hR w) (e w)).2 (hZ w)
  refine ⟨γ, hγ, hg, fun t w => ?_⟩
  have h1 := hg (Multiplicative.toAdd t) w
  rw [← exp_mul_eq (A := Multiplicative.toAdd t • Z w) (by rw [Matrix.smul_mul, Matrix.mul_smul, ← e])] at h1
  have h2 := congrArg (· * C' w) h1
  simp only [Matrix.mul_assoc, hR, Matrix.mul_one] at h2
  exact h2

theorem comm_of_place (hcm : IsCMExt F E σ) {g p : Matrix (Fin d) (Fin d) (AE F E)} (hg : At (evI F) (g - 1))
    (h : ∀ w, g.map (piInf (B.emb w)) * p.map (piInf (B.emb w)) = p.map (piInf (B.emb w)) * g.map (piInf (B.emb w))) :
    g * p = p * g := by
  refine eq_of_at hcm B.emb ?_ fun w => by rw [Matrix.map_mul, Matrix.map_mul, h]
  have e : g * p - p * g = (g - 1) * p - p * (g - 1) := by noncomm_ring
  rw [e]
  exact at_sub (at_mul_right hg _) (at_mul_left hg _)

theorem exists_levi (hcm : IsCMExt F E σ) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (h : Hyp (σ : E →+* E) W.J H.x H.y H.ι ι')
    {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W)
    (hp : ∀ t, mat (γ t) * prX (cA σ : AE F E →+* AE F E) (incM F W.J) (incV F H.x) (incV F H.y) =
      prX (cA σ : AE F E →+* AE F E) (incM F W.J) (incV F H.x) (incV F H.y) * mat (γ t))
    (hq : ∀ t, mat (γ t) * prY (cA σ : AE F E →+* AE F E) (incM F W.J) (incV F H.x) (incV F H.y) =
      prY (cA σ : AE F E →+* AE F E) (incM F W.J) (incV F H.x) (incV F H.y) * mat (γ t)) :
    ∃ (τ : Multiplicative ℝ →* (AE F E)ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
      ∀ t, IsLevi H (τ t) (γ₁ t) (γ t) := by
  have hA := hyp_adelic hcm h
  have m1 : mat (γ 1) = 1 := by rw [map_one]; rfl
  have mm : ∀ a b, mat (γ (a * b)) = mat (γ a) * mat (γ b) := fun a b => by rw [map_mul]; rfl
  let τ₀ : Multiplicative ℝ →* AE F E :=
    { toFun := fun t => (mat (γ t) *ᵥ incV F H.x) ⬝ᵥ incM F W.J *ᵥ ((cA σ : AE F E →+* AE F E) ∘ incV F H.y)
      map_one' := by rw [m1, Matrix.one_mulVec, hA.xy]
      map_mul' := fun a b => by
        rw [mm, ← Matrix.mulVec_mulVec, hA.mulVec_eq_smul_of_commute_prX (hp b), Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul, mul_comm,
          ← hA.mulVec_eq_smul_of_commute_prX (hp b)] }
  set f : Multiplicative ℝ → Matrix (Fin d₁) (Fin d₁) (AE F E) := fun t => incM F ι' * mat (γ t) * incM F H.ι with hf
  have hι : ∀ t, mat (γ t) * incM F H.ι = incM F H.ι * f t := fun t => hA.levi_ι (hp t) (hq t)
  have f1 : f 1 = 1 := by rw [hf]; simp only [m1, Matrix.mul_one]; exact hA.left
  have fm : ∀ a b, f (a * b) = f a * f b := fun a b => by
    calc f (a * b) = incM F ι' * mat (γ a) * (mat (γ b) * incM F H.ι) := by simp only [hf, mm, Matrix.mul_assoc]
      _ = _ := by rw [hι b, ← Matrix.mul_assoc]
  have gram : (incM F H.ι)ᵀ * incM F W.J * (incM F H.ι).map (cA σ) = incM F W₁.J := by
    have e : (incM F H.ι).map (cA σ) = incM F (H.ι.map σ) := by
      ext i j
      exact (inclR_sigma _).symm
    rw [← hH.gram, e, incM, incM, incM, incM, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have mc : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) (AE F E)) (Q : Matrix (Fin b) (Fin c) (AE F E)),
      (P * Q).map (cA σ) = P.map (cA σ) * Q.map (cA σ) := fun P Q => Matrix.map_mul (f := (cA σ).toRingHom)
  have fU : ∀ t, (f t)ᵀ * incM F W₁.J * (f t).map (cA σ) = incM F W₁.J := fun t => by
    have hu : (mat (γ t))ᵀ * incM F W.J * (mat (γ t)).map (cA σ) = incM F W.J := (γ t).2
    calc (f t)ᵀ * incM F W₁.J * (f t).map (cA σ)
        = (incM F H.ι * f t)ᵀ * incM F W.J * (incM F H.ι * f t).map (cA σ) := by
          rw [← gram, mc (incM F H.ι) (f t), Matrix.transpose_mul (incM F H.ι) (f t)]; simp only [Matrix.mul_assoc]
      _ = (incM F H.ι)ᵀ * ((mat (γ t))ᵀ * incM F W.J * (mat (γ t)).map (cA σ)) * (incM F H.ι).map (cA σ) := by
          rw [← hι, mc, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, gram]
  let γ₁ : Multiplicative ℝ →* UA σ W₁.J :=
    { toFun := fun t => ⟨⟨f t, f t⁻¹, by rw [← fm, mul_inv_cancel, f1], by rw [← fm, inv_mul_cancel, f1]⟩, fU t⟩
      map_one' := Subtype.ext (Units.ext f1)
      map_mul' := fun a b => Subtype.ext (Units.ext (fm a b)) }
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have fc : Continuous f :=
    (continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp hγ.1))).matrix_mul continuous_const
  refine ⟨τ₀.toHomUnits, γ₁, ⟨?_, fun t u hu => ?_⟩, fun t => ⟨hA.mulVec_eq_smul_of_commute_prX (hp t), ?_, hι t⟩⟩
  · have hu : Continuous fun t : Multiplicative ℝ => ((γ₁ t).1 : GL (Fin d₁) (AE F E)) :=
      Units.continuous_iff.2 ⟨fc, fc.comp continuous_inv⟩
    exact hu.subtype_mk _
  · have e : mat (γ₁ t) - 1 = incM F ι' * (mat (γ t) - 1) * incM F H.ι := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hA.left]; rfl
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hγ.2 t u hu, Matrix.mul_zero, Matrix.zero_mul]
  · exact hA.levi_y (hq t) (γ t).2 rfl

theorem exists_parts (hcm : IsCMExt F E σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    {C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ} (hC : ∀ w, IsFrame (Complex.I • W.J.map (B.emb w).1) (C w))
    (Y : InfinitePlace F → Mat r s) (hY : ∀ w, Y w ∈ upq r s) :
    ∃ γu ∈ Lines σ W, ∃ γl ∈ Lines σ W, ∃ γk ∈ Lines σ W, (∀ t, γu t ∈ unip σ W H) ∧
      (∃ (τ : Multiplicative ℝ →* (AE F E)ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
        ∀ t, IsLevi H (τ t) (γ₁ t) (γl t)) ∧ (∀ t, γk t ∈ KInf σ W B.emb) ∧
      ∃ Yu Yl Yk : InfinitePlace F → Mat r s, IsGen B.emb C γu Yu ∧ IsGen B.emb C γl Yl ∧ IsGen B.emb C γk Yk ∧
        ∀ w, Y w = Yu w + Yl w + Yk w := by
  obtain ⟨ι', h⟩ := exists_hyp hcm hW hH
  have hA := hyp_adelic hcm h
  choose C' hR using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hR w)
  set p : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ := fun w =>
    prX (starRingEnd ℂ) (W.J.map (B.emb w).1) ((B.emb w).1 ∘ H.x) ((B.emb w).1 ∘ H.y) with hp
  set q : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ := fun w =>
    prY (starRingEnd ℂ) (W.J.map (B.emb w).1) ((B.emb w).1 ∘ H.x) ((B.emb w).1 ∘ H.y) with hq
  have hG : ∀ w, Grading (p w) (1 - p w - q w) (q w) (W.θ w) := fun w => by
    obtain ⟨hι, c, hc, hy⟩ := hH.cartan w
    exact grading_place (hyp_place hcm h (B.emb w).1) (hW.cartan w).1 hι hc hy
  set Z : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ := fun w => C w * Y w * C' w with hZ
  have hZC : ∀ w, Z w * C w = C w * Y w := fun w => by
    rw [hZ]; simp only [Matrix.mul_assoc, hL, Matrix.mul_one]
  have hadj := fun w => adj_parts (hG w) (hyp_place hcm h (B.emb w).1).adj_pq (hyp_place hcm h (B.emb w).1).adj_qp
    (adj_cartan (hW.cartan w)) ((upq_iff (hC w).1 (hR w) (hZC w)).1 (hY w))
  obtain ⟨γu, hu, gu, eu⟩ := exists_line hcm hC hR _ fun w => (hadj w).1
  obtain ⟨γl, hl, gl, el⟩ := exists_line hcm hC hR _ fun w => (hadj w).2.1
  obtain ⟨γk, hk, gk, ek⟩ := exists_line hcm hC hR _ fun w => (hadj w).2.2
  refine ⟨γu, hu, γl, hl, γk, hk, fun t => Subgroup.subset_closure ⟨hA.mulVec_eq_self_of_mul_prX_eq_prX ?_, hA.unip_ι ?_⟩,
    exists_levi hcm hH h hl (fun t => comm_of_place (B := B) hcm (hl.2 t) fun w => ?_)
      (fun t => comm_of_place (B := B) hcm (hl.2 t) fun w => ?_), fun t => ⟨hk.2 t, fun w => ?_⟩, _, _, _, gu, gl, gk,
    fun w => ?_⟩
  · refine eq_of_at hcm B.emb ?_ fun w => ?_
    · have e : ∀ g P : Matrix (Fin d) (Fin d) (AE F E), g * P - P = (g - 1) * P := fun g P => by noncomm_ring
      rw [e]
      exact at_mul_right (hu.2 t) _
    · rw [Matrix.map_mul, eu, prX_piInf hcm]
      exact (exp_up (hG w) _ _).1
  · refine eq_of_at hcm B.emb ?_ fun w => ?_
    · have e : ∀ g P Q : Matrix (Fin d) (Fin d) (AE F E), P * P = P → P * Q = 0 →
          (1 - P) * g * (1 - P - Q) - (1 - P - Q) = (1 - P) * (g - 1) * (1 - P - Q) := fun g P Q h1 h2 => by
        have : (1 - P) * (1 - P - Q) = 1 - P - Q := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_sub, h1, h2, Matrix.mul_one]; abel
        rw [Matrix.mul_sub _ g, Matrix.sub_mul _ ((1 - P) * 1), Matrix.mul_one, this]
      rw [e _ _ _ hA.pp hA.pq]
      exact at_mul_right (at_mul_left (hu.2 t) _) _
    · simp only [Matrix.map_mul, Matrix.map_sub _ (map_sub (piInf (B.emb w))),
        Matrix.map_one _ (map_zero (piInf (B.emb w))) (map_one (piInf (B.emb w)))]
      rw [eu, prX_piInf hcm, prY_piInf hcm]
      exact (exp_up (hG w) _ _).2
  · rw [el, prX_piInf hcm]
    exact exp_mul_eq (by rw [Matrix.smul_mul, Matrix.mul_smul, (hG w).mid_p])
  · rw [el, prY_piInf hcm]
    exact exp_mul_eq (by rw [Matrix.smul_mul, Matrix.mul_smul, (hG w).mid_q])
  · rw [ek]
    exact exp_mul_eq (by rw [Matrix.smul_mul, Matrix.mul_smul, ((hG w).comm_cpt _).eq])
  · rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, ← (hG w).dec, Matrix.mul_assoc, hZC,
      ← Matrix.mul_assoc, hL, Matrix.one_mul]

theorem sumPl_add₃ {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (a b c : ∀ w, Module.End ℂ (V w)) : sumPl (fun w => a w + b w + c w) = sumPl a + sumPl b + sumPl c := by
  have e : ∀ (w : ι) (L L' : Module.End ℂ (V w)), atPl w (L + L') = atPl w L + atPl w L' := fun w L L' =>
    (PiTensorProduct.mapMultilinear ℂ V V).map_update_add (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L L'
  simp only [sumPl, e, Finset.sum_add_distrib]

theorem sumPl_act {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat r s →ₗ[ℂ] Module.End ℂ V) (c : ι → ℂ) {Y a b e : ι → Mat r s} (h : ∀ w, Y w = a w + b w + e w) :
    sumPl (V := fun _ => V) (fun w => act (Y w) + (c w * (Y w).trace) • 1) =
      sumPl (V := fun _ => V) (fun w => act (a w) + (c w * (a w).trace) • 1) +
        sumPl (V := fun _ => V) (fun w => act (b w) + (c w * (b w).trace) • 1) +
        sumPl (V := fun _ => V) (fun w => act (e w) + (c w * (e w).trace) • 1) := by
  rw [← sumPl_add₃]
  congr 1
  funext w
  rw [h w, map_add, map_add, Matrix.trace_add, Matrix.trace_add, mul_add, mul_add, add_smul, add_smul]
  abel

theorem line_decomposition : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ γ ∈ Lines σ W, ∃ γu ∈ Lines σ W, ∃ γl ∈ Lines σ W, ∃ γk ∈ Lines σ W, (∀ t, γu t ∈ unip σ W H') ∧
      (∃ (τ : Multiplicative ℝ →* (AE F E)ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
        ∀ t, IsLevi H' (τ t) (γ₁ t) (γl t)) ∧ (∀ t, γk t ∈ KInf σ W B.emb) ∧
      ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ g₁ g₂ g₃ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
        ActsD (evI F) (fun t => om (1, γu (Multiplicative.ofAdd t))) f g₁ →
        ActsD (evI F) (fun t => om (1, γl (Multiplicative.ofAdd t))) f g₂ →
        ActsD (evI F) (fun t => om (1, γk (Multiplicative.ofAdd t))) f g₃ → f₁ = g₁ + g₂ + g₃ := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ hH γ hγ
  classical
  have hb := hpair.base
  have hX := hpair.herm
  have hW := hpair.skew
  have hAL : ActsLaws := actsLaws
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  choose A hA hAθ using fun w => frameEx_holds _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => frameEx_holds _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_piInf]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws hAL hder hvl F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hpair.weil
  obtain ⟨c, hact⟩ := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder hvl F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ
    hwp.1.1
  obtain ⟨Y, hY, hgen⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin d) r' s' B.emb (incM F W.J) Complex.I C hb.cm hC1 γ hγ
  obtain ⟨γu, hu, γl, hl, γk, hk, h1, h2, h3, Yu, Yl, Yk, gu, gl, gk, hsum⟩ := exists_parts hb.cm hW hH hC Y hY
  refine ⟨γu, hu, γl, hl, γk, hk, h1, h2, h3, fun f hf f₁ g₁ g₂ g₃ a0 a1 a2 a3 => ?_⟩
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  have val : ∀ δ ∈ Lines σ W, ∀ Z, IsGen B.emb C δ Z → ∀ g : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) (Φ T) g →
      g = Φ (sumPl (fun w => fockAct2 r s r' s' (Z w) + (c w * (Z w).trace) • 1) T) := fun δ hδ Z hZ g hg =>
    (hAL F (Fin n × Fin d) _ _ _).2.2.1 _ hg
      ((hAL F (Fin n × Fin d) _ _ (Φ T)).1 _ (fun t => map_zero _) (hact δ hδ Z hZ T))
  rw [val γ hγ Y hgen f₁ a0, val γu hu Yu gu g₁ a1, val γl hl Yl gl g₂ a2, val γk hk Yk gk g₃ a3, sumPl_act _ c hsum,
    LinearMap.add_apply, LinearMap.add_apply, Φ.map_add, Φ.map_add]

end GlobalTheory.IndLine.Iwasawa

end
