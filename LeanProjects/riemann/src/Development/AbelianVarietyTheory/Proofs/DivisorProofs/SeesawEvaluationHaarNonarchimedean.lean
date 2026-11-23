import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHaarStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviTorusEvaluation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionMaximalCompactTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallRatInv

private theorem I_rat_schA (hKP : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a b : ℕ} {G₁ : Geo σ a b} {X : Chars F E} {om₁ : Rep σ G₁.V G₁.W}
    {om₁' : Rep σ G₁.V' G₁.W} (hT₁ : IsTriple B G₁ X om₁ om₁') (Ψ : Fn F b (a + b)) (hΨ : Ψ ∈ schA F _)
    (γ : UA σ G₁.W.J) (hγ : γ ∈ ratU σ G₁.W.J) (h : UA σ G₁.W.J) :
    G₁.M'.I om₁' Ψ (γ * h) = G₁.M'.I om₁' Ψ h := by
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hKP.base
  have hV' : IsPair B G₁.M' X.α (X.α / X.β) om₁' G₁.q (b - G₁.q) (a + b - (G₁.p + G₁.q)) (G₁.p + G₁.q) :=
    { base := hT₁.base, herm := hT₁.geo.hV', skew := hT₁.geo.hW, good := hT₁.geo.hM', hX := hT₁.chars.heckeα,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT₁.chars.heckeα hT₁.chars.heckeβ, resX := hT₁.chars.resα,
      resW := by rw [add_comm a b]; exact GlobalTheory.ThKRatInv.resEtaPow_div hT₁.chars.resα hT₁.chars.resβ, weil := hT₁.weil' }
  have hinv := ((hTB F E σ B _ _ _ _ G₁.M' _ _ om₁' _ _ _ _ hV').1 Ψ hΨ).2.1
  unfold Model.I
  congr 1
  funext g
  simpa using hinv 1 (one_mem _) γ hγ g h

end GlobalTheory.ConeSmallRatInv

namespace GlobalTheory.ConeSmallRatInv

private theorem unip_fix {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {u : UA σ W.J} (hu : u ∈ unip σ W H') :
    mat u *ᵥ incV F H'.x = incV F H'.x := by
  induction hu using Subgroup.closure_induction with
  | mem g hg => exact hg.1
  | one => exact Matrix.one_mulVec _
  | mul g g' _ _ h1 h2 => rw [show mat (g * g') = mat g * mat g' from rfl, ← Matrix.mulVec_mulVec, h2, h1]
  | inv g _ h1 =>
    conv_lhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, show mat g⁻¹ * mat g = 1 from Units.inv_mul g.1, Matrix.one_mulVec]

private theorem coneI_levi_rat (hKP : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b}
    {H : Plane E (b + 2) b} {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H')
    {e'} (he : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') (K : Subgroup (UA σ G.V'.J)) (μK : Measure K)
    (μ : Measure (AE F E)ˣ) {X om om' om₁ om₁'} (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    (Φ' : Fn F (b + 2) (a + (b + 2))) (hΦ' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) (z : ℂ)
    (h₁ : UA σ G₁.W.J) (hh₁ : h₁ ∈ ratU σ G₁.W.J) (m₀ : UA σ G.W.J) (hL : IsLevi H' 1 h₁ m₀)
    (u : UA σ G.W.J) (hu : u ∈ unip σ G.W H') (h : UA σ G.W.J) :
    GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z (u * m₀ * h) =
      GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z h := by
  have hΦs : Φ' ∈ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΦ').2
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hlaw : ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e' (om' (1, u * m₀) Ψ) = om₁' (1, h₁) (e' Ψ) := by
    intro Ψ hΨ
    have k := GlobalTheory.ThK.evLaw_isoB hKP.base F E σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁ 1 h₁ m₀ hL u hu Ψ hΨ
    simp only [mul_one, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at k
    exact k
  have hx : mat (u * m₀) *ᵥ incV F H'.x = incV F H'.x := by
    rw [show mat (u * m₀) = mat u * mat m₀ from rfl, ← Matrix.mulVec_mulVec, hL.1, Units.val_one, one_smul, unip_fix hu]
  generalize u * m₀ = m at hlaw hx
  unfold GlobalTheory.ConeSmall.coneI
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only
  congr 2
  have hΨ : om' (k.1, h) Φ' ∈ schA F _ := hW.pres _ _ hΦs
  have e1 : om' (k.1, m * h) Φ' = om' (1, m) (om' (k.1, h) Φ') := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hact : actAB (cA σ) ((1, m) : UA σ G.V'.J × UA σ G.W.J) (shiftB σ H H' l) = shiftB σ H H' l := by
    ext i j
    simp only [actAB, shiftB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_apply]
    congr 1
    conv_rhs => rw [← hx]
    simp [mat, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (1, m) (om' (k.1, h) Φ')) =
      om' (1, m) (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) := by
    rw [hW.impl (1, m) (shiftB σ H H' l) _ hΨ, hact]
  have hρ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' l) _ hΨ
  rw [e1, e2, hlaw _ hρ]
  have habs : ∀ Y, G₁.M'.I om₁' (om₁' (1, h₁) Y) 1 = G₁.M'.I om₁' Y h₁ := by
    intro Y
    simp only [Model.I, theta]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  rw [habs, show h₁ = h₁ * 1 by rw [mul_one], I_rat_schA hKP hT₁ _ (he.maps _ hρ) h₁ hh₁ 1]

private theorem rat_scalar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ : Chr F E}
    (hχ : IsHecke F E χ) (c : Eˣ) (z : ℂ) :
    (χ (Units.map (inclR (F := F) (AF F)).toMonoidHom c) : ℂ) *
      ((absE F E (Units.map (inclR (F := F) (AF F)).toMonoidHom c) : ℝ) : ℂ) ^ z = 1 := by
  rw [hχ.2 c, GlobalTheory.Doubling.absE_inclR]
  simp

end GlobalTheory.ConeSmallRatInv

namespace GlobalTheory.ConeSmallRatInv

private theorem mul_inv_mem_unip {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {t : (AE F E)ˣ} {h₁ : UA σ W₁.J} {m p : UA σ W.J} (hl : IsLevi H' t h₁ m)
    (hpx : mat p *ᵥ incV F H'.x = t.1 • incV F H'.x)
    (hpι : ∀ z, ∃ a : AE F E, mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x) :
    p * m⁻¹ ∈ unip σ W H' := by
  have hmi : mat m⁻¹ * mat m = 1 := Units.inv_mul m.1
  have hhi : mat h₁ * mat h₁⁻¹ = 1 := Units.mul_inv h₁.1
  have hmul : mat (p * m⁻¹) = mat p * mat m⁻¹ := rfl
  have hx : mat m⁻¹ *ᵥ incV F H'.x = (t⁻¹).1 • incV F H'.x := by
    calc mat m⁻¹ *ᵥ incV F H'.x = mat m⁻¹ *ᵥ ((t⁻¹).1 • (t.1 • incV F H'.x)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = (t⁻¹).1 • incV F H'.x := by
          rw [← hl.1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hι : mat m⁻¹ * incM F H'.ι = incM F H'.ι * mat h₁⁻¹ := by
    calc mat m⁻¹ * incM F H'.ι = mat m⁻¹ * (incM F H'.ι * (mat h₁ * mat h₁⁻¹)) := by rw [hhi, Matrix.mul_one]
      _ = (mat m⁻¹ * mat m) * incM F H'.ι * mat h₁⁻¹ := by
          rw [← Matrix.mul_assoc (incM F H'.ι), ← hl.2.2]; simp only [Matrix.mul_assoc]
      _ = incM F H'.ι * mat h₁⁻¹ := by rw [hmi, Matrix.one_mul]
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · rw [hmul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul, hpx, smul_smul, Units.inv_mul, one_smul]
  · obtain ⟨a, ha⟩ := hpι (mat h₁⁻¹ *ᵥ z)
    refine ⟨a, ?_⟩
    rw [hmul, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat m⁻¹) (incM F H'.ι), hι, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_mulVec z (mat h₁), hhi, Matrix.one_mulVec]

private lemma cA_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (a : AE F E) : cA σ (cA σ a) = a := by
  have hs : σ.comp σ = AlgHom.id F E := AlgHom.ext hσ
  have h : (cA σ).comp (cA σ) = AlgHom.id (AF F) (AE F E) := by
    simp only [cA, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, hs, Algebra.TensorProduct.map_id]
  exact DFunLike.congr_fun h a

private theorem nontrivial_AE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Nontrivial (AE F E) := by
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  infer_instance

open GlobalTheory.PlaneLeviExt in

private theorem levi_data {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ r s r₁ s₁ : ℕ}
    (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (p : UA σ W.J) (hp : p ∈ ratU σ W.J) (t : (AE F E)ˣ) (ht : mat p *ᵥ incV F H'.x = t.1 • incV F H'.x) :
      (∃ c : Eˣ, t = Units.map (inclR (F := F) (AF F)).toMonoidHom c) ∧
      ∃ h₁ ∈ ratU σ W₁.J, ∀ z : Fin d₁ → AE F E, ∃ a : AE F E,
        mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x := by
  have hσ : ∀ z, σ (σ z) = z := GlobalTheory.PlaneLevi.invol_of_good hB
  have hu := isUnit_sq σ hσ B hW hW₁ hA
  set S := incM F (frame H') with hSdef
  set T := incM F (coframe hA.rank H') with hTdef
  have hST : S * T = 1 := S_T hu
  have hTS : T * S = 1 := T_S hu
  set P := mat p with hPdef
  set q := T * P * S with hqdef
  set G := incM F (Matrix.fromBlocks W₁.J 0 0 hyp) with hGdef
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := fun X Y => Matrix.map_mul (f := (cA σ).toRingHom)
  have hP : Pᵀ * incM F W.J * P.map (cA σ) = incM F W.J := p.2
  clear_value S T P q G
  have hG : Sᵀ * incM F W.J * S.map (cA σ) = G := by
    rw [hSdef, hGdef, ← gram_frame σ hσ B hW hA, incM_mul, incM_mul, incM_transpose, cA_incM]
  have hSq : S * q = P * S := by
    rw [hqdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hST, Matrix.one_mul]
  have hq : qᵀ * G * q.map (cA σ) = G := by
    rw [← hG]
    calc qᵀ * (Sᵀ * incM F W.J * S.map (cA σ)) * q.map (cA σ)
        = (S * q)ᵀ * incM F W.J * (S * q).map (cA σ) := by
          rw [Matrix.transpose_mul, hmap]; simp only [Matrix.mul_assoc]
      _ = Sᵀ * (Pᵀ * incM F W.J * P.map (cA σ)) * S.map (cA σ) := by
          rw [hSq, Matrix.transpose_mul, hmap]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]
  have hSe : S *ᵥ Pi.single (Sum.inr 0) 1 = incV F H'.x := by
    rw [Matrix.mulVec_single_one]
    ext i; simp [hSdef, incM, frame, twoCols, incV]
  have hqe : q *ᵥ Pi.single (Sum.inr 0) 1 = t.1 • Pi.single (Sum.inr 0) 1 := by
    rw [hqdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSe, ht, Matrix.mulVec_smul, ← hSe,
      Matrix.mulVec_mulVec, hTS, Matrix.one_mulVec]
  have hcol : ∀ k, q k (Sum.inr 0) = if k = Sum.inr 0 then t.1 else 0 := by
    intro k
    have := congrFun hqe k
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply] using this

  have hC1 : ∀ j, q (Sum.inr 1) (Sum.inl j) = 0 := by
    intro j
    have h := congrFun (congrFun hq (Sum.inr 0)) (Sum.inl j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hcol, Fintype.sum_sum_type,
      Fin.sum_univ_two, hGdef, incM, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, hyp] at h
    simp at h
    rw [← cA_cA σ hσ (q _ _), h, map_zero]
  set A : Matrix (Fin d₁) (Fin d₁) (AE F E) := Matrix.of fun i j => q (Sum.inl i) (Sum.inl j) with hAdef
  have hA1 : Aᵀ * incM F W₁.J * A.map (cA σ) = incM F W₁.J := by
    ext i j
    have h := congrFun (congrFun hq (Sum.inl i)) (Sum.inl j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, hGdef, incM, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, hyp, hC1] at h
    simp at h
    rw [hAdef]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, incM] using h
  have hdetJ : IsUnit (incM F W₁.J).det := by
    have := RingHom.map_det (inclR (F := F) (AF F)) W₁.J
    rw [incM]
    exact (this ▸ (GlobalTheory.LeviAdapted.det_ne_zero hW₁).isUnit.map (inclR (F := F) (AF F)) :)
  have hdetA : IsUnit A.det := by
    have h := congrArg Matrix.det hA1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
    have h2 : (A.map (cA σ)).det = cA σ A.det := (AlgHom.map_det (cA σ) A).symm
    rw [h2] at h
    have h3 : A.det * cA σ A.det = 1 := by
      refine hdetJ.mul_left_cancel ?_
      linear_combination h
    exact isUnit_iff_exists.mpr ⟨_, h3, by rw [mul_comm]; exact h3⟩
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdetA
  let h₁ : UA σ W₁.J := ⟨hAu.unit, by show (hAu.unit.1)ᵀ * incM F W₁.J * (hAu.unit.1).map (cA σ) = incM F W₁.J; exact hA1⟩
  have hmat : mat h₁ = A := IsUnit.unit_spec hAu
  obtain ⟨p₀, hp₀⟩ := hp
  have hP₀ : P = incM F p₀.1 := by
    rw [hPdef]
    exact (congrArg Units.val hp₀).symm
  have hq₀ : q = incM F (coframe hA.rank H' * p₀.1 * frame H') := by
    rw [hqdef, incM_mul, incM_mul, hP₀, hSdef, hTdef]
  set q₀ := coframe hA.rank H' * p₀.1 * frame H' with hq₀def
  clear_value q₀
  haveI : Nontrivial (AE F E) := nontrivial_AE
  have htc : t.1 = inclR (F := F) (AF F) (q₀ (Sum.inr 0) (Sum.inr 0)) := by
    have := hcol (Sum.inr 0)
    rw [if_pos rfl, hq₀] at this
    exact this.symm
  have hc0 : q₀ (Sum.inr 0) (Sum.inr 0) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at htc
    exact t.ne_zero htc
  let A₀ : Matrix (Fin d₁) (Fin d₁) E := Matrix.of fun i j => q₀ (Sum.inl i) (Sum.inl j)
  have hA₀ : A = incM F A₀ := by
    rw [hAdef, hq₀]; rfl
  have hdet₀ : A₀.det ≠ 0 := by
    intro h0
    have := RingHom.map_det (inclR (F := F) (AF F)) A₀
    rw [h0, map_zero] at this
    apply hdetA.ne_zero
    rw [hA₀]
    exact this.symm
  refine ⟨⟨Units.mk0 _ hc0, Units.ext htc⟩, h₁, ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A₀ hdet₀, ?_⟩, fun z => ?_⟩
  · apply Units.ext
    exact hA₀.symm.trans hmat.symm
  · set w : Fin d₁ ⊕ Fin 2 → AE F E := Sum.elim z 0 with hwdef
    have hιS : incM F H'.ι *ᵥ z = S *ᵥ w := by
      rw [hSdef, incM_frame, Matrix.fromCols_mulVec, hwdef, Sum.elim_comp_inl, Sum.elim_comp_inr]
      simp
    set w' := q *ᵥ w with hw'def
    have hw1 : w' (Sum.inr 1) = 0 := by
      simp [hw'def, hwdef, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hC1]
    have hwl : w' ∘ Sum.inl = A *ᵥ z := by
      ext i; simp [hw'def, hwdef, hAdef, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have hwr : incM F (twoCols H') *ᵥ (w' ∘ Sum.inr) = w' (Sum.inr 0) • incV F H'.x := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Function.comp_apply, hw1, mul_zero, add_zero]
      simp [incM, twoCols, incV, mul_comm]
    refine ⟨w' (Sum.inr 0), ?_⟩
    rw [hmat, hιS, Matrix.mulVec_mulVec, ← hSq, ← Matrix.mulVec_mulVec, ← hw'def, hSdef, incM_frame,
      Matrix.fromCols_mulVec, hwl, hwr]

end GlobalTheory.ConeSmallRatInv

open GlobalTheory.ConeSmallRatInv in
theorem _root_.GlobalTheory.T.seesaw_evaluation_haar_nonarchimedean : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (z : ℂ) (p : UA σ G.W.J), p ∈ ratU σ G.W.J → GlobalTheory.ConeSmallSer.StabLn H'.x p → ∀ h : UA σ G.W.J,
      GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z (p * h) = GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z h := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' z p hp hst h
  obtain ⟨t, ht⟩ := hst
  obtain ⟨⟨c, rfl⟩, h₁, hh₁, hpι⟩ := levi_data hT.base hT.geo.hW hT₁.geo.hW hC.hH' p hp t ht
  have hσ := GlobalTheory.PlaneLevi.invol_of_good hT.base
  obtain ⟨mt, hmt, -⟩ := GlobalTheory.CtLeviLevel.exists_levi_mat σ B hσ G.W hT.geo.hW G₁.W H' hC.hH' (Units.map (inclR (F := F) (AF F)).toMonoidHom c)
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.LeviUnitary.exists_isLevi hT.base hT.geo.hW hT₁.geo.hW hC.hH' h₁
  have hm : IsLevi H' (Units.map (inclR (F := F) (AF F)).toMonoidHom c) h₁ (mt * m₁) := by
    have hmul : ∀ g g' : UA σ G.W.J, mat (g * g') = mat g * mat g' := fun _ _ => rfl
    have h1 : mat (1 : UA σ G₁.W.J) = 1 := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hmul, ← Matrix.mulVec_mulVec, hm₁.1, Units.val_one, one_smul, hmt.1]
    · rw [hmul, ← Matrix.mulVec_mulVec, hm₁.2.1, inv_one, Units.val_one, map_one, one_smul, hmt.2.1]
    · rw [hmul, Matrix.mul_assoc, hm₁.2.2, ← Matrix.mul_assoc, hmt.2.2, h1, Matrix.mul_one]
  have hu := mul_inv_mem_unip hm ht hpι
  have hL1 : IsLevi (W₁ := G₁.W) H' 1 (1 : UA σ G₁.W.J) (1 : UA σ G.W.J) := by
    have h1 : mat (1 : UA σ G₁.W.J) = 1 := rfl
    have h2 : mat (1 : UA σ G.W.J) = 1 := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [h2, Matrix.one_mulVec, Units.val_one, one_smul]
    · rw [h2, Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul]
    · rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  have hlaw := GlobalTheory.T.eisenstein_haar_stabilizer_integral hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' z
  calc GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z (p * h)
      = GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z ((p * (mt * m₁)⁻¹) * 1 * (mt * (1 * m₁ * h))) := by
        congr 1; group
    _ = GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z (mt * (1 * m₁ * h)) :=
        coneI_levi_rat hKP hC he K μK μ hT hT₁ Φ' hΦ' z 1 (one_mem _) 1 hL1 _ hu _
    _ = GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z (1 * m₁ * h) := by
        rw [hlaw _ mt hmt, rat_scalar hT.chars.heckeβ c, one_mul]
    _ = GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z h :=
        coneI_levi_rat hKP hC he K μK μ hT hT₁ Φ' hΦ' z h₁ hh₁ m₁ hm₁ 1 (one_mem _) h
