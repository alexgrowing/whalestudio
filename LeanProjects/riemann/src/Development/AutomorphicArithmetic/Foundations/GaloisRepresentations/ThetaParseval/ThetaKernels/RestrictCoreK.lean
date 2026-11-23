import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetRestrictsToPair
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilPairGlobalCharacter
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaInnerProductFormula
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFHeisOFK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsSplitFunctionalDoubled
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaDoublingInnerProduct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnitaryCharacterTrivialOfLocal

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblTargetRestrictCore
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF in
theorem restrict_core_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h hd hhd f₁ f₂ hf₁ hf₂
  obtain ⟨ι, hιc, hιm, hιq, hιs, hιd⟩ := GlobalTheory.T.exists_continuous_unitaryDiagonalEmbedding_doubled F E σ nT JT
  have ext : ∀ a b : GAF σ (dblG JT), mtF σ (dblG JT) a = mtF σ (dblG JT) b → a = b := fun a b hab =>
    (HR (AF F) σ (dblG JT)).subtype_injective (Units.ext hab)
  have hdι : hd = ι h := ext _ _ (by rw [hhd, hιm])
  subst hdι
  have hsc := fun h' => _root_.GlobalTheory.T.weil_pair_global_character F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h' (ι h') (hιm h')
  choose c hc1 hc using hsc
  have hth := _root_.GlobalTheory.T.theta_inner_product_formula F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  by_cases h0 : ∃ f₀, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0
  swap
  · push_neg at h0
    rw [h0 f₁ hf₁]
    have hz : ∀ g : WOF F E nS nT → ℂ, deltaT (0 : WOF F E nS nT → ℂ) g = 0 := fun g => by
      funext x; simp [deltaT]
    simp only [map_zero, hz]
  obtain ⟨f₀, hf₀, hf₀0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hf₀0
  set fs := heisOF σ JS JT ξ₀ B.ψ y f₀ with hfs
  have hfsθ : IsThetaFunOF σ JS JT ξ₀ B.ψ fs := _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ y f₀ hf₀
  have hfs0 : fs 0 ≠ 0 := by
    have : symplOHF σ JS JT ξ₀ 0 y = 0 := by simp [symplOHF, symplOF, hOF]
    simp only [hfs, heisOF, this, AddChar.map_zero_eq_one, one_mul, zero_add]
    exact hy
  have top0 : topR (0 : WOF F E nS (nT + nT)) = 0 := by ext i j; rfl
  have bot0 : botR (0 : WOF F E nS (nT + nT)) = 0 := by ext i j; rfl
  have dl0 : ∀ a b : WOF F E nS nT → ℂ, deltaT a b 0 = a 0 * conj (b 0) := fun a b => by
    rw [deltaT_apply, top0, bot0, neg_zero]
  have hfsn : fs 0 * conj (fs 0) ≠ 0 := mul_ne_zero hfs0 ((map_ne_zero _).2 hfs0)
  have omi : ∀ h' : GAF σ JT, ω (1, h') (ω (1, h')⁻¹ fs) = fs := fun h' => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have pres := hω.om_pres
  have key : ∀ h' (a : ℂ), ωd (1, ι h') (deltaT (ω (1, h')⁻¹ fs) fs) 0 = a * (fs 0 * conj (fs 0)) → c h' = a := by
    intro h' a ha
    have e := congrFun (hc h' (ω (1, h')⁻¹ fs) fs (pres _ _ hfsθ) hfsθ) 0
    rw [Pi.smul_apply, smul_eq_mul, omi, dl0, ha] at e
    exact (mul_right_cancel₀ hfsn e).symm
  have hone : c 1 = 1 := by
    refine key 1 1 ?_
    have p1 : ((1 : GAF σ JS), (1 : GAF σ JT)) = 1 := rfl
    have p2 : ((1 : GAF σ JS), (1 : GAF σ (dblG JT))) = 1 := rfl
    rw [map_one, p1, p2, inv_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply, dl0, one_mul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    refine key (a * b) _ ?_
    have e1 : ((1 : GAF σ JS), ι (a * b)) = (1, ι a) * (1, ι b) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    set g := ω ((1 : GAF σ JS), a * b)⁻¹ fs with hg
    have hgθ : IsThetaFunOF σ JS JT ξ₀ B.ψ g := pres _ _ hfsθ
    have comb : ω (1, a) (ω (1, b) g) = fs := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, hg, omi]
    rw [e1, map_mul, Module.End.mul_apply, hc b g fs hgθ hfsθ, map_smul,
      hc a (ω (1, b) g) fs (pres _ _ hgθ) hfsθ, comb]
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, dl0]
    ring
  let cc : GAF σ JT →* Circle :=
    { toFun := fun h' => ⟨c h', mem_sphere_zero_iff_norm.2 (hc1 h')⟩
      map_one' := Circle.ext hone
      map_mul' := fun a b => Circle.ext (hmul a b) }
  have hcc : ∀ h', (cc h' : ℂ) = c h' := fun _ => rfl
  have hcont : Continuous cc := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun h₀ => ?_)
    set g₁ := ω (1, h₀)⁻¹ fs
    have hg₁ : IsThetaFunOF σ JS JT ξ₀ B.ψ g₁ := pres _ _ hfsθ
    have hN : Continuous fun h' : GAF σ JT => ωd (1, ι h') (deltaT g₁ fs) 0 :=
      (hωd.om_cont _ (hth _ _ hg₁ hfsθ) 0).comp (continuous_const.prodMk hιc)
    have hD : Continuous fun h' : GAF σ JT => ω (1, h') g₁ 0 * conj (fs 0) :=
      ((hω.om_cont _ hg₁ 0).comp (continuous_const.prodMk continuous_id)).mul continuous_const
    have hD0 : ω (1, h₀) g₁ 0 * conj (fs 0) ≠ 0 := by rw [omi]; exact hfsn
    have hev : ∀ᶠ h' in nhds h₀, ω (1, h') g₁ 0 * conj (fs 0) ≠ 0 := hD.continuousAt.eventually_ne hD0
    refine ((hN.continuousAt).div hD.continuousAt hD0).congr (hev.mono fun h' hh' => ?_)
    show ωd (1, ι h') (deltaT g₁ fs) 0 / (ω (1, h') g₁ 0 * conj (fs 0)) = c h'
    rw [hc h' g₁ fs hg₁ hfsθ, Pi.smul_apply, smul_eq_mul, dl0, mul_div_assoc, div_self hh', mul_one]
  have hrat : ∀ γ ∈ GQF σ JT, cc γ = 1 := by
    intro γ hγ
    apply Circle.ext
    rw [hcc, Circle.coe_one]
    have e1 := hωd.om_aut 1 (Subgroup.one_mem _) (ι γ) (hιq γ hγ) _ (hth _ _ hfsθ hfsθ)
    have e2 := hω.om_aut 1 (Subgroup.one_mem _) γ hγ fs hfsθ
    rw [hc γ fs fs hfsθ hfsθ, Pi.smul_apply, smul_eq_mul, dl0, dl0, e2] at e1
    have := mul_right_cancel₀ hfsn (e1.trans (one_mul _).symm)
    exact this
  have hsplit : ∀ e, IsSplitIdemF σ e → ∀ g, SuppAtF σ e JT g → cc g = 1 := by
    intro e he g hg
    have hee : e * e = e := he.1
    obtain ⟨y, hy⟩ : ∃ y : (AEF F E)ˣ, IsDetAtF σ e JT g y := by
      have hd1 : (mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) = 1 :=
        (Matrix.GeneralLinearGroup.det (matHomF σ JT g)).mul_inv
      have hd2 : ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) * (mtF σ JT g).det = 1 :=
        (Matrix.GeneralLinearGroup.det (matHomF σ JT g)).inv_mul
      refine ⟨⟨e * (mtF σ JT g).det + (1 - e),
        e * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + (1 - e), ?_, ?_⟩, rfl⟩
      · linear_combination ((mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ)
          - (mtF σ JT g).det - ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + 1) * hee + e * hd1
      · linear_combination ((mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ)
          - (mtF σ JT g).det - ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + 1) * hee + e * hd2
    have m1 : mtF σ JS (1 : GAF σ JS) = 1 := by unfold mtF; rw [map_one]; rfl
    have hx1 : IsDetAtF σ e JS 1 1 := by
      show ((1 : (AEF F E)ˣ) : AEF F E) = e * (mtF σ JS 1).det + (1 - e)
      rw [m1, Matrix.det_one, Units.val_one]; ring
    have hS1 : SuppAtF σ e JS 1 := fun i j => by rw [m1, sub_self]; simp
    obtain ⟨rd, hrd, hrd'⟩ := hωd.om_split e he 1 (ι g) hS1 (hιs e g hg) 1 y hx1 (hιd e g y hy)
    obtain ⟨r, hr, hr'⟩ := hω.om_split e he 1 g hS1 hg 1 y hx1 hy
    obtain ⟨ℓ, hℓ, a, b, ha, hb, hℓab⟩ := _root_.GlobalTheory.T.exists_split_functional_doubled F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
    have hheis := _root_.GlobalTheory.T.theta_doubling_inner_product F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
    have dadd : ∀ f f' : WOF F E nS nT → ℂ, deltaT (f + f') b = deltaT f b + deltaT f' b := fun f f' => by
      funext x; simp only [deltaT_apply, Pi.add_apply, add_mul]
    have dsmul : ∀ (s : ℂ) (f : WOF F E nS nT → ℂ), deltaT (s • f) b = s • deltaT f b := fun s f => by
      funext x; simp only [deltaT_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    let ℓ₁ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => ℓ (deltaT f b)
        map_add' := fun f f' => by simp only [dadd, map_add]
        map_smul' := fun s f => by simp only [dsmul, map_smul, RingHom.id_apply] }
    have hℓ₁ : ∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ℓ₁ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ₁ f := by
      intro u hu f hf
      let ũ : WOF F E nS (nT + nT) := (Matrix.fromRows u 0).submatrix finSumFinEquiv.symm id
      have ht : topR ũ = u := by
        ext i j
        simp only [ũ, topR, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
          Matrix.fromRows_apply_inl, id]
      have hb0 : botR ũ = 0 := by
        ext i j
        simp only [ũ, botR, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
          Matrix.fromRows_apply_inr, Matrix.zero_apply, id]
      have hu' : ∀ i j, cAF σ e * ũ i j = ũ i j := by
        intro i j
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
        rcases i with i | i <;>
          simp only [ũ, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
            Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero, id, hu]
      have h0b : heisOF σ JS JT ξ₀ B.ψ 0 b = b := by
        funext x; simp [heisOF, symplOHF, symplOF, hOF]
      show ℓ (deltaT (heisOF σ JS JT ξ₀ B.ψ u f) b) = ℓ (deltaT f b)
      have e3 := hheis ũ f b
      rw [ht, hb0, neg_zero, h0b] at e3
      rw [← e3, hℓ ũ hu' _ (hth f b hf hb)]
    have E1 := hrd' ℓ hℓ _ (hth a b ha hb)
    rw [hc g a b ha hb, map_smul, smul_eq_mul] at E1
    have E2 : ℓ (deltaT (ω (1, g) a) b) = (r : ℂ) * (splitFacOF χS χT 1 y : ℂ) * ℓ (deltaT a b) := hr' ℓ₁ hℓ₁ a ha
    have s1 : (splitFacOF χS χT 1 y : ℂ) = χS y := by simp [splitFacOF]
    have s2 : (splitFacOF χS 1 1 y : ℂ) = χS y := by simp [splitFacOF]
    rw [E2, s1] at E1
    rw [s2] at E1
    have hs : (χS y : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hcr : c g * r = rd :=
      mul_right_cancel₀ (mul_ne_zero hs hℓab) (by linear_combination E1)
    have hcg : c g = ((rd / r : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hr.ne'), hcr]
    have hn := hc1 g
    rw [hcg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hrd hr)] at hn
    apply Circle.ext
    rw [hcc, Circle.coe_one, hcg, hn, Complex.ofReal_one]
  have hall := _root_.GlobalTheory.T.unitary_character_trivial_of_local F E σ B hB nT JT hT cc hcont hrat hsplit h
  rw [hc h f₁ f₂ hf₁ hf₂, ← hcc, hall, Circle.coe_one, one_smul]
end GlobalTheory.DblTargetRestrictCore
end
end
