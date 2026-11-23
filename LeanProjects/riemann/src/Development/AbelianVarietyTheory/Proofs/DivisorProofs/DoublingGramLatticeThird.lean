import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfIsStabSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldIntegralFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledLeftInvariantContinuousStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DoublingNonOpen

open GlobalTheory.Eis in

theorem nonOpen_vanish : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → 1 ≤ d →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χX (((n : ℂ) - (d : ℂ)) / 2),
    (∀ s : ℂ, (d : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g) →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∀ s : ℂ, (d : ℝ) / 2 < s.re → ∀ 𝓕 : Set (UA σ W.J), IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
      ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → GlobalTheory.ThKLiftCusp.IsCuspW W f → ∀ h, ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖GlobalTheory.Eis.term (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, x)) q‖ₑ ∂μ ≠ ⊤ →
      ∫ x in 𝓕, f x * (∑' q : {q : GlobalTheory.Eis.Cosets (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) // ¬ ∃ δ ∈ ratU σ W.J,
        ((q.out : ratU σ W₂.J) : UA σ W₂.J) * (i (1, δ))⁻¹ ∈ (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype)},
        GlobalTheory.Eis.term (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, x)) q.1) * (((χX (Matrix.GeneralLinearGroup.det x.1))⁻¹ : Circle) : ℂ) ∂μ = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ s hs 𝓕 h𝓕
    f hf hfΓ hfd hcusp h hfin
  obtain ⟨hic, hΦc, hwc⟩ := GlobalTheory.DblUnfoldCont.continuity_pair hKP F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i
    hi K hK hIw φ₀ hφ₀ hLI μ hμ
  haveI := hμ
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalRing (Matrix (Fin d) (Fin d) (AE F E)) := Matrix.topologicalRing
  haveI : IsTopologicalRing (Matrix (Fin (d + d)) (Fin (d + d)) (AE F E)) := Matrix.topologicalRing
  haveI : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (GL (Fin (d + d)) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  haveI : IsTopologicalGroup (UA σ W₂.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : Countable (ratU σ W.J) := GlobalTheory.QDom.countable_ratU σ W.J
  have hrat : ∀ δ ∈ ratU σ W.J, i (1, δ) ∈ ratU σ W₂.J := by
    intro δ hδ
    obtain ⟨d₀, hd₀⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hδ)
    refine Subgroup.mem_subgroupOf.2 (MonoidHom.mem_range.2 ⟨blkGL finSumFinEquiv ((1 : GL (Fin d) E), d₀), ?_⟩)
    apply Units.ext
    change ((blkGL finSumFinEquiv ((1 : GL (Fin d) E), d₀) : GL _ E) : Matrix _ _ E).map (inclR (AF F)) =
      mat (i (1, δ))
    rw [val_blkGL, blkMat_map _ _ (map_zero _), hi]
    have h1 : mat δ = (d₀ : Matrix _ _ E).map (inclR (AF F)) := by
      show δ.1.val = _
      rw [← hd₀]; rfl
    rw [h1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have hα1 : ∀ γ ∈ ratU σ W.J, χX (Matrix.GeneralLinearGroup.det γ.1) = 1 := by
    intro γ hγ
    obtain ⟨d₀, hd₀⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hγ)
    rw [← hd₀]
    have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (inclR (AF F)) d₀) =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* AE F E) (Matrix.GeneralLinearGroup.det d₀) := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rw [h1]
    exact hP.hX.2 _
  haveI : Countable (ratU σ W₂.J) := GlobalTheory.QDom.countable_ratU σ W₂.J
  have hLIs := (hLI s hs).1

  have hcls : ∀ x y : ratU σ W₂.J, GlobalTheory.AutomorphicL2Unitary.mk ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype).subgroupOf (ratU σ W₂.J)) x =
      GlobalTheory.AutomorphicL2Unitary.mk _ y ↔ (x : UA σ W₂.J) * (y : UA σ W₂.J)⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype := by
    intro x y
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    constructor
    · rintro ⟨γ, rfl⟩
      have := Subgroup.mem_subgroupOf.1 γ.2
      simpa [mul_inv_rev] using (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype).inv_mem this
    · intro hxy
      refine ⟨⟨y * x⁻¹, Subgroup.mem_subgroupOf.2 ?_⟩, by simp⟩
      simpa using (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype).inv_mem hxy
  have hfix : ∀ (c : GlobalTheory.Eis.Cosets (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J)) (γ : ratU σ W₂.J), GlobalTheory.AutomorphicL2Unitary.rmul _ γ c = c ↔
      ((c.out : ratU σ W₂.J) : UA σ W₂.J) * γ * ((c.out : ratU σ W₂.J) : UA σ W₂.J)⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype := by
    intro c γ
    conv_lhs => rw [← Quotient.out_eq c]
    rw [GlobalTheory.AutomorphicL2Unitary.rmul_mk, hcls]
    simp only [Subgroup.coe_mul]

  have hQst : ∀ (q : {q : GlobalTheory.Eis.Cosets (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) // ¬ ∃ δ ∈ ratU σ W.J,
        ((q.out : ratU σ W₂.J) : UA σ W₂.J) * (i (1, δ))⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype}) (δ : ratU σ W.J),
      ¬ ∃ δ' ∈ ratU σ W.J, (((GlobalTheory.AutomorphicL2Unitary.rmul _ (⟨i (1, δ), hrat δ δ.2⟩ : ratU σ W₂.J) q.1).out : ratU σ W₂.J) :
        UA σ W₂.J) * (i (1, δ'))⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype := by
    rintro q δ ⟨δ', hδ', hmem⟩
    refine q.2 ⟨δ' * (δ : UA σ W.J)⁻¹, mul_mem hδ' (inv_mem δ.2), ?_⟩
    have e1 : GlobalTheory.AutomorphicL2Unitary.mk ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype).subgroupOf (ratU σ W₂.J)) (q.1.out * ⟨i (1, δ), hrat δ δ.2⟩) =
        GlobalTheory.AutomorphicL2Unitary.mk _ (GlobalTheory.AutomorphicL2Unitary.rmul _ (⟨i (1, δ), hrat δ δ.2⟩ : ratU σ W₂.J) q.1).out :=
      (congrArg (GlobalTheory.AutomorphicL2Unitary.rmul _ (⟨i (1, δ), hrat δ δ.2⟩ : ratU σ W₂.J)) (Quotient.out_eq q.1)).trans
        (Quotient.out_eq _).symm
    have e2 := (hcls _ _).1 e1
    simp only [Subgroup.coe_mul] at e2
    have e3 := (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype).mul_mem e2 hmem
    have e4 : i (1, δ' * (δ : UA σ W.J)⁻¹) = i (1, δ') * (i (1, δ))⁻¹ := by
      rw [← map_inv, ← map_mul, Prod.inv_mk, inv_one, Prod.mk_mul_mk, one_mul]
    rw [e4, mul_inv_rev, inv_inv]
    simpa [mul_assoc] using e3
  let act : {q : GlobalTheory.Eis.Cosets (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) // ¬ ∃ δ ∈ ratU σ W.J,
        ((q.out : ratU σ W₂.J) : UA σ W₂.J) * (i (1, δ))⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype} → ratU σ W.J → {q : GlobalTheory.Eis.Cosets (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) // ¬ ∃ δ ∈ ratU σ W.J,
        ((q.out : ratU σ W₂.J) : UA σ W₂.J) * (i (1, δ))⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype} := fun q δ =>
    ⟨GlobalTheory.AutomorphicL2Unitary.rmul _ (⟨i (1, δ), hrat δ δ.2⟩ : ratU σ W₂.J) q.1, hQst q δ⟩
  have hact : ∀ q δ, (act q δ).1 = GlobalTheory.AutomorphicL2Unitary.rmul _ (⟨i (1, δ), hrat δ δ.2⟩ : ratU σ W₂.J) q.1 := fun _ _ => rfl
  have h1 : ∀ q, act q 1 = q := fun q => Subtype.ext (by
    rw [hact]
    convert GlobalTheory.AutomorphicL2Unitary.rmul_one q.1 using 2
    exact Subtype.ext (by simp [← Prod.one_eq_mk]))
  have hm : ∀ q a b, act (act q a) b = act q (a * b) := fun q x y => Subtype.ext (by
    rw [hact, hact, hact, ← GlobalTheory.AutomorphicL2Unitary.rmul_mul]
    congr 1
    exact Subtype.ext (by simp only [Subgroup.coe_mul]; rw [← map_mul, Prod.mk_mul_mk, one_mul]))
  let w : UA σ W.J → ℂ := fun g => (((χX (Matrix.GeneralLinearGroup.det g.1))⁻¹ : Circle) : ℂ)
  have hwmul : ∀ x y, w (x * y) = w x * w y := fun x y => by
    simp only [w, Subgroup.coe_mul, map_mul, mul_inv, Circle.coe_mul]
  have hwΓ : ∀ γ ∈ ratU σ W.J, w γ = 1 := fun γ hγ => by simp only [w, hα1 γ hγ, inv_one, Circle.coe_one]
  have hwdet : ∀ x : UA σ W.J, Matrix.GeneralLinearGroup.det x.1 = 1 → w x = 1 := fun x hx => by
    simp only [w, hx, map_one, inv_one, Circle.coe_one]
  have hw1 : ∀ x, ‖w x‖ₑ = 1 := fun x => by rw [← ofReal_norm_eq_enorm, Circle.norm_coe, ENNReal.ofReal_one]
  let T : {q : GlobalTheory.Eis.Cosets (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) // ¬ ∃ δ ∈ ratU σ W.J,
        ((q.out : ratU σ W₂.J) : UA σ W₂.J) * (i (1, δ))⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype} → UA σ W.J → ℂ := fun q x =>
    GlobalTheory.Eis.term (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, x)) q.1 * w x
  have hT : ∀ q (δ : ratU σ W.J) x, T q ((δ : UA σ W.J) * x) = T (act q δ) x := fun q δ x => by
    have e : i (h, (δ : UA σ W.J) * x) = i (1, δ) * i (h, x) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
    simp only [T]
    rw [e, hwmul, hwΓ _ δ.2, one_mul]
    exact congrArg (· * w x) (GlobalTheory.Eis.term_mul_left hLIs ⟨i (1, δ), hrat δ δ.2⟩ (i (h, x)) q.1)
  have hTc : ∀ q, Continuous (T q) := fun q =>
    ((hΦc s).comp (continuous_const.mul (hic.comp (continuous_const.prodMk continuous_id)))).mul hwc
  have hPinv : ∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype, aOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype p = 1 →
      ∀ g, (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (p * g) = (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g := by
    intro p hp1 g
    have hl := (mem_degPSOf.1 hφ₀).1 p g
    have hh : hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K (p * g) =
        hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K g := by
      show iwAbs _ K (↑p * g) = iwAbs _ K g
      rw [IsIwasawa.iwAbs_left hIw p g]
      simp [absAOf, hp1]
    rw [flatOf_apply, flatOf_apply, hh, hl, hp1]
    simp
  have hfin' : ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖T q x‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul_right ?_ _)
    simp only [T, enorm_mul, hw1, mul_one]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun q => ‖GlobalTheory.Eis.term (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, x)) q‖ₑ)
  have hvan : ∀ q (S : Subgroup (UA σ W.J)), (∀ g, g ∈ S ↔ ∃ hg : g ∈ ratU σ W.J, act q ⟨g, hg⟩ = q) →
      ∀ D : Set (UA σ W.J), IsFundamentalDomain S D μ →
      IntegrableOn (fun x => f x * T q x) D μ → ∫ x in D, f x * T q x ∂μ = 0 := by
    intro q S hS D hD hint
    have hS' : ∀ g, g ∈ S ↔ g ∈ ratU σ W.J ∧ ((q.1.out : ratU σ W₂.J) : UA σ W₂.J) * i (1, g) *
        ((q.1.out : ratU σ W₂.J) : UA σ W₂.J)⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype := fun g => by
      rw [hS]
      exact ⟨fun ⟨hg, e⟩ => ⟨hg, (hfix q.1 ⟨i (1, g), hrat g hg⟩).1 (congrArg Subtype.val e)⟩,
        fun ⟨hg, e⟩ => ⟨hg, Subtype.ext ((hfix q.1 ⟨i (1, g), hrat g hg⟩).2 e)⟩⟩
    exact GlobalTheory.T.doubled_left_invariant_continuous F E σ B d _ _ W hP.skew hP.base.cm W₂ hJ i hi _ (hΦc s) hLIs hPinv w hwc hwmul hwΓ hwdet μ hμ
      f hf hfΓ hcusp _ (q.1.out : ratU σ W₂.J).2 q.2 S hS' h D hD hint
  have key := GlobalTheory.T.unfold_integral_fundamental_domain (ratU σ W.J) μ 𝓕 _ act T f h𝓕 h1 hm hT (fun q => (hTc q).aestronglyMeasurable) hfΓ
    hf.aestronglyMeasurable hfin' hvan
  refine Eq.trans ?_ key
  congr 1
  funext x
  simp only [T]
  rw [tsum_mul_right, mul_assoc]

end GlobalTheory.DoublingNonOpen

end
