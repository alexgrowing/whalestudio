import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GoodProjEval

open GlobalTheory.Mem.SRe Formalism.L2.SG.Pf.unitaryCongruence

theorem multR_left_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (v₀ : (MP R).Vec) (S : MMap (MP R)) (hS : S ∈ MultR R F) :
    ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g := by
  intro γ hγ g
  induction hS using Submodule.span_induction with
  | mem x hx => exact (hx.aut v₀).left γ hγ g
  | zero => rfl
  | add x y _ _ hx hy =>
    show x v₀ (γ * g) + y v₀ (γ * g) = x v₀ g + y v₀ g
    rw [hx, hy]
  | smul c x _ hx =>
    show c • x v₀ (γ * g) = c • x v₀ g
    rw [hx]

theorem goodOp_star_ev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), RowLevelMatchAt R F X h t → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → (star (Gd.Rg (star φ)) : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (postOn (MP R) R.e0 S) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ Gd t v₀ hM S hS φ hφ
  obtain ⟨σ, red, -, hB, hC⟩ := hM
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G σ.symm.toEquiv
  obtain ⟨hgood, hmul, hsurj, hker⟩ := hB.1
  choose s hsK hsred using hsurj
  have hinv := multR_left_inv R F v₀ S hS
  have hEv := evalAct_intertwines D G Pl0 T A Ks R F X h t v₀ σ red hB S hS φ hφ hinv

  have hF1 : ∀ k ∈ X.B.I.Kset, X.B.R (1, k) (star φ) = X.B.R (1, s (red k)) (star φ) := by
    intro k hk
    classical
    let a : G0g D.nd → ℂ := fun γ => if γ = red k then 1 else 0
    let s' : G0g D.nd → X.B.I.Gf := Function.update s (red k) k
    have hs' : ∀ γ, s' γ ∈ X.B.I.Kset ∧ red (s' γ) = γ := by
      intro γ
      by_cases hγ : γ = red k
      · subst hγ
        simp only [s', Function.update_self]
        exact ⟨hk, trivial⟩
      · simp only [s', Function.update_of_ne hγ]
        exact ⟨hsK γ, hsred γ⟩
    have e1 := hEv a s' hs'
    have e2 := hEv a s (fun γ => ⟨hsK γ, hsred γ⟩)
    have hsum : ∀ u : G0g D.nd → X.B.I.Gf,
        (∑ γ, star (a γ) • star (X.B.R (1, u γ) (star φ)) : L2X X) = star (X.B.R (1, u (red k)) (star φ)) := by
      intro u
      rw [Finset.sum_eq_single (red k)]
      · simp [a]
      · intro γ _ hγ
        simp [a, hγ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    rw [hsum] at e1 e2
    have e3 : star (X.B.R (1, k) (star φ)) = (star (X.B.R (1, s (red k)) (star φ)) : L2X X) := by
      apply Lp.ext
      have : s' (red k) = k := by simp [s']
      rw [this] at e1
      exact e1.trans e2.symm
    exact star_injective e3

  have hKgK : X.B.I.Kg X.B.g ⊆ X.B.I.Kset := fun x hx => hx.1
  have hKgO : IsOpen (X.B.I.Kg X.B.g) :=
    X.B.I.topf_open X.B.g (Nat.one_le_iff_ne_zero.2 (Formalism.L2.SG.Pf.RowDictPf.level_ne_zero X))
  have h1Kg : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    rw [← hker 1 (K_one _)]
    have := hmul 1 (K_one _) 1 (K_one _)
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have hvol_pos : 0 < X.B.μf (X.B.I.Kg X.B.g) := hKgO.measure_pos X.B.μf ⟨1, h1Kg⟩
  have hvol_fin : X.B.μf (X.B.I.Kg X.B.g) < ⊤ :=
    lt_of_le_of_lt (measure_mono hKgK) ((Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).measure_lt_top)
  set C : G0g D.nd → Set X.B.I.Gf := fun γ => (fun y => (s γ)⁻¹ * y) ⁻¹' X.B.I.Kg X.B.g with hCdef
  have hCmem : ∀ γ k, k ∈ C γ ↔ k ∈ X.B.I.Kset ∧ red k = γ := by
    intro γ k
    show (s γ)⁻¹ * k ∈ X.B.I.Kg X.B.g ↔ _
    constructor
    · intro hk'
      have hk2 : k = s γ * ((s γ)⁻¹ * k) := by group
      have hKk : k ∈ X.B.I.Kset := by rw [hk2]; exact K_mul _ (hsK γ) (hKgK hk')
      refine ⟨hKk, ?_⟩
      rw [hk2, hmul _ (hsK γ) _ (hKgK hk'), (hker _ (hKgK hk')).2 hk', mul_one, hsred]
    · rintro ⟨hKk, hrk⟩
      have hK' : (s γ)⁻¹ * k ∈ X.B.I.Kset := K_mul _ (K_inv _ (hsK γ)) hKk
      refine (hker _ hK').1 ?_
      have := hmul (s γ) (hsK γ) _ hK'
      rw [mul_inv_cancel_left, hrk, hsred] at this
      exact (left_eq_mul.mp this)
  have hCmeas : ∀ γ, MeasurableSet (C γ) := fun γ =>
    (hKgO.preimage (continuous_const.mul continuous_id)).measurableSet
  have hCvol : ∀ γ, X.B.μf (C γ) = X.B.μf (X.B.I.Kg X.B.g) := fun γ =>
    measure_preimage_mul X.B.μf _ _

  set vol : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal with hvol
  have hvol0 : (vol : ℂ) ≠ 0 := by
    rw [hvol]
    exact_mod_cast (ENNReal.toReal_pos hvol_pos.ne' hvol_fin.ne).ne'
  have hRg : Gd.Rg (star φ) = ∑ γ, D.ntypes.e0.coeff γ • X.B.R (1, s γ) (star φ) := by
    apply ext_inner_left ℂ
    intro x
    rw [Gd.Rg_spec.2 x (star φ), inner_sum]
    simp_rw [inner_smul_right]
    have hpt : ∀ k, eg X k * ⟪x, X.B.R (1, k) (star φ)⟫_ℂ =
        ∑ γ, (C γ).indicator (fun _ => D.ntypes.e0.coeff γ / (vol : ℂ) * ⟪x, X.B.R (1, s γ) (star φ)⟫_ℂ) k := by
      intro k
      by_cases hk : k ∈ X.B.I.Kset
      · have hgk := hgood k hk
        have heg : eg X k = D.ntypes.e0.coeff (red k) / (vol : ℂ) := by
          unfold eg
          rw [dif_pos ⟨hk, ⟨red k, hgk⟩⟩]
          congr 1
          exact Formalism.L2.SG.Pf.rowDictEgWellDef_holds X k _ _ (Classical.choose_spec _) hgk
        rw [Finset.sum_eq_single (red k)]
        · rw [Set.indicator_of_mem ((hCmem _ k).2 ⟨hk, rfl⟩), heg, hF1 k hk]
        · intro γ _ hγ
          exact Set.indicator_of_notMem (fun hm => hγ ((hCmem γ k).1 hm).2.symm) _
        · intro hn
          exact absurd (Finset.mem_univ _) hn
      · have heg : eg X k = 0 := by
          unfold eg
          rw [dif_neg (fun h' => hk h'.1)]
        rw [heg, zero_mul]
        symm
        refine Finset.sum_eq_zero fun γ _ => Set.indicator_of_notMem (fun hm => hk ((hCmem γ k).1 hm).1) _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finset_sum _ (fun γ _ => (integrable_indicator_iff (hCmeas γ)).2
      (integrableOn_const (by rw [hCvol]; exact hvol_fin.ne)))]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_indicator_const _ (hCmeas γ), Measure.real, hCvol, ← hvol, Complex.real_smul]
    field_simp

  have hstar : (star (Gd.Rg (star φ)) : L2X X) =
      ∑ γ, star (D.ntypes.e0.coeff γ) • star (X.B.R (1, s γ) (star φ)) := by
    rw [← conjL_apply (muX X), hRg, map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply]
    rfl
  rw [hstar]
  refine (hEv (fun γ => D.ntypes.e0.coeff γ) s (fun γ => ⟨hsK γ, hsred γ⟩)).trans
    (Filter.Eventually.of_forall fun x => ?_)
  have hc : (fun g => star (D.ntypes.e0.coeff (σ.symm g))) = RealDat.eC (A := A) D.what₂.embLL := by
    funext g
    rw [hC (σ.symm g), MulEquiv.apply_symm_apply]
  show gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (fun g => star (D.ntypes.e0.coeff (σ.symm g))) (S v₀) _ =
    R.e0 (S v₀) _
  rw [hc]
  rfl

end GlobalTheory.GoodProjEval
