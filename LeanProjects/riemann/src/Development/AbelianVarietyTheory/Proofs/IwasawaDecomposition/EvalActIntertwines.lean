import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeFnFinsetSumSmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem coeFn_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type} [Fintype ι] (c : ι → ℂ)
    (u : ι → Lp ℂ 2 μ) :
    ((∑ i, c i • u i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ∑ i, c i * (u i : α → ℂ) x := by
  first
  | exact @_root_.GlobalTheory.FinsetSumSmulCoe.main
  | exact _root_.GlobalTheory.FinsetSumSmulCoe.main
  | (apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetSumSmulCoe.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetSumSmulCoe.main ..)

theorem sum_smul_apply {ι α : Type} [Fintype ι] (L : ι → (α → ℂ) →ₗ[ℂ] (α → ℂ)) (c : ι → ℂ) (φ : α → ℂ) (y : α) :
    (∑ i, c i • L i) φ y = ∑ i, c i * L i φ y := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp

theorem iotaX_symm_rat {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : X.B.I.GA)
    (hz : z ∈ X.B.I.GFset) : (iotaX X h).symm z ∈ GQ (D.sp.Y 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (z : I.GA), z ∈ I.GFset →
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm z ∈ GQ (D.sp.Y 0) := by
    intro I hI z hz
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm z =
        (Formalism.IndefR.RationalEmbedding.iota D).symm z := rfl
    rw [e, Formalism.IndefR.RationalEmbedding.iota_rat, ContinuousMulEquiv.apply_symm_apply]
    exact hz
  exact aux X.B.I h z hz

theorem ev_translate {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G')
    (red : X.B.I.Gf → G0g D.nd) (hB : LevelMatchB R F X h t σ red) (S : MMap (MP R)) (hS : S ∈ MultR R F)
    (k : X.B.I.Gf) (hk : k ∈ X.B.I.Kset) (x : X.B.I.GA) :
    ev (MP R) v₀ S ((iotaX X h).symm (x * (1, k)) * t) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
  have hk' := hB.2 k hk S hS v₀ ((iotaX X h).symm x * t)
  refine Eq.trans ?_ hk'
  have e : (iotaX X h).symm (x * (1, k)) * t = (iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k) := by
    unfold kap
    rw [map_mul]
    group
  show S v₀ _ = S v₀ _
  rw [e]
  rfl

theorem evalAct_intertwines : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) [Fintype (G0g D.nd)] (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G') (red : X.B.I.Gf → G0g D.nd), LevelMatchB R F X h t σ red → ∀ S ∈ MultR R F, ∀ f : L2X X, (f =ᵐ[muX X] fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g) → ∀ (a : G0g D.nd → ℂ) (s : G0g D.nd → X.B.I.Gf), (∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ) → (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star f)) : L2X X) =ᵐ[muX X] fun x => gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (fun g => star (a (σ.symm g))) (S v₀) ((iotaX X h).symm x * t) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F _ X h t v₀ σ red hB S hS f hf hinv a s hs
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec

  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      ev (MP R) v₀ S ((iotaX X h).symm (γ * y) * t) = ev (MP R) v₀ S ((iotaX X h).symm y * t) := by
    intro γ hγ y
    show S v₀ _ = S v₀ _
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have key : ∀ k ∈ X.B.I.Kset, ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
    intro k hk
    have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
      Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
    have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
      have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
      rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
    obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
    have e1 := X.B.R_spec (1, k) f
    have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
        ev (MP R) v₀ S ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
      refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = ev (MP R) v₀ S ((iotaX X h).symm y * t)) h1 ?_
      rw [h2]
      exact hf
    filter_upwards [e1, e3] with x a1 a3
    rw [a1]
    show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
    rw [a3]
    obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
    rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
      hφinv γ hγ]
    exact ev_translate R F X h t v₀ σ red hB S hS k hk x
  have hall : ∀ᵐ x ∂(muX X), ∀ γ, ((X.B.R (1, s γ) f : L2X X) : X.B.I.GA → ℂ) x =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red (s γ)))) (S v₀) ((iotaX X h).symm x * t) :=
    ae_all_iff.2 fun γ => key (s γ) (hs γ).1
  have hsum := coeFn_sum_smul (μ := muX X) (fun γ => star (a γ)) (fun γ => star (X.B.R (1, s γ) (star f)))
  filter_upwards [hsum, hall] with x b1 b2
  rw [b1]
  simp only [Formalism.L2.SG.Pf.RowDictPf.R_star, star_star]
  simp only [b2, (hs _).2]
  unfold gaL
  refine Eq.trans ?_ (sum_smul_apply _ _ _ _).symm
  refine Fintype.sum_equiv σ.toEquiv _ _ (fun γ => ?_)
  show _ = star (a (σ.symm (σ γ))) * _
  rw [MulEquiv.symm_apply_apply]
  rfl

end GlobalTheory.Mem.SRe

end
