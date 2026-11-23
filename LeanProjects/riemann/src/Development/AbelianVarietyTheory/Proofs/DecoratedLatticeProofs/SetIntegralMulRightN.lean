import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramePeriod

variable {D : D7}

theorem setIntegral_mul_right_N {ρ : ℕ} (B : BesLev D ρ) (G : flagN B.d → ℂ)
    (hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n, G (γ * n) = G n) (y : flagN B.d) :
    ∫ n in B.vN.𝓝, G (n * y) ∂B.vN.ν = ∫ n in B.vN.𝓝, G n ∂B.vN.ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  haveI : DiscreteTopology (NFlagQ B.V B.d.e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B.V B.d.e => (⟨γ.1.1, γ.2⟩ : GQ B.V)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B.V => (x : GA D B.V)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B.V ρ B.d.e (isIsoSub_e B.d)).1
  have hcov' : ∀ x : flagN B.d, ∃ s ∈ NFlagQ B.V B.d.e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : flagN B.d, B.vN.ν.map (· * a) = B.vN.ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vN.ν (NFlagQ B.V B.d.e) hK hcov' a
  have hmp : MeasurePreserving (· * y) B.vN.ν B.vN.ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) B.vN.ν B.vN.ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) G B.vN.𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B.V B.d.e) ((· * y⁻¹) ⁻¹' B.vN.𝓝) B.vN.ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

theorem inner_N {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n ∂B.vN.ν =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨-, -, hconj, -, -⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  have hx' : GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹ ∈ flagN B.d := hconj x hx h
  have hpy : psiBes ψ B.d 1 (vecB B.o B.ζ) (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x := hψconj x h
  have hn1 : psiBes ψ B.d 1 (vecB B.o B.ζ) x * star (psiBes ψ B.d 1 (vecB B.o B.ζ) x) = 1 := by
    have hnorm : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) x‖ = 1 := by simp only [psiBes, psiE]; exact hψ.2.1 _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  let y : flagN B.d := ⟨_, hx'⟩
  have hpt : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * besFun ψ 1 B.d B.o B.ζ φ f h (n * y) := fun n => by
    simp only [besFun, rTrans, Subgroup.coe_mul, y]
    rw [psiBes_mul B.d ψ 1 _ n.2 hx', hpy, star_mul]
    have e1 : (n : GA D B.V) * (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) *
        GlobalTheory.MixPer.embA B.d B.o h = (n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x := by group
    rw [e1]
    linear_combination (-(φ h * f ((n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x) *
      star (psiBes ψ B.d 1 (vecB B.o B.ζ) (n : GA D B.V)))) * hn1
  simp_rw [hpt]
  rw [integral_const_mul, setIntegral_mul_right_N B _ hG y]

theorem per_flagN {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) :
    B.per ψ φ (rTrans x f) = psiBes ψ B.d 1 (vecB B.o B.ζ) x * B.per ψ φ f := by
  unfold BesLev.per besPer
  simp_rw [inner_N B ψ hψ.1 φ f hf hx]
  exact integral_const_mul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_embA (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) {g : GL n k}
    {h : GA D B.A} (hh : p.IsLoc FA h g) : p.IsLoc F (GlobalTheory.MixPer.embA B.d B.o h) (embX c g) := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  rw [GlobalTheory.MixPer.embA_apply]
  refine ⟨GlobalTheory.LocGrp.suppAt_wittLeviEmbedding B.d (GlobalTheory.LocGrp.suppAt_emb B.o hh.1),
    GlobalTheory.LocGrp.eq_embX F _ g ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (GlobalTheory.LocGrp.intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r =>
      (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩
      (hY _ j (by simp only; omega))

end GlobalTheory.NormalFramePeriod

end
