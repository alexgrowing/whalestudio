import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefMapNormEquivariantBasisOfPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AdTh.CoefC

open MvPolynomial

section General

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)

def upL : VV K lam →ₛₗ[φ] VV K' lam where
  toFun := CoefExt.up φ lam
  map_add' x y := Subtype.ext (by simp [CoefExt.up, map_add])
  map_smul' a x := Subtype.ext (by simp [CoefExt.up, smul_eq_C_mul, map_mul, map_C])

theorem upL_apply (v : VV K lam) : upL φ lam v = CoefExt.up φ lam v := rfl

theorem up_id (v : VV K lam) : CoefExt.up (RingHom.id K) lam v = v :=
  Subtype.ext (by simp [CoefExt.up, MvPolynomial.map_id])

theorem up_comp {K'' : Type} [Field K''] (ψ : K' →+* K'') (v : VV K lam) :
    CoefExt.up ψ lam (CoefExt.up φ lam v) = CoefExt.up (ψ.comp φ) lam v :=
  Subtype.ext (by simp [CoefExt.up, MvPolynomial.map_map])

theorem up_bVV_linearIndependent : LinearIndependent K' fun j => CoefExt.up φ lam (bVV K lam j) := by
  classical
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · intro v _
    obtain ⟨a, rfl⟩ := CoefExt.exists_coord φ lam v
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Module.finrank_eq_card_basis (bVV K' lam)]

theorem up_linearIndependent (ψ : K →+* ℂ) {m : ℕ} (b : Fin m → VV K lam) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun j => CoefExt.up ψ lam (b j) :=
  CoefExt.linearIndependent (φ := RingHom.id K) (c₀ := upL ψ lam) (c' := upL ψ lam)
    (fun v => by rw [upL_apply, up_id]; rfl) (up_bVV_linearIndependent ψ lam) b hb

theorem injective_of_basis {W : Type} [AddCommGroup W] [Module K W] {ι : Type} [Fintype ι] (B : Module.Basis ι K (VV K lam))
    (c : VV K lam →ₗ[K] W) (h : LinearIndependent K fun j => c (B j)) : Function.Injective c := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hs : ∑ j, B.repr x j • c (B j) = 0 := by
    rw [← hx]
    conv_rhs => rw [← B.sum_repr x]
    simp only [map_sum, map_smul]
  have h0 := Fintype.linearIndependent_iff.1 h _ hs
  rw [← B.sum_repr x]
  simp [h0]

end General

end GlobalTheory.AdTh.CoefC

open GlobalTheory.AdTh.CoefC in
set_option maxHeartbeats 800000 in

theorem GlobalTheory.AdTh.CoefC.coefMap_complex_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ (hw : VsV D i T.Q.c.F), hwOK T.Q.c (lamV D i) hw → ‖c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) hw)‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (rhoM T.Q.c (fun τ => embF T.Q.c (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v)) = (R.cV i).ρ γ (c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v))) ∧ Submodule.span ℂ (Set.range fun v => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v)) = ⊤ ∧ (∀ (m : ℕ) (b : Fin m → VsV D i T.Q.c.F), LinearIndependent T.Q.c.F b → LinearIndependent ℂ (fun j => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (b j)))) ∧ Function.Injective c0 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hT i hstd c0 hc hw hwo
  obtain ⟨gramR, c0R, c0L, hT', hC⟩ := hc
  have hE : ∀ v : VsV D i D.what₂.LL, c0 (CoefExt.up D.what₂.embLL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw', h⟩ := hC v
    rw [show CoefExt.up D.what₂.embLL (lamV D i) v = w from Subtype.ext hw'.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT'.mapL i

  have hli : ∀ (m : ℕ) (b : Fin m → VsV D i ℂ), LinearIndependent ℂ b → LinearIndependent ℂ fun j => c0 (b j) :=
    fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) (c' := c0) hE h2 b hb
  have hinj : Function.Injective c0 := by
    classical
    let B := (bVV ℂ (lamV D i)).reindex (Fintype.equivFin _)
    refine injective_of_basis (lamV D i) B c0 ?_
    exact hli _ _ B.linearIndependent
  refine ⟨?_, ?_, ?_, fun m b hb => hli m _ (up_linearIndependent _ _ b hb), hinj⟩
  ·
    have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hstd
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hstd.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : CoefExt.up (inC T.Q.c) (lamV D i) hw = CoefExt.up D.what₂.embLL (lamV D i) v := by
      apply Subtype.ext
      show MvPolynomial.map (inC T.Q.c) (hw : Pol T.Q.c.F D.what₂.Tau (Vc D i).rank) =
        MvPolynomial.map D.what₂.embLL (Formalism.L2.DIV.ten _)
      have hw' := hwo
      unfold hwOK at hw'
      rw [hw', GlobalTheory.Proof.TensorMapDescent.map_ten, GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      rw [Formalism.L2.DIV.map_extremal, Formalism.L2.DIV.map_extremal]
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := inner_of_coefTie (hT'.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  ·
    intro γ γE hγ v
    let alg := algebraMap T.Q.c.F D.what₂.LL
    have hres : D.what₂.embLL.comp alg = inC T.Q.c := res_embLL T hT.alg hT.laws.pins.2.2.1
    have hup : ∀ w : VsV D i T.Q.c.F, c0 (CoefExt.up (inC T.Q.c) (lamV D i) w) = c0L i (CoefExt.up alg (lamV D i) w) := by
      intro w
      rw [← hE, up_comp, hres]
    have hlab : (fun τ => alg.comp (embF T.Q.c (tauE D τ))) = labLL D := by
      funext τ
      apply RingHom.ext
      intro x
      apply D.what₂.embLL.injective
      have e1 := RingHom.congr_fun (embV_spec (σ' := RingHom.id ℂ) D.what₂.embLL (by rfl) τ) x
      have e2 := RingHom.congr_fun hres (embF T.Q.c (tauE D τ) x)
      exact e2.trans e1.symm
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    rw [hup, hup, rhoM, dif_pos hu, hγE, CoefExt.up_rhoVr, hlab]
    exact h1 γ γE hγ _
  ·
    have hs := CoefExt.span_top (W := (R.cV i).W) (c' := c0) hE h3
    refine top_le_iff.1 (hs ▸ Submodule.span_le.2 ?_)
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, rfl⟩ := CoefExt.exists_coord (inC T.Q.c) (lamV D i) w
    rw [map_sum]
    exact Submodule.sum_mem _ fun j _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
