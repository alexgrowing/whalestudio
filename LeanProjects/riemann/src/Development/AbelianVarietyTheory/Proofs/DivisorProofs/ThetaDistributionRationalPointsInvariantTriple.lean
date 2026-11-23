import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairOfTransposedGramInverseGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RatInvTheta

theorem inclR_inj (D : D7) : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem sigR_inclR (D : D7) (e : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (F := D.host.F) (AF D.host.F) e) =
      inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig e) := by
  simp [sigR, inclR]

theorem mem_GQ_of {D : D7} (V : HSp D) (g : GA D V) (z : GL (Fin V.rank) D.host.E)
    (hz : mt V g = (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) :
    g ∈ GQ V := by
  refine ⟨z, ?_, Units.ext ?_⟩
  · have hm : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
        JR (AF D.host.F) V.gram := g.2
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
        ((z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map
          (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact sigR_inclR D _
    rw [hz, hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram
    apply Matrix.map_injective (inclR_inj D)
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · exact hz.symm

theorem thetaSum_rat_inv : ∀ {D : D7} {a a' : ℕ} (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ γ ∈ ratU D.sp.cm.sig Γ.V.J, ∀ γ' ∈ ratU D.sp.cm.sig Γ.W.J, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin a × Fin (a + a')),
      GlobalTheory.WeilM.thetaSum D.host.F (om (γ, γ') Φ) = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  intro D a a' Bs Γ X om om' hT γ hγ γ' hγ' Φ hΦ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hT.base a Γ.V _ _ hT.geo.hV
  obtain ⟨hJ, L, hL, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hT.base (a + a') Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T := GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hT.geo.hV.lat h3 (fun _ => (a - Γ.p, Γ.p))
  let S := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L hL h6
    (fun _ => (Γ.p + Γ.q, a + a' - (Γ.p + Γ.q)))
  have eA : Γ.V.J = T.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E (X.β / X.α) :=
    ⟨hT.chars.heckeβ.1.div' hT.chars.heckeα.1, fun x => by
      rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]⟩
  have rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range (X.β / X.α)
      (a + a') := by
    intro x
    have e₁ := hT.chars.resβ x
    have e₂ := hT.chars.resα x
    rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂, hT.geo.even.neg_one_pow]
    split_ifs
    · simp
    · rcases Nat.even_or_odd a with h | h
      · have h' : Even a' := (Nat.even_add.mp hT.geo.even).mp h
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
      · have h' : Odd a' := by
          rcases Nat.even_or_odd a' with h'' | h''
          · exact absurd ((Nat.even_add.mp hT.geo.even).mpr h'') (Nat.not_even_iff_odd.mpr h)
          · exact h''
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hT.base S T Γ.V Γ.W _ _ _ _ hT.geo.hV hT.geo.hW
    eA eB Γ.M hT.geo.hM X.β (X.β / X.α) hT.chars.heckeβ hcW hT.chars.resβ rW om hT.weil
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.WeilSchrodinger.match_pair D S T Γ.V.J Γ.W.J (-1) eA eB γ γ'
  obtain ⟨z, hz⟩ := hγ
  obtain ⟨z', hz'⟩ := hγ'
  have hhQ : h ∈ GQ T := by
    refine mem_GQ_of T h z ?_
    rw [hh]
    exact (congrArg Units.val hz).symm
  have hgQ : g ∈ GQ S := by
    have m1 := congrArg Matrix.transpose (Units.mul_inv z')
    have m2 := congrArg Matrix.transpose (Units.inv_mul z')
    rw [Matrix.transpose_mul, Matrix.transpose_one] at m1 m2
    let Z : GL (Fin (a + a')) D.host.E :=
      ⟨((z'⁻¹ : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ,
        ((z' : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ, m1, m2⟩
    refine mem_GQ_of S g Z ?_
    rw [hg]
    have h0 : γ'.1 = Matrix.GeneralLinearGroup.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) z' := hz'.symm
    show ((γ'.1)⁻¹ : GL (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)).1ᵀ = _
    rw [h0, ← map_inv]
    rfl
  have hf :=
    GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D Bs.ψ (GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D Bs.ψ hT.base.std) S T Γ.V.J Γ.W.J (-1) eA eB (Fin T.rank × Fin S.rank) Γ.M.co
      hT.geo.hM.rat Φ hΦ
  have key := hth γ γ' g h hh hg Φ hΦ
  have e0 := GlobalTheory.WeilBridge.thetaTr_zero D Γ.M.co Bs.ψ Φ
  have e1 := hω.om_aut g hgQ h hhQ _ hf
  exact key.trans (e1.trans e0)

end GlobalTheory.RatInvTheta
