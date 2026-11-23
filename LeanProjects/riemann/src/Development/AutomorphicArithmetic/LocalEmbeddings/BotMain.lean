import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.BotReading
import Development.AutomorphicArithmetic.LocalEmbeddings.BotPair
import Development.AutomorphicArithmetic.LocalEmbeddings.BotLocal
import Development.AutomorphicArithmetic.DivisorFrames.ThetaTransformFockModelEqOfStandardChar
import Development.AutomorphicArithmetic.DivisorFrames.StdSectionFirstEqProdLocal
import Development.AutomorphicArithmetic.DivisorFrames.StdSectionSecondEqProdLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

variable {D : D7}

set_option maxHeartbeats 3200000 in

theorem match_of_tri (hH : GlobalTheory.Published.HoweDualityReal) (hPr : GlobalTheory.FunPr.Hypotheses₂) (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {T : Type} {A A' WW : HSp D}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW) {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E}
    {S : T → Finset (Pl D.host.E)} (hX : X.Is ψ θ α β νH S) (t : T) (hT : GlobalTheory.SquareComm.IsTriple A A' WW (α t) (β t))
    (hν : ChrEq (α t / β t) (νH t))
    (hτ : ∀ v : Pl D.host.F, (∃ w ∈ S t, w.under (𝓞 D.host.F) = v) → ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∀ w ∈ S t, w.under (𝓞 D.host.F) = v → splitPrime τ = w)
    (hram : ∀ w ∈ S t, ¬ GlobalTheory.LFun.UnrAt (α t / β t) w)
    (hunr : ∀ w : Pl D.host.E, (∀ w' ∈ S t, w'.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) →
      GlobalTheory.LFun.UnrAt (α t) w ∧ GlobalTheory.LFun.UnrAt (β t) w)
    (hid : ∀ w ∈ S t, IsSplitIdem D (atPl w 1) ∧ atPl w 1 + cA D (atPl w 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1))
    (hε : X.e t = ∑ w ∈ S t, atPl w 1) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (hf : GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t)) (hf' : GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t)) :
    ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
      (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi)
      (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW (α t) (β t) (X.ω t) (X.ω' t) Pi rf rl p p' ∧
      ((∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) = 0) ∨
        ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank) (κ : ℂ),
          p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) ≠ 0 ∧
          p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) = κ • p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW (X.f' t) P')) := by
  classical
  have hA := hX.weil t
  have hB := hX.weil' t
  have sA : IsSelfDualC (GlobalTheory.Grid.sgn true A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.rigA.1
  obtain ⟨Bs, Γ, Xc, om, om', h, hTr, hTA, hTB, hLV, hLV', hLW, hP, hPw⟩ :=
    exists_reading_lat hψ FA FA' FW hT hA hB sA hX.rigA'.1 hX.rigW.1 (S t) hτ hram hunr
  obtain rfl := h.ψ
  obtain ⟨R, Rf, hM⟩ := hLM _ _ _ Bs _ _ Γ Xc om om' hTr
  have hg := hTr.geo
  have hinj : Function.Injective fun i : Bs.P => splitPrime (Bs.τ i) := fun i j hij =>
    Subtype.ext ((splitPrime_under (Bs.τ i)).symm.trans ((congrArg (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) hij).trans
      (splitPrime_under (Bs.τ j))))
  have hmem : ∀ i : Bs.P, splitPrime (Bs.τ i) ∈ S t := fun i => (hPw _).2 ⟨i, rfl⟩
  have ha : ∀ i : Bs.P, IsSplitIdem D (atPl (splitPrime (Bs.τ i)) 1) ∧
      atPl (splitPrime (Bs.τ i)) 1 + cA D (atPl (splitPrime (Bs.τ i)) 1) =
        algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV i.1 1) := fun i => by
    have := hid _ (hmem i)
    rwa [splitPrime_under] at this
  have he : X.e t = ∑ i : Bs.P, atPl (splitPrime (Bs.τ i)) 1 := by
    have : S t = Finset.univ.image fun i : Bs.P => splitPrime (Bs.τ i) := by
      ext w; simp [hPw]
    rw [hε, this, Finset.sum_image fun i _ j _ hij => hinj hij]
  choose I I' φ φ' lam hI hI' sφ sφ' nφ nφ' nlam hφφ' eφ eφ' using fun i : Bs.P =>
    local_pair h hM sA hX.rigA.2.1 hLV X.rA'.β X.rW.β hν i (by rw [hP]; exact i.2) (hX.expo t _ (hmem i))
  let Φ : ∀ v : Pl D.host.F, (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if hv : v ∈ Bs.P then φ ⟨v, hv⟩ else Γ.M.vac v
  let Φ' : ∀ v : Pl D.host.F, (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if hv : v ∈ Bs.P then φ' ⟨v, hv⟩ else Γ.M'.vac v
  have e1 : ∀ i : Bs.P, Φ i = φ i := fun i => dif_pos i.2
  have e1' : ∀ i : Bs.P, Φ' i = φ' i := fun i => dif_pos i.2
  have e2 : ∀ v ∉ Bs.P, Φ v = Γ.M.vac v := fun v hv => dif_neg hv
  have e2' : ∀ v ∉ Bs.P, Φ' v = Γ.M'.vac v := fun v hv => dif_neg hv
  have hall : ∀ v, (Φ v ∈ GlobalTheory.WeilM.SB _ ∧ Φ v ≠ 0) ∧ (Φ' v ∈ GlobalTheory.WeilM.SB _ ∧ Φ' v ≠ 0) ∧ Rf.p v (Φ v) = Rf.p' v (Φ' v) := by
    intro v
    by_cases hv : v ∈ Bs.P
    · rw [e1 ⟨v, hv⟩, e1' ⟨v, hv⟩]
      exact ⟨⟨sφ _, nφ _⟩, ⟨sφ' _, nφ' _⟩, hφφ' ⟨v, hv⟩⟩
    · rw [e2 v hv, e2' v hv]
      exact ⟨⟨(hg.hM.vac v).1, (hg.hM.vac v).2.1⟩, ⟨(hg.hM'.vac v).1, (hg.hM'.vac v).2.1⟩, (hM.fin.sph v (by rw [hP]; exact hv)).1⟩
  have ev : ∀ᶠ v in Filter.cofinite, Φ v = Γ.M.vac v := Bs.P.eventually_cofinite_notMem.mono e2
  have ev' : ∀ᶠ v in Filter.cofinite, Φ' v = Γ.M'.vac v := Bs.P.eventually_cofinite_notMem.mono e2'
  obtain ⟨f₀, nf₀, ef₀⟩ := exists_pure_pair true A WW hT.rank.symm Γ.M h.JW h.JX sA hX.rigW.1 hψ hTr.base hg.hV hg.hW hg.hM
    (fun s hs => hLV ▸ GlobalTheory.BigDat.star_mem_conjSub hs) hLW hθ hX.isVac.2.theta (GlobalTheory.BigDat.vac_ne_zero (S := GlobalTheory.Grid.neg A) hX.isVac) hX.isVac.2.lat
    (Subtype.val : Bs.P → _) Subtype.val_injective _ ha he _ _ _ (fun i u => (half_iff (Bs.τ i) (ha i).2 u).1)
    (fun i u => (half_iff (Bs.τ i) (ha i).2 u).2)
    (fun i u => ((Γ.V.bas i)⁻¹).1 * u.map (piW (Bs.τ i)) * ((Γ.W.bas i)⁻¹).1ᵀ)
    (fun i u x => by rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul])
    (fun i u => by
      congr 2
      exact Matrix.ext fun p q => (map_mul (piW (Bs.τ i)) _ _).trans (by rw [piW_atPl_one, one_mul]; rfl))
    (fun i z => by
      obtain ⟨u, hu⟩ := exists_map_piW (Bs.τ i) ((Γ.V.bas i).1 * z * (Γ.W.bas i).1ᵀ)
      refine ⟨u, ?_⟩
      beta_reduce
      rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul,
        Units.inv_mul, transpose_one, Matrix.mul_one])
    I (fun i => GlobalTheory.BigNZ.isLagrModel_of_isLin (hI i)) (hX.fst t)
    (fun x hx => by
      by_contra hn
      exact hx (if_neg fun h' => hn h'.1))
    Φ (fun v => (hall v).1.1) (fun v hv => e2 v fun h' => hv ⟨v, h'⟩ rfl) one_ne_zero
    (fun x hx => by
      rw [one_mul]
      refine Eq.trans ?_ (UpperTheory.stdSectionFirst_eq_prod_local D _ _ (hX.idem t) Bs.P Subtype.val Bs.τ hPw hinj (X.c t) (α t / β t) A WW X.rA.β X.rW.β
        A'.rank hT.rank.symm x hx).symm
      exact Finset.prod_congr rfl fun i _ => by rw [e1 i]; exact eφ i x)
  have dV' : ∀ i : Bs.P, IsUnit ((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i)) := fun i => by
    refine ((Matrix.isUnit_transpose _).2 (Γ.V'.bas i).isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).2 ?_)
    have := RingHom.map_det (Bs.τ i : D.host.E →+* Fv D.host.F i.1) Γ.V'.J
    refine (this ▸ IsUnit.map _ (Ne.isUnit ?_) : IsUnit ((Bs.τ i : D.host.E →+* Fv D.host.F i.1).mapMatrix Γ.V'.J).det)
    rw [h.JW₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Formalism.L2.Theta.gram_det_ne A')
  have dW : ∀ i : Bs.P, IsUnit ((Γ.W.J.map (Bs.τ i))ᵀ * (Γ.W.bas i).1) := fun i => by
    refine ((Matrix.isUnit_transpose _).2 ((Matrix.isUnit_iff_isUnit_det _).2 ?_)).mul (Γ.W.bas i).isUnit
    have := RingHom.map_det (Bs.τ i : D.host.E →+* Fv D.host.F i.1) Γ.W.J
    refine (this ▸ IsUnit.map _ (Ne.isUnit ?_) : IsUnit ((Bs.τ i : D.host.E →+* Fv D.host.F i.1).mapMatrix Γ.W.J).det)
    rw [h.JX, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) (Formalism.L2.Theta.gram_det_ne WW)
  obtain ⟨f₁, nf₁, ef₁⟩ := exists_pure_pair false A' WW hT.rank.symm Γ.M' h.JW₁ h.JX hX.rigA'.1 hX.rigW.1 hψ hTr.base hg.hV' hg.hW
    hg.hM' (fun s hs => hLV' ▸ GlobalTheory.BigDat.star_mem_conjSub hs) hLW hθ hX.isVac'.2.theta (GlobalTheory.BigDat.vac_ne_zero hX.isVac')
    hX.isVac'.2.lat (Subtype.val : Bs.P → _) Subtype.val_injective (fun i => cA D (atPl (splitPrime (Bs.τ i)) 1))
    (fun i => ⟨GlobalTheory.BigDat.splitIdem_conj (ha i).1, by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, (ha i).2]⟩)
    (η := cA D (X.e t)) (by rw [he, map_sum]) _ _ _ (fun i u => (half_iff (Bs.τ i) (ha i).2 u).2)
    (fun i u => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact (half_iff (Bs.τ i) (ha i).2 u).1)
    (fun i u => -((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i) * u.map (piW ((Bs.τ i).comp D.sp.cm.sig)) * (Γ.W.J.map (Bs.τ i))ᵀ *
      (Γ.W.bas i).1))
    (fun i u x => by rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, neg_add])
    (fun i u => by
      congr 4
      exact Matrix.ext fun p q => (map_mul (piW ((Bs.τ i).comp D.sp.cm.sig)) _ _).trans (by
        rw [← GlobalTheory.FlipMatch.RowChart.piW_cA_eq, GlobalTheory.DualPairCheck.cA_cA, piW_atPl_one, one_mul]; rfl))
    (fun i z => by
      obtain ⟨g₁, h₁⟩ := dV' i
      obtain ⟨g₂, h₂⟩ := dW i
      obtain ⟨u, hu⟩ := exists_map_piW ((Bs.τ i).comp D.sp.cm.sig) ((g₁⁻¹).1 * (-z) * (g₂⁻¹).1)
      refine ⟨u, ?_⟩
      beta_reduce
      rw [hu, Matrix.mul_assoc _ _ (Γ.W.bas i).1, ← h₁, ← h₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
        Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, neg_neg])
    I' (fun i => GlobalTheory.BigNZ.isLagrModel_of_isLin (hI' i)) (hX.snd t)
    (fun x hx => by
      by_contra hn
      exact hx (if_neg fun h' => hn h'.1))
    Φ' (fun v => (hall v).2.1.1) (fun v hv => e2' v fun h' => hv ⟨v, h'⟩ rfl) (κ := ∏ i, lam i)
    (Finset.prod_ne_zero_iff.2 fun i _ => nlam i)
    (fun x hx => by
      refine Eq.trans ?_ (congrArg (_ * ·) (UpperTheory.stdSectionSecond_eq_prod_local D _ _ (hX.idem t) Bs.P Subtype.val Bs.τ hPw hinj (X.c t) (α t / β t)
        A.rank A' WW X.rA'.β X.rW.β hT.rank.symm x hx).symm)
      beta_reduce
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [e1' i]; exact eφ' i x)
  obtain ⟨L, rL, eL⟩ := UpperTheory.theta_transform_fock_model_eq_of_standard_char D Bs.ψ θ hψ hθ true A WW _ hT.rank.symm Γ.V Γ.W Γ.M h.JW h.JX hg.hM FA FW Bs.emb
    (fun w => by obtain ⟨τ, h1, h2, -, h4⟩ := h.cart w; exact ⟨τ, h1, by rw [h2]; simp, h4⟩) f₀ Φ nf₀
    (fun v => (hall v).1.1) ev (fun v => (hall v).1.2) (ef₀.symm ▸ hf)
  obtain ⟨L', rL', eL'⟩ := UpperTheory.theta_transform_fock_model_eq_of_standard_char D Bs.ψ θ hψ hθ false A' WW _ hT.rank.symm Γ.V' Γ.W Γ.M' h.JW₁ h.JX hg.hM' FA' FW Bs.emb
    (fun w => by obtain ⟨τ, h1, -, h3, h4⟩ := h.cart w; exact ⟨τ, h1, by rw [h3]; simp, h4⟩) f₁ Φ' nf₁
    (fun v => (hall v).2.1.1) ev' (fun v => (hall v).2.1.2) (ef₁.symm ▸ hf')
  rw [ef₀] at eL
  rw [ef₁] at eL'
  have pA : ∀ P, GlobalTheory.TripleAssembly.mapA Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf
      (GlobalTheory.SquareComm.fockF Bs.ψ θ true FA FW (X.f t) P) =
      R.p (L P) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p v (Φ v)) := fun P => by
    have := GlobalTheory.T.seesaw_weil_zeta_factor hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM 1
      (fun _ => L P) (fun _ => Φ) (fun _ => ⟨fun v => (hall v).1.1, ev⟩) (by
        rw [Fin.sum_univ_one]
        exact Submodule.subset_span ⟨L P, Φ, rL ▸ ⟨P, rfl⟩, fun v => (hall v).1.1, ev, rfl⟩)
    rwa [Fin.sum_univ_one, Fin.sum_univ_one, eL] at this
  have pB : ∀ P, GlobalTheory.TripleAssembly.mapB Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf
      (GlobalTheory.SquareComm.fockF Bs.ψ θ false FA' FW (X.f' t) P) =
      R.p' (L' P) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p' v (Φ' v)) := fun P => by
    have := GlobalTheory.T.seesaw_weil_zeta_archimedean hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM 1
      (fun _ => L' P) (fun _ => Φ') (fun _ => ⟨fun v => (hall v).2.1.1, ev'⟩) (by
        rw [Fin.sum_univ_one]
        exact Submodule.subset_span ⟨L' P, Φ', rL' ▸ ⟨P, rfl⟩, fun v => (hall v).2.1.1, ev', rfl⟩)
    rwa [Fin.sum_univ_one, Fin.sum_univ_one, eL'] at this
  have tA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hψ hθ true A WW FA FW _ _ _ hA
  have tB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hψ hθ false A' WW FA' FW _ _ _ hB
  obtain ⟨oA, oB⟩ := GlobalTheory.T.algF_map_mapA_and_mapB_eq_top hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨iA, iB⟩ := GlobalTheory.T.mapA_mapB_invariant_under_finite_group hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨lA, lB⟩ := GlobalTheory.T.seesaw_weil_local_factor_eq hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨fA, fB⟩ := GlobalTheory.T.seesaw_weil_archimedean_factor hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨dA, dB⟩ := GlobalTheory.T.seesaw_weil_unramified_factor hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  have ir := GlobalTheory.T.seesaw_weil_global_factor hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  refine ⟨ModuleCat.of ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), _, _, GlobalTheory.TripleAssembly.mapA Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf,
    GlobalTheory.TripleAssembly.mapB Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf,
    ⟨hA, hB, ir, ⟨tA.1, tA.2, oA, iA, lA, fA, dA⟩, ⟨tB.1, tB.2, oB, iB, lB, fB, dB⟩⟩, ?_⟩
  refine (em _).imp id fun hn => ?_
  obtain ⟨P, hP0⟩ := not_forall.1 hn
  obtain ⟨g, hg', eg⟩ : R.p (L P) ∈ (Γ.M'.Pol Bs.ψ Bs.emb).map R.p' := hM.real.quot'.onto ▸ Submodule.mem_top
  obtain ⟨P', rfl⟩ : g ∈ LinearMap.range L' := rL' ▸ hg'
  refine ⟨P, P', 1, hP0, ?_⟩
  rw [one_smul]
  refine (pA P).trans (Eq.trans ?_ (pB P').symm)
  rw [eg, funext fun v => (hall v).2.2]

end GlobalTheory.BotMatch

end
