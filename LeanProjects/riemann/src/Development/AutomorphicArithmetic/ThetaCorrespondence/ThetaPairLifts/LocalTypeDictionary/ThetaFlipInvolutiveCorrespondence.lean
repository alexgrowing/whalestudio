import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopGridStagePolynomialExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaParameterDictionaryBijective
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StageUniqueOfArchimedeanTriple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFlipTensorMatch

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.TopFlip
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}
set_option maxHeartbeats 1600000 in
theorem thetaFlip_tuple_match (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hL : L.Is μ₀) (W : G.Weil) (i j : Fin D.R.m)
    {A : Fr (spW G i j)} {A₁ : Fr (spW₁ G i j)} {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hA : IsGridFr W _ A)
    (hA₁ : IsGridFr W _ A₁) (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁) (t : T) (B : Frames G) (ρ : RealMatch W) (M : Vol G)
    (hst : SquareStanding G t) (hM : M.Is t) {ωA ωB}
    (hωA : GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA)
    (hωB : GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB) :
    ∃ Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p' ∧
      ∀ ε, IsIdemSum ε (locPl G t) → ∀ Ξ Ψ (u : Pl D.host.E → ℂ) F F',
        (∀ w ∈ locPl G t, Ξ w ∈ GlobalTheory.WeilM.SB _ ∧ Ψ w ∈ GlobalTheory.WeilM.SB _ ∧ zetaA G t i j w (Ξ w) = u w • zetaB G t i j w (Ψ w)) →
        IsLinA B t i j ρ ε Ξ F → IsLinB B t i j ρ ε Ψ F' →
        ∀ n Φ (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)),
        (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
        IsFinF W.ψ W.θ true A (frSum AV AV₁) F ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) F' ∧
        IsFinF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') ∧
        ∀ P P' (g : ℂ), p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) F' P') ≠ 0 →
          p (fockF W.ψ W.θ true A (frSum AV AV₁) F P) = g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) F' P') →
          ((∏ w ∈ locPl G t, u w) * ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ)) •
              p (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) =
            g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') P') := by
  have hT := (GlobalTheory.SquareDict.dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁).1 hst M hM
  obtain ⟨e, Bs, Γ, X, om₀, om₀', h, hT₀, hti⟩ := exists_tiedBoth hL W t i j hst M hM
  have hR : GlobalTheory.TripleRead.IsReading W.ψ A A₁ (frSum AV AV₁) _ _ (e.symm.trans finSumFinEquiv) Bs Γ X :=
    ⟨h.ψ, h.JW, h.JW₁, by
      rw [h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← GlobalTheory.SquareIdent.blkMat_submatrix, GlobalTheory.Doubling.gram_hsum]
      rfl, fun w => by
      obtain ⟨τ, a, b, c, d⟩ := h.cart w
      refine ⟨τ, a, b.trans (hA τ).2.symm, c.trans (congrArg Neg.neg (hA₁ τ).2.symm), d.trans ?_⟩
      rw [GlobalTheory.SquareAlg.cart_frSum, (hV τ).2, (hV₁ τ).2, ← GlobalTheory.SquareIdent.blkMat_submatrix], h.α, h.β⟩
  obtain ⟨om, om', R, Rf, hm, rf, rl, p, p', hM', HA, HB⟩ :=
    _root_.GlobalTheory.TopFlip.thetaFlip_tensor_match hP.howeDualityReal hP hTL W.θ_is A A₁ _ hT hωA hωB hR hT₀
  have hT' := hm.triple
  have H := fun (w : Pl D.host.E) (hw : w ∈ locPl G t) => local_charts hL W B t i j M hst h hm hti hw
  choose! ιA ι ιB ι' l hl h1 h2 h3 h4 h5 h6 h7 using H
  obtain ⟨f, -, f2, f3⟩ := GlobalTheory.T.exists_gaussianVacuum_product_unitVacua hL W ρ t i j M hst e Bs Γ X om om' h hT' hti.1
  obtain ⟨f', -, g2, g3⟩ := GlobalTheory.T.unitVacua_product_eq_gaussianDatum_smallModel hL W ρ t i j M hst e Bs Γ X om om' h hT' hti
  obtain ⟨hs, a⟩ := mixglobA hL W B ρ t i j M hst e Bs Γ X om om' h hT' hti.1 f f3 ι h3
  obtain ⟨hs', b⟩ := mixglobB hL W B ρ t i j M hst e Bs Γ X om om' h hT' hti f' g3 ι' h4
  have vA : ∏ w ∈ locPl G t, ιA w (Γ.M.vac _) 0 = ∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0 := Finset.prod_congr rfl fun w hw => by
    have k := GlobalTheory.T.mixedModel_vacuum_eq_integralMatrix_indicator hL W B t i j M hst e Bs Γ X om om' h hT' hti.1 w hw _ (h3 w hw)
    have k2 := fourierSum_ind (A := Fin ((locGrid G t w).rank (i + 1, j + 1))) (psiAt W w)⁻¹ (isUnif_unifAt w)
      (Assignment.one.block (Fin ((locGrid G t w).rank (i, j + 1))) (Fin ((locGrid G t w).rank (i + 1, j))))ᶜ (ι w (Γ.M.vac _) 0)
    rw [← k] at k2
    rw [h5 w hw _ (hT'.geo.hM.vac _).1 0 k2.1, k2.2]
  have vB : ∏ w ∈ locPl G t, ιB w (Γ.M'.vac _) 0 = ∏ w ∈ locPl G t, ι' w (Γ.M'.vac _) 0 := Finset.prod_congr rfl fun w hw => by
    have k := GlobalTheory.T.mixedModel_vacuum_eq_smul_integralMatrix_indicator hL W B t i j M hst e Bs Γ X om om' h hT' hti w hw _ (h4 w hw)
    have k2 := fourierSum_ind (A := Fin ((locGrid G t w).rank (i, j))) (psiAt W w) (isUnif_unifAt w)
      (Assignment.one.block (Fin ((locGrid G t w).rank (i, j + 1))) (Fin ((locGrid G t w).rank (i + 1, j)))) (ι' w (Γ.M'.vac _) 0)
    rw [← k] at k2
    rw [h6 w hw _ (hT'.geo.hM'.vac _).1 0 k2.1, k2.2]
  have la := GlobalTheory.T.negW_local_functions_theta_pure_tensor hL W B t i j M hst e Bs Γ X om om' h hT' hti.1 ρ f
    (datumA_vac ρ i j t ▸ GlobalTheory.SquareIdent.isDatum_of_isDatumA f3) ιA h1
  have lb := GlobalTheory.TopFlip.LinSmall.isDatum_linB hL W B t i j M hst e Bs Γ X om om' h hT' hti ρ f'
    (datumB_vac ρ i j t ▸ GlobalTheory.SquareIdent.isDatum_of_isDatumB g3) ιB h2
  rw [vA] at la
  rw [vB] at lb
  refine ⟨_, rf, rl, p, p', hM', fun ε hε Ξ Ψ u F F' hΞ hF hF' n Φ τ τ' hn ⟨ε', hε', c, d⟩ => ?_⟩
  have hf : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (flipAt W t i j w (n w) (Φ w)) := fun w hw =>
    LocTensor.isNatDatum_flipAt hL W i j hw (notMem_of_standing hst hw) (hn w hw).1 (hn w hw).2
  have hinj : ∀ w ∈ locPl G t, ∀ w' ∈ locPl G t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w = w' :=
    fun w hw w' hw' e => Good.under_injOn hL G t hw hw' e
  obtain ⟨φ, p1, p2⟩ := exists_finPart hT'.geo.hM hti.1.2.2.1 hinj (fun w φ => ι w φ = flipAt W t i j w (n w) (Φ w))
    fun w hw => (h3 w hw).1.2.2 (mem_SB_of_isNatDatum (hf w hw))
  obtain ⟨φ', q1, q2⟩ := exists_finPart hT'.geo.hM' hti.1.2.2.1 hinj (fun w φ => ι' w φ = Φ w)
    fun w hw => (h4 w hw).1.2.2 (mem_SB_of_isNatDatum (hn w hw).2)
  obtain ⟨χ, r1, r2⟩ := exists_finPart hT'.geo.hM hti.1.2.2.1 hinj (fun w φ => ιA w φ = Ξ w)
    fun w hw => (h1 w hw).1.2.2 (hΞ w hw).1
  obtain ⟨χ', s1, s2⟩ := exists_finPart hT'.geo.hM' hti.1.2.2.1 hinj (fun w φ => ιB w φ = Ψ w)
    fun w hw => (h2 w hw).1.2.2 (hΞ w hw).2.1
  have dA := GlobalTheory.SquareIdent.isDatum_of_isDatumA (a ε' hε' n _ τ hf d φ p1 p2)
  have dB := GlobalTheory.SquareIdent.isDatum_of_isDatumB (b ε' hε' n _ τ' (fun w hw => (hn w hw).2) c φ' q1 q2)
  have dF := la ε hε Ξ F hF χ r1 r2
  have dF' := lb ε hε Ψ F' hF' χ' s1 s2
  have gA := isGauss_smul f2 hs
  have gB := isGauss_smul g2 hs'
  have y₀ := pureT_loc hL hm hti.1 r1 s1 (c := fun w => l w * u w) fun w hw =>
    h7 w hw _ (r1.1 _) _ (s1.1 _) _ (by rw [r2 w hw, s2 w hw]; exact (hΞ w hw).2.2)
  have y₁ := pureT_loc hL hm hti.1 p1 q1 (c := fun w => l w * ((levVol G t i j w : ℝ) : ℂ)⁻¹) fun w hw =>
    h7 w hw _ (p1.1 _) _ (q1.1 _) _ (by
      rw [h5 w hw _ (p1.1 _) (n w) (by rw [p2 w hw]; exact hf w hw), h6 w hw _ (q1.1 _) (n w) (by rw [q2 w hw]; exact (hn w hw).2),
        p2 w hw, q2 w hw]
      exact (zeta_flip hL W i j hst hw).2 _ _ (hn w hw).1 (hn w hw).2)
  obtain ⟨_, k1⟩ := HA _ gA 0
  obtain ⟨_, k2⟩ := HB _ gB 0
  refine ⟨(k1 _ r1 _ dF).1, (k2 _ s1 _ dF').1, (k1 _ p1 _ dA).1, (k2 _ q1 _ dB).1, fun P P' g hne hg => ?_⟩
  obtain ⟨x, hx⟩ := HA _ gA P
  obtain ⟨y, hy⟩ := HB _ gB P'
  rw [(hy _ s1 _ dF').2] at hne hg
  rw [(hx _ r1 _ dF).2, y₀] at hg
  rw [(hx _ p1 _ dA).2, (hy _ q1 _ dB).2, y₁]
  generalize (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (χ' v)) = z₀ at hne hg
  generalize (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (φ' v)) = z
  have hz : z₀ ≠ 0 := fun h0 => hne (by rw [h0, TensorProduct.tmul_zero])
  obtain ⟨lz, hlz⟩ := Module.Projective.exists_dual_eq_one ℂ hz
  have e1 : (∏ w ∈ locPl G t, l w * u w) • x = g • y := by
    have := congrArg (TensorProduct.rid ℂ R.Pi ∘ LinearMap.lTensor R.Pi lz) hg
    simpa [hlz] using this
  have hV : ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun w hw => (zeta_flip hL W i j hst hw).1)
  have e2 : (∏ w ∈ locPl G t, u w) * ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ) *
      ∏ w ∈ locPl G t, l w * ((levVol G t i j w : ℝ) : ℂ)⁻¹ = ∏ w ∈ locPl G t, l w * u w := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Complex.ofReal_prod]
    field_simp
  change _ • (x ⊗ₜ[ℂ] (_ • z) : GlobalTheory.TripleAssembly.PiT R Γ Rf) = g • (y ⊗ₜ[ℂ] z : GlobalTheory.TripleAssembly.PiT R Γ Rf)
  rw [TensorProduct.tmul_smul, smul_smul, e2, TensorProduct.smul_tmul', e1, TensorProduct.smul_tmul']
end GlobalTheory.TopFlip
end
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.TopFlip
private theorem away_imaginary_inv {D : D7} {m : ℕ} {z : ℂ} (h : GlobalTheory.KappaArith.AwayIm D m z) : GlobalTheory.KappaArith.AwayIm D m z⁻¹ := by
  obtain ⟨ζ, ⟨a, k, k', ⟨b, hb⟩, ha⟩, rfl⟩ := h
  refine ⟨ζ⁻¹, ?_, map_inv₀ _ _⟩
  by_cases hm : m = 0
  · subst hm
    exact ⟨0, 1, 1, by simp, by simp⟩
  have hm' : (m : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hb' : (m : D.what₂.LL) ^ k' = (a : D.what₂.LL) * (b : D.what₂.LL) := by exact_mod_cast congrArg (fun x : 𝓞 D.what₂.LL => (x : D.what₂.LL)) hb
  have hζ : ζ ≠ 0 := fun h0 => pow_ne_zero k' hm' (by rw [hb', ← ha, h0, zero_mul, zero_mul])
  refine ⟨b * (m : 𝓞 D.what₂.LL) ^ k, k', k' + k, ⟨a, by rw [pow_add, hb]; ring⟩, ?_⟩
  have e : ((b * (m : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) = (b : D.what₂.LL) * (m : D.what₂.LL) ^ k := by push_cast; rfl
  rw [e, hb', ← ha]
  field_simp
private theorem fock_move_relation {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} {A : Fr W}
    {A₁ : Fr W₁} {B : Fr X} {α β : (AE D)ˣ →* Circle} {ωA ωB Pi rf rl p p'} (hm : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p')
    {h : GA D X} (hh : h ∈ GfC X) {f f'} (hf : IsFinF ψ θ true A B f) (hf' : IsFinF ψ θ false A₁ B f') {a b : ℂ} (hb : b ≠ 0)
    {P P'} {g : ℂ} (hne : p' (fockF ψ θ false A₁ B f' P') ≠ 0)
    (hg : p (fockF ψ θ true A B f P) = g • p' (fockF ψ θ false A₁ B f' P')) :
    p' (fockF ψ θ false A₁ B (b⁻¹ • ωB (1, h) f') P') ≠ 0 ∧
      p (fockF ψ θ true A B (a • ωA (1, h) f) P) = (a * g * b) • p' (fockF ψ θ false A₁ B (b⁻¹ • ωB (1, h) f') P') := by
  have mA : fockF ψ θ true A B f P ∈ algF ψ θ true A B := Submodule.subset_span ⟨_, _, hf, rfl⟩
  have mB : fockF ψ θ false A₁ B f' P' ∈ algF ψ θ false A₁ B := Submodule.subset_span ⟨_, _, hf', rfl⟩
  rw [om_fockF hθ A B hm.weilA hh hf, om_fockF hθ A₁ B hm.weilB hh hf', map_smul, map_smul, hm.mapA.eqf h hh _ mA, hg, map_smul,
    hm.mapB.eqf h hh _ mB]
  refine ⟨smul_ne_zero (inv_ne_zero hb) fun h0 => hne ?_, ?_⟩
  · have e := hm.mapB.eqf h⁻¹ (inv_mem hh) _ (hm.mapB.stabX.1 h hh _ mB)
    rw [hm.mapB.eqf h hh _ mB, h0, map_zero, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, one_mul,
      ← Prod.one_eq_mk, map_one, Module.End.one_apply] at e
    exact e
  · rw [smul_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hb, mul_one]
end GlobalTheory.TopFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFlip_involutive_correspondence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (M : Vol G), M.Is t → ∀ s s' : NNReal, M.ν (.grid (i + 1) (j + 1)) = s • X.m → M.ν (.grid i j) = s' • X.m' →
      ∀ Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (X.ω t) (X.ω' t) Pi rf rl p p' →
      ∀ n Φ (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)), (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip S.B t ρ i j n Φ τ τ' →
      ∀ P P' (g : ℂ), p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) P') ≠ 0 →
        p (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P) = g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) P') →
        ((s : ℝ) : ℂ) • p (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) =
          (κ t * ((s' : ℝ) : ℂ) * g) • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') P') := by
  intro hP hK hM
  obtain ⟨F1, H1⟩ := _root_.GlobalTheory.T.theta_parameter_dictionary_bijective hP
  obtain ⟨F2, H2⟩ := _root_.GlobalTheory.T.theta_stage_unique hP hK hM
  refine ⟨max F1 F2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, H1⟩ := H1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, H2⟩ := H2 ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  replace H1 := H1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G
  replace H2 := H2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G
  have hst : ∀ t, SquareStanding G t := fun t => GlobalTheory.ThetaRegularizationComparison.standing hR hR.size.2.1.eleven_le hL G t
  intro W S hψ hN ρ i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  obtain ⟨σ, σ', hσ⟩ := H1 W i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  replace H2 := H2 W i j _ _ _ _ _ X hSC A A₁ (frSum AV AV₁)
  have hIs := hSC.2.2.2.2.2.2.2
  have hrk : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := congrArg (· % 2) (Nat.add_right_cancel hSC.2.2.2.1)
  have eα : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j = Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) := fun t => by
    rw [← hrk]; rfl
  have eβ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) := by
    rw [← hrk]; rfl
  have hI : X.Is W.ψ W.θ (fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (fun t => nuH G t i j)
      (locPl G) := by
    simp only [eα, eβ]
    exact hIs
  obtain ⟨h, hh, cA, cB, y, hcA, hcB, hmv⟩ := GlobalTheory.TopFlip.exists_move hL hst S.B ρ hTG hI hV hV₁
  obtain ⟨x, hx⟩ := GlobalTheory.TopFlip.zeta_std hL W S.B X hst (hTG.1 ▸ hI.rigA.2.1) (hTG.2.1 ▸ hI.rigA'.2.1)
    (by have := hI.rigW.2.1; rwa [hTG.2.2.1] at this)
  obtain ⟨s₀, hs₀, hs⟩ := GlobalTheory.TopFlip.MeasW.exists_ratio (G := G) hL i j X.m hI.meas.1
  obtain ⟨c₁, hc₁, hc⟩ := GlobalTheory.TopFlip.MeasLevel.measure_mul_levVol (G := G) hL hst i j X.m' hI.meas'.1
  set u : T → ℂ := fun t => ∏ w ∈ locPl G t, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) with hu
  have hu0 : ∀ t, u t ≠ 0 := fun t => Finset.prod_ne_zero_iff.2 fun w _ => Units.ne_zero _
  have hξ0 : ∀ t, ((Lc.xi t y : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have hs₀' : ((s₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs₀
  have hc₁' : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁
  refine ⟨fun t => ((s₀ : ℝ) : ℂ) * cA⁻¹ * cB * (c₁ : ℂ)⁻¹ * ((Lc.xi t y : Circle) : ℂ) * (u t)⁻¹, fun t => ⟨?_, ?_⟩, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs₀' (inv_ne_zero hcA)) hcB) (inv_ne_zero hc₁')) (hξ0 t))
      (inv_ne_zero (hu0 t))
  · obtain ⟨z, hz, ez⟩ := GlobalTheory.TopFlipNu.nu_arith hL hN.chars i j x t fun w hw => (hx t w hw).1
    obtain ⟨ζ, h1, h2⟩ := ((GlobalTheory.XiAway.xi_awayIm hL t (hN.chars.xi t) (Qn G t) y).mul
      (GlobalTheory.TopFlip.away_imaginary_inv (GlobalTheory.XiAway.xi_awayIm hL μ₀ (hN.chars.xi μ₀) (Qn G t) y))).mul (GlobalTheory.TopFlip.away_imaginary_inv hz)
    refine ⟨ζ, h1, ?_⟩
    have e : u t = z * u μ₀ := ez
    have := hξ0 μ₀
    dsimp only
    rw [h2, e, mul_inv]
    field_simp
  intro t M hM' s s' es es' Pi rf rl p p' hm n Φ τ τ' hn hfl P P' g hne hg
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, H⟩ := _root_.GlobalTheory.TopFlip.thetaFlip_tuple_match hP hM hL W i j hA hA₁ hV hV₁ t S.B ρ M (hst t) hM'
    (hI.weil t) (hI.weil' t)
  obtain ⟨f1, f2, f3, f4, H⟩ := H _ (hI.idem t) _ _ _ _ _ (fun w hw => (hx t w hw).2) (hmv t).1 (hmv t).2 n Φ τ τ' hn hfl
  obtain ⟨E, c, hc0, eA, eB⟩ := H2 t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' (by rw [← eα, ← eβ]; exact hm₀) (by rw [← eα, ← eβ]; exact hm)
  obtain ⟨k1, k2⟩ := GlobalTheory.TopFlip.fock_move_relation W.θ_is hm hh (hσ t).1 (hσ t).2.1 (a := cA⁻¹) (mul_ne_zero hcB (hξ0 t)) hne hg
  rw [eB _ (Submodule.subset_span ⟨_, _, f2, rfl⟩)] at k1 k2
  rw [eA _ (Submodule.subset_span ⟨_, _, f1, rfl⟩)] at k2
  have k3 := H P P' (c⁻¹ * (cA⁻¹ * g * (cB * ((Lc.xi t y : Circle) : ℂ)))) (fun h0 => k1 (by rw [h0, map_zero]))
    (E.injective (by rw [map_smul, mul_smul, ← k2, smul_smul, inv_mul_cancel₀ hc0, one_smul]))
  rw [eA _ (Submodule.subset_span ⟨_, _, f3, rfl⟩), eB _ (Submodule.subset_span ⟨_, _, f4, rfl⟩)]
  have e1 : s = s₀ := hs t M hM' s es
  have e2 : ((s' : ℝ) : ℂ) * ((∏ w ∈ locPl G t, GlobalTheory.TopFlip.levVol G t i j w : ℝ) : ℂ) = c₁ := by exact_mod_cast hc t M hM' s' es'
  have k4 := congrArg E k3
  rw [map_smul, map_smul] at k4
  change (u t * _) • _ = _ at k4
  generalize ((∏ w ∈ locPl G t, GlobalTheory.TopFlip.levVol G t i j w : ℝ) : ℂ) = V at e2 k4
  have hV0 : V ≠ 0 := fun h0 => hc₁' (by rw [← e2, h0, mul_zero])
  have hs' : ((s' : ℝ) : ℂ) ≠ 0 := fun h0 => hc₁' (by rw [← e2, h0, zero_mul])
  have := hu0 t
  rw [(eq_inv_smul_iff₀ (mul_ne_zero this hV0)).2 k4, smul_smul, smul_smul, smul_smul, e1, ← e2]
  congr 1
  field_simp
end
