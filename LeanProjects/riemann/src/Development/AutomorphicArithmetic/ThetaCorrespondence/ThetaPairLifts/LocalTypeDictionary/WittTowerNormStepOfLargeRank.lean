import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepFirst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.QuadraticTowerLargeStepStageDictionary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsQuadraticTowerStage
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerStageNormFactorization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DivisibilityAlongQuadraticTower
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealEmbeddingsOfCharactersOfSameExponent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilRepresentationRealization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepFirstStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepBig
open GlobalTheory.Square
end GlobalTheory.SqStepBig
end
noncomputable section
namespace GlobalTheory.SqStepBig
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LFun
section IndefiniteRowSideFullHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem theta_tower_step_exists_triple (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} (hB : B.IsGood σ) {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {X : Chars F E}
    (c : X.IsGood B a a') : ∃ om om', IsTriple B Γ X om om' := by
  have hd : ∀ {χ χ' : Chr F E}, IsHecke F E χ → IsHecke F E χ' → IsHecke F E (χ / χ') := fun h h' =>
    ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]⟩
  obtain ⟨om, hom⟩ := _root_.GlobalTheory.WeilExGen.exists_weil_representation_realization hP F E σ B hB a (a + a') Γ.V Γ.W _ _ _ _ g.hV g.hW Γ.M g.hM X.β (X.β / X.α)
    c.heckeβ (hd c.heckeβ c.heckeα) c.resβ (resEtaPow_quot c.resβ c.resα)
  obtain ⟨om', hom'⟩ := _root_.GlobalTheory.WeilExGen.exists_weil_representation_realization hP F E σ B hB a' (a + a') Γ.V' Γ.W _ _ _ _ g.hV' g.hW Γ.M' g.hM' X.α (X.α / X.β)
    c.heckeα (hd c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_quot c.resα c.resβ)
  exact ⟨om, om', hB, g, c, hom, hom'⟩
theorem exists_pivot_pair (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩
theorem theta_tower_step_pair_real_part (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} (hB : B.IsGood σ)
    {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {Xa Xb : Chars F E} (xa : Xa.IsGood B a a') (xb : Xb.IsGood B a a') {la lb : ℂ}
    (H : ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), IsMatched B Γ Xa om om' R Rf → IsMatched B Γ Xb om₀ om₀' R Rf₀ →
      IsConst B Γ Xa om om' R Rf c → IsConst B Γ Xb om₀ om₀' R Rf₀ c₀ →
      ∃ k : (AE F E)ˣ, c * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (c₀ * la))
    {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')} (g₂ : (reG Γ V V' Z).IsGood B) :
    ∃ oa oa' ob ob' R Ra Rb da db, IsMatched B (reG Γ V V' Z) Xa oa oa' R Ra ∧ IsMatched B (reG Γ V V' Z) Xb ob ob' R Rb ∧
      IsConst B (reG Γ V V' Z) Xa oa oa' R Ra da ∧ IsConst B (reG Γ V V' Z) Xb ob ob' R Rb db ∧ db ≠ 0 ∧
      ∃ k : (AE F E)ˣ, da * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * la) := by
  obtain ⟨oa, oa', ha⟩ := _root_.GlobalTheory.SqStepBig.theta_tower_step_exists_triple hP hB g xa
  obtain ⟨ob, ob', hb⟩ := _root_.GlobalTheory.SqStepBig.theta_tower_step_exists_triple hP hB g xb
  have ha₂ : IsTriple B (reG Γ V V' Z) Xa oa oa' := ⟨hB, g₂, xa, ha.weil, ha.weil'⟩
  have hb₂ : IsTriple B (reG Γ V V' Z) Xb ob ob' := ⟨hB, g₂, xb, hb.weil, hb.weil'⟩
  obtain ⟨R, Ra, Rb, ca, cb, m1, m2, k1, k2, hcb⟩ := _root_.GlobalTheory.SqStepBig.exists_pivot_pair hP hK hM ha hb
  obtain ⟨R₂, Sa, Sb, da, db, n1, n2, l1, l2, hdb⟩ := _root_.GlobalTheory.SqStepBig.exists_pivot_pair hP hK hM ha₂ hb₂
  obtain ⟨k, hk⟩ := H R oa oa' Ra ob ob' Rb ca cb m1 m2 k1 k2
  obtain ⟨k', hk'⟩ := _root_.GlobalTheory.T.divisibility_along_quadratic_tower hP hK hM F E σ B a a' Γ V V' Z Xa Xb R R₂ oa ob oa' ob' Ra Rb Sa Sb ca cb da db
    m1 m2 n1 n2 k1 k2 l1 l2
  refine ⟨oa, oa', ob, ob', R₂, Sa, Sb, da, db, n1, n2, l1, l2, hdb, k * k', mul_left_cancel₀ hcb ?_⟩
  have e : ((Xa.ν (k * k') / Xb.ν (k * k') : Circle) : ℂ) =
      ((Xa.ν k / Xb.ν k : Circle) : ℂ) * ((Xa.ν k' / Xb.ν k' : Circle) : ℂ) := by
    rw [map_mul, map_mul, ← div_mul_div_comm, Circle.coe_mul]
  rw [e]
  linear_combination lb * hk' + ((Xa.ν k' / Xb.ν k' : Circle) : ℂ) * db * hk
end IndefiniteRowSideFullHecke
theorem theta_tower_step_norm_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (C : ℂ) (ζ : D.what₂.LL),
          GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
          lam t = C * D.what₂.embLL ζ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) *
            GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) * c t ∧
          lam μ₀ = C * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) *
            GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) * c μ₀ := by
  intro hP hK hM
  refine gbig_of_three (gbig_both GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage (_root_.GlobalTheory.T.tower_stage_fit_factor_alt hP hK hM)) (gbig_both (_root_.GlobalTheory.T.quadratic_tower_exists hP) GlobalTheory.T.squareNu_ratio_values_roots_of_unity)
    (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) ?_
  rintro D T Lc sc G μ₀ C x b ⟨qb, qd⟩ ⟨qs, qx⟩ qf W S hψ hN i j p A A' WW X lam e hX hF he
  obtain ⟨e₁, e₂, s, hα⟩ := hK.2.2
  obtain ⟨emb, hemb⟩ := qb W hψ i j _ _ A A' WW X hX
  obtain ⟨B₀, he₀, f₀⟩ := hemb μ₀
  obtain ⟨Γ₀, o₀, p₀, q₀, g₀, -⟩ := qd W hψ i j _ _ A A' WW X lam μ₀ B₀ hX hF f₀
  have b1 := g₀.eBig
  have b2 := g₀.aBig
  have b3 := g₀.lt
  have hV₀ := g₀.hV
  have hW₀ := g₀.hW
  rw [p₀, q₀] at b1 b2 hW₀
  rw [p₀] at hV₀
  obtain ⟨n, hn⟩ : ∃ n, A.rank = n + 2 := ⟨A.rank - 2, by omega⟩
  obtain ⟨Y', V₁, H₀, hY', hV₁, hH₀⟩ := GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace _ _ _ B₀ f₀.2.1 A.rank n hn (by omega) Γ₀.V _ _ (by omega) (by omega) hV₀
    0 (n + 1) (by omega) (by omega)
  obtain ⟨Z', W₁, H₀', hZ', hW₁, hH₀'⟩ := GlobalTheory.T.skewHermitian_selfDual_lattice_hyperbolic_plane_splitting _ _ _ B₀ f₀.2.1 (A.rank + A'.rank) (n + A'.rank) (by omega) (by omega) Γ₀.W
    _ _ (by omega) (by omega) hW₀ 0 (n + 1) (by omega) (by omega)
  obtain ⟨B, ΛB, sB, nB, oB⟩ := GlobalTheory.T.exists_selfDual_orientedModel_conjugate_hermitian D B₀ f₀.2.1 f₀.2.2.1 n _ _ V₁ hV₁
  obtain ⟨WW₁, ΛW, sW, nW, oW⟩ := GlobalTheory.T.exists_selfDual_orientedModel_scaled_skewHermitian D B₀ f₀.2.1 f₀.2.2.1 _ _ _ W₁ hW₁
  obtain rfl : n = B.rank := oB.1.symm
  obtain ⟨s1, s2, s3, s4, -, s6, -, s8⟩ := id hX
  obtain ⟨Y, hY, y1, y2, y3⟩ := qs W hψ i j p 0 B A' WW₁ ΛB X.rA'.Λ ΛW sB s8.rigA'.1 sW (by omega) s2 (by omega) s4
    (by simpa using nB) s6 (by simpa using nW) oW.1.symm
  obtain ⟨c, hc⟩ := qf W S hψ hN i j p 0 B A' WW₁ Y hY
  haveI : Nonempty T := ⟨μ₀⟩
  refine ⟨B, A', WW₁, Y, c, hY, hc.isConst, fun t => ?_⟩
  obtain ⟨Bs, hes, f⟩ := hemb t
  have hee : Bs.emb = B₀.emb := hes.trans he₀.symm
  have f₁ : Fit G W i j t μ₀ Bs B.rank A'.rank := Fit.down_left (hn ▸ f)
  obtain ⟨Γ, o, pΓ, qΓ, g, HX⟩ := qd W hψ i j _ _ A A' WW X lam t Bs hX hF f
  obtain ⟨Γ₁, o₁, pΓ₁, qΓ₁, g₁, HY⟩ := qd W hψ i j _ _ B A' WW₁ Y c t Bs hY hc f₁
  obtain ⟨U, U₁, H, u1, u2, u3, u4, hH⟩ := GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis _ _ _ f.2.1.cm B₀ Bs hee _ _ _ V₁ H₀ 0 (B.rank + 1) (by omega) (by omega)
    hY'.lat hV₁.lat hH₀
  obtain ⟨Z, Z₁, H', z1, z2, z3, z4, hH'⟩ := GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis _ _ _ f.2.1.cm B₀ Bs hee _ _ _ W₁ H₀' 0 (B.rank + 1) (by omega) (by omega)
    hZ'.lat hW₁.lat hH₀'
  have eV : reS Γ.V U = reS (reS Γ₀.V Y') U := reS_congr U (o₀.1.eq o.1)
  have eW : reS Γ.W Z = reS (reS Γ₀.W Z') Z := reS_congr Z (o₀.2.2.eq o.2.2)
  have eV₁ : reS Γ₁.V U₁ = reS V₁ U₁ := reS_congr U₁ (oB.eq (y1 ▸ o₁.1))
  have eW₁ : reS Γ₁.W Z₁ = reS W₁ Z₁ := reS_congr Z₁ (oW.eq (y3 ▸ o₁.2.2))
  have eV' : reS Γ₁.V' Γ.V' = reS Γ.V' Γ.V' := reS_congr Γ.V' (o.2.1.eq (y2 ▸ o₁.2.1))
  have hV' : (reS Γ.V' Γ.V').IsHerm D.sp.cm.sig Bs Γ.q (A'.rank - Γ.q) := g.hV'
  have g₂ : (reG Γ U Γ.V' Z).IsGood Bs := isGood_reG g (by rw [eV, pΓ]; exact isHerm_rebase hee hY' u1 u3) hV'
    (by rw [eW, pΓ, qΓ]; exact isSkew_rebase hee hZ' z1 z3)
  have g₃ : (reG Γ₁ U₁ Γ.V' Z₁).IsGood Bs := by
    refine isGood_reG g₁ ?_ (by rw [eV', qΓ₁, ← qΓ]; exact hV') ?_
    · rw [eV₁, pΓ₁]
      convert isHerm_rebase hee hV₁ u2 u4 using 1 <;> omega
    · rw [eW₁, pΓ₁, qΓ₁]
      convert isSkew_rebase hee hW₁ z2 z4 using 1 <;> omega
  obtain ⟨oa, oa', ob, ob', R, Ra, Rb, da, db, m1, m2, k1, k2, hdb, k, hk⟩ :=
    _root_.GlobalTheory.SqStepBig.theta_tower_step_pair_real_part hP hK hM f.2.1 g f.2.2.2.1 f.2.2.2.2.1 HX g₂
  obtain ⟨pa, pa', pb, pb', R₁, Sa, Sb, ca, cb, n1, n2, l1, l2, hcb, k', hk'⟩ :=
    _root_.GlobalTheory.SqStepBig.theta_tower_step_pair_real_part hP hK hM f.2.1 g₁ f₁.2.2.2.1 f₁.2.2.2.2.1 HY g₃
  obtain ⟨C₀, -, HC⟩ := stepAlpha_cast (hα _ _ D.sp.cm.sig) Bs hn he (reG Γ U Γ.V' Z) (reG Γ₁ U₁ Γ.V' Z₁) H H' R R₁ eV' qΓ qΓ₁
    (by show Γ₁.p + 1 = Γ.p; rw [pΓ, pΓ₁]) (by show H.IsAdapted _ _ (reS Γ.V U) (reS Γ₁.V U₁) _ _; rw [eV, eV₁]; exact hH)
    (by show H'.IsAdapted _ _ (reS Γ.W Z) (reS Γ₁.W Z₁) _ _; rw [eW, eW₁]; exact hH')
  have E1 := HC _ _ _ _ _ _ _ m1 n1 _ _ k1 l1
  have E0 := HC _ _ _ _ _ _ _ m2 n2 _ _ k2 l2
  obtain ⟨ζ, hζ, eζ⟩ := qx W S hN i j t k
  obtain ⟨ζ', hζ', eζ'⟩ := qx W S hN i j t k'
  have hz : D.what₂.embLL ζ ≠ 0 := eζ ▸ Circle.coe_ne_zero _
  have hz0 : ζ ≠ 0 := fun h => hz (by rw [h, map_zero])
  rw [eζ] at hk
  rw [eζ'] at hk'
  have hc0 := hc.1 μ₀
  refine ⟨Bs, e₁, e₂, s, H.𝔟, H'.𝔟, C₀ * lam μ₀ * cb / (db * c μ₀), ζ' * ζ⁻¹, f.1, hζ'.mul (awayUnit_inv hz0 hζ), ?_, ?_⟩
  · change da = _ * _ * charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ * _ at E1
    rw [map_mul, map_inv₀]
    generalize stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) = u at E1 ⊢
    generalize charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) = L at E1 ⊢
    field_simp
    linear_combination (-c μ₀) * hk + lam μ₀ * c μ₀ * E1 + C₀ * u * L * lam μ₀ * hk'
  · change db = _ * _ * charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ * _ at E0
    generalize stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) = u at E0 ⊢
    generalize charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) = L at E0 ⊢
    field_simp
    linear_combination lam μ₀ * E0
end GlobalTheory.SqStepBig
end
noncomputable section
namespace GlobalTheory.SqStepBig
open GlobalTheory.Square
theorem theta_tower_norm_step_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  intro hP hK hM
  refine gbig_of_three (_root_.GlobalTheory.SqStepBig.theta_tower_step_norm_identity hP hK hM) GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient GlobalTheory.T.partialHeckeLFunction_square_eq_primitive ?_
  intro D T Lc sc G μ₀ C x b q1 q2 q3 W S hψ hN i j p A A' WW X lam e Lf hX hF he hL
  obtain ⟨B, B', WW₁, Y, c, hY, hc, H⟩ := q1 W S hψ hN i j p A A' WW X lam e hX hF he
  have he2 := two_le_half hX he
  have hlam := hF.1
  have hne : ∀ t, Lf t e * c t ≠ 0 := fun t => by
    obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, C', ζ, -, -, et, -⟩ := H t
    rw [q3 i j t e (Lf t) he2 (hL t)] at et
    have h := hlam t
    rw [et] at h
    exact mul_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul h)) (right_ne_zero_of_mul h)
  refine ⟨B, B', WW₁, Y, c, fun t => lam t / (Lf t e * c t), hY, hc, fun t => ⟨div_ne_zero (hlam t) (hne t), ?_⟩, fun t => ?_⟩
  · rw [mul_assoc, div_mul_cancel₀ _ (hne t)]
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, C', ζ, hB, hζ, et, e0⟩ := H t
    rw [q3 i j t e (Lf t) he2 (hL t)] at et
    rw [q3 i j μ₀ e (Lf μ₀) he2 (hL μ₀)] at e0
    have ht := hlam t
    have h0 := hlam μ₀
    rw [et] at ht
    rw [e0] at h0
    have key := stepRatio_swap (C := C') (q2 W S hψ hN i j t Bs e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) hB
      (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul ht))))
      (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h0))) hζ
    beta_reduce
    rw [et, e0, mul_assoc _ (Lf t e), mul_assoc _ (Lf μ₀ e), mul_div_cancel_right₀ _ (hne t),
      mul_div_cancel_right₀ _ (hne μ₀)]
    exact key
end GlobalTheory.SqStepBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.witt_tower_norm_step_of_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  first | exact @_root_.GlobalTheory.SqStepBig.theta_tower_norm_step_large_rank | exact _root_.GlobalTheory.SqStepBig.theta_tower_norm_step_large_rank | (intros; apply _root_.GlobalTheory.SqStepBig.theta_tower_norm_step_large_rank <;> assumption)
end
