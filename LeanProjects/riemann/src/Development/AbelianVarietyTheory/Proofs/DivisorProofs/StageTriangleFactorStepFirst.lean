import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingsSharedBaseTowerStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFitFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTripleCoherence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedHyperbolicPlaneRescaleRebasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelConjugateHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelScaledSkewHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidificationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuRatioValuesRootsOfUnity

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

theorem awayUnit_inv {K : Type} [Field K] {m : ℕ} {x : K} (hx : x ≠ 0) (h : IsAwayUnit m x) : IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨b, hb⟩, hxa⟩ := h
  refine ⟨(m : 𝓞 K) ^ k * b, k', k + k', ?_, ?_⟩
  · rw [pow_add, hb]
    exact mul_dvd_mul_left _ (dvd_mul_left _ _)
  · have hb' : (m : K) ^ k' = (a : K) * (b : K) := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) hb
    have : ((((m : 𝓞 K) ^ k * b : 𝓞 K)) : K) = (m : K) ^ k * (b : K) := by push_cast; ring
    rw [this, hb', ← hxa]
    field_simp

theorem stepRatio_swap {K P : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {m : ℕ} {S₀ : Finset P} {cc qq : P → ℕ} {u u₀ C : ℂ} {ζ : K}
    (h : StepRatio σ m S₀ cc qq u₀ u) (h0 : u₀ ≠ 0) (hζ : IsAwayUnit m ζ) :
    StepRatio σ m S₀ cc qq (C * σ ζ * u) (C * u₀) := by
  obtain ⟨b, g, g', hb, hg, e⟩ := h
  have h1 : b * ∏ v ∈ S₀, (g v : K) / (g' v : K) ≠ 0 := fun hz => h0 (by rw [e, hz, map_zero, zero_mul])
  refine ⟨ζ * b⁻¹, g', g, hζ.mul (awayUnit_inv (left_ne_zero_of_mul h1) hb), fun v hv => (hg v hv).symm, ?_⟩
  have h2 : ∏ v ∈ S₀, (g' v : K) / (g v : K) = (∏ v ∈ S₀, (g v : K) / (g' v : K))⁻¹ := by
    rw [← Finset.prod_inv_distrib]; simp only [inv_div]
  have h3 : σ (b * ∏ v ∈ S₀, (g v : K) / (g' v : K)) ≠ 0 := (map_ne_zero σ).2 h1
  rw [h2, mul_assoc ζ, ← mul_inv, map_mul, map_inv₀, e]
  field_simp

theorem gbig_of_three {Q1 Q2 Q3 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2) (h3 : GBig Q3)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q3 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  refine ⟨max a1 (max a2 a3), fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨c3, x3, g3⟩ := h3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max c1 (max c2 c3), max x1 (max x2 x3), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ hε
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hμ G
  · exact g3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ hε
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hμ G

theorem two_le_half {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {p q e : ℕ} {A A' WW : HSp D} {X : Tri T A A' WW} (h : GlobalTheory.SqTower.IsStageC W i j p q X)
    (he : A.rank = A'.rank + 2 * e) : 2 ≤ e := by
  obtain ⟨hp, hq, hA, hA', -⟩ := h
  obtain ⟨k, hk⟩ := D.R.k_even
  obtain ⟨m, hm⟩ := D.R.m_even
  obtain ⟨t, ht⟩ := D.R.t_odd
  have h2 := D.R.two_le_m
  have h3 := D.R.three_m_lt_t
  have e1 : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have e2 : sLen D = D.R.k + D.R.m - 1 + 6 := rfl
  simp only [pp, qq] at *
  omega

end GlobalTheory.SqStepBig

end

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LFun

section IndefiniteRowSideFullHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem reS_congr {n : ℕ} {X X₂ : Spc F E n} (Y : Spc F E n) (h : X₂.J = X.J ∧ X₂.L = X.L) : reS X₂ Y = reS X Y := by
  cases X; cases X₂; obtain ⟨h1, h2⟩ := h; cases h1; cases h2; rfl

theorem isHerm_rebase {B₀ B : Base F E} (he : B.emb = B₀.emb) {n r s : ℕ} {Y Y' : Spc F E n} (h : Y.IsHerm σ B₀ r s)
    (hθ : Y'.θ = Y.θ) (hb : ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) : (reS Y Y').IsHerm σ B r s :=
  { herm := h.herm, sig := fun w => by rw [he]; exact h.sig w, lat := h.lat, dual := h.dual
    cartan := fun w => by rw [he]; show IsCartan _ (Y'.θ w); rw [hθ]; exact h.cartan w
    bas := hb }

theorem isSkew_rebase {B₀ B : Base F E} (he : B.emb = B₀.emb) {n r s : ℕ} {Y Y' : Spc F E n} (h : Y.IsSkew σ B₀ r s)
    (hθ : Y'.θ = Y.θ) (hb : ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) : (reS Y Y').IsSkew σ B r s :=
  { skew := h.skew, sig := fun w => by rw [he]; exact h.sig w, lat := h.lat, dual := h.dual
    cartan := fun w => by rw [he]; show IsCartan _ (Y'.θ w); rw [hθ]; exact h.cartan w
    bas := hb }

theorem isGood_reG {B : Base F E} {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {V : Spc F E a} {V' : Spc F E a'}
    {Z : Spc F E (a + a')} (hV : (reS Γ.V V).IsHerm σ B (a - Γ.p) Γ.p) (hV' : (reS Γ.V' V').IsHerm σ B Γ.q (a' - Γ.q))
    (hZ : (reS Γ.W Z).IsSkew σ B (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) : (reG Γ V V' Z).IsGood B :=
  ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hZ, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
    ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩

theorem resEtaPow_quot {R K' : Type} [CommRing R] [CommRing K'] [Algebra R K'] {K : Subgroup Rˣ}
    {χ χ' : K'ˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem exists_isTriple (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} (hB : B.IsGood σ) {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {X : Chars F E}
    (c : X.IsGood B a a') : ∃ om om', IsTriple B Γ X om om' := by
  have hd : ∀ {χ χ' : Chr F E}, IsHecke F E χ → IsHecke F E χ' → IsHecke F E (χ / χ') := fun h h' =>
    ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]⟩
  obtain ⟨om, hom⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hB a (a + a') Γ.V Γ.W _ _ _ _ g.hV g.hW Γ.M g.hM X.β (X.β / X.α)
    c.heckeβ (hd c.heckeβ c.heckeα) c.resβ (resEtaPow_quot c.resβ c.resα)
  obtain ⟨om', hom'⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hB a' (a + a') Γ.V' Γ.W _ _ _ _ g.hV' g.hW Γ.M' g.hM' X.α (X.α / X.β)
    c.heckeα (hd c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_quot c.resα c.resβ)
  exact ⟨om, om', hB, g, c, hom, hom'⟩

theorem exists_pair (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, GlobalTheory.T.real_maps_two_triples_agree hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩

theorem pair_reG (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} (hB : B.IsGood σ)
    {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {Xa Xb : Chars F E} (xa : Xa.IsGood B a a') (xb : Xb.IsGood B a a') {la lb : ℂ}
    (H : ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), IsMatched B Γ Xa om om' R Rf → IsMatched B Γ Xb om₀ om₀' R Rf₀ →
      IsConst B Γ Xa om om' R Rf c → IsConst B Γ Xb om₀ om₀' R Rf₀ c₀ →
      ∃ k : (AE F E)ˣ, c * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (c₀ * la))
    {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')} (g₂ : (reG Γ V V' Z).IsGood B) :
    ∃ oa oa' ob ob' R Ra Rb da db, IsMatched B (reG Γ V V' Z) Xa oa oa' R Ra ∧ IsMatched B (reG Γ V V' Z) Xb ob ob' R Rb ∧
      IsConst B (reG Γ V V' Z) Xa oa oa' R Ra da ∧ IsConst B (reG Γ V V' Z) Xb ob ob' R Rb db ∧ db ≠ 0 ∧
      ∃ k : (AE F E)ˣ, da * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * la) := by
  obtain ⟨oa, oa', ha⟩ := exists_isTriple hP hB g xa
  obtain ⟨ob, ob', hb⟩ := exists_isTriple hP hB g xb
  have ha₂ : IsTriple B (reG Γ V V' Z) Xa oa oa' := ⟨hB, g₂, xa, ha.weil, ha.weil'⟩
  have hb₂ : IsTriple B (reG Γ V V' Z) Xb ob ob' := ⟨hB, g₂, xb, hb.weil, hb.weil'⟩
  obtain ⟨R, Ra, Rb, ca, cb, m1, m2, k1, k2, hcb⟩ := exists_pair hP hK hM ha hb
  obtain ⟨R₂, Sa, Sb, da, db, n1, n2, l1, l2, hdb⟩ := exists_pair hP hK hM ha₂ hb₂
  obtain ⟨k, hk⟩ := H R oa oa' Ra ob ob' Rb ca cb m1 m2 k1 k2
  obtain ⟨k', hk'⟩ := GlobalTheory.T.real_maps_triple_coherence hP hK hM F E σ B a a' Γ V V' Z Xa Xb R R₂ oa ob oa' ob' Ra Rb Sa Sb ca cb da db
    m1 m2 n1 n2 k1 k2 l1 l2
  refine ⟨oa, oa', ob, ob', R₂, Sa, Sb, da, db, n1, n2, l1, l2, hdb, k * k', mul_left_cancel₀ hcb ?_⟩
  have e : ((Xa.ν (k * k') / Xb.ν (k * k') : Circle) : ℂ) =
      ((Xa.ν k / Xb.ν k : Circle) : ℂ) * ((Xa.ν k' / Xb.ν k' : Circle) : ℂ) := by
    rw [map_mul, map_mul, ← div_mul_div_comm, Circle.coe_mul]
  rw [e]
  linear_combination lb * hk' + ((Xa.ν k' / Xb.ν k' : Circle) : ℂ) * db * hk

theorem stepAlpha_cast {e₁ e₂ s : ℤˣ} (h : StepAlpha σ e₁ e₂ s) (B : Base F E) {a b a' e : ℕ} (hab : a = b + 2)
    (he : a = a' + 2 * e) (Γ : Geo σ a a') (Γ₁ : Geo σ b a') (H : Plane E a b) (H' : Plane E (a + a') (b + a'))
    (R : RealMaps F a a') (R₁ : RealMaps F b a') (h1 : Γ₁.V' = Γ.V') (h2 : Γ.q = 0) (h3 : Γ₁.q = 0) (h4 : Γ₁.p + 1 = Γ.p)
    (h5 : H.IsAdapted σ B Γ.V Γ₁.V 0 (b + 1)) (h6 : H'.IsAdapted σ B Γ.W Γ₁.W 0 (b + 1)) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B Γ X om om' R Rf → IsMatched B Γ₁ X om₁ om₁' R₁ Rf₁ →
      ∀ c c₁, IsConst B Γ X om om' R Rf c → IsConst B Γ₁ X om₁ om₁' R₁ Rf₁ c₁ →
        c = C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) * charL X.ν (X.S₀ : Set (Pl F)) (e : ℂ) * c₁ := by
  subst hab
  have := h B b a' Γ Γ₁ H H' R R₁ h1 h2 h3 h4 h5 h6
  rwa [show (b + 2 - a') / 2 = e by omega] at this

end IndefiniteRowSideFullHecke

theorem gbig_both {Q₁ Q₂ : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) : GBig fun G μ C x b => Q₁ G μ C x b ∧ Q₂ G μ C x b :=
  gbig_of_three h₁ h₂ h₂ fun _ _ _ _ _ a b _ => ⟨a, b⟩

theorem step_identity : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
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
  refine gbig_of_three (gbig_both GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage (GlobalTheory.T.tower_stage_fit_factor hP hK hM)) (gbig_both (GlobalTheory.T.self_dual_lattice_rank_bound hP) GlobalTheory.T.squareNu_ratio_values_roots_of_unity)
    (GlobalTheory.T.exists_factor_of_stage_triangle hP hK hM) ?_
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
    pair_reG hP hK hM f.2.1 g f.2.2.2.1 f.2.2.2.2.1 HX g₂
  obtain ⟨pa, pa', pb, pb', R₁, Sa, Sb, ca, cb, n1, n2, l1, l2, hcb, k', hk'⟩ :=
    pair_reG hP hK hM f.2.1 g₁ f₁.2.2.2.1 f₁.2.2.2.2.1 HY g₃
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

theorem towerStep_big : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  intro hP hK hM
  refine gbig_of_three (step_identity hP hK hM) GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient GlobalTheory.T.partialHeckeLFunction_square_eq_primitive ?_
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
