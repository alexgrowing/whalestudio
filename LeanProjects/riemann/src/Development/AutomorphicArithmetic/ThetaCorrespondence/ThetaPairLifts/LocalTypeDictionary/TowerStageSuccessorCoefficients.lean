import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSuccessorCoefficients
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.QuadraticTowerLargeStepStageDictionary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerNormStepOfLargeRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSuccessorCoefficientsStatement

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
namespace GlobalTheory.HermitianSkewAdaptation
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (IsSplitBasis)
open scoped Matrix
section Planes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
end Planes
section Transport
open GlobalTheory.SqStepK GlobalTheory.SqStepBig
variable {D : D7}
end Transport
section Cast
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem const_pair_alt (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} (hB : B.IsGood σ)
    {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {Xa Xb : Chars F E} (xa : Xa.IsGood B a a') (xb : Xb.IsGood B a a') {la lb : ℂ}
    (hlb : lb ≠ 0)
    (H : ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), IsMatched B Γ Xa om om' R Rf → IsMatched B Γ Xb om₀ om₀' R Rf₀ →
      IsConst B Γ Xa om om' R Rf c → IsConst B Γ Xb om₀ om₀' R Rf₀ c₀ →
      ∃ k : (AE F E)ˣ, c * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (c₀ * la))
    {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')} (g₂ : (reG Γ V V' Z).IsGood B) :
    ∃ (R : RealMaps F a a') (d : ℂ) (k : (AE F E)ˣ), d ≠ 0 ∧
      GlobalTheory.SqStepK.HasConstR B (reG Γ V V' Z) R Xa (d * ((Xa.ν k / Xb.ν k : Circle) : ℂ) * la) ∧
      GlobalTheory.SqStepK.HasConstR B (reG Γ V V' Z) R Xb (d * ((Xb.ν k / Xb.ν k : Circle) : ℂ) * lb) := by
  obtain ⟨oa, oa', ob, ob', R, Ra, Rb, da, db, m1, m2, k1, k2, hdb, k, hk⟩ := _root_.GlobalTheory.SqStepBig.theta_tower_step_pair_real_part hP hK hM hB g xa xb H g₂
  refine ⟨R, db / lb, k, div_ne_zero hdb hlb, ⟨oa, oa', Ra, m1, ?_⟩, ⟨ob, ob', Rb, m2, ?_⟩⟩
  · convert k1 using 1
    field_simp
    linear_combination -hk
  · convert k2 using 1
    rw [div_self', Circle.coe_one, mul_one, div_mul_cancel₀ _ hlb]
end Cast
open GlobalTheory.SqStepBig in
theorem tower_stage_successor_relation_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
      (Y : Tri T A B' WW₁) (lam c : T → ℂ) (e : ℕ), GlobalTheory.SqTower.IsStageC W i j p (q + 1) X →
      GlobalTheory.SqTower.IsStageC W i j p q Y → GlobalTheory.SqStepK.IsStepB X Y → Factor X W.ψ W.θ lam → Factor Y W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (b : ℕ)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank (b + 2)) (Γ₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank b)
        (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (b + 2) b) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (A.rank + (b + 2)) (A.rank + b))
        (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank (b + 2)) (R₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank b) (d d₁ : ℂ)
        (k k₁ : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ),
        GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ A'.rank = b + 2 ∧ Γ₁.V = Γ.V ∧ Γ₁.p = Γ.p ∧ Γ₁.q + 1 = Γ.q ∧
        H.IsAdapted D.sp.cm.sig Bs Γ.V' Γ₁.V' 0 (b + 1) ∧ H'.IsAdapted D.sp.cm.sig Bs Γ.W Γ₁.W A.rank (A.rank + b + 1) ∧
        d ≠ 0 ∧ d₁ ≠ 0 ∧ ∀ t' ∈ ({t, μ₀} : Set T),
          GlobalTheory.SqStepK.HasConstR Bs Γ R (GlobalTheory.SqStep.chs G i j t')
            (d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t') ∧
          GlobalTheory.SqStepK.HasConstR Bs Γ₁ R₁ (GlobalTheory.SqStep.chs G i j t')
            (d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t') := by
  intro hP hK hM
  refine gbig_of_three GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage (_root_.GlobalTheory.T.tower_stage_fit_factor_alt hP hK hM) GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage ?_
  rintro D T Lc sc G μ₀ C x b qb qd - W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY ⟨hA, ⟨ι, x, y, hs⟩, ι', x', y', hs'⟩ hF hc he t
  obtain ⟨emb, hemb⟩ := qb W hψ i j _ _ A A' WW X hX
  obtain ⟨Bs, -, f⟩ := hemb t
  have hn : A'.rank = B'.rank + 2 := hs.1
  have f₁ : Fit G W i j t μ₀ Bs A.rank B'.rank := Fit.down_right (hn ▸ f)
  obtain ⟨Γ, o, pΓ, qΓ, g, HX⟩ := qd W hψ i j _ _ A A' WW X lam t Bs hX hF f
  obtain ⟨Γ₁, o₁, pΓ₁, qΓ₁, g₁, HY⟩ := qd W hψ i j _ _ A B' WW₁ Y c t Bs hY hc f₁
  obtain ⟨U, H, hU, hH⟩ := plane_herm f.2.1 hs (neg_ne_zero.2 one_ne_zero) o.2.1 o₁.2.1 g.hV' g₁.hV' (i₀ := 0) (i₁ := B'.rank + 1)
    (by omega) (by omega)
  obtain ⟨Z, H', hZ, hH'⟩ := plane_skew f.2.1 hs' o.2.2 o₁.2.2 g.hW g₁.hW (i₀ := A.rank) (i₁ := A.rank + B'.rank + 1)
    (by omega) (by omega)
  have eV : reS Γ₁.V Γ.V = reS Γ.V Γ.V := reS_congr Γ.V (o.1.eq (hA ▸ o₁.1))
  have hV : (reS Γ.V Γ.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p := g.hV
  have g₂ : (reG Γ Γ.V U Z).IsGood Bs := isGood_reG g hV hU hZ
  have g₃ : (reG Γ₁ Γ.V Γ₁.V' Γ₁.W).IsGood Bs := isGood_reG g₁ (by rw [eV, pΓ₁, ← pΓ]; exact hV) g₁.hV' g₁.hW
  obtain ⟨R, d, k, hd, c1, c2⟩ := _root_.GlobalTheory.HermitianSkewAdaptation.const_pair_alt hP hK hM f.2.1 g f.2.2.2.1 f.2.2.2.2.1 (hF.1 μ₀) HX g₂
  obtain ⟨R₁, d₁, k₁, hd₁, c3, c4⟩ := _root_.GlobalTheory.HermitianSkewAdaptation.const_pair_alt hP hK hM f.2.1 g₁ f₁.2.2.2.1 f₁.2.2.2.2.1 (hc.1 μ₀) HY g₃
  obtain ⟨Γ', K, K', R', e1, e2, e3, e4, e5, e6⟩ := cast_rank Bs hn (reG Γ Γ.V U Z) (reG Γ₁ Γ.V Γ₁.V' Γ₁.W) H H' R eV
    (pΓ₁.trans pΓ.symm) (by show Γ₁.q + 1 = Γ.q; rw [qΓ, qΓ₁]) hH hH'
  refine ⟨Bs, B'.rank, Γ', _, K, K', R', R₁, d, d₁, k, k₁, f.1, hn, e1, e2, e3, e4, e5, hd, hd₁, ?_⟩
  rintro t' (rfl | rfl)
  · exact ⟨e6 _ _ c1, c3⟩
  · exact ⟨e6 _ _ c2, c4⟩
end GlobalTheory.HermitianSkewAdaptation
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
theorem _root_.GlobalTheory.T.tower_stage_successor_coefficients_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
      (Y : Tri T A B' WW₁) (lam c : T → ℂ) (e : ℕ), GlobalTheory.SqTower.IsStageC W i j p (q + 1) X →
      GlobalTheory.SqTower.IsStageC W i j p q Y → GlobalTheory.SqStepK.IsStepB X Y → Factor X W.ψ W.θ lam → Factor Y W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (b : ℕ)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank (b + 2)) (Γ₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank b)
        (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (b + 2) b) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (A.rank + (b + 2)) (A.rank + b))
        (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank (b + 2)) (R₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank b) (d d₁ : ℂ)
        (k k₁ : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ),
        GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ A'.rank = b + 2 ∧ Γ₁.V = Γ.V ∧ Γ₁.p = Γ.p ∧ Γ₁.q + 1 = Γ.q ∧
        H.IsAdapted D.sp.cm.sig Bs Γ.V' Γ₁.V' 0 (b + 1) ∧ H'.IsAdapted D.sp.cm.sig Bs Γ.W Γ₁.W A.rank (A.rank + b + 1) ∧
        d ≠ 0 ∧ d₁ ≠ 0 ∧ ∀ t' ∈ ({t, μ₀} : Set T),
          GlobalTheory.SqStepK.HasConstR Bs Γ R (GlobalTheory.SqStep.chs G i j t')
            (d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t') ∧
          GlobalTheory.SqStepK.HasConstR Bs Γ₁ R₁ (GlobalTheory.SqStep.chs G i j t')
            (d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t') := by
  first | exact @_root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt | exact _root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt | (intros; apply _root_.GlobalTheory.HermitianSkewAdaptation.tower_stage_successor_relation_alt <;> assumption)
end
