import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapDualMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifOfOrtho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDualFormIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero

set_option autoImplicit false

noncomputable section

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CechPic (cls lam)

namespace GlobalTheory.HodgeRiemFibre

theorem hermForm_smul_one_comb {J : Type} [DecidableEq J] {n : ℕ} (e : Fin n ≃ J) (c : ℂ) {m m' : ℕ}
    (j : Fin m → J) (j' : Fin m' → J) (a : Fin m → ℂ) (a' : Fin m' → ℂ) :
    hermForm (c • (1 : Matrix (Fin n) (Fin n) ℂ)) (∑ l, a l • (Pi.single (e.symm (j l)) (1 : ℂ) : Fin n → ℂ))
      (∑ l, a' l • (Pi.single (e.symm (j' l)) (1 : ℂ) : Fin n → ℂ)) =
      c * ∑ l : Fin m, ∑ l' : Fin m', (if j l = j' l' then a l * star (a' l') else (0 : ℂ)) := by
  simp only [hermForm, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, star_sum, star_smul,
    sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  have hs : star (Pi.single (e.symm (j' l')) (1 : ℂ) : Fin n → ℂ) = Pi.single (e.symm (j' l')) 1 := by
    ext t; by_cases h : t = e.symm (j' l') <;> simp [Pi.single_apply, h]
  rw [hs, single_dotProduct]
  simp only [Pi.single_apply, e.symm.injective.eq_iff]
  split_ifs <;> simp [mul_comm]

def fibrePol {S : Scheme.{0}} (Q : Out.PolAV S) {y : Sp ℂ ⟶ S} (d : (PPAS.ofPolAV Q).RiemannData y) :
    Out.PolAV (Sp ℂ) :=
  have h : IsGrpPullback d.B Q.A y d.φ := d.isPull
  have hL := pull_isLB Q.isLB d.φ
  { A := d.B
    isAb := PolPull.isAbelianScheme_of_isGrpPullback Q.isAb h
    g := Q.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
    L := Q.L.pull d.φ
    isLB := hL
    rigid := PolBaseChange.rigidified_pull h Q.rigid
    sym := PolBaseChange.sym_pull h Q.sym
    ample := by
      obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hL hL).1 rfl
      obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
        (x := y (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
      exact relAmple_pull h.1 Q.isLB hL ((isGen_iff w).1 hw) U hU
        (fun z => by rwa [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]) Q.ample
    ktriv := by
      obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hL hL).1 rfl
      exact kTriv_pull h Q.isLB hL ((isGen_iff w).1 hw) Q.ktriv }

theorem exists_lift {S : Scheme.{0}} (Q : Out.PolAV S) {y : Sp ℂ ⟶ S} (d : (PPAS.ofPolAV Q).RiemannData y)
    (P : Out.PolAV (Sp ℂ)) {n : ℕ} (u' : HolUnif P.A P.L n) (Hm' : Matrix (Fin n) (Fin n) ℂ) (χ' : u'.Λ → ℂ)
    (hA' : u'.IsAH Hm' χ') (f : d.B ⟶ P.A) (hf : IsMonHom f)
    (hL : LBIso (lbPow (P.L.pull f.left) 1) (lbPow (Q.L.pull d.φ) 1)) :
    ∃ F : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin n → ℂ), (∀ a b, hermForm Hm' (F a) (F b) = hermForm d.H a b) ∧
      ∀ w v w', IsTangent v → d.u.IsDiff w v → u'.IsDiff w' (v ≫ f) → F w = w' := by
  have hB : IsAbelianScheme d.B := (fibrePol Q d).isAb
  have hL₁ := pull_isLB Q.isLB d.φ
  obtain ⟨rig, hr⟩ := (fibrePol Q d).rigid
  obtain ⟨u₁, H₁, χ₁, -, hH₁, -⟩ := thetaUnifAV_all (fibrePol Q d) rig hr
  let u₂ : HolUnif d.B (Q.L.pull d.φ) Q.g := u₁
  have hH₂ : u₂.IsAH H₁ χ₁ := hH₁
  obtain ⟨-, -, -, -, g1, g2, -⟩ :=
    GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all (fibrePol Q d) Q.g u₁ H₁ χ₁ hH₁
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all P n u' Hm' χ' hA'
  obtain ⟨F₁, hF₁, -, hd₁, -⟩ := HomLinear.exists_linear_of_isMonHom d.B d.B hB hB d.L (Q.L.pull d.φ) Q.g Q.g d.u u₂
    g1 g2 (𝟙 _) inferInstance
  obtain ⟨F₂, hF₂, -, hd₂, -⟩ := HomLinear.exists_linear_of_isMonHom d.B P.A hB P.isAb (Q.L.pull d.φ) P.L Q.g n u₂ u'
    h1 h2 f hf
  have hp : lam (cls (Q.L.pull d.φ) hL₁) (fst d.B d.B) (snd d.B d.B) = lam (cls d.L d.isLB) (fst d.B d.B) (snd d.B d.B) := by
    rw [← d.pol, CechPic.cls_pull Q.isLB _ hL₁]
    exact (PPAS.pull_sqMap_lam d.isPull _).symm
  have hdiag : lam (cls (Q.L.pull d.φ) hL₁) (𝟙 d.B) (𝟙 d.B) = lam (cls d.L d.isLB) (𝟙 d.B) (𝟙 d.B) := by
    have := congrArg (CechPic.pull (lift (𝟙 d.B) (𝟙 d.B)).left) hp
    rwa [CechPic.pull_lam, CechPic.pull_lam, lift_fst, lift_snd] at this
  refine ⟨F₂ ∘ₗ F₁, fun a b => ?_, fun w v w' hv hw hw' => ?_⟩
  · have e₁ := RiemIndep.hermForm_eq_of_lam d.u u₂ (𝟙 _) F₁ d.isLB hL₁ hF₁ d.isAH hH₂ hdiag a b
    have e₂ := GlobalTheory.hermForm_pull_eq_of_lbIso_pow d.B P.A (Q.L.pull d.φ) P.L hL₁ P.isLB Q.g n u₂ u' H₁ χ₁ Hm' χ' hH₂ hA'
      f F₂ hF₂ 1 1 hL (F₁ a) (F₁ b)
    rw [Nat.cast_one, _root_.one_mul, _root_.one_mul] at e₂
    exact e₂.trans e₁
  · obtain ⟨-, k₁⟩ := hd₁ w v hv hw
    rw [Category.comp_id] at k₁
    obtain ⟨t₂, k₂⟩ := hd₂ _ v hv k₁
    obtain ⟨c, -, hc⟩ := h1 _ t₂
    exact (hc _ k₂).trans (hc _ hw').symm

end GlobalTheory.HodgeRiemFibre

end SlopeTestRemainingChoices

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

theorem GlobalTheory.HodgeRiemFibre.hodge_gram_eq : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (Q : Out.PolAV T) (θ : Q.A.left ⟶ s.T.Z.t.G.left), IsGrpPullback Q.A s.T.Z.t.G b θ → LBIso (s.T.Z.t.PP.L.pull θ) Q.L → ∀ (σ' : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ' → ∀ (yc : CxPts (genStr s.T.Z) σ') (y₀ : Sp ℂ ⟶ T), y₀ ≫ b = yc.1 ≫ genι s.T.Z → ∀ (u : EigFrame s.T.Z σ' (yc.1 ≫ genι s.T.Z)) (d : (PPAS.ofPolAV Q).RiemannData y₀) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → Fin Q.g → ℂ), (∀ τ i, ∃ v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff (z τ i) v ∧ v.left ≫ d.φ ≫ θ = u.v τ i) → (∀ τ b₁ b₂, (x.hodge σ').gram yc u τ b₁ b₂ = (Real.pi : ℂ) * hermForm d.H (z τ b₂) (z τ b₁)) ∧ ∀ τ τ' b₁ b₂, τ ≠ τ' → hermForm d.H (z τ b₁) (z τ' b₂) = 0 := by
  intro _ _ D A N j S κ s x T b Q θ hθ hL σ hσ yc y₀ hy u d z hz
  have hcomp₀ : IsGrpPullback d.B s.T.Z.t.G (y₀ ≫ b) (d.φ ≫ θ) := IsGrpPullback.comp d.isPull hθ
  have hB : IsAbelianScheme d.B := (GlobalTheory.HodgeRiemFibre.fibrePol Q d).isAb
  have hzb : ¬ LiesIn yc (genBd s.T.Z) := fun hl => by
    refine mem_genBd_iff.1 hl (abLocusOne _ _ s.T.Z.t.semi ℂ (y₀ ≫ b) ?_ ⟨IsLocalRing.closedPoint ℂ, ?_⟩)
    · have := hB.proper
      rw [← hcomp₀.1.isoPullback_inv_snd]
      infer_instance
    · rw [hy]
      exact Scheme.Hom.comp_apply _ _ _
  obtain ⟨f, hf⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hzb
  have hfH := hf
  obtain ⟨ψ, σ', k, w, hψ, hσ', hgood, horth, hpt, hmap⟩ := hf
  rcases hψ with rfl | rfl
  swap
  · exact absurd (hσ' ▸ hgood) (Formalism.L2.Pj.not_good_conj _ hσ)
  obtain rfl : σ' = σ := by simpa using hσ'
  have hw : (cxPt s.T.Z ((s.U σ').un k w)).1 = yc.1 := by
    rw [hpt]; simp [spMap]
  obtain ⟨P, m, n, e, u', χ', hAH, hlift⟩ := GlobalTheory.OrthoFibreUnif.exists_unif_of_ortho _ A.H S.Dw κ.l (S.Xo κ.l) κ.c N σ'
    (s.U σ').toPj (Formalism.L2.Pj.xiR D) ((one_le_two.trans S.two_le).trans S.rank_eq.ge) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj (s.U σ').toPj).1 (s.unf σ' hσ).1) k w (s.xiAbs σ' k) horth
  have hqz : cxPt s.T.Z ((s.U σ').un k w) = yc := Subtype.ext hw
  have hpt' : y₀ ≫ b = GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ') ((s.U σ').un k w) ≫ s.T.Z.jQ ≫ Limits.pullback.fst _ _ := by
    rw [hy, ← hw]
    exact Category.assoc _ _ _
  have hcomp := hcomp₀
  rw [hpt'] at hcomp
  obtain ⟨φ, hφ, hφL, hφv⟩ := GlobalTheory.HodgeFibIso.exists_hom s.T.Z
    (GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ') ((s.U σ').un k w)) ((s.U σ').un k w).x
    (ptF_fst _).symm (GlobalTheory.HodgeRiemFibre.fibrePol Q d) _ hcomp (GlobalTheory.CM.EllComp.lbIso_pull_comp hL d.φ) P m
  obtain ⟨L, hL1, hL2⟩ := GlobalTheory.HodgeRiemFibre.exists_lift Q d P.pol u' _ χ' hAH φ hφ hφL
  have hfq : ∀ τ i, f.v τ i = (cxFrame s.T.Z ((s.U σ').un k w)).v τ i := fun τ i => by
    rw [hmap τ i, spMap_dualMap_id, Category.id_comp]
  have hLz : ∀ τ i, L (z τ i) = ∑ l, f.co u τ l i • Pi.single (e.symm ⟨τ, l⟩) (1 : ℂ) := fun τ i => by
    obtain ⟨v₀, ht, hd, hv₀⟩ := hz τ i
    obtain ⟨w₀, hw₀, hw₀m, hw₀c⟩ := GlobalTheory.HodgeSmooth.exists_lift_comb _ hqz f u hfq τ i
    obtain ⟨v, w', hvc, hw'v, hw'd⟩ := hlift τ (fun l => f.co u τ l i)
    have hvw := GlobalTheory.HodgeFibIso.isCombAt_unique hvc hw₀c
    have hmap := hφv v₀ w₀ w' hw₀.1 (hw₀m.trans hv₀.symm) (hw'v.trans hvw)
    exact hL2 _ v₀ _ ht hd (hmap ▸ hw'd)
  have key : ∀ (τ τ' : D.host.E →+* ℂ) (i : Fin (S.Dw.mult τ)) (i' : Fin (S.Dw.mult τ')),
      hermForm d.H (z τ i) (z τ' i') = (((2 * Formalism.L2.Pj.xiR D : ℝ) : ℂ)) *
        ∑ l : Fin (S.Dw.mult τ), ∑ l' : Fin (S.Dw.mult τ'),
          (if (⟨τ, l⟩ : Σ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ)) = ⟨τ', l'⟩ then
            f.co u τ l i * star (f.co u τ' l' i') else 0) := by
    intro τ τ' i i'
    rw [← hL1, hLz, hLz, GlobalTheory.HodgeRiemFibre.hermForm_smul_one_comb e _
      (fun l => (⟨τ, l⟩ : Σ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ)))
      (fun l => (⟨τ', l⟩ : Σ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ)))]
  refine ⟨fun τ b₁ b₂ => ?_, fun τ τ' b₁ b₂ hne => ?_⟩
  · rw [key, x.hodge_gram hfH u τ]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_eq_mul]
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [key]
    have : ∀ (l : Fin (S.Dw.mult τ)) (l' : Fin (S.Dw.mult τ')),
        (⟨τ, l⟩ : Σ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ)) ≠ ⟨τ', l'⟩ := fun l l' hh => hne (congrArg Sigma.fst hh)
    simp [this]

end
