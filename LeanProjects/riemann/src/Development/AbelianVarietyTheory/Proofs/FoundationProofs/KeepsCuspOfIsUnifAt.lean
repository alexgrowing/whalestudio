import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostHalfRootAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSecRdUNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecMemIdealLatHat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelKeeps

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.Dict (castFr)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_transl (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (γ : LevelAut Dw l) {e : Ix Dw → ℤ} {f : Rul Xo c}
    (hf : f ∈ secZ Xo c e) {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] (y : FrPt Xo c S) :
    evR Xo c (transl Xo c γ f) y = evR Xo c f (move Xo c γ y) := by
  obtain ⟨p, φ, u, hu⟩ := GlobalTheory.FlagTan.fromTest_of_isLocalRing y
  rw [GlobalTheory.FlagTan.evR_eq (transl_mem_secZ hpq hA γ hf).1 hu, GlobalTheory.FlagTan.evR_eq hf.1
    ((GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA).nat γ p.R S φ u _ y _ hu (levR_move hpq hA γ u)
      (levR_move hpq hA γ y))]
  rfl

variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

theorem exists_sec_two (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 1 ≤ r) (k : U.Comp) {x : Frame (U.X k).Ψ r}
    (hx : x ∈ (U.X k).dom) : ∃ f ∈ sec Xo c 0 2, rdU U f k x ≠ 0 := by
  obtain ⟨x₀, hx₀, b₀, hb₀, e₀⟩ : ∃ x' : (U.X k).dom, GlobalTheory.FrameNorm.IsUnitFr (U.X k) x'.1 ∧
      ∃ b ∈ Bor (U.X k).Ψ r, x'.1 = rmul x b :=
    ((GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU).1 k ⟨x, hx⟩).imp
      fun _ h => ⟨h.1, h.2.1⟩
  obtain ⟨f, hf, h0⟩ := GlobalTheory.DictLevel.exists_sec_rdU_ne_zero (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr k 2 even_two x₀ hx₀
  refine ⟨f, hf, fun h => h0 ?_⟩
  show rdU U f k x₀.1 = 0
  rw [e₀, (hU.2.2.2.2.1 0 2 ⟨fun _ => antitone_const, even_two⟩ f hf k).2.1 x hx b₀ hb₀, h, mul_zero]

variable {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ}

open Limits MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj in

theorem exists_carries (hU : IsUnf U) (hP : HasPeriods φ)
    (hef : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b)))
    (hG : ∀ k k', (U.X k).Gm = (U.X k').Gm) (hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0)
    {s s' : Dw.La →ₗ[𝓞 E] Dw.La} {k : U.Comp} (x : (U.X k).dom) {y' : FrPt Xo c (CAt σ)}
    (hm : levR (s, s') (U.un k x) y') : ∃ k' δ, Carries φ s k k' δ := by
  obtain ⟨ρ, ν, -, hν, hm⟩ := hm
  obtain ⟨k', x', t, ht⟩ := hU.2.2.1 y'
  obtain ⟨P, -, p, hy, -⟩ := hP k x
  obtain ⟨P', -, p', hy', -⟩ := hP k' x'
  have hu : F.u (ik k) P ≫ ρ = F.u (ik k') P' := ((congrArg (· ≫ ρ) hy).symm.trans (hm.1.symm.trans (ht.1.trans hy')))
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨g₁, h₁, e₁, hh₁, hex⟩ := exists_isometry_of_sabMap F ν p p' hu
  obtain ⟨δ, hδ, hφ⟩ := GlobalTheory.GeoLevel.exists_isMatch_of_models (F.Di (ik k)) (φ k) (g₁.trans (φ k'))
    (Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm) ((hU.2.1 k).1.trans (hU.2.1 k').1.symm)
    (hG _ _) (hxi _ _) (hef k) (fun a b => by rw [← e₁]; exact hef k' _ _)
  refine ⟨k', δ, hδ, hG _ _, g₁, e₁, fun a ha => ?_, hφ⟩
  refine (GlobalTheory.UnifPoint.div_eq_iff p'.2.1 (F.ex_add _ P' p') (F.ex_ker _ P' p') hM0 _ _).1 ?_
  apply Over.OverMorphism.ext
  rw [hh₁, ← map_smul h₁, hex, ← F.ex_eta _ P' p' a ha, ← F.ex_eta _ P p _ (GlobalTheory.LevStab.map_mem_smul_top _ _ ha)]
  change (F.u _ P ≫ (Xo.univ.eta (s a)).left) ≫ ν.φ = F.u _ P' ≫ (Xo.univ.eta a).left
  rw [Category.assoc, hν.2.1, ← Category.assoc, hu]

theorem exists_const (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hP : HasPeriods φ)
    (hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0) (γ : LevelAut Dw l) {k k' : U.Comp} {δ : GL (Fin r) E}
    (h : Carries φ (levFull Dw l γ).1 k k' δ) {w : Ix Dw → ℤ} (hw : Even (w none)) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c w) :
    ∃ z : ℂ, ∀ x ∈ (U.X k).dom, rdU U (transl Xo c γ f) k x = z * rdU U f k' (lact δ (castFr h.mt.psi x)) := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hA' : l.A.Coprime l.M := by rw [hA]; exact Nat.coprime_one_left _
  obtain ⟨z, -, hz⟩ := exists_const_of_carries (w := 0) (n := 2) (s' := (levFull Dw l γ).2) hσ hU hpq hA hP hxi
    ⟨fun _ => antitone_const, even_two⟩ (transl Xo c γ)
    (fun f hf => by rw [← secZ_nat] at hf ⊢; exact transl_mem_secZ hpq hA' γ hf)
    (fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := levR_move hpq hA' γ y
      exact ⟨ρ, ν, _, hν, hm, fun f hf => by rw [← secZ_nat] at hf; exact evR_transl hpq hA' γ hf y⟩) h
  obtain ⟨m, hm⟩ := hw
  refine ⟨z ^ m, fun x hx => ?_⟩
  obtain ⟨ρ, ν, -, hν, hmv⟩ := levR_move hpq hA' γ (U.un k ⟨x, hx⟩)
  obtain ⟨a₁, b₁⟩ := move_eq hσ hpq hA hP h hν ⟨x, hx⟩ hmv
  obtain ⟨t₀, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen _ _ a₁ b₁
  have key : ∀ (w : Ix Dw → ℤ), ∀ f ∈ secZ Xo c w, rdU U (transl Xo c γ f) k x =
      toC (t₀ : CAt σ) ^ w none * rdU U f k' (lact δ (castFr h.mt.psi x)) := fun w f hf => by
    have v1 : rdU U (transl Xo c γ f) k x = toC (evR Xo c (transl Xo c γ f) (U.un k ⟨x, hx⟩)) := dif_pos hx
    have v2 : rdU U f k' (lact δ (castFr h.mt.psi x)) = toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩)) :=
      dif_pos (h.mt.mem_dom hx)
    rw [v1, v2, evR_transl hpq hA' γ hf, GlobalTheory.FlagTan.evR_frBor hf ht, Fintype.prod_option]
    simp only [Option.elim, one_zpow, Finset.prod_const_one, mul_one]
    exact congrArg (· * toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩))) (Units.val_zpow_eq_zpow_val (α := ℂ) t₀ _)
  obtain ⟨f₂, hf₂, h0⟩ := exists_sec_two hσ hU (hU.1 ▸ hpq) k' (h.mt.mem_dom hx)
  have h2 := hz f₂ hf₂ x hx
  rw [← secZ_nat] at hf₂
  rw [key _ f₂ hf₂] at h2
  have h3 : toC (t₀ : CAt σ) ^ (2 : ℤ) = z := mul_right_cancel₀ h0 h2
  rw [key w f hf, hm, ← two_mul, zpow_mul, h3]

theorem conj_mem (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 1 ≤ r) (hA : l.A = 1)
    (hΓ : ∀ k γ, IsUStab (U.X k).Gm (U.X k).Λ γ →
      (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, γ.1 *ᵥ v = v + l.M • u) → γ ∈ (U.X k).Γ)
    {k k' : U.Comp} {δ : GL (Fin r) E} (h : IsMatch (U.X k) (U.X k') δ) {γ : GL (Fin r) E} (hγ : γ ∈ (U.X k).Γ) :
    δ * γ * δ⁻¹ ∈ (U.X k').Γ := by
  have h' := GlobalTheory.UnitConst.isMatch_symm h
  have h'' := GlobalTheory.UnitConst.isMatch_trans (GlobalTheory.UnitConst.isMatch_trans h'
    (isMatch_of_isUStab _ ((U.X k).Γ_stab γ hγ))) h
  rw [← mul_assoc] at h''
  refine hΓ k' _ ⟨h''.iso, h''.lat⟩ fun v hv => ?_
  obtain ⟨u, hu, e⟩ := GlobalTheory.GammaLevel.trivial_mod_of_mem E H Dw l Xo c σ r U hσ hU hr hA k (hΓ k) γ hγ _
    ((h'.lat v).1 hv)
  refine ⟨_, (h.lat u).1 hu, ?_⟩
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem rdU_transl_mem (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hG : ∀ k k', (U.X k).Gm = (U.X k').Gm) (hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0)
    (hΓ : ∀ k γ, IsUStab (U.X k).Gm (U.X k).Λ γ →
      (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, γ.1 *ᵥ v = v + l.M • u) → γ ∈ (U.X k).Γ)
    {G : WTZ E} (hw : Even G.2) (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (modelWt U G k) γ = 1) (γ : LevelAut Dw l)
    {f : Rul Xo c} (hf : f ∈ secZ Xo c (exZ Dw G)) (hfc : rdU U f ∈ holSub U.X (modelWt U G)) :
    rdU U (transl Xo c γ f) ∈ holSub U.X (modelWt U G) := by
  have hA' : l.A.Coprime l.M := by rw [hA]; exact Nat.coprime_one_left _
  refine holCusp_mem_holSub _ _ fun k => ?_
  obtain ⟨g, e, F, ik, φ, hef, hpt⟩ := hU.2.2.2.2.2
  have hP : HasPeriods φ := fun k x => (hpt k x).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  obtain ⟨x₀, hx₀⟩ := (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
  obtain ⟨k', δ, h⟩ := exists_carries hU hP hef hG hxi ⟨x₀, hx₀⟩ (levR_move hpq hA' γ _)
  obtain ⟨z, hz⟩ := exists_const hσ hU hpq hA hP hxi γ h hw hf
  have hQ := GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hfc k'
  have hla : ∀ (τ : (U.X k').Ψ) i, modelWt U G k' τ i = modelWt U G k ⟨τ.1, h.mt.mem τ⟩ i := fun τ i => by
    unfold modelWt
    rw [h.mt.p0]
  refine mem_SS_of_isMatch E r _ _ δ h.mt _ _ hla _ _ z ⟨?_, fun x hx b hb => ?_, fun γ' hγ' x hx => ?_⟩ hQ hz
  · exact ((hQ.1.1.1.comp ((GlobalTheory.Dict.Extend.differentiable_lact δ).comp
      (GlobalTheory.Dict.Pull.cast_diff h.mt.psi)).differentiableOn fun x hx => h.mt.mem_dom hx).const_mul z).congr hz
  · rw [hz _ (AR.Up.OntoS.dom_rmul _ hx hb), hz x hx, GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
      hQ.1.1.2.1 _ (h.mt.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.mt.psi hb), GlobalTheory.Dict.Pull.cast_bchar h.mt.psi hla,
      mul_left_comm]
  · have hc := conj_mem hσ hU (hU.1 ▸ hpq) hA hΓ h.mt hγ'
    have e1 := hQ.1.1.2.2 _ hc _ (h.mt.mem_dom hx)
    rw [hχ _ _ hc, one_mul, GlobalTheory.Dict.Extend.lact_lact, inv_mul_cancel_right] at e1
    have e2 : lact δ (castFr h.mt.psi (lact γ' x)) = lact (δ * γ') (castFr h.mt.psi x) :=
      GlobalTheory.UnitConst.lact_cast_lact rfl h.mt.psi γ' δ x
    rw [hz _ (AR.Up.OntoS.dom_lact _ hγ' hx), hz x hx, hχ _ _ hγ', one_mul, e2, e1]

theorem keepsCusp_of_isUnf {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) {G : WTZ E}
    (hw : Even G.2) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hG : ∀ σ, GoodEmb c σ → ∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0)
    (hΓ : ∀ σ, GoodEmb c σ → ∀ k γ, IsUStab ((U σ).X k).Gm ((U σ).X k).Λ γ →
      (∀ v ∈ ((U σ).X k).Λ, ∃ u ∈ ((U σ).X k).Λ, γ.1 *ᵥ v = v + l.M • u) → γ ∈ ((U σ).X k).Γ)
    (hχ : ∀ σ, GoodEmb c σ → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (modelWt (U σ) G k) γ = 1) :
    KeepsCusp U G := fun h f hf => by
  rw [mem_cuspW] at hf ⊢
  exact ⟨pull_mem_secZ hpq (by rw [hA]; exact Nat.coprime_one_left _) h hf.1, fun σ hσ =>
    rdU_transl_mem hσ (hU σ hσ) hpq hA (fun k k' => (hG σ hσ k k').1) (fun k k' => (hG σ hσ k k').2) (hΓ σ hσ) hw
      (hχ σ hσ) h⁻¹ hf.1 (hf.2 σ hσ)⟩

end Free

section Record

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Indef.Tree Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.SlopeRec
open scoped Matrix TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mem_group {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hU : IsUnf U) (hA : l.A = 1) (hr0 : 0 < r) {V : HSp D}
    (hr : V.rank = r) {dict : GA D V → Σ k, Frame (U.X k).Ψ r} {Kf : Subgroup (GA D V)}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (hW : ∀ k, ModelW V hr (U.X k)) (h0 : ∀ k, IsOrthogonalFrame (U.X k) x₀)
    (hK : IsLevelK V l.M Kf) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hfr : ∀ h, ∃ g, ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) g) * x₀ τ.1)
    (k : U.Comp) (γ : GL (Fin r) D.host.E) (hγ : IsUStab (U.X k).Gm (U.X k).Λ γ)
    (hc0 : ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, γ.1 *ᵥ v = v + l.M • u) : γ ∈ (U.X k).Γ := by
  have hc : ∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, γ.1 *ᵥ x - x = (l.M : D.host.E) • y := fun x hx => by
    obtain ⟨y, hy, e⟩ := hc0 x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj U) hU hA hr0 k γ hγ hc
  have hmu : MuUnit V dict fun _ => 1 := by
    refine ⟨fun _ _ => (one_mul _).symm, fun _ => norm_one, fun _ _ => rfl, fun h => ?_⟩
    subst hr
    obtain ⟨g, hg⟩ := hfr h
    exact GlobalTheory.FrameEquiv.GenMove.isUnitFr_of_archM V _ (hW _) (h0 _) (hth _) g _ hg
  have h1 := GlobalTheory.PrincCore.root_eq_one V hr hr0 U.X dict _ Kf th hth hD hmu _ l.three_le hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end Record

end GlobalTheory.LevelKeeps
