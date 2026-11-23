import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMove
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevActMemMlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyComponentIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReadingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelLiftFiniteCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCharacterOnLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyUnfoldingCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingDeterminantRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTraceFormLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedLatticeMapRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedLatticeMapExists

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem isMatch_div {X X' : Data E r} {a b : GL (Fin r) E} (ha : IsMatch X X' a) (hb : IsMatch X X' b) :
    IsMatch X' X' (b * a⁻¹) := by
  have hri : ∀ v, (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  refine ⟨rfl, rfl, rfl, fun u v => ?_, fun v => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb.iso, ← ha.iso, hri, hri]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hb.lat, ha.lat, hri]

omit [NumberField E] [IsCMField E] in
theorem lact_div {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (z : Frame Ψ r) :
    lact (b * a⁻¹) (castFr rfl (lact a z)) = lact b z := by
  funext τ
  change ((b * a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
    ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ) = (b : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel_right]

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ}

theorem comp_unique (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q)
    (hA : l.A = 1) (hP : Pinned U e F ik φ) {k k₁ k₂ : U.Comp} {δ₁ δ₂ : GL (Fin r) E}
    (h₁ : IsMatch (U.X k) (U.X k₁) δ₁) (h₂ : IsMatch (U.X k) (U.X k₂) δ₂) {γ : Dw.La →ₗ[𝓞 E] Dw.La}
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hm : IsLevMove ρ ν γ LinearMap.id)
    (m₁ : MarkRel l (φ k) (φ k₁) (F.t (ik k)) (F.t (ik k₁)) γ δ₁)
    (m₂ : MarkRel l (φ k) (φ k₂) (F.t (ik k)) (F.t (ik k₂)) γ δ₂) (x : (U.X k).dom) : k₁ = k₂ := by
  obtain ⟨y', hy⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hm.1 _ (U.un k x)).1
  obtain ⟨a₁, b₁⟩ := GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k₁ δ₁ h₁ γ ρ ν m₁ hm x y' hy
  obtain ⟨a₂, b₂⟩ := GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k₂ δ₂ h₂ γ ρ ν m₂ hm x y' hy
  obtain ⟨t₀, ht⟩ := exists_frBor_gen _ _ (a₂.symm.trans a₁) (b₂.symm.trans b₁)
  obtain ⟨_, -, _, -, he⟩ := (hU.2.2.2.1 k₁ k₂ _ _).1 ⟨_, ht⟩
  exact (congrArg Sigma.fst he).symm

theorem exists_const (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q)
    (hA : l.A = 1) (hP : Pinned U e F ik φ)
    (hex : ∀ (k : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ) (ρ : Xo.X ⟶ Xo.X)
      (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n →
      ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom,
      Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)))
    {k k' : U.Comp} {δ₀ : GL (Fin r) E} (h₀ : IsMatch (U.X k) (U.X k') δ₀) {γ : Dw.La →ₗ[𝓞 E] Dw.La}
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hm : IsLevMove ρ ν γ LinearMap.id)
    (m₀ : MarkRel l (φ k) (φ k') (F.t (ik k)) (F.t (ik k')) γ δ₀) (n : ℕ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') →
      ∀ (k₁ k₁' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k₁) (U.X k₁') δ), k₁ = k →
      MarkRel l (φ k₁) (φ k₁') (F.t (ik k₁)) (F.t (ik k₁')) γ δ → ∀ x ∈ (U.X k₁).dom,
      Formalism.L2.PjFree.rdU U f' k₁ x = ε * Formalism.L2.PjFree.rdU U f k₁' (lact δ (castFr h.psi x)) := by
  obtain ⟨ε, hε, hc⟩ := GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame E H Dw l Xo c σ r U U hσ hU hU k k' δ₀ h₀ ρ ν hm.1
    (GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k' δ₀ h₀ γ ρ ν m₀ hm)
    (fun x y' t hx hy ht => GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move E H Dw l Xo c σ r U hσ hU ρ ν k k' x _ y' t hy ht hx
      (fun τ i => by rw [h₀.dmin_eq]; exact hx _ i)) n
  refine ⟨ε, hε, fun w hw f hf f' hf' hv k₁ k₁' δ h hk m x hx => ?_⟩
  subst hk
  obtain rfl : k₁' = k' := comp_unique hσ hU hpq hA hP h h₀ hm m m₀ ⟨x, hx⟩
  obtain ⟨ν₀, hν₀, hy₀⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have hm₀ : IsLevMove (𝟙 Xo.X) ν₀ LinearMap.id LinearMap.id :=
    ⟨Category.id_comp _, fun a => by rw [hν₀]; exact (Category.comp_id _).trans (Category.id_comp _).symm,
      fun a => by rw [hν₀]; exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
  have := hex k₁' _ (isMatch_div h₀ h) _ ν₀ hm₀.1
    (GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP _ _ _ _ _ _ _ (m₀.div m) hm₀) w n hw f hf f hf
    (fun y y' hy => by
      rw [(GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₀ hm₀.1 _ y).2 y y' ν₀ rfl (hy₀ _ y) hy]) _ (h₀.mem_dom hx)
  rw [hc w hw f hf f' hf' hv x hx, this, lact_div]

end Free

section Record

open NumberField IsDedekindDomain CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts
open GlobalTheory.Member (FinCong)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftGrp (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    Subgroup (Formalism.L2.DIV.G0 Pg r × GA D V) where
  carrier := {p | IsLift V hr β Pg p.1 p.2}
  one_mem' := isLift_one V hr β Pg
  mul_mem' := by
    rintro ⟨g, κ⟩ ⟨g', κ'⟩ ⟨a, h, b⟩ ⟨a', h', b'⟩
    refine ⟨mul_mem a a', by rw [Prod.snd_mul, map_mul]; exact mul_mem h h', fun w => ?_⟩
    have := map_mul (Formalism.L2.DIV.redAt β w.1) ⟨_, h⟩ ⟨_, h'⟩
    rw [b, b'] at this
    refine Eq.trans (congrArg _ (Subtype.ext ?_)) this
    exact map_mul (finR V hr) κ κ'
  inv_mem' := by
    rintro ⟨g, κ⟩ ⟨a, h, b⟩
    refine ⟨inv_mem a, by rw [Prod.snd_inv, map_inv]; exact inv_mem h, fun w => ?_⟩
    have := map_inv (Formalism.L2.DIV.redAt β w.1) ⟨_, h⟩
    rw [b] at this
    refine Eq.trans (congrArg _ (Subtype.ext ?_)) this
    exact map_inv (finR V hr) κ

variable {G : Type} [Group G]

end Record

end GlobalTheory.GeoLevel
