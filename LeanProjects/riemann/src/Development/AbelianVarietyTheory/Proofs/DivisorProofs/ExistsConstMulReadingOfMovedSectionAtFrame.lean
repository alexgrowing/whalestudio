import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneConstRatioOfCommonRatio
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalOfLeHolSub
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

set_option autoImplicit false

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

set_option maxHeartbeats 1000000 in

theorem exists_const_rdU_of_moveMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.IsUnf U' → ∀ (k : U.Comp) (k' : U'.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U' k k' h ρ ν → (∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → FrMove ρ ν (U.un k x) y' → FrBor t (U'.un k' ⟨_, h.mem_dom x.2⟩) y' → cabs (t none : CAt σ) = 1) → ∀ n : ℕ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = ε * Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x)) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' k k' δ h ρ ν hρ hM hone n
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  have hex : ∀ x : (U.X k).dom, ∃ (y' : FrPt Xo c (CAt σ)) (t₀ : (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' ∧
      FrBor (fun i => Option.elim i t₀ (fun _ => 1)) (U'.un k' ⟨_, h.mem_dom x.2⟩) y' := fun x => by
    obtain ⟨y', hy'⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k x)).1
    obtain ⟨t₀, ht₀⟩ := exists_frBor_gen _ y' (hM x y' hy').1 (hM x y' hy').2
    exact ⟨y', t₀, hy', ht₀⟩
  choose y' t₀ hm hb using hex
  have hla : ∀ (w : (E →+* ℂ) × ℕ → ℕ) (τ : (U'.X k').Ψ) (i : Fin r),
      Formalism.L2.PjFree.laU U' w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := fun w τ i => by
    unfold Formalism.L2.PjFree.laU
    rw [h.p0]
  have key : ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x : (U.X k).dom,
      Formalism.L2.PjFree.rdU U f' k x.1 = Formalism.L2.PjFree.toC (t₀ x : CAt σ) ^ n *
        Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x.1)) := fun w hD f hf f' hf' hv x => by
    have v1 : Formalism.L2.PjFree.rdU U f' k x.1 = Formalism.L2.PjFree.toC (evR Xo c f' (U.un k x)) := dif_pos x.2
    have v2 : Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x.1)) =
      Formalism.L2.PjFree.toC (evR Xo c f (U'.un k' ⟨_, h.mem_dom x.2⟩)) := dif_pos (h.mem_dom x.2)
    have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f hf _ _ (y' x) (hb x)
    have v4 : Formalism.L2.PjFree.toC (wchar (ex Dw w n) (fun i => Option.elim i (t₀ x) (fun _ => 1)) : CAt σ) =
        Formalism.L2.PjFree.toC (t₀ x : CAt σ) ^ n := by
      have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) (fun i => Option.elim i (t₀ x) (fun _ => 1)) : CAt σ) =
          ∏ j, Formalism.L2.PjFree.toC (((fun i => Option.elim i (t₀ x) (fun _ => 1) : Ix Dw → (CAt σ)ˣ) j : (CAt σ)ˣ) : CAt σ) ^ ex Dw w n j := rfl
      rw [this, Finset.prod_eq_single none]
      · rfl
      · rintro (_ | j) _ hj
        · exact (hj rfl).elim
        · exact one_pow _
      · intro hn; exact (hn (Finset.mem_univ _)).elim
    rw [v1, v2, hv _ _ (hm x), v3, ← v4]
    rfl
  obtain ⟨ε, hε, hc⟩ := GlobalTheory.exists_norm_one_const_ratio_of_common_ratio (Frame (U.X k).Ψ r)
    {p : ((E →+* ℂ) × ℕ → ℕ) × Rul Xo c × Rul Xo c // Dom p.1 n ∧ p.2.1 ∈ sec Xo c p.1 n ∧ p.2.2 ∈ sec Xo c p.1 n ∧
      ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c p.2.2 y = evR Xo c p.2.1 y'}
    (U.X k).dom (FourierCoefficientDomain.isOpen_dom _) (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected
    (fun i => Formalism.L2.PjFree.rdU U i.1.2.2 k)
    (fun i x => Formalism.L2.PjFree.rdU U' i.1.2.1 k' (lact δ (castFr h.psi x)))
    (fun x => if hx : x ∈ (U.X k).dom then Formalism.L2.PjFree.toC (t₀ ⟨x, hx⟩ : CAt σ) ^ n else 0)
    (fun i => (hU.2.2.2.2.1 _ n i.2.1 _ i.2.2.2.1 k).1)
    (fun i => (hU'.2.2.2.2.1 _ n i.2.1 _ i.2.2.1 k').1.comp ((GlobalTheory.Dict.Extend.differentiable_lact δ).comp
      (GlobalTheory.Dict.Pull.cast_diff h.psi)).differentiableOn fun x hx => h.mem_dom hx)
    (fun i x hx => by
      rw [dif_pos hx]
      exact key _ i.2.1 _ i.2.2.1 _ i.2.2.2.1 i.2.2.2.2 ⟨x, hx⟩)
    (fun ⟨⟨w, f, f'⟩, hD, hf, hf', hv⟩ x hx => by
      obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
      have hsec := hU.2.2.2.2.1 w n hD f' hf' k
      have hQ := hU'.2.2.2.2.1 w n hD f hf k'
      have h1 : ‖Formalism.L2.PjFree.toC (t₀ x₀ : CAt σ)‖ = 1 := hone x₀ _ _ hx₀ (hm x₀) (hb x₀)
      have v5 := congrArg norm (key w hD f hf f' hf' hv x₀)
      rw [norm_mul, norm_pow, h1, one_pow, one_mul, e₀, hsec.2.1 x hx b₀ hb₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (hla w), norm_mul, norm_mul] at v5
      exact mul_left_cancel₀ (norm_ne_zero_iff.2 (AR.Up.OntoE.bchar_ne _ _ hb₀)) v5)
  exact ⟨ε, hε, fun w hD f hf f' hf' hv x hx => hc ⟨⟨w, f, f'⟩, hD, hf, hf', hv⟩ x hx⟩

end GlobalTheory.GeoLevel
