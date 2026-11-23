import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodCoordinatesQuadraticRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffinePeriodCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffinePeriodCoordinateConjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixOfLatticeEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneOfTraceFormPreservedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriangularFrameEigenScalarStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameGam

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem scalar_of_cover (X : Data E r) (hr : 0 < r) (τ₁ : E →+* ℂ)
    (κ : Frame X.Ψ r → Fin r → ℂ) (hκ : ContinuousOn κ X.dom)
    (hopen : ∀ O : Set (Frame X.Ψ r), IsOpen O → O ⊆ X.dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ,
      ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ)
    (S : Set (Matrix (Fin r) (Fin r) E))
    (cov : ∀ x ∈ X.dom, ∃ W ∈ S, ∀ v ∈ X.Λ, ∀ w ∈ X.Λ,
      (κ x ⬝ᵥ Data.emb τ₁ (W *ᵥ v)) * (κ x ⬝ᵥ Data.emb τ₁ w) =
        (κ x ⬝ᵥ Data.emb τ₁ (W *ᵥ w)) * (κ x ⬝ᵥ Data.emb τ₁ v)) :
    ∃ W ∈ S, ∃ ζ : E, W = ζ • (1 : Matrix (Fin r) (Fin r) E) :=
  GlobalTheory.T.period_coordinates_quadratic_relation E r X hr τ₁ κ hκ hopen S cov

theorem exists_row (X : Data E r) (τ₁ : E →+* ℂ) (h : τ₁ ∈ X.Ψ) (i : ℕ) (hi : X.p0 + i + 1 = r) :
    ∃ κ : Frame X.Ψ r → Fin r → ℂ, ContinuousOn κ X.dom ∧
      (∀ O : Set (Frame X.Ψ r), IsOpen O → O ⊆ X.dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ,
        ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ) ∧
      ∀ x ∈ X.dom, ∀ v, Formalism.L2.PjFree.perFr X x v τ₁ i = κ x ⬝ᵥ Data.emb τ₁ v :=
  GlobalTheory.T.exists_affine_period_coordinate E r X τ₁ h i hi

theorem exists_col (X : Data E r) (τ₁ : E →+* ℂ) (h : τ₁ ∉ X.Ψ) (i : ℕ) (hi : X.p0 = i + 1) :
    ∃ κ : Frame X.Ψ r → Fin r → ℂ, ContinuousOn κ X.dom ∧
      (∀ O : Set (Frame X.Ψ r), IsOpen O → O ⊆ X.dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ,
        ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ) ∧
      ∀ x ∈ X.dom, ∀ v, Formalism.L2.PjFree.perFr X x v τ₁ i = κ x ⬝ᵥ Data.emb τ₁ v :=
  GlobalTheory.T.exists_affine_period_coordinate_conj E r X τ₁ h i hi

theorem exists_matrix (X : Data E r) (w : X.Λ →ₗ[𝓞 E] X.Λ) :
    ∃ W : Matrix (Fin r) (Fin r) E, ∀ v : X.Λ, W *ᵥ (v : Fin r → E) = (w v : Fin r → E) :=
  GlobalTheory.T.exists_matrix_of_lattice_endomorphism E r X w

theorem unit_of_trace (X : Data E r) (hr : 0 < r) (ζ : E)
    (h : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, Algebra.trace ℚ E (-X.ξ0 * (ζ * cc ζ * herm X.Gm u v)) =
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm u v)) : ζ * cc ζ = 1 :=
  GlobalTheory.T.norm_one_of_trace_form_preserved E r X hr ζ h

end Lin

section Top

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem top_eig {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (tri : ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → ℂ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      eb e τ i = h (∑ j, cf j • eb e τ j))
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (hi : ∀ j, j ≤ i) :
    ∃ y : ℂ, ∀ w, h w (e.symm ⟨τ, i⟩) = y * w (e.symm ⟨τ, i⟩) :=
  GlobalTheory.T.triangular_frame_eigen_scalar E H Dw g e h tri τ i hi

end Top

end GlobalTheory.FrameGam

namespace GlobalTheory.FrameGam

open GlobalTheory.PeriodTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem herm_smul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ζ : E) (u v : Fin r → E) :
    herm G (ζ • u) (ζ • v) = ζ * cc ζ * herm G u v := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, cc, map_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.FrameGam

namespace GlobalTheory.FrameGam

open GlobalTheory.PeriodTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem lie_scalar (U : Formalism.L2.PjFree.Unf Xo c σ r) (hU : Formalism.L2.PjFree.IsUnf U) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hrel : ∀ τ, Formalism.L2.PjFree.relab c σ τ = τ)
    (k : U.Comp) {g₀ : GL (Fin r) E} (hg : g₀ ∈ (U.X k).Γ) (hr : 0 < r) :
    ∃ ρ : (E →+* ℂ) → ℂ, (∀ τ, ‖ρ τ‖ = 1) ∧ ∀ (x : (U.X k).dom) τ (i : Fin (Dw.mult τ)),
      IsCombAt (S := CAt σ) (U.un k ⟨lact g₀ x.1, KU.lact_dom _ hg x.2⟩).x
        ((U.un k ⟨lact g₀ x.1, KU.lact_dom _ hg x.2⟩).u τ) (Pi.single i (ρ τ)) ((U.un k x).u τ i) := by
  classical
  have hU' := hU
  obtain ⟨hr', hty, -, hbor, -, g, e, F, ik, φ, hEF, hF⟩ := hU
  obtain ⟨hEU, hEL, hTE, -⟩ := GlobalTheory.exp_four_clauses E H Dw l Xo c σ hσ g e F
  choose P h1 h2 h3 h4 h5 using hF k
  let x' : (U.X k).dom → (U.X k).dom := fun x => ⟨lact g₀ x.1, KU.lact_dom _ hg x.2⟩
  have S1 : ∀ x, ∃ (gam : (F.Di (ik k)).La ≃ₗ[𝓞 E] (F.Di (ik k)).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di (ik k)).EF (gam a) (gam b) = (F.Di (ik k)).EF a b) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La), ∃ e, gam a = a + l.M • e) ∧
      (∀ a, ∃ e, gam a = a + l.A • e) ∧ (∀ a, P (x' x) (gam a) = h (P x a)) ∧
      ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → ℂ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        eb e τ i = h (∑ j, cf j • eb e τ j) := by
    intro x
    have hpt : (U.un k (x' x)).x = (U.un k x).x := PointWell.pt_lact hU' k x hg
    have hu : F.u (ik k) (P x) = F.u (ik k) (P (x' x)) := by rw [← h3, ← h3, hpt]
    obtain ⟨gam, h, c0, c1, c2, c3⟩ := (F.fibre _ _ _ (h2 x) (h2 (x' x))).1 hu
    refine ⟨gam, h, c0, c1, c2, c3, ?_⟩
    have hexp := hEU (ik k) _ _ (h2 x) (h2 (x' x)) gam h c0 c1 c2 c3
    obtain ⟨t, ht⟩ := (hbor k k x (x' x)).2
      ⟨g₀, hg, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨by
        show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
        simp, fun a b h => one_apply_ne h.ne'⟩, by
        congr 1
        funext τ
        exact (Matrix.mul_one (mat (lact g₀ x.1) τ)).symm⟩
    intro τ i
    obtain ⟨cf, hcf, hz, hc⟩ := ht.2.1 τ i
    refine ⟨cf, hcf ▸ (t _).isUnit, hz, ?_⟩
    have d1 := h4 (x' x) τ i
    have d2 := derivAt_of_comb (e := e) (F := F) hEL (h2 x) (w := eb e τ) (fun j => h4 x τ j)
      (by rw [← h3 x]; exact hc)
    have d3 := isDerivAt0_comp (e2 := fun z => (F.ex (ik k) (P (x' x)) z).left) h (fun z => hexp z) d2
    exact derivAt_unique hTE (h2 (x' x)) d1 d3
  have hstab := (U.X k).Γ_stab g₀ hg
  let GΛ : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k).Λ := gamL (U.X k) hstab
  let wm : ((F.Di (ik k)).La ≃ₗ[𝓞 E] (F.Di (ik k)).La) → ((U.X k).Λ ≃ₗ[𝓞 E] (U.X k).Λ) :=
    fun gam => (φ k).symm.trans (gam.trans ((φ k).trans GΛ.symm))
  have hgl : ∀ gam a, (g₀ : Matrix (Fin r) (Fin r) E) *ᵥ (wm gam (φ k a) : Fin r → E) =
      (φ k (gam a) : Fin r → E) := fun gam a => by
    rw [← gamL_coe (U.X k) hstab]
    show ((GΛ (GΛ.symm (φ k (gam ((φ k).symm (φ k a))))) : (U.X k).Λ) : Fin r → E) = _
    simp
  have hP : ∀ (x : (U.X k).dom) a q, P x a q =
      Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (e q).1 (e q).2 := fun x a q => by
    rw [h1 x a q, hrel]
  have hlact : ∀ (x : (U.X k).dom) (v : Fin r → E) τ (i : ℕ),
      Formalism.L2.PjFree.perFr (U.X k) (x' x).1 ((g₀ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        Formalism.L2.PjFree.perFr (U.X k) x.1 v τ i := fun x v τ i => perFr_lact_fx (U.X k) x.1 hstab v τ i
  obtain ⟨τ₁, i₁, htop, κ, hκ, hopen, hper⟩ : ∃ (τ₁ : E →+* ℂ) (i₁ : Fin (Dw.mult τ₁)), (∀ j, j ≤ i₁) ∧
      ∃ κ : Frame (U.X k).Ψ r → Fin r → ℂ, ContinuousOn κ (U.X k).dom ∧
      (∀ O : Set (Frame (U.X k).Ψ r), IsOpen O → O ⊆ (U.X k).dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ,
        ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ) ∧
      ∀ x ∈ (U.X k).dom, ∀ v, Formalism.L2.PjFree.perFr (U.X k) x v τ₁ i₁ = κ x ⬝ᵥ Data.emb τ₁ v := by
    obtain ⟨hp0, hΨ⟩ := hty k
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hcm := (U.X k).cmType
    rcases Nat.eq_zero_or_pos Dw.p with hp | hp
    · obtain ⟨τ₁, hτ⟩ : ∃ τ, τ ∉ (U.X k).Ψ := by
        by_cases h : τ0 ∈ (U.X k).Ψ
        · exact ⟨_, (hcm τ0).1 h⟩
        · exact ⟨τ0, h⟩
      have hm : Dw.mult τ₁ = Dw.q := if_neg fun h => hτ ((hΨ τ₁).2 h)
      refine ⟨τ₁, ⟨Dw.q - 1, by omega⟩, fun j => ?_, exists_col (U.X k) τ₁ hτ _ (by simp only; omega)⟩
      have := j.2
      exact Fin.le_def.2 (by simp only; omega)
    · obtain ⟨τ₁, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
        by_cases h : τ0 ∈ (U.X k).Ψ
        · exact ⟨τ0, h⟩
        · exact ⟨_, by_contra fun h' => h ((hcm τ0).2 h')⟩
      have hm : Dw.mult τ₁ = Dw.p := if_pos ((hΨ τ₁).1 hτ)
      refine ⟨τ₁, ⟨Dw.p - 1, by omega⟩, fun j => ?_, exists_row (U.X k) τ₁ hτ _ (by simp only; omega)⟩
      have := j.2
      exact Fin.le_def.2 (by simp only; omega)
  let S : Set (Matrix (Fin r) (Fin r) E) := {W | ∃ gam : (F.Di (ik k)).La ≃ₗ[𝓞 E] (F.Di (ik k)).La,
    (∀ a b, (F.Di (ik k)).EF (gam a) (gam b) = (F.Di (ik k)).EF a b) ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La), ∃ e, gam a = a + l.M • e) ∧
    (∀ a, ∃ e, gam a = a + l.A • e) ∧ ∀ v : (U.X k).Λ, W *ᵥ (v : Fin r → E) = (wm gam v : Fin r → E)}
  obtain ⟨W, ⟨gam, c0, c1, c2, hW⟩, ζ, rfl⟩ := scalar_of_cover (U.X k) hr τ₁ κ hκ hopen S (by
    intro x hx
    obtain ⟨gam, h, c0, c1, c2, c3, tri⟩ := S1 ⟨x, hx⟩
    obtain ⟨W, hW⟩ := exists_matrix (U.X k) (wm gam).toLinearMap
    obtain ⟨y, hy⟩ := top_eig e h tri τ₁ i₁ htop
    have key : ∀ a, κ x ⬝ᵥ Data.emb τ₁ (W *ᵥ (φ k a : Fin r → E)) =
        y * (κ x ⬝ᵥ Data.emb τ₁ (φ k a : Fin r → E)) := fun a => by
      have e1 := hP (x' ⟨x, hx⟩) (gam a) (e.symm ⟨τ₁, i₁⟩)
      have e2 := hP ⟨x, hx⟩ a (e.symm ⟨τ₁, i₁⟩)
      rw [c3 a, hy, e2, Equiv.apply_symm_apply, ← hgl gam a, hlact ⟨x, hx⟩] at e1
      rw [hW (φ k a), ← hper x hx, ← hper x hx]
      exact e1.symm
    refine ⟨W, ⟨gam, c0, c1, c2, hW⟩, fun v hv w hw => ?_⟩
    obtain ⟨a, ha⟩ := (φ k).surjective ⟨v, hv⟩
    obtain ⟨b, hb⟩ := (φ k).surjective ⟨w, hw⟩
    have ea : (φ k a : Fin r → E) = v := congrArg Subtype.val ha
    have eb' : (φ k b : Fin r → E) = w := congrArg Subtype.val hb
    rw [← ea, ← eb', key a, key b]
    ring)
  have hζv : ∀ a, (φ k (gam a) : Fin r → E) = ζ • ((g₀ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E)) := fun a => by
    have e1 := hW (φ k a)
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at e1
    rw [← hgl gam a, ← e1, Matrix.mulVec_smul]
  have hcc : ζ * cc ζ = 1 := unit_of_trace (U.X k) hr ζ fun u hu v hv => by
    obtain ⟨a, ha⟩ := (φ k).surjective ⟨u, hu⟩
    obtain ⟨b, hb⟩ := (φ k).surjective ⟨v, hv⟩
    have ea : (φ k a : Fin r → E) = u := congrArg Subtype.val ha
    have eb' : (φ k b : Fin r → E) = v := congrArg Subtype.val hb
    have e1 := hEF k (gam a) (gam b)
    rw [c0, hEF k a b, hζv, hζv, herm_smul, hstab.1, ea, eb'] at e1
    exact e1.symm
  have hnorm : ∀ τ : E →+* ℂ, ‖τ ζ‖ = 1 := fun τ => by
    have e1 := congrArg τ hcc
    rw [map_mul, map_one, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj] at e1
    have e2 : Complex.normSq (τ ζ) = 1 := by exact_mod_cast e1
    rw [Complex.normSq_eq_norm_sq] at e2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e2
  have hd : ∀ j, (e j).1 ζ ≠ 0 := fun j h0 => by
    have := hnorm (e j).1
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  let Dz : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.piCongrRight fun j => LinearEquiv.smulOfNeZero ℂ ℂ _ (hd j)
  have hDz : ∀ z q, Dz z q = (e q).1 ζ * z q := fun z q => rfl
  refine ⟨fun τ => τ ζ, hnorm, fun x τ i => ?_⟩
  have rel : ∀ a, P (x' x) (gam a) = Dz (P x a) := fun a => by
    funext q
    rw [hDz, hP, hP, hζv, perFr_smul, hlact]
  have hexp := hEU (ik k) _ _ (h2 x) (h2 (x' x)) gam Dz c0 c1 c2 rel
  have d' := isDerivAt0_comp (e2 := fun z => (F.ex (ik k) (P (x' x)) z).left) Dz (fun z => hexp z) (h4 x τ i)
  have hw : Dz (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ j, (Pi.single i (τ ζ) : Fin (Dw.mult τ) → ℂ) j • eb e τ j := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
    funext q
    rw [hDz]
    by_cases hq : q = e.symm ⟨τ, i⟩
    · subst hq
      simp [eb]
    · simp [eb, Pi.single_eq_of_ne hq]
  rw [hw] at d'
  have := hEL (ik k) _ (h2 (x' x)) _ (eb e τ) ((U.un k (x' x)).u τ) (Pi.single i (τ ζ)) _
    (fun j => h4 (x' x) τ j) d'
  rw [h3 (x' x)]
  exact this

end GlobalTheory.FrameGam

namespace GlobalTheory.FrameGam

open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Semi Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem gram_frPt [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (y y' : FrPt Xo c (CAt σ))
    (e : y.x = y'.x) (τ : E →+* ℂ) (ρ : ℂ) (hρ : ‖ρ‖ = 1)
    (h : ∀ i, IsCombAt (S := CAt σ) y'.x (y'.u τ) (Pi.single i ρ) (y.u τ i)) :
    x.gram (cxPt Z y) (cxFrame Z y) τ = x.gram (cxPt Z y') (cxFrame Z y') τ := by
  obtain ⟨x1, o1, u1, t1, e1, b1, s1, g1⟩ := y
  obtain ⟨x2, o2, u2, t2, e2, b2, s2, g2⟩ := y'
  obtain rfl : x1 = x2 := e
  let ρ' : CAt σ := ρ
  have key : ∀ i, IsCombAtG Z.t ((cxPt Z ⟨x1, o2, u2, t2, e2, b2, s2, g2⟩).1 ≫ genι Z)
      ((cxFrame Z ⟨x1, o2, u2, t2, e2, b2, s2, g2⟩).v τ)
      (fun a => (ρ • (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) a i)
      ((cxFrame Z ⟨x1, o1, u1, t1, e1, b1, s1, g1⟩).v τ i) := fun i => by
    have e3 : tanOf (t := Xo.univ.t) (t1 τ i) = ρ' • tanOf (t := Xo.univ.t) (t2 τ i) := by
      have := (LieMet.isComb_iff (fun j => tanOf (t := Xo.univ.t) (t2 τ j)) (Pi.single i ρ')
        (tanOf (t := Xo.univ.t) (t1 τ i))).1 (h i)
      have hs : (∑ j, (Pi.single i ρ' : Fin (Dw.mult τ) → CAt σ) j • tanOf (t := Xo.univ.t) (t2 τ j)) =
          ρ' • tanOf (t := Xo.univ.t) (t2 τ i) := by
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same]
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj, zero_smul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      exact this.trans hs
    refine (LieMet.isComb_iff ((cxFrame Z ⟨x1, o2, u2, t2, e2, b2, s2, g2⟩).vec τ) _
      ((cxFrame Z ⟨x1, o1, u1, t1, e1, b1, s1, g1⟩).vec τ i)).2 ?_
    refine Eq.trans ?_ (Finset.sum_eq_single i ?_ ?_).symm
    rotate_left
    · intro j _ hj
      simp [Matrix.one_apply_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
    have e4 : (cxFrame Z ⟨x1, o1, u1, t1, e1, b1, s1, g1⟩).vec τ i =
        lieEquiv Z (⟨x1, o2, u2, t2, e2, b2, s2, g2⟩ : FrPt Xo c (CAt σ)) (Category.assoc _ _ _).symm (tanOf (t := Xo.univ.t) (t1 τ i)) :=
      tan_ext rfl
    have e5 : (cxFrame Z ⟨x1, o2, u2, t2, e2, b2, s2, g2⟩).vec τ i =
        lieEquiv Z (⟨x1, o2, u2, t2, e2, b2, s2, g2⟩ : FrPt Xo c (CAt σ)) (Category.assoc _ _ _).symm (tanOf (t := Xo.univ.t) (t2 τ i)) :=
      tan_ext rfl
    rw [e4, e5, e3, map_smul]
    have h1 : (ρ • (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) i i = ρ := by simp
    beta_reduce
    rw [h1]
    rfl
  have hc := x.gram_change (cxFrame Z ⟨x1, o2, u2, t2, e2, b2, s2, g2⟩) (cxFrame Z ⟨x1, o1, u1, t1, e1, b1, s1, g1⟩) τ _ key
  refine hc.trans ?_
  have h1 : (starRingEnd ℂ) ρ * ρ = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hρ]
    simp
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [mul_comm, show star ρ = (starRingEnd ℂ) ρ from rfl, h1, one_smul]

end GlobalTheory.FrameGam

namespace GlobalTheory.FrameGam

theorem gram_lact : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (g₀ : GL (Fin N) D.host.E), g₀ ∈ (s.fd k).Γ → ∀ (f f' : (s.fd k).dom), f'.1 = ReciprocityTheory.ChartRestriction.G.FD.lact g₀ f.1 → ∀ t, x.gramW L k f' t = x.gramW L k f t ∧ x.gramOm L k f' t = x.gramOm L k f t := by
  intro D A N j S κ s L k x g₀ hg f f' hf t
  obtain rfl : f' = ⟨lact g₀ f.1, KU.lact_dom _ hg f.2⟩ := Subtype.ext hf
  obtain ⟨ρ, hρ, hc⟩ := lie_scalar (s.U κ.σ₀) s.isUnf κ.good_σ₀ (fun τ => rfl) k hg
    (lt_of_lt_of_le two_pos S.two_le)
  have hgram : ∀ τ, x.gram (s.framePt k ⟨lact g₀ f.1, KU.lact_dom _ hg f.2⟩)
      (s.lieFrame k ⟨lact g₀ f.1, KU.lact_dom _ hg f.2⟩) τ = x.gram (s.framePt k f) (s.lieFrame k f) τ := fun τ =>
    (gram_frPt x _ _ (PointWell.pt_lact s.isUnf k f hg).symm τ (ρ τ) (hρ τ) (hc f τ)).symm
  constructor
  · simp only [ToroidalCompactificationData.gramW, hgram]
  · simp only [ToroidalCompactificationData.gramOm, hgram]

end GlobalTheory.FrameGam
