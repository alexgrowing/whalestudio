import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnfGroupContainsCongruenceUptoRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RootOfUnityEqOneOfConjCongruence
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfEventuallyDotProductStarEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory.PrincCore

theorem unitary_of_first_minor {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (hr : 0 < r)
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (J x₀ : Matrix (Fin r) (Fin r) ℂ) (hJ : J.IsHermitian) (hd : J.det ≠ 0)
    (h : ∀ u : Matrix (Fin r) (Fin r) ℂ, (u.map (starRingEnd ℂ))ᵀ * J * u = J →
      ‖lminor (gram τ G (u * x₀)) ⟨1, by omega⟩‖ = 1)
    (w : Matrix (Fin r) (Fin r) ℂ) (hw : wᵀ * G.map τ * w.map (starRingEnd ℂ) = G.map τ) :
    (w.map (starRingEnd ℂ))ᵀ * J * w = J := by
  have hA : (G.map τ).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hG b a]
    exact (IsCMField.complexEmbedding_complexConj E τ _).symm
  have tr : ∀ u : Matrix (Fin r) (Fin r) ℂ, uᵀ * Jᵀ * u.map (starRingEnd ℂ) = Jᵀ →
      (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
    intro u hu
    have := congrArg Matrix.transpose hu
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
  obtain ⟨t, ht, hAt⟩ := GlobalTheory.UnitaryOrbitForm.eq_smul_of_norm_eq_one_on_orbit r (G.map τ) Jᵀ
    (col x₀ ⟨0, hr⟩) hA hJ.transpose (by rwa [Matrix.det_transpose]) (by
      intro u hu
      rw [← h u (tr u hu)]
      congr 1
      unfold lminor
      rw [Matrix.det_unique]
      simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, hermC, dotProduct, Matrix.mulVec, col,
        Matrix.map_apply, Matrix.mul_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]
      rfl)
  apply tr
  rw [hAt, Matrix.mul_smul, Matrix.smul_mul] at hw
  exact smul_right_injective _ (by exact_mod_cast ht : (t : ℂ) ≠ 0) hw

theorem exists_lattice_congr (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n M : ℕ) (hM : M ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) (g : GL (Fin n) (GlobalTheory.AdLat.RA F E))
    (κ : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (δ : Matrix (Fin n) (Fin n) E)
    (hκ : ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      κ *ᵥ z - z = M • y)
    (he : δ.map (inclR (F := F) (Af F)) * g.1 = g.1 * κ) :
    ∃ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      ∀ x ∈ Λ, ∃ y ∈ Λ, δ *ᵥ x - x = (M : E) • y := by
  obtain ⟨Λ, h1, h2, h3, -⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hL hs
  refine ⟨Λ, h2, h3, fun x hx => ?_⟩
  have hx' : x ∈ GlobalTheory.AdLat.latOf F g.1 (L : Set (Fin n → E)) := h1 ▸ hx
  obtain ⟨z, hz, hzx⟩ := hx'
  obtain ⟨y, hy, hzy⟩ := hκ z hz
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM
  refine ⟨(M : E)⁻¹ • (δ *ᵥ x - x), ?_, by rw [smul_smul, mul_inv_cancel₀ hME, one_smul]⟩
  show _ ∈ (Λ : Set (Fin n → E))
  rw [h1]
  refine ⟨y, hy, ?_⟩
  let i : E →+* GlobalTheory.AdLat.RA F E := inclR (F := F) (Af F)
  have hf : ∀ v : Fin n → E, GlobalTheory.AdLat.fv F v = i ∘ v := fun _ => rfl
  have e1 : i ∘ (δ *ᵥ x) = δ.map i *ᵥ (i ∘ x) := funext fun a => RingHom.map_mulVec i δ x a
  have e2 : i ∘ (δ *ᵥ x) - i ∘ x = M • (g.1 *ᵥ y) := by
    rw [e1, ← hf x, ← hzx, Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, hzy,
      Matrix.mulVec_smul]
  rw [hf]
  funext a
  have e3 := congrFun e2 a
  simp only [Pi.sub_apply, Function.comp, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_sub] at e3 ⊢
  rw [e3, ← map_natCast i M, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hME, map_one, one_mul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000 in

theorem root_eq_one {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (hr0 : 0 < r) {Comp : Type}
    (X : Comp → Data D.host.E r) (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ)
    (Kf : Subgroup (GA D V)) (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr) (hmu : MuUnit V dict mu)
    (M : ℕ) (hM : 3 ≤ M) (hK : IsLevelK V M Kf) (k : Comp) (γ γ' : GL (Fin r) D.host.E) (hγ' : γ' ∈ (X k).Γ)
    (hc : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, (γ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ x - x = (M : D.host.E) • y)
    (u : D.host.E) (n : ℕ) (hn : 0 < n) (hu : u ^ n = 1)
    (he : (γ' : Matrix (Fin r) (Fin r) D.host.E) = u • (γ : Matrix (Fin r) (Fin r) D.host.E)) : u = 1 := by
  classical
  subst hr
  obtain ⟨-, -, ⟨x0, hx0, heq⟩, -, -, hfib⟩ := hD
  obtain ⟨hdom, g, hg⟩ := hx0 k
  obtain ⟨-, hrat, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := heq g
    rw [hg] at this
    exact this
  have hun : ∀ τ : (X k).Ψ, ((γ'.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ'.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    refine unitary_of_first_minor hr0 τ.1 (X k).Gm (X k).Gm_herm _ (mat (x0 k) τ) ?_ ?_ ?_ _ ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, HSpace.gram]
      rw [← V.herm.eq (V.frame b) (V.frame a)]
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ τ.1.injective).2 (gram_det_ne V)
    · intro w hw
      obtain ⟨h, hh, hw'⟩ := hsur (Function.update (fun _ => 1) τ w) (by
        intro τ'
        by_cases e : τ' = τ
        · subst e
          simpa using hw
        · simp [Function.update_of_ne e])
      obtain ⟨γ'', h1, h2⟩ := key h hh
      have h3 := hmu.2.2.2 (g * h)
      rw [h2] at h3
      have h4 := h3 τ ⟨1, by omega⟩
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.dmin_lact (X k) h1] at h4
      unfold dmin at h4
      rw [hact, hw', Function.update_self] at h4
      exact h4
    · have hcc : (γ'.1.map τ.1).map (starRingEnd ℂ) =
          (γ'.1.map cc).map τ.1 := by
        ext a b
        exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
      rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ']
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  obtain ⟨γ'', h1, h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ', mul_mem h1 hγ', ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ').1.map τ.1 * mat (x0 k) τ
    rw [hact, hw, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀
  obtain ⟨hκ1, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have h0 : finHom V h = 1 := hh
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := hκ1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  let f : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := V.frame.equivFun.toLinearMap.restrictScalars _
  have hhat : latHat V = GlobalTheory.AdLat.hat D.host.F (V.L0.map f : Set (Fin V.rank → D.host.E)) := by
    unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, f x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hspan : Submodule.span D.host.E (V.L0.map f : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (V.L0.map f : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  rw [hhat] at hκ2
  obtain ⟨Λ', g1, g2, g3⟩ := exists_lattice_congr D.host.F D.host.E V.rank M (by omega) (V.L0.map f)
    (V.standardTuple_isLattice.fg.map f) hspan (finHom V g) (finHom V κ⁻¹).1 δ.1 hκ2 (by
      rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul])
  obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases e : τ ∈ (X k).Ψ
    · exact ⟨⟨τ, e⟩⟩
    · exact ⟨⟨_, not_not.1 (fun e' => e (((X k).cmType τ).2 e'))⟩⟩
  have hm : ∀ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h1' : archM V (th k τ) 1 = 1 := by
    unfold archM
    rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine GlobalTheory.root_of_unity_eq_one_of_conj_congruence D.host.E V.rank M n (X k).Λ Λ' γ.1 δ.1 u τ.1
    (archM V (th k τ) g⁻¹) hr0 hM hn hu (X k).Λ_fg g1 (X k).Λ_span g2 hc g3 ?_ ?_
  · have := congrArg Matrix.det (hm g⁻¹ g)
    rw [inv_mul_cancel, h1', Matrix.det_one, Matrix.det_mul] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  · rw [← he, ← hw τ, ← hδ1 τ, ← hm, ← hm]
    have e : infHom V (h * g⁻¹) = infHom V (g⁻¹ * γ₀) := by
      rw [map_mul, map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hinf, mul_inv_cancel_right]
    unfold archM
    rw [e]

theorem hasPrinc_core : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M := by
  intro D T h j hj σ hσ k γ hγ hc
  obtain ⟨hgood, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hnum j hj).2.1
  have hM : 3 ≤ T.Q.l.M := le_trans (hgood 2 Nat.prime_two) (Nat.div_le_self _ _)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (h.unf j hj σ hσ) hA hr k γ hγ hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hK := h.levelK j hj σ hσ
  rw [← h.pins.2.1.1] at hK
  have h1 := root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
    (h.muUnit j hj σ hσ) _ hM hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.PrincCore
