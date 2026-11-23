import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletionEmbeddingsSingleFrobeniusOrbitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSignStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnramiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDatumFrobeniusRestrictHostFieldStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem reads_orbit_invFrob : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  intro D l _ P K LL W c κ h2 hq hd hcl hK
  set φ := DV.frobG D l with hφ
  set n := Module.finrank ℚ_[l] ↥(K0 K) with hn
  have hτ := fun a => GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  have hg := fun τ => GlobalTheory.T.existsUnique_embeddingReadsGaloisElement D.host K LL c κ τ
  let τa : ZMod n → (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := fun a => (hτ a).exists.choose
  have hover : ∀ a, Over W (τa a) a := fun a => (hτ a).exists.choose_spec
  let g : ZMod n → D.R.GG := fun a => (hg (τa a)).exists.choose
  have hread : ∀ a, Reads D.host c κ (τa a) (g a) := fun a => (hg (τa a)).exists.choose_spec
  have smul : ∀ u v : D.R.GG, D.host.sigmaOf (u * v) = D.host.sigmaOf u * D.host.sigmaOf v :=
    fun u v => map_mul (D.host.gal).symm u v
  have hK0 : K0 K = K.1 := inf_eq_left.mpr hK

  have step : ∀ a, g (a + 1) = g a * φ⁻¹ := by
    intro a
    refine (hg (τa (a + 1))).unique (hread (a + 1)) ?_
    intro z
    set x := D.host.sigmaOf φ⁻¹ z with hx
    have hz : D.host.sigmaOf φ x = z := by
      rw [hx, ← AlgEquiv.mul_apply, ← smul, mul_inv_cancel]
      show (D.host.gal).symm 1 z = z
      rw [map_one]; rfl
    let y : ↥(K0 K) := ⟨((c x : ↥K.1) : Om l), ⟨(c x).2, hK (c x).2⟩⟩
    have hy : algebraMap ↥(K0 K) ↥K.1 y = c x := Subtype.ext rfl
    have hσ := GlobalTheory.T.periodDatum_frobenius_restrict_hostField D P K c h2 hq hd x y hy
    have ov : ∀ b (t : ↥(K0 K)), τa b (algebraMap ↥(K0 K) ↥K.1 t) = W.emb b t := by
      intro b t
      have := congrArg (fun f => f t) (hover b)
      simpa using this
    have hemb : W.emb (a + 1) ((P.PD K).σ y) = W.emb a y := by
      have := congrArg (fun f => f y) (W.emb_σ a)
      simpa using this
    calc τa (a + 1) (c z) = τa (a + 1) (c (D.host.sigmaOf φ x)) := by rw [hz]
      _ = τa (a + 1) (algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y)) := by rw [hσ]
      _ = W.emb (a + 1) ((P.PD K).σ y) := ov _ _
      _ = W.emb a y := hemb
      _ = τa a (algebraMap ↥(K0 K) ↥K.1 y) := (ov _ _).symm
      _ = τa a (c x) := by rw [hy]
      _ = κ (D.host.sigmaOf (g a) x) := hread a x
      _ = κ (D.host.sigmaOf (g a * φ⁻¹) z) := by rw [smul, AlgEquiv.mul_apply]

  have hfr : n = Module.finrank ℚ_[l] ↥K.1 := by
    rw [hn]; exact (IntermediateField.equivOfEq hK0).toLinearEquiv.finrank_eq
  have hlen : n = orderOf φ⁻¹ := by
    rw [orderOf_inv]
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (Ideal.span {(l : ℤ)}) (⊥ : Ideal (𝓞 D.host.E)) (by
        intro x hx
        simp only [Ideal.mem_comap, Ideal.mem_bot] at hx
        have : x = 0 := (algebraMap ℤ (𝓞 D.host.E)).injective_int (by simpa using hx)
        rw [this]; exact Ideal.zero_mem _)
    have := hQ
    have : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQc.symm⟩
    have hfrob := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D l h2 hq hd).1 Q
    let c' : D.host.E →+* PadicAlgCl l := (K.1.val : ↥K.1 →ₐ[ℚ_[l]] Om l).toRingHom.comp c
    have hc' : ∀ x, c' x ∈ K.1 := fun x => (c x).2
    have hcl' : (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c') := hcl
    have := (GlobalTheory.T.completion_embeddings_single_frobenius_orbit D.host l h2 hq hd c' K hc' hcl' Q (D.host.sigmaOf φ) hfrob).1
    have hφg : D.host.galE (D.host.sigmaOf φ) = φ :=
      (D.host.gal).apply_symm_apply φ
    rw [hfr, this, hφg]
  have hpos : 0 < n := by
    rw [hfr]
    have := K.2
    exact Module.finrank_pos
  have : NeZero n := ⟨hpos.ne'⟩
  refine ⟨g, ⟨hlen, ?_⟩, ?_⟩
  · have hk : ∀ k : ℕ, g (k : ZMod n) = g 0 * φ⁻¹ ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ, step, ih]
        exact (mul_assoc _ _ _).trans (congrArg _ (pow_succ φ⁻¹ k).symm)
    intro a
    have := hk a.val
    rwa [ZMod.natCast_zmod_val] at this
  · intro τ a h
    have : τ = τa a := (hτ a).unique h (hover a)
    subst this
    exact hread a

end GlobalTheory.HTW.Rec
