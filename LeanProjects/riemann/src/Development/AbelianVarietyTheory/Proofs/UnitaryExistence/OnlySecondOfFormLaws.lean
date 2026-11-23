import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ContinuousIffCrdA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InvariantProbabilityLatticeQuotientUniqueStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LactMul

noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def DatumSign {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) {r : ℕ} (V' : ConjugateFieldNorm.HSpace D.host.E r)
    (ε : ℤˣ) : Prop :=
  ∃ φ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), Function.Injective φ ∧
    LinearMap.range φ = ConjugateFieldNorm.latAt D.host.F D.host.AA V' 1 ∧
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (-D.host.xi0 * herm V'.Gm (φ x) (φ y))

theorem invProb_iff (V : HSp D) (hP : VolPairEx V) (hV : FinVol V) (ν : Measure (AutQ V)) :
    IsProbabilityMeasure ν ∧ RightInv V ν ↔ ν = muQ1 V := by
  have hp := volPair_isVolPair V hP
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.lcsc_adelic_unitary_group _ _ D.sp.cm.sig _ V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : (volPair V).1.IsHaarMeasure := hp.1.1
  have hV' := hV
  rw [FinVol, muQ_univ] at hV'
  have hq : muQ1 V = ((volPair V).1 (volPair V).2)⁻¹ • ((volPair V).1.restrict (volPair V).2).map (autMk V) := by
    rw [muQ1, if_pos (show _ ∧ _ from hV), muQ_univ]; rfl
  constructor
  · rintro ⟨h1, h2⟩
    rw [hq]
    exact GlobalTheory.T.invariant_probability_lattice_quotient_unique _ (GQ V) _ _ hp.2 hV'.2 ν h2
  · rintro rfl
    refine ⟨inferInstance, fun h ρ hρ s hs => ?_⟩
    have hm := autMk_measurable V
    have e : autMk V ⁻¹' (ρ ⁻¹' s) = (· * h) ⁻¹' (autMk V ⁻¹' s) := by
      ext g; exact iff_of_eq (congrArg (· ∈ s) (hρ g))
    have hs' : MeasurableSet (ρ ⁻¹' s) := by
      change MeasurableSet (autMk V ⁻¹' (ρ ⁻¹' s))
      rw [e]; exact measurable_mul_const h (hm hs)
    have hri := GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) _ hp.2 hV'.1 hV'.2
    have : (volPair V).1.IsMulRightInvariant := ⟨hri⟩
    have hF : IsFundamentalDomain (GQ V) ((Equiv.mulRight h⁻¹) ⁻¹' (volPair V).2) (volPair V).1 :=
      hp.2.preimage_of_equiv (measurePreserving_mul_right _ h⁻¹).quasiMeasurePreserving (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) (volPair V).1
    rw [hq, Measure.smul_apply, Measure.smul_apply]
    congr 1
    rw [show ((volPair V).1.restrict (volPair V).2).map (autMk V) s = _ from
      congrArg (fun m : Measure (AutQ V) => m s) (GlobalTheory.AutQuotCheck.map_restrict_eq (GQ V) _ hp.2 hF),
      Measure.map_apply hm hs', Measure.map_apply hm hs, Measure.restrict_apply (hm hs'),
      Measure.restrict_apply (hm hs), e, ← measure_preimage_mul_right (volPair V).1 h (_ ∩ _ ⁻¹' _)]
    congr 1
    ext g
    simp

def numsOf (D : D7) : ConjugateFieldNorm.Nums D.host.E where
  k := D.R.k
  m := D.R.m
  g := D.host.g
  g_prime := D.host.g_prime
  g_ne := D.host.g_ne
  Nc := Ideal.absNorm D.host.ccK
  Nc_pos := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 D.host.ccK_ne_bot)
  AA := D.host.AA
  Os := D.what₂.phiO.range

def SpaceW (T : Core D) : Prop := ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j

def spW (D : D7) (j : (numsOf D).J) : ConjugateFieldNorm.HSpace D.host.E D.R.r := spOf (D.sp.W j) (D.sp.W_rank j j.2.1 j.2.2)

variable {T : Core D} (hW : SpaceW T)

def psi (j : (numsOf D).J) {σ} (hσ : GoodEmb T.Q.c σ) : ConjugateFieldNorm.GA D.host.F (spW D j) ≃* GA D (T.V j σ) :=
  (exists_isCoord (T.V j σ) (hW j j.2 σ hσ) (D.sp.W_rank j j.2.1 j.2.2)).choose

def parOf (π : Fin 2 → 𝓞 D.host.E) : ConjugateFieldNorm.CorePar D.host.F (numsOf D) where
  H := T.Q.H
  l := T.Q.l
  c := T.Q.c
  Dw j := T.Q.Dw j
  Xo j := T.Q.Xo j
  U j σ := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)
  V j := spW D j
  dict j σ hσ g := T.dict j σ (psi hW j hσ g)
  mu j σ hσ g := T.mu j σ (psi hW j hσ g)
  Kf j := (T.Kf j T.σ₀).comap (psi hW j T.good_σ₀).toMonoidHom
  pi := π

def GenBy (T : Core D) (π : Fin 2 → 𝓞 D.host.E) : Prop :=
  ∀ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = Ideal.span {T.Q.H.bar (π k)}

def RecTies : Prop :=
  T.Q.H.d = D.host.d ∧ (T.Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ T.Q.PinField ∧
    ∀ (j : (numsOf D).J) σ (hσ : GoodEmb T.Q.c σ),
      (T.Kf j σ).comap (psi hW j hσ).toMonoidHom = (T.Kf j T.σ₀).comap (psi hW j T.good_σ₀).toMonoidHom

def ArchEquiv (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Prop :=
  ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    ∃ x0 : ∀ c, Frame ((T.U j σ).X c).Ψ D.R.r, (∀ c, x0 c ∈ ((T.U j σ).X c).dom ∧ ∃ g, T.dict j σ g = ⟨c, x0 c⟩) ∧
      ∀ g, ∀ h ∈ GinfC (T.V j σ), ∃ γ' ∈ ((T.U j σ).X (T.dict j σ g).1).Γ,
        T.dict j σ (g * h) = ⟨(T.dict j σ g).1,
          lact γ' (rmul (T.dict j σ g).2 (archMat (T.V j σ) th hr x0 h (T.dict j σ g).1))⟩

def OnlyFirst (T : Core D) : Prop :=
  ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → Continuous (T.mu j σ) ∧ ArchEquiv T j σ

def OnlySecond (π : Fin 2 → 𝓞 D.host.E) : Prop :=
  (∀ i, π i ∈ Algebra.adjoin ℤ {T.Q.H.w0} ∧ π i * T.Q.H.bar (π i) = (D.host.g i : 𝓞 D.host.E)) ∧
  ∀ j : (numsOf D).J, ((∃ ε, DatumSign (T.Q.Dw j) (spW D j) ε) → DatumSign (T.Q.Dw j) (spW D j) 1) ∧
    (∀ σ (hσ : GoodEmb T.Q.c σ), (IsUnf (T.U j σ) → (parOf hW π).PinDict j σ hσ) ∧
      ∀ g : ConjugateFieldNorm.GA D.host.F (spW D j), g.1.1.val.det = 1 → g.2.1.val.det = 1 → (parOf hW π).mu j σ hσ g = 1) ∧
    AutomorphismGroupTopologies.WeightField (parOf hW π) j ∧ AutomorphismGroupTopologies.FrameExt (parOf hW π) j ∧ AutomorphismGroupTopologies.PtOnComp (parOf hW π) j

variable (π : Fin 2 → 𝓞 D.host.E)

end GlobalTheory.CoreLawsCompare
