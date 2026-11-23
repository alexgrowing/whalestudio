import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensionalStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistRead

theorem matRep_apply {F Γ : Type} [CommRing F] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) F)
    (g : Γ) (v : Fin k → F) : matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]

theorem local_twist_dual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {n : ℕ}
    (R T U : ↥(GK K) →* Matrix (Fin n) (Fin n) ↥LL.1)
    (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1)
    (hν : ∀ g x, ν g x = χ g • x) (hR : ∀ g, R g = χ g • T g)
    (hU : ∀ g, U g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (T g⁻¹).transpose)
    (dR : IsDR (P.PD K) (matRep R)) (dν : IsDR (P.PD K) ν)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ) (hc : ∀ a : ℤ, multV (P.PD K) ν τ a = if a = c then 1 else 0) :
    IsDR (P.PD K) (matRep T) ∧ IsDR (P.PD K) (matRep U) ∧
      ∀ a : ℤ, multV (P.PD K) (matRep T) τ a = multV (P.PD K) (matRep R) τ (a + c) ∧
        multV (P.PD K) (matRep U) τ a = multV (P.PD K) (matRep R) τ (c - a - 1) := by
  have hRT : ∀ g x, matRep R g x = χ g • matRep T g x := by
    intro g x
    rw [matRep_apply, matRep_apply, hR, Matrix.smul_mulVec]
  have dT : IsDR (P.PD K) (matRep T) :=
    (GlobalTheory.TwistDR.isDR_twist_iff l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν).2 dR
  have jT : ∀ a : ℤ, multV (P.PD K) (matRep R) τ (a + c) = multV (P.PD K) (matRep T) τ a :=
    GlobalTheory.TwistJump.multV_twist_char l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν τ c hc
  have hb : Function.Bijective (dotProductBilin ↥LL.1 ↥LL.1 :
      (Fin n → ↥LL.1) →ₗ[↥LL.1] (Fin n → ↥LL.1) →ₗ[↥LL.1] ↥LL.1) :=
    (dotProductEquiv ↥LL.1 (Fin n)).bijective
  have hd := GlobalTheory.T.galois_representation_hom_finite_dimensional l P AI hT K LL _ (matRep T) _ (matRep U) _ 1 hb (by
    intro g x y
    rw [matRep_apply, matRep_apply, hU, zpow_one]
    simp only [dotProductBilin_apply_apply, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]) dT
  refine ⟨dT, hd.1, fun a => ⟨(jT a).symm, ?_⟩⟩
  have h1 := hd.2 τ (-a - 1) hs
  have h2 := jT (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at h1
  rw [show -a - 1 + c = c - a - 1 by ring] at h2
  rw [h1, h2]

set_option maxHeartbeats 1000000 in

theorem twist_dual_mult : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (χ : GE D.nd →* GL (Fin 1) (D.nd.O i)) (c : ℤ), Continuous (fun g => rO D.nd i r x g) → (∀ g, (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i)) 0 0 = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)) → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) χ) w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) χ) τ = {c} → IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) ∧ IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (a + c) : ℕ) : ℤ) ∧ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (c - a - 1) : ℕ) : ℤ) := by
  intro D i w hw hT LL' h τ' τ hτ r x χ c hr hχ dr dχ hc
  have tie := D.loc_tie i w hw
  set f : D.nd.O i →+* ↥LL'.1 :=
    (IntermediateField.inclusion h).toRingHom.comp (D.nbr i w hw).toLL with hf
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (continuous_subtype_val.comp (D.nbr i w hw).eO_cont)
  have hmap : ∀ (m : ℕ) (ρ : GE D.nd →* GL (Fin m) (D.nd.O i)),
      mapRep (algebraMap ↥LL'.1 (Qbar (D.nd.l i))) (mapRep f ρ) = mapRep (iotaOQ D.nd D.naut i) ρ := by
    intro m ρ
    ext g a b
    exact (tie.1 _).symm
  have cr : Continuous (fun g => ((mapRep f (r x) g : GL (Fin D.R.nV) ↥LL'.1) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) ↥LL'.1)) := hr.matrix_map hfc
  have cχ : Continuous (fun g => ((mapRep f χ g : GL (Fin 1) ↥LL'.1) : Matrix (Fin 1) (Fin 1) ↥LL'.1)) := by
    refine Continuous.matrix_map (A := fun g => (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i))) ?_ hfc
    refine continuous_matrix fun a b => ?_
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp only [hχ]
    exact D.nd.chi_cont i 1
  have tr := tie.2.2 LL' h _ _ cr
  have tχ := tie.2.2 LL' h _ _ cχ
  rw [hmap] at tr tχ
  have dr' := tr.2.1.1 dr
  have dχ' := tχ.2.1.1 dχ
  have jr := (tr.2.2.2 τ τ' hτ).2 dr'
  have jχ := (tχ.2.2.2 τ τ' hτ).2 dχ'
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := (D.nbr i w hw).Kw.2
    have := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL'
      (fun σ y => h ((D.nbr i w hw).LL_split σ y)) inferInstance).2
    rw [Nat.card_eq_fintype_card]
    exact this
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hrep : matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x))) =
      (D.nbr i w hw).repE LL' ((mapRep f (r x)).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [matRep_apply]
    rfl
  have key := local_twist_dual (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) hT (D.nbr i w hw).Kw LL' hs
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))
    ((D.nbr i w hw).repE LL' ((mapRep f χ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype))
    (fun g => f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ))
    (by
      intro g v
      funext a
      change Matrix.mulVec ((χ (ι g) : Matrix (Fin 1) (Fin 1) (D.nd.O i)).map f) v a = _
      rw [Subsingleton.elim a 0]
      simp [Matrix.mulVec, dotProduct, hχ])
    (by
      intro g
      ext a b
      congr 1
      change f (rO D.nd i r x (ι g) a b) = f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g) a b)
      rw [← map_mul, Units.mul_inv_cancel_left])
    (by
      intro g
      have e := congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
      have e' : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
          ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) :=
        by
        have e2 := congrArg (IntermediateField.inclusion h) e
        exact e2.trans ((IntermediateField.inclusion h).commutes _)
      rw [← e']
      ext a b
      congr 1
      change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
          rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
      rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
      congr 1
      ring)
    (by
      rw [hrep]
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dr')
    (by
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dχ')
    τ' c
    (by
      intro a
      refine (jχ a).symm.trans ?_
      rw [hc, Multiset.count_singleton]
      split_ifs <;> rfl)
  rw [hrep] at key
  refine ⟨key.1, key.2.1, fun a => ⟨?_, ?_⟩⟩
  · exact (key.2.2 a).1.trans (jr (a + c)).symm
  · exact (key.2.2 a).2.trans (jr (c - a - 1)).symm

end GlobalTheory.TwistRead
