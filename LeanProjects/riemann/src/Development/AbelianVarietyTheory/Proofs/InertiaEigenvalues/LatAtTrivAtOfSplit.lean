import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedEntriesIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportedAdelicPointEqOneWhereIdempotentVanishesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentAddConjSupportFinitePrimeToPStatement

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdAtPrime

theorem isIdemSum_idem (D : D7) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (hQ : GlobalTheory.ExportSeries.SplitSet Q) : IsIdemSum (idem Q) Q := by
  obtain ⟨e, he⟩ := hQ
  have : idem Q = e := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
    rw [hsum, GlobalTheory.ExportSeries.idem]
    exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.ExportSeries.idemAt_eq (hes PP hPP)
  rw [this]
  exact he

theorem bnd_inv_of_hLat_std (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (p : ℕ) (k : Bridge.Gf V)
    (hk : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank) :
    Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom k.1)⁻¹.1 := by
  refine ⟨1, Nat.coprime_one_left p, fun i j Q => ?_⟩
  have hx : (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V k := by
    rw [hk]
    refine Submodule.mem_pi.2 fun i' _ => ?_
    by_cases h : i' = j
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have := (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL k _).1 hx i Q
  have e : (fun j' => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
      ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) j')) = Pi.single j 1 := by
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [e, Matrix.mulVec_single_one] at this
  rw [Nat.cast_one, one_mul]
  exact this

set_option maxHeartbeats 1600000 in

theorem latAt_trivAt_of_split : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → StdBase B → ∀ (p bad : ℕ), p.Prime → p ∣ bad → ∀ (Q : Finset (Formalism.L2.DIV.Pl D.host.E)), GlobalTheory.ExportSeries.SplitSet Q → (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ hQ : GA D V, SuppAt (idem Q) V hQ → hQ ∈ GfC V ∧ ∀ (h h' : GA D V) (γ : GQ V) (k : Bridge.Gf V), SplitOffBad V bad h' → Formalism.UG.bc (Lev.swapAE D) k.1 ∈ Formalism.L2.DIV.St B.F.βS → finPt V (h * hQ) = Bridge.ratF V γ * finPt V h' * k → (⟨B.latAt (Bridge.ratF V γ⁻¹ * finPt V h * 1)⟩ : GenLat D.host.E V.rank).TrivAt p := by
  intro D V W B hB hS p bad hp hpb Q hQs hpQ hQ hsQ
  have hQsum := isIdemSum_idem D Q hQs
  have hinf : infPart D (idem Q) = 0 := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := hQsum
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun PP hPP => GlobalTheory.ExportSeries.SpecGood.infPart_eq_zero_of_isIdemAt D PP _ (hes PP hPP)
  refine ⟨GlobalTheory.WeilProduct.mem_GfC_of_supp (a := idem Q + cA D (idem Q)) ?_ hsQ, ?_⟩
  · rw [map_add, GlobalTheory.PlaceIdem.infPart_cA, hinf, map_zero, add_zero]
  intro h h' γ k hh' hk heq
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  have hL0 : (B.F.ΛS : Set (Fin V.rank → D.host.E)) = L0c D V := hS.2.2.1
  have hstd : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    apply SetLike.coe_injective
    rw [GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, ← hL0, hS.2.2.2.2]
  rw [GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0]
  have hg : Bridge.ratF V γ⁻¹ * finPt V h * 1 = finPt V h' * k * (finPt V hQ)⁻¹ := by
    have e1 : finPt V (h * hQ) = finPt V h * finPt V hQ := map_mul _ _ _
    have e2 : finPt V h = Bridge.ratF V γ * finPt V h' * k * (finPt V hQ)⁻¹ :=
      eq_mul_inv_of_mul_eq (e1.symm.trans heq)
    have e3 : Bridge.ratF V γ⁻¹ = (Bridge.ratF V γ)⁻¹ := map_inv (Bridge.ratF V) γ
    have key : ∀ {G : Type} [Group G] (a b c d f : G), b = a * c * d * f⁻¹ → a⁻¹ * b * 1 = c * d * f⁻¹ := by
      intro G _ a b c d f hb
      rw [hb, mul_one, mul_assoc, mul_assoc, inv_mul_cancel_left, ← mul_assoc]
    exact (congrArg (fun x => x * finPt V h * 1) e3).trans (key _ _ _ _ _ e2)
  rw [hg]
  have hk1 : ∀ k : Bridge.Gf V, Formalism.UG.bc (Lev.swapAE D) k.1 ∈ Formalism.L2.DIV.St B.F.βS →
      Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    intro k hk
    have hr : Bridge.IsRatMat V 1 1 := by
      simp [Bridge.IsRatMat]
    have e4 : Bridge.ratF V 1 * 1 * k = k := by
      rw [map_one (Bridge.ratF V), one_mul, one_mul]
    have e5 : B.latAt k = B.latAt 1 := by
      ext x
      have := GlobalTheory.ExportSeries.Base.mem_latAt_iff hB.frame hr 1 k hk x
      rw [e4, inv_one, Units.val_one, Matrix.one_mulVec] at this
      exact this
    exact (GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0 k).symm.trans
      (e5.trans ((GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0 1).trans hstd))
  have hkS : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank := hk1 k hk
  have hkS' : Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    refine hk1 k⁻¹ ?_
    rw [Subgroup.coe_inv, map_inv]
    exact inv_mem hk
  set M := Matrix.GeneralLinearGroup.map (n := Fin V.rank) ι.toRingHom with hM
  have hsupp : ∀ (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (g : GA D V), IsIdemSum e P →
      (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V g →
      Bnd p (M (finPt V g).1).1 ∧ Bnd p (M (finPt V g).1)⁻¹.1 := by
    intro e P g he hp' hs
    obtain ⟨S, hSf, hSp, hS0⟩ := GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p D ι hid hcj p e P he hp'
    exact GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite p hp _ (M (finPt V g).1) S hSf hSp fun Q hQ i j => GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes D ι V e g hs Q (hS0 Q hQ) i j
  obtain ⟨-, e', P', he', hb', hs'⟩ := hh'
  have hp' : ∀ PP ∈ P', (p : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hpP
    obtain ⟨c, rfl⟩ := hpb
    exact hb' PP hPP (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpP)
  obtain ⟨b1, b1'⟩ := hsupp e' P' h' he' hp' hs'
  obtain ⟨b3, b3'⟩ := hsupp (idem Q) Q hQ hQsum hpQ hsQ
  have b2' : Bnd p (M k.1)⁻¹.1 := bnd_inv_of_hLat_std D ι h1 h2 V hstd p k hkS
  have b2 : Bnd p (M k.1).1 := by
    have := bnd_inv_of_hLat_std D ι h1 h2 V hstd p k⁻¹ hkS'
    rwa [Subgroup.coe_inv, map_inv, inv_inv] at this
  have eM : M (finPt V h' * k * (finPt V hQ)⁻¹).1 = M (finPt V h').1 * M k.1 * (M (finPt V hQ).1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
  refine GlobalTheory.T.bounded_entries_integral D ι h1 h2 V hstd p _ ?_ ?_
  · rw [eM, Units.val_mul, Units.val_mul]
    exact bnd_mul p _ _ _ (bnd_mul p _ _ _ b1 b2) b3'
  · rw [eM, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    exact bnd_mul p _ _ _ b3 (bnd_mul p _ _ _ b2' b1')

end GlobalTheory.StdAtPrime
