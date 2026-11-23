import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfPairing
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem toMatrix_mem_latRat (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    LinearMap.toMatrix' x ∈ latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) := by
  have hA : D.host.AA = D.host.AA0 := by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
      refine Matrix.ext fun i j => ?_
      have h1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
        funext a
        rw [Finset.sum_apply, Pi.single_apply, ← hss a j]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [Matrix.sum_apply, LinearMap.toMatrix'_apply]
      change r * x (Pi.single j 1) i = _
      rw [h1, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, genMap, Matrix.of_apply]
      ring
    rw [e]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨r, hA ▸ hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
      ext i j; rfl
    rw [e]
    exact smul_mem_latRat c hx

theorem smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 E))}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c)
    (Q : HeightOneSpectrum (𝓞 E)) : (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ expS SS Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hy Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ expS SS Q)⁻¹ → (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 2 (by field_simp)
  · exact key 0 (by simp)
  · exact key 1 (by simp)

theorem conj_comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (h0 : infPart D e = 0) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : Formalism.L2.Col.cO D.host.E s ∉ P.asIdeal := hs
  have hne : Formalism.L2.Col.cO D.host.E s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (by rw [show s = 0 from RingOfIntegers.ext h, map_zero])
  have h1 : finPart D (e * incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h2 := GlobalTheory.PlaceVec.cF_mem_int (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1)
  rw [← GlobalTheory.AdelicLatMove.toEAf_cA, RingHom.map_mul (cA D)] at h2
  have h3 : cA D (incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) = incA D (s : D.host.E)⁻¹ := by
    change incA D (star (star (s : D.host.E))⁻¹) = _
    rw [star_inv₀, star_star]
  rw [h3] at h2
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (GlobalTheory.PlaceVec.finPart_mem_intAE h2) _
    (finTens_mem_latO (one_mem_intAf _) (toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.PlaceVec.infPart_cA h0
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem char_sympl_halfB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ u ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), ψ (symplO S T (c • u) (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) = 1 := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ _ ⟨ΛS, dS, eS⟩ ⟨ΛT, dT, eT⟩ y hy u hu
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hu
  change ψ (symplO S T (c • u) ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r)) = 1
  have hmem : c • ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
    have e1 : c • ((LinearMap.toMatrix' y).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E) • y)).map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j
      rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, map_sum, nsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun PP _ => ?_
      change _ = cA D (es PP) * incA D ((c : D.host.E) * LinearMap.toMatrix' y i j)
      rw [RingHom.map_mul (incA D), map_natCast, mul_left_comm]
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc dS (hes PP hPP) ?_ (smul_mem_locP hc hy _)
    refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  have h := char_sympl_eq_one hP.std dS dT hu hmem
  rw [← symplHom_apply, map_nsmul] at h
  rw [← symplHom_apply, map_nsmul]
  exact h

end GlobalTheory.AdForm.HalfPairing
