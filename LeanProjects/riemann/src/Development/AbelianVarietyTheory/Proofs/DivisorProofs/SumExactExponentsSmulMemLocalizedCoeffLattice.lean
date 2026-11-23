import Mathlib
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.RowLat
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulMemLocPOfVal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquare
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem natCast_notMem_of_not_dvd [StarRing K] (w : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ m) : (m : 𝓞 K) ∉ w.asIdeal := by
  intro h
  apply hm
  have h1 : ((m : ℕ) : 𝓞 K ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  unfold Formalism.EigenvalueLevelCeiling.plc
  exact (CharP.cast_eq_zero_iff (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) m).1 h1

theorem factor_mem (w : HeightOneSpectrum (𝓞 K)) (p e n : ℕ) (ν : Fin n → ℕ)
    (hpw : ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 K) ∉ w.asIdeal) (hI : Formalism.CohomologicalDescent.LA.InclZ n n le_rfl ν p e) :
    ∀ f ∈ (Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n ν).map (toK K (Fin n × Fin n)),
      ((p : K) ^ e) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
        ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K (Fin n × Fin n))) := by
  obtain ⟨m, hm, hmx⟩ := hI
  have hm0 : (m : K) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hm (dvd_zero p)
  have hval : w.valuation K ((m : K)⁻¹) ≤ 1 := by
    have h1 : w.valuation K (algebraMap (𝓞 K) K (m : 𝓞 K)) = 1 :=
      (w.valuation_eq_one_iff_notMem).2 (hpw m hm)
    rw [map_natCast] at h1
    rw [map_inv₀, h1, inv_one]
  rintro _ ⟨g, hg, rfl⟩
  rw [GlobalTheory.StdDual.dualWeyl_eq, ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))] at hg
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨b, hb, rfl⟩ := hq
    have hbD : b ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.subset_span hb
    have h1 := GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom (𝓞 K)) le_rfl ν _ (hmx b hbD)
    have h2 := GlobalTheory.JetOpWeylLat.smul_mem_localizationAt_of_valuation w hval (Submodule.mem_map_of_mem (f := toK K (Fin n × Fin n)) h1)
    convert h2 using 1
    rw [GlobalTheory.JetOpWeylLat.toK_map_int, GlobalTheory.JetOpWeylLat.toK_map_int, map_zsmul, ← Int.cast_smul_eq_zsmul K,
      smul_smul]
    congr 1
    push_cast
    field_simp
  | zero => simpa using zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add, smul_add]
    exact add_mem ha hb
  | smul a g _ hg =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ a hg

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem tensor_mem (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (c : K)
    (e : ι → ℕ)
    (h : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      (c ^ e τ) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)))) :
    ∀ z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      (c ^ ∑ τ, e τ) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  classical
  have key : ∀ y ∈ nabStd K lam, (c ^ ∑ τ, e τ) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro y hy
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hy
    induction hy using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨F, hF, rfl⟩ := hP
      choose t ht hFt using fun τ => (lc_mem_locP w _ _).1 (h τ (F τ) (hF τ))
      have hnot : (∏ τ, t τ) ∉ w.asIdeal :=
        Submonoid.prod_mem w.asIdeal.primeCompl (t := Finset.univ) (f := t) (fun τ _ => ht τ)
      refine (lc_mem_locP w _ _).2 ⟨∏ τ, t τ, hnot, ?_⟩
      have hFt' : ∀ τ, (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ ∈
          (delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)) := fun τ => by
        have e1 : t τ • c ^ e τ • F τ = (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ :=
          (algebraMap_smul K (t τ) _).symm.trans (smul_smul _ _ _)
        convert hFt τ using 1
        exact e1.symm
      have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) ∈ delStd K lam :=
        Submodule.subset_span ⟨_, hFt', rfl⟩
      have e2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) =
          ((algebraMap (𝓞 K) K (∏ τ, t τ)) * c ^ ∑ τ, e τ) • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ) := by
        simp only [map_smul, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod, map_mul,
          Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.rename_C]
        congr 2
        rw [← map_prod, Finset.prod_pow_eq_pow_sum]
      rw [e2] at hmem
      convert hmem using 1
      exact (algebraMap_smul K (∏ τ, t τ) _).symm.trans (smul_smul _ _ _)
    | zero => simpa using zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact add_mem ha hb
    | smul a y _ hy =>
      have e3 : (c ^ ∑ τ, e τ) • a • y = a • (c ^ ∑ τ, e τ) • y := smul_comm _ _ _
      convert Submodule.smul_mem _ a hy using 1
      exact e3
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (lc_mem_locP w _ _).1 hz
  obtain ⟨t, ht, htz⟩ := (lc_mem_locP w _ _).1 (key _ hsz)
  refine (lc_mem_locP w _ _).2 ⟨t * s, lc_mul_notMem w ht hs, ?_⟩
  convert htz using 1
  exact (mul_smul t s _).trans (congrArg (t • ·) (smul_comm s _ z))

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

theorem exZ_sum_smul_mem_locP_delAtr :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ)
      (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
      Submodule.IsLattice E L → ∀ (w : HeightOneSpectrum (𝓞 K)), ∀ x ∈ nabAtr emb lam L,
        (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) • x ∈
          Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam L) := by
  intro E K _ _ _ _ _ ι _ n emb lam L hL w x hx
  have hM : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ L)) := fun τ =>
    du_dualFr_lattice basisAtEx _ (tauLatLattice E K ι n emb τ L hL)
  choose B hB using fun τ => basisAtEx K n _ (hM τ) w
  have hx1 : (x : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ L)) :=
    lc_le_locP w _ hx
  rw [(nabDelLoc K ι n lam _ hM w B hB).1] at hx1
  obtain ⟨z, hz, hzx⟩ := hx1
  have hfac : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      ((Formalism.EigenvalueLevelCeiling.plc w : K) ^ Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w)) • f ∈
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n))) := fun τ =>
    factor_mem w (Formalism.EigenvalueLevelCeiling.plc w) _ n (lam τ).natW (fun m hm => natCast_notMem_of_not_dvd w hm)
      (Formalism.CohomologicalDescent.LA.exact_z_specialization n n le_rfl _ (natW_antitone _) _ (Formalism.EigenvalueLevelCeiling.plc_prime w))
  have hz' := tensor_mem w lam (Formalism.EigenvalueLevelCeiling.plc w : K) _ hfac z hz
  refine (GlobalTheory.LvT.Built.ValLat.mem_localization_delAtr emb lam w hL B hB _).2 ⟨_, hz', ?_⟩
  have e1 : (actP lam B) z = (x : Pol K ι n) := hzx
  rw [map_smul, e1]
  refine (algebraMap_smul K (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^
    (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) (x : Pol K ι n)).symm.trans ?_
  simp only [map_pow, map_natCast]

end GlobalTheory.OntoExponentsLat
