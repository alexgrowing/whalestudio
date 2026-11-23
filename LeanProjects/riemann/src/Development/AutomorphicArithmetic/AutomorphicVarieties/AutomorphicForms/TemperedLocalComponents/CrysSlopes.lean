import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeRhamLeFiltrationShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeRhamInfFiltration
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusIterateMatrixForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DdRLeFilAndInfFilEqBotOfHodgeTateMult
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusResidueDegreeFixes
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiltrationEntriesOfFrobeniusMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallinePeriodMatrixRelation
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallineOfPlaceOver
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiltrationInverseFrobeniusMatrix

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.Pst GlobalTheory.PstCoeff UpperTheory.V.Loc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Sat

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem val_inv_eq' (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

private theorem mem_eig {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (g : Weil h) (hg : deg g = -1) (b : ℂ) (hb : b ∈ algSat n (normV w) B) : b ∈ (rc (algNorm σ)).eig g := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  have hBα : B = Finset.univ.val.map α := hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  have e' : rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
    rw [rec_algNorm H, e, WD.lpTw_mk]
    refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
    simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
  simp only [hBα, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton,
    Multiset.mem_map] at hb
  obtain ⟨i, -, rfl⟩ := hb
  rw [e', WD.eig_mk, WDRep.diag_ρ, charpoly_diagEnd, hg,
    mem_roots (monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).ne_zero, IsRoot, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [val_inv_eq']
  simp

end Sat

private theorem norm_root {l : ℕ} [Fact l.Prime] {x y : Om l} (hy : aeval y (minpoly ℚ_[l] x) = 0) : ‖y‖ = ‖x‖ := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have e : minpoly ℚ_[l] x = minpoly ℚ_[l] y :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx)
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, e]

private theorem rep_slope {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ) (hf : 0 < f)
    (hσ : ∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (hc : IsCrys ((PP l).PD K) ρ) (β : Om l)
    (x : V ⊗[ℚ_[l]] Bcr l) (hx : x ∈ Dcris ((PP l).PD K) ρ) (h0 : x ≠ 0)
    (hq : aeval ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ f)
      (minpoly ℚ_[l] β) x = 0) :
    (∀ a : ℤ, DdR ((PP l).PD K) ρ ≤ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a →
      ‖((l : Om l) ^ f) ^ (-a) * β‖ ≤ 1) ∧
    ∀ b : ℤ, DdR ((PP l).PD K) ρ ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) (b + 1) = ⊥ →
      ‖((l : Om l) ^ f) ^ b * β⁻¹‖ ≤ 1 := by
  let e := Module.finBasis ℚ_[l] V
  obtain ⟨M, M', A, hM, hA, hφ, hρ⟩ := UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys K ρ e hc
  obtain ⟨F, -, hF⟩ := UpperTheory.frobenius_iterate_matrix_form K M A hA hφ f
  obtain ⟨γ, hγ, hr⟩ := UpperTheory.crystalline_period_matrix_relation K f hσ ρ e M M' hM hρ F hF x hx h0 _
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral β)) hq
  have hn := norm_root hr
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have := UpperTheory.filtration_entries_of_frobenius_matrix K f hf hσ M M' A F hM hA hφ hF a (UpperTheory.de_rham_le_filtration_shift K ρ e M M' hM hρ a ha) γ hγ
    rwa [norm_mul, hn, ← norm_mul] at this
  · have := UpperTheory.filtration_inverse_frobenius_matrix K f hf hσ M M' A F hM hA hφ hF b (UpperTheory.de_rham_inf_filtration K ρ e M M' hM hρ b hb) γ hγ
    rwa [norm_mul, norm_inv, hn, ← norm_inv, ← norm_mul] at this

end UpperTheory.V.Af

open UpperTheory.V.Af in
theorem UpperTheory.V.Af.crysSlopes :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.CrysSlopes := by
  intro _ F Ω _ _ _ _ _ p _ _ ι n m r _ w A h O _ _ _ Bw hj hcr hJ σ B hB rc hrc hwd b hb
  obtain ⟨T⟩ := tiedP p
  have hp : IsPstAt (PP p) Bw (r.comp (Dec (F := F) A).subtype) := by
    obtain ⟨L, r', h1, h2⟩ := hcr
    exact ⟨L, r', h1, GlobalTheory.PstOfCrys.isPst_of_isCrys T _ h2⟩
  obtain ⟨L, r', hm, hpst, hw⟩ := wdAt_of_isPstAt ι Bw h hj hp
  have hc : IsCrys ((PP p).PD Bw.Kw) (Bw.repE L r') := (hm.isCrysAt_iff (PP p)).1 hcr
  obtain ⟨g, hg⟩ := deg_surjective (h := h) (-1)
  have he := mem_eig hrc σ B hB g hg b hb
  rw [← hwd, hw] at he
  obtain ⟨x, hx, h0, hq⟩ := UpperTheory.crystalline_of_place_over (PP p) ι Bw h hj (Bw.repE L r') hpst hc g hg b he _
    (minpoly.aeval ℚ_[p] (ι.symm b))
  obtain ⟨hf, hσ⟩ := UpperTheory.frobenius_residue_degree_fixes (PP p) Bw h hj
  haveI := L.2
  haveI : FiniteDimensional ℚ_[p] (Fin n → ↥L.1) := Module.Finite.trans ↥L.1 _
  obtain ⟨hlo, hhi⟩ := rep_slope Bw.Kw _ hf hσ (resQ (Bw.repE L r'))
    ((GlobalTheory.BSCoeff.isCrys_resQ_iff (PP p) _).2 hc) (ι.symm b) x (by rw [GlobalTheory.BSCoeff.Dcris_resQ]; exact hx) h0 hq
  have hsplit : ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[p]] Om p) (y : ↥Bw.Kw.1), τ y ∈ L.1 := fun τ y => hm.1 (Bw.LL_split τ y)
  have hJ' : ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[p]] ↥L.1, ∃ τ : F →+* Om p, IsInduced Bw τ τ' := fun τ' =>
    ⟨(L.1.val.comp τ').toRingHom.comp ((Bw.j.comp (algebraMap F Ω)).codRestrict Bw.Kw.1 Bw.j_E), fun _ => rfl⟩
  have hmult : ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[p]] ↥L.1) (c : ℤ), (∀ i, -m i ≠ c) →
      multV ((PP p).PD Bw.Kw) (Bw.repE L r') τ' c = 0 := fun τ' c hc' => by
    obtain ⟨τ, hτ⟩ := hJ' τ'
    have h1 := IsJumpsAt.count_eq (PP p) hm hτ (hJ τ L τ' hτ) c
    rw [Multiset.count_eq_zero.2 (by simpa using hc')] at h1
    exact h1.symm
  have hdR : Bw.IsdRE (PP p) L r' := by
    obtain ⟨τ, hτ⟩ := hJ' (Bw.Kw.1.val.codRestrict L.1.toSubalgebra (hsplit _))
    obtain ⟨L₁, r₁, h1, h2, -⟩ := hJ τ L _ hτ
    exact (hm.isdRAt_iff (PP p)).1 ⟨L₁, r₁, h1, h2⟩
  obtain ⟨k1, k2⟩ := UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult (PP p) hsplit (Bw.repE L r') (finiteDimensional_DdR _ _ hdR)
  have hq' : ι.symm ((normV w : ℕ) : ℂ) = (p : Om p) ^ resDeg p w := by
    rw [map_natCast, normV_eq_pow (hj.mem_placesOver h), Nat.cast_pow]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [map_mul, map_zpow₀, map_inv₀, hq']
    refine hhi a (eq_bot_iff.2 fun y hy => ?_)
    have := k2 a fun τ c hc' => hmult τ c fun i => by have := ha i; omega
    have hy1 := hy.1
    rw [DdR_resQ] at hy1
    exact this.le ⟨hy1, hy.2⟩
  · rw [map_mul, map_zpow₀, hq', ← neg_neg a]
    refine hlo (-a) fun y hy => ?_
    rw [DdR_resQ] at hy
    exact k1 (-a) (fun τ c hc' => hmult τ c fun i => by have := ha i; omega) hy

end
