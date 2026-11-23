import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupLatticeLocalisationOfUnitBall
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSideStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasis

theorem exists_basis_of_loc (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module K V] (N : Set V)
    (h0 : (0 : V) ∈ N) (hadd : ∀ f ∈ N, ∀ g ∈ N, f + g ∈ N)
    (hsm : ∀ (x t : 𝓞 K), t ∉ P.asIdeal → ∀ f ∈ N, ((x : K) / (t : K)) • f ∈ N)
    (hsp : ∀ f : V, ∃ c : K, c ≠ 0 ∧ c • f ∈ N)
    (m : ℕ) (g : Fin m → V)
    (hbd : ∀ f ∈ N, ∃ t : 𝓞 K, t ∉ P.asIdeal ∧ ∃ c : Fin m → 𝓞 K, (t : K) • f = ∑ k, (c k : K) • g k) :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) K V), (∀ s, B s ∈ N) ∧
      ∀ f ∈ N, ∀ s, ∃ x t : 𝓞 K, t ∉ P.asIdeal ∧ B.repr f s = (x : K) / (t : K) := by
  classical
  have hle : P.asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 K) := fun t ht =>
    mem_nonZeroDivisors_of_ne_zero fun h => ht (h ▸ P.asIdeal.zero_mem)
  let R := Localization.subalgebra.ofField K P.asIdeal.primeCompl hle
  haveI : IsLocalization.AtPrime R P.asIdeal := (inferInstance : IsLocalization P.asIdeal.primeCompl R)
  haveI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) P.ne_bot R
  have mk'_coe : ∀ (x : 𝓞 K) (t : P.asIdeal.primeCompl),
      ((IsLocalization.mk' R x t : R) : K) = (x : K) / ((t : 𝓞 K) : K) := by
    intro x t
    have ht : ((t : 𝓞 K) : K) ≠ 0 := by
      intro h
      exact t.2 ((show (t : 𝓞 K) = 0 by exact_mod_cast h) ▸ P.asIdeal.zero_mem)
    rw [eq_div_iff ht]
    have h := congrArg (algebraMap R K) (IsLocalization.mk'_spec R x t)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    exact h
  have memR : ∀ r : R, ∃ x t : 𝓞 K, t ∉ P.asIdeal ∧ (r : K) = (x : K) / (t : K) := by
    intro r
    obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl r
    exact ⟨x, t, t.2, mk'_coe x t⟩
  have inR : ∀ x t : 𝓞 K, t ∉ P.asIdeal → ∃ r : R, (r : K) = (x : K) / (t : K) :=
    fun x t ht => ⟨IsLocalization.mk' R x (⟨t, ht⟩ : P.asIdeal.primeCompl), mk'_coe x ⟨t, ht⟩⟩
  have smul_def : ∀ (r : R) (f : V), r • f = (r : K) • f := fun r f => rfl
  let NR : Submodule R V :=
    { carrier := N
      add_mem' := fun {a b} ha hb => hadd a ha b hb
      zero_mem' := h0
      smul_mem' := fun r f hf => by
        obtain ⟨x, t, ht, hr⟩ := memR r
        change r • f ∈ N
        rw [smul_def, hr]
        exact hsm x t ht f hf }
  let L : Submodule R V := Submodule.span R (Set.range g)
  have hNL : NR ≤ L := by
    intro f hf
    obtain ⟨t, ht, c, hc⟩ := hbd f hf
    have ht0 : (t : K) ≠ 0 := by
      intro h
      exact ht ((show t = 0 by exact_mod_cast h) ▸ P.asIdeal.zero_mem)
    have hf' : f = ∑ k, ((c k : K) / (t : K)) • g k := by
      have : f = (t : K)⁻¹ • ((t : K) • f) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [this, hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, div_eq_inv_mul]
    rw [hf']
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := inR (c k) t ht
    rw [← hr, ← smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI : Module.Finite R L := Module.Finite.span_of_finite R (Set.finite_range g)
  haveI : NoZeroSMulDivisors R V := ⟨fun {r f} h => by
    rw [smul_def] at h
    rcases smul_eq_zero.1 h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h⟩
  haveI : NoZeroSMulDivisors R L := ⟨fun {r x} h =>
    (smul_eq_zero.1 (congrArg Subtype.val h : r • (x : V) = 0)).imp id fun h' => Subtype.ext h'⟩
  haveI : Module.IsTorsionFree R L := inferInstance
  haveI : Module.Free R L := Module.free_of_finite_type_torsion_free'
  obtain ⟨n, B'⟩ := Submodule.basisOfPidOfLE hNL (Module.Free.chooseBasis R L)
  let v : Fin n → V := fun s => ((B' s : NR) : V)
  have hliR : LinearIndependent R v :=
    B'.linearIndependent.map' NR.subtype (Submodule.ker_subtype NR)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing R K).1 hliR
  have hexp : ∀ y : NR, (y : V) = ∑ s, ((B'.repr y s : R) : K) • v s := by
    intro y
    have h := congrArg (fun y : NR => (y : V)) (B'.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    rfl
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro f _
    obtain ⟨c, hc, hcf⟩ := hsp f
    have h1 : c • f ∈ Submodule.span K (Set.range v) := by
      rw [show c • f = ((⟨c • f, hcf⟩ : NR) : V) from rfl, hexp]
      exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
    have h2 := Submodule.smul_mem _ c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  let B := Module.Basis.mk hli hspan
  have hBv : ∀ s, B s = v s := fun s => Module.Basis.mk_apply hli hspan s
  refine ⟨n, B, fun s => ?_, fun f hf s => ?_⟩
  · rw [hBv]; exact (B' s).2
  · have e1 : f = B.equivFun.symm (fun s => ((B'.repr ⟨f, hf⟩ s : R) : K)) := by
      rw [Module.Basis.equivFun_symm_apply]
      simp only [hBv]
      exact hexp ⟨f, hf⟩
    have e2 : B.repr f s = ((B'.repr ⟨f, hf⟩ s : R) : K) := by
      have e3 := congrArg (fun u => B.equivFun u s) e1
      simp only [LinearEquiv.apply_symm_apply] at e3
      rw [← Module.Basis.equivFun_apply]
      exact e3
    obtain ⟨x, t, ht, hr⟩ := memR (B'.repr ⟨f, hf⟩ s)
    exact ⟨x, t, ht, e2.trans hr⟩

end GlobalTheory.LocBasis

namespace GlobalTheory.GeoTie

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem supLattice_fg (YS : NX.NExpRealS Rl cG S) (fw : FWTie T0 Rl.toRealDat κ v₀) (j : Fin D.R.m) : ((S.A ((j : ℕ) + 1)).MK).FG := by
  classical
  obtain ⟨m, g', hg'⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).1
  have hsc : ∀ (a : S.Ks) (w : Fin (Rl.nW j) → D.what₂.LL),
      (YS.fi j).e.symm ((YS.fi j).eK a • w) = a • (YS.fi j).e.symm w := by
    intro a w
    rw [← algebraMap_smul D.what₂.LL ((YS.fi j).eK a) w, (YS.fi j).eK_LL, LinearEquiv.map_smul, algebraMap_smul]
  let d : 𝓞 T0.Q.c.F → 𝓞 S.Ks := fun c =>
    ⟨(YS.fi j).eK.symm (c : T0.Q.c.F), map_isIntegral_int (YS.fi j).eK.symm.toRingHom c.isIntegral_coe⟩
  refine Submodule.fg_iff_exists_fin_generating_family.2 ⟨m, fun k => (YS.fi j).e.symm (g' k), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ((YS.fi j).mkK _).2 ?_
    rw [LinearEquiv.apply_symm_apply, ← hg']
    exact Submodule.subset_span ⟨k, rfl⟩
  · intro x hx
    have h1 : (YS.fi j).e x ∈ Submodule.span (𝓞 T0.Q.c.F) (Set.range g') := by
      rw [hg']; exact ((YS.fi j).mkK x).1 hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun k => d (c k), ?_⟩
    calc ∑ k, d (c k) • (YS.fi j).e.symm (g' k) = (YS.fi j).e.symm (∑ k, c k • g' k) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← algebraMap_smul T0.Q.c.F (c k) (g' k)]
          have e1 : ((c k : T0.Q.c.F)) = (YS.fi j).eK ((YS.fi j).eK.symm (c k)) := ((YS.fi j).eK.apply_symm_apply _).symm
          rw [show algebraMap (𝓞 T0.Q.c.F) T0.Q.c.F (c k) = (c k : T0.Q.c.F) from rfl, e1, hsc,
            ← algebraMap_smul S.Ks (d (c k))]
          rfl
      _ = x := by rw [hc, LinearEquiv.symm_apply_apply]

end GlobalTheory.GeoTie

namespace GlobalTheory.GeoTie

theorem locBall_basis_exists : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∃ (n : ℕ) (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))), (∀ s, B s ∈ locBall YS fw iC b j) ∧ ∀ g ∈ locBall YS fw iC b j, ∀ s, ‖embS S iC b (B.repr g s)‖ ≤ 1 := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j hsp
  classical
  set P := placeAt (embS S iC b) with hP
  have hS1 : ∀ f ∈ locBall YS fw iC b j, ∃ t : 𝓞 S.Ks, t ∉ P.asIdeal ∧
      (show ↥(S.A ((j : ℕ) + 1)).WK from ((t : S.Ks) • f : NX.FmK S ((j : ℕ) + 1))).1 ∈ (S.A ((j : ℕ) + 1)).MK := by
    have hS1a : ∀ f ∈ locBall YS fw iC b j, ∀ y : (Rl.FW j).Pt (placeC YS iC b),
        (Rl.FW j).nrm (placeC YS iC b) y ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
          ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ ≤ 1 :=
      GlobalTheory.T.norm_le_one_of_mem_localUnitBall_side D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j
    intro f hf
    obtain ⟨s, hs, hsf⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (Rl.FW j)
      (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).2 (placeC YS iC b) _ (hS1a f hf)
    have heK : ∀ a : S.Ks, (YS.fi j).eK a = eKs YS a := fun a =>
      (algebraMap T0.Q.c.F D.what₂.LL).injective (((YS.fi j).eK_LL a).trans (eKs_LL YS a).symm)
    let t : 𝓞 S.Ks := ⟨(YS.fi j).eK.symm (s : T0.Q.c.F), map_isIntegral_int (YS.fi j).eK.symm.toRingHom s.isIntegral_coe⟩
    have ht : eKs YS (t : S.Ks) = (s : T0.Q.c.F) := by
      rw [← heK]; exact (YS.fi j).eK.apply_symm_apply _
    refine ⟨t, ?_, ?_⟩
    · intro htP
      apply hs
      change ‖embC YS iC b (s : T0.Q.c.F)‖ < 1
      rw [← ht, embC_eKs]
      exact htP
    · refine ((YS.fi j).mkK _).2 ?_
      change (YS.fi j).e ((t : S.Ks) • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1) ∈ (Rl.FW j).MK
      rw [← algebraMap_smul D.what₂.LL (t : S.Ks), LinearEquiv.map_smul, ← (YS.fi j).eK_LL, algebraMap_smul, heK, ht]
      rw [← algebraMap_smul T0.Q.c.F s] at hsf
      exact hsf
  have hS2 : ((S.A ((j : ℕ) + 1)).MK).FG := supLattice_fg YS fw j

  have hunit : ∀ t : 𝓞 S.Ks, t ∉ P.asIdeal → ‖embS S iC b (t : S.Ks)‖ = 1 := fun t ht =>
    le_antisymm (norm_int_le_one _ t) (not_lt.1 ht)
  have hloc : ∀ x t : 𝓞 S.Ks, t ∉ P.asIdeal → ‖embS S iC b ((x : S.Ks) / (t : S.Ks))‖ ≤ 1 := by
    intro x t ht
    rw [map_div₀, norm_div, hunit t ht, div_one]
    exact norm_int_le_one _ x

  have h0 : (0 : NX.FmK S ((j : ℕ) + 1)) ∈ locBall YS fw iC b j := by
    intro z
    rw [map_zero]
    simp [valC_zero]
  have hadd : ∀ f ∈ locBall YS fw iC b j, ∀ g ∈ locBall YS fw iC b j, f + g ∈ locBall YS fw iC b j := by
    intro f hf g hg z
    rw [map_add, Submodule.coe_add, valC_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf z) (hg z))
  have hsm : ∀ (x t : 𝓞 S.Ks), t ∉ P.asIdeal → ∀ f ∈ locBall YS fw iC b j,
      (((x : S.Ks) / (t : S.Ks)) • f) ∈ locBall YS fw iC b j := by
    intro x t ht f hf z
    rw [valC_cuspOf_smul, norm_mul]
    exact mul_le_one₀ (hloc x t ht) (norm_nonneg _) (hf z)
  obtain ⟨m, g0, hg0⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hS2
  have hgWK : ∀ k, g0 k ∈ (S.A ((j : ℕ) + 1)).WK := fun k => by
    have h : g0 k ∈ (S.A ((j : ℕ) + 1)).MK := hg0 ▸ Submodule.subset_span ⟨k, rfl⟩
    exact h.1
  let g : Fin m → NX.FmK S ((j : ℕ) + 1) := fun k => ⟨g0 k, hgWK k⟩
  have hbd : ∀ f ∈ locBall YS fw iC b j, ∃ t : 𝓞 S.Ks, t ∉ P.asIdeal ∧ ∃ c : Fin m → 𝓞 S.Ks,
      (t : S.Ks) • f = ∑ k, (c k : S.Ks) • g k := by
    intro f hf
    obtain ⟨t, ht, htf⟩ := hS1 f hf
    rw [← hg0] at htf
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 htf
    refine ⟨t, ht, c, Subtype.ext ?_⟩
    rw [← hc]
    change _ = (S.A ((j : ℕ) + 1)).WK.subtype (∑ k, (c k : S.Ks) • g k)
    refine Eq.trans ?_ (map_sum (S.A ((j : ℕ) + 1)).WK.subtype
      (fun k => ((c k : S.Ks) • g k : ↥(S.A ((j : ℕ) + 1)).WK)) Finset.univ).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (algebraMap_smul S.Ks (c k) (g0 k)).symm
  obtain ⟨n, B, hB, hrep⟩ := GlobalTheory.LocBasis.exists_basis_of_loc S.Ks P (NX.FmK S ((j : ℕ) + 1))
    (locBall YS fw iC b j) h0 hadd hsm hsp m g hbd
  refine ⟨n, B, hB, fun f hf s => ?_⟩
  obtain ⟨x, t, ht, hx⟩ := hrep f hf s
  rw [hx]
  exact hloc x t ht

end GlobalTheory.GeoTie
