import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypePartLeEigensystemPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartLeEigensystemPartPrincipalLevelStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ClosureImageSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeHasSphericalHeckeEigensystem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonzeroLiftPartTypeGivesNonzeroTypeVectorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.IsotPart

theorem eq_zero_of_mem_iSup_eig {M : Type} [AddCommGroup M] [Module ℂ M] {ι κ : Type} (op : κ → M →ₗ[ℂ] M) (ev : ι → κ → ℂ)
    (E : ι → Submodule ℂ M) (hE : ∀ a k, ∀ x ∈ E a, op k x = ev a k • x) (Ec : Submodule ℂ M) (evc : κ → ℂ)
    (hEc : ∀ k, ∀ x ∈ Ec, op k x = evc k • x) (S : Finset ι) (hS : ∀ a ∈ S, ∃ k, ev a k ≠ evc k) :
    ∀ x ∈ Ec, x ∈ (⨆ a ∈ S, E a) → x = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro x _ hx
    simpa using hx
  | insert a S ha ih =>
    intro x hxc hx
    obtain ⟨k, hk⟩ := hS a (Finset.mem_insert_self a S)
    have ih' := ih (fun b hb => hS b (Finset.mem_insert_of_mem hb))
    rw [Finset.iSup_insert, Submodule.mem_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    set f : M →ₗ[ℂ] M := op k - ev a k • LinearMap.id with hf
    have hfy : f y = 0 := by
      rw [hf, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hE a k y hy, sub_self]
    have hmap : ∀ b, (E b).map f ≤ E b := by
      rintro b _ ⟨u, hu, rfl⟩
      have e1 : f u = (ev b k - ev a k) • u := by
        rw [hf, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hE b k u hu, sub_smul]
      rw [e1]
      exact (E b).smul_mem _ hu
    have hfz : f z ∈ ⨆ b ∈ S, E b := by
      have h1 : (⨆ b ∈ S, E b).map f ≤ ⨆ b ∈ S, E b := by
        rw [Submodule.map_iSup]
        refine iSup_le fun b => ?_
        rw [Submodule.map_iSup]
        exact iSup_le fun hb => (hmap b).trans (le_iSup₂ (f := fun b (_ : b ∈ S) => E b) b hb)
      exact h1 ⟨z, hz, rfl⟩
    have hfx : f (y + z) = (evc k - ev a k) • (y + z) := by
      rw [hf, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hEc k _ hxc, sub_smul]
    have hmem : (evc k - ev a k) • (y + z) ∈ ⨆ b ∈ S, E b := by
      rw [← hfx, map_add, hfy, zero_add]
      exact hfz
    have h0 := ih' _ (Ec.smul_mem _ hxc) hmem
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hk
    · exact h

theorem heckeOn_of_mem_partFull {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {B : Finset (GA D V)}
    (hB : Hecke₂ V J χ Sb P d B) (x : MMap M) (hx : x ∈ partFull θ M J χ Sb c) :
    heckeOn M B x = c P d • x := by
  have h2 := ((mem_partFull θ M J χ Sb c x).1 hx).2 P d B hB
  ext v g
  simp [heckeOn, postOn_apply, h2 v]

theorem exists_carried_agree : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ) (w : (R.HW i (sg0 D A3.A)).H), w ≠ 0 → w ∈ R.Wc' i c → w ∈ R.Wp3 i p → ∃ c', R.Carries p c' ∧ ∀ P d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) R.SF P d B → c' P d = c P d := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH i p c w hw0 hwc hwp
  classical
  obtain ⟨hCore, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hinj := (hCore.models.HW i (sg0 D A3.A)).1
  by_contra hcon
  push_neg at hcon
  set J := levS _ (R.βW i) (R.datWp i R.triv) with hJ
  set χ := levChi _ (R.βW i) (R.datWp i R.triv) with hχ
  let κ := {t : Pl D.host.E × List ℤ × Finset (GA D (Wc D i)) // Hecke₂ (Wc D i) J χ R.SF t.1 t.2.1 t.2.2}
  let op : κ → MMap (R.MW i (sg0 D A3.A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A3.A)) := fun k => heckeOn (R.MW i (sg0 D A3.A)) k.1.2.2
  let E : {c' : Pl D.host.E → List ℤ → ℂ // R.Carries p c'} → Submodule ℂ (MMap (R.MW i (sg0 D A3.A))) :=
    fun a => partFull R.θ (R.MW i (sg0 D A3.A)) J χ R.SF a.1
  have hWp : R.Wp3 i p = ⨆ a : {c' : Pl D.host.E → List ℤ → ℂ // R.Carries p c'}, R.Wc' i a.1 := by
    show (⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c'), R.Wc' i c') = _
    exact iSup_subtype'
  have hwp' : w ∈ ⨆ a : {c' : Pl D.host.E → List ℤ → ℂ // R.Carries p c'}, R.Wc' i a.1 := hWp ▸ hwp
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hwp'
  have hew : (R.HW i (sg0 D A3.A)).e w ∈ ⨆ a ∈ s, E a := by
    have h1 : (⨆ a ∈ s, R.Wc' i a.1).map (R.HW i (sg0 D A3.A)).e ≤ ⨆ a ∈ s, E a := by
      rw [Submodule.map_iSup]
      refine iSup_le fun a => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun ha => ?_
      refine le_trans ?_ (le_iSup₂ (f := fun a (_ : a ∈ s) => E a) a ha)
      rintro _ ⟨z, hz, rfl⟩
      exact (Submodule.mem_inf.1 hz).2
    exact h1 ⟨w, hs, rfl⟩
  have hz := eq_zero_of_mem_iSup_eig op (fun a k => a.1 k.1.1 k.1.2.1) E
    (fun a k x hx => heckeOn_of_mem_partFull R.θ _ J χ R.SF a.1 k.2 x hx)
    (partFull R.θ (R.MW i (sg0 D A3.A)) J χ R.SF c) (fun k => c k.1.1 k.1.2.1)
    (fun k x hx => heckeOn_of_mem_partFull R.θ _ J χ R.SF c k.2 x hx) s
    (fun a _ => by
      obtain ⟨P, d, B, hB, hne⟩ := hcon a.1 a.2
      exact ⟨⟨(P, d, B), hB⟩, hne⟩)
    _ (Submodule.mem_inf.1 hwc).2 hew
  exact hw0 (hinj (hz.trans (map_zero _).symm))

theorem eec_le_of_agree : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (c c' : Pl D.host.E → List ℤ → ℂ), (∀ P d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) R.SF P d B → c' P d = c P d) → R.EEc c ≤ R.EEc c' := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH i c c' hag x hx
  obtain ⟨hCore, hSF, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  obtain ⟨-, hg, hoffG, -⟩ := GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hCore.lev
  obtain ⟨nY, hβY⟩ := hCore.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  obtain ⟨nW, hβW⟩ := hCore.lev.βW i
  rw [RealDat3.EEc, Submodule.mem_comap, partDual, mem_partFull] at hx ⊢
  refine ⟨hx.1, fun P d B hB v => ?_⟩
  rw [hx.2 P d B hB v]
  obtain ⟨e, f, ϖ, α, hoff, -⟩ := id hB
  have hG := (hoffG R.SF hSF P).1 hoff
  have levY := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβY P
      (by rw [Nat.cast_pow]; exact fun hm => (hg _ P hG).1 (P.isPrime.mem_of_pow_mem nY hm))
      (fun PP hPP => hG PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have levW := GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) _ (R.datWp i R.triv) hβW P
      (by rw [one_pow, Nat.cast_one]; exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1))
      (fun PP hPP => hG PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have hYlab : GlobalTheory.Hk3.IsLab (Yc D 0) P d := ⟨B, ((levY.2.1 R.SF d B).1 hB).2⟩
  have hdd : dualLab (dualLab d) = d := by simp [dualLab, List.map_reverse, List.map_map, Function.comp_def]
  have hWlab : GlobalTheory.Hk3.IsLab (Wc D i) P (dualLab d) := by
    have h := ((GlobalTheory.LabEq.isLab_W_iff (s := 1) R.toRealDat F.lv2 hCore i P (dualLab d) hG).1).2
    rw [hdd] at h
    exact h hYlab
  obtain ⟨B', hB'⟩ := hWlab
  have e1 := hag P (dualLab d) B' ((levW.2.1 R.SF (dualLab d) B').2 ⟨hoff, hB'⟩)
  beta_reduce
  rw [e1]

theorem exists_isEigOf_of_vec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (i : Fin D.R.m), (∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((Y.PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) ((Y.PW i).ψ κ)) x) → ∃ c, principalLevelFrame.IsEigOf (Y.PW i) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) R.SF π c := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH π i hvec
  classical
  obtain ⟨hCore, hSF, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hPW : ∀ i, GlobalTheory.StdFrame.StdPsi Y.hF (Y.PW i) := fun i => Y.stdPsi.2 i
  have hsc : ∀ Pr d B, GlobalTheory.Hk3.SphOp (Wc D i) Pr d B → ∃ a : ℂ, ∀ x ∈ π.S,
      (∀ κ, (Y.PW i).ψ κ ∈ GlobalTheory.Hk3.hyp (Wc D i) Pr → Formalism.L2.NG.rt D.host.E D.R.r κ x = x) → principalLevelFrame.Hecke₃ (Y.PW i) B x = a • x :=
    fun Pr d B h => GlobalTheory.T.sphericalHecke_scalar_on_spherical_vectors Y.hF (Y.PW i) (hPW i) π Pr d B h
  obtain ⟨c0, hBase⟩ := hCore.lev.βW i
  rw [one_pow] at hBase
  have hfix : ∀ Pr d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) R.SF Pr d B → ∀ x,
      principalLevelFrame.IsTypeVec ((Y.PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) ((Y.PW i).ψ κ)) x →
      ∀ κ, (Y.PW i).ψ κ ∈ GlobalTheory.Hk3.hyp (Wc D i) Pr → Formalism.L2.NG.rt D.host.E D.R.r κ x = x := by
    intro Pr d B hB x hx κ hκ
    have hOff : OffS D R.SF Pr := by
      obtain ⟨e, f, ϖ, α, h, -⟩ := hB
      exact h
    have hGood : GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 Pr :=
      ((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hCore.lev).2.2.1 R.SF hSF Pr).mp hOff
    have hN : ((1 : ℕ) : 𝓞 D.host.E) ∉ Pr.asIdeal := by
      rw [Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).mp Pr.isPrime.ne_top
    have hL := (GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) 1 (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A))) hBase Pr hN
      (fun PP hPP => by
        rcases hPP with h | h
        · exact hGood PP (Or.inl h)
        · exact absurd h (Finset.notMem_empty PP))).1 _ hκ
    have := hx κ hL.1
    rw [this]
    dsimp only
    rw [hL.2, one_smul]
  refine ⟨fun Pr d => if h : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) R.SF Pr d B then
      (hsc Pr d h.choose (GlobalTheory.RowEig.sph_of_full h.choose_spec)).choose else 0, hvec, ?_, ?_⟩
  · intro Pr d B hB x hxS hx
    have hex : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) R.SF Pr d B := ⟨B, hB⟩
    have hxf := hfix Pr d B hB x hx
    dsimp only
    rw [dif_pos hex, GlobalTheory.RowEig.heckeOperator_eq_of_spherical (Y.PW i) Pr d B hex.choose (GlobalTheory.RowEig.sph_of_full hB)
      (GlobalTheory.RowEig.sph_of_full hex.choose_spec) x hxf]
    exact (hsc Pr d hex.choose (GlobalTheory.RowEig.sph_of_full hex.choose_spec)).choose_spec x hxS hxf
  · intro Pr d hne
    exact dif_neg hne

theorem isot_part : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (hL : Lam3 Z), (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, (principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F.lv2 true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F.lv2 true))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT (D.what₂.ft σ)))).comap R.HE.e ≤ R.EEp3 (Classical.choose hL (D.what₂.ft σ)) := by
  intro hPr D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hiso σ
  obtain ⟨hCore, hSF, hEE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hSch := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hPr.2.2.2.2 R.toRealDat
  have hPY : GlobalTheory.StdFrame.StdPsi Y.hF Y.PY := Y.stdPsi.1
  have hPW : ∀ i, GlobalTheory.StdFrame.StdPsi Y.hF (Y.PW i) := fun i => Y.stdPsi.2 i
  set i0 : Fin D.R.m := ⟨0, Y.hm⟩ with hi0
  set p := Classical.choose hL (D.what₂.ft σ) with hp
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT (D.what₂.ft σ)) with hπ

  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hiso σ i0)
  have hyW := (Y.tied.lift.isot i0 (D.what₂.ft σ) y).1 hy
  rw [Y.prtWE] at hyW
  obtain ⟨U, hU, hUeq⟩ := hyW
  have hUe : U = (R.HW i0 (sg0 D A3.A)).e (Y.mj.eW i0 y) := by
    apply (PiTensorProduct.lift : Mult.MMap (R.MW i0 (sg0 D A3.A)) ≃ₗ[ℂ] _).injective
    exact hUeq.trans (Y.mjRead i0 y)
  have hey0 : Y.mj.eW i0 y ≠ 0 := fun h => hy0 (GlobalTheory.Mem.R3.MjCoord.eW_inj Y i0 (h.trans (map_zero _).symm))
  have hU0 : U ≠ 0 := by
    rw [hUe]
    intro h
    exact hey0 ((hCore.models.HW i0 (sg0 D A3.A)).1 (h.trans (map_zero _).symm))
  have hne : principalLevelFrame.isotL R.θ (Y.PW i0) (R.MW i0 (sg0 D A3.A)) (levS _ (R.βW i0) (R.datWp i0 (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i0 (sg0 D A3.A)) π ≠ ⊥ := by
    intro h
    have h' : U ∈ (⊥ : Submodule ℂ (Mult.MMap (R.MW i0 (sg0 D A3.A)))) := h ▸ hU
    exact hU0 ((Submodule.mem_bot ℂ).1 h')
  obtain ⟨c, hc⟩ := exists_isEigOf_of_vec D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH π i0
    (GlobalTheory.T.nonzero_liftPart_type_gives_nonzero_typeVector hPr D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH π i0 hne)

  obtain ⟨w, hw, hwU⟩ := GlobalTheory.T.typePart_le_eigensystemPart_principalLevel R.toRealDat F.lv2 hH.ok.ok2 hCore R.SF hSF Y.hF Y.PY Y.PW hPY hPW π i0 c hc i0 U hU
  have hwe : w = Y.mj.eW i0 y := (hCore.models.HW i0 (sg0 D A3.A)).1 (hwU.trans hUe)
  have hwc : Y.mj.eW i0 y ∈ R.Wc' i0 c := by rw [hWc, ← hwe]; exact hw

  have hy' : y ∈ Submodule.span ℂ ((Z.jW i0) '' ((s0Of R F).Wp i0 p : Set (Fin ((s0Of R F).dW i0) → D.what₂.LL))) := by
    rw [← ((Classical.choose_spec hL).1 i0 p).2]
    exact (le_iSup (fun σ' : {σ' : D.what₂.FT // Classical.choose hL σ' = p} => D.what₂.isot ((i0 : ℕ) + 1) σ'.1)
      ⟨D.what₂.ft σ, rfl⟩) hy
  have hwp : Y.mj.eW i0 y ∈ R.Wp3 i0 p := by
    have hm : Y.mj.eW i0 y ∈ (Submodule.span ℂ ((Z.jW i0) '' ((s0Of R F).Wp i0 p : Set (Fin ((s0Of R F).dW i0) → D.what₂.LL)))).map (Y.mj.eW i0) :=
      ⟨y, hy', rfl⟩
    rw [Submodule.map_span] at hm
    refine Submodule.span_le.2 ?_ hm
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, GlobalTheory.Mem.R3.MjCoord.eW_jW_eq Z i0 z]
    have h3 : (R.toCx3 F).w0C false i0 (cpt A3.A.v0.embedding z) ∈ (R.toCx3 F).Wp i0 p := hz
    have h2 : (R.toCx3 F).w0C false i0 (cpt A3.A.v0.embedding z) =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i0 z) :=
      GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i0 z
    rw [h2] at h3
    exact h3
  obtain ⟨c', hcar, hag⟩ := exists_carried_agree D G Pl0 I0 T A3 Ks R F cG hP hH i0 p c _ hey0 hwc hwp
  have hle := eec_le_of_agree D G Pl0 I0 T A3 Ks R F cG hP hH i0 c c' hag

  intro x hx
  rw [Submodule.mem_comap] at hx
  obtain ⟨x', hx', hxe⟩ := GlobalTheory.T.rowTypePart_le_eigensystemPart R.toRealDat F.lv2 (s := 1) hCore hSch R.SF hSF Y.hF Y.PY Y.PW hPY hPW π i0 c hc true
    (R.HE.e x) hx
  have hxx : x' = x := hCore.models.HE.1 hxe
  subst hxx
  rw [← hEE] at hx'
  exact (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.EEc c) c' hcar) (hle hx')

end GlobalTheory.Mem.IsotPart

end
