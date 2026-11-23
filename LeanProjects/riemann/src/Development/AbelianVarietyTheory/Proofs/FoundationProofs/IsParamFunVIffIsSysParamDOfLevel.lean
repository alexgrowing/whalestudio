import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}

theorem isParamVec_iff_isSysParam (hJ : SphOff J χ Sb) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ Sb)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = v) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : List ℤ → ℂ} (hc : ∀ d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c d • f) (B : Multiset ℂˣ) :
    IsParamVec D.sp.cm.sig V.gram (frameLat V) h ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) f B ↔
      IsSysParam D.sp.cm.sig V.rank h c B := by
  have hx : f ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext (hf k hk)
  have hs := isEigenSys_of_heckeLin hJ hv h hx hc
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  exact ⟨hs.isSysParam, hs.isParamVec h0 hx
    (fun hv => (SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hL.span_eq_top h hv hd).imp fun _ he => he.1)
    fun hw τ hτ => ((((exists_isInertChart _ (isCMExt_host D) v).2 w h hw).2.2.2.2 τ hτ).2 _ _ _ hH hL.fg
      hL.span_eq_top hd).imp fun _ he => he.1⟩

theorem isParamFunV_iff_isSysParamD (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g)
    {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  forall₂_congr fun v hv => forall₂_congr fun w h => isParamVec_iff_isSysParam hJ hv h h0 (hf v hv) (hc w) (B w)

theorem isParamFunV_iff_isSysParamD_of_level (hJ : SphOff J χ Sb) {f : GA D V → ℂ} (h0 : f ≠ 0)
    (hf : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    (hc : ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) (B : Fam D.host.E) :
    IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B :=
  isParamFunV_iff_isSysParamD hJ h0 (fun _ hv _ hk => fixed_of_level hJ hv hf hk) hc B

variable {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S}

theorem isParamFunV_iff_of_mem_partFull (hJ : SphOff J χ Sb) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    {T : MMap M} (hT : T ∈ partFull θ M J χ Sb c) {x : M.Vec} (h0 : T x ≠ 0) (B : Fam D.host.E) :
    IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B :=
  have h := (mem_partFull θ M J χ Sb c T).1 hT
  isParamFunV_iff_isSysParamD_of_level hJ h0 (((GlobalTheory.MultMem.mem_mult_iff ..).1 h.1).lev x)
    (fun P d R hR => h.2 P d R hR x) B

theorem isParamFunV_iff_of_mem_partDual (hJ : SphOff J χ Sb) {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ}
    {T : MMap M} (hT : T ∈ partDual θ M J χ Sb c) {x : M.Vec} (h0 : T x ≠ 0) (B : Fam D.host.E) :
    IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank (fun P d => c P (dualLab d)) B :=
  isParamFunV_iff_of_mem_partFull hJ hT h0 B

theorem param_iff_sysParam (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (B : Fam D.host.E) (hJ : SphOff J χ Sb) :
    (∀ f : GA D V → ℂ, f ≠ 0 →
      (∀ v ∉ Sb, ∀ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, ∀ g, f (g * emb D.sp.cm.sig V.gram v k) = f g) →
      (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = c P d • f) →
      (IsParamFunV V Sb f B ↔ IsSysParamD D Sb V.rank c B)) ∧
    ∀ (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S),
      ∀ T ∈ partFull θ M J χ Sb c, ∀ x : M.Vec, T x ≠ 0 →
        (IsParamFunV V Sb (T x) B ↔ IsSysParamD D Sb V.rank c B) :=
  ⟨fun _ h0 hf hc => isParamFunV_iff_isSysParamD hJ h0 hf hc B,
    fun _ _ _ _ hT _ h0 => isParamFunV_iff_of_mem_partFull hJ hT h0 B⟩

theorem sphOff_KsphC (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    SphOff (KsphC V ∅) (fun _ => 1) Sb := fun P _ => by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (comp_finAdEquiv D) P
  exact ⟨e, f, h, fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

end GlobalTheory.LFun

end
