import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorIndicatorMemHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorIndicatorMemHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDef
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairVrGramPRatPosDef

noncomputable section

namespace GlobalTheory.SplitTransfer

section Abstract

open Formalism.UG GlobalTheory.PRep

theorem heckeVec_indicator {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {x : V} (hx : x ∈ fixed ρ K) {S : Set G} (hm : ∀ g ∈ S, ∀ k ∈ K, g * k ∈ S) (R : Finset ι)
    (g : ι → G) (hR : ∀ i ∈ R, g i ∈ S) (hR' : ∀ y ∈ S, ∃! i, i ∈ R ∧ (g i)⁻¹ * y ∈ K) :
    GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) x = ∑ i ∈ R, ρ (g i) x := by
  classical
  have hinj : Set.InjOn (fun i : ι => (g i : G ⧸ K)) R := fun γ hγ δ hδ e =>
    (hR' _ (hR δ hδ)).unique ⟨hγ, QuotientGroup.eq.1 e⟩ ⟨hδ, by simp⟩
  rw [GlobalTheory.LFun.heckeVec, finsum_eq_sum_of_support_subset (s := R.image fun i : ι => (g i : G ⧸ K)),
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g γ)
    rw [hk, Set.indicator_of_mem (hm _ (hR γ hγ) k k.2), map_mul, Module.End.mul_apply,
      GlobalTheory.LGrp.mem_fixed.1 hx _ k.2]
    simp
  · intro c hc
    have : c.out ∈ S := by
      by_contra h0
      exact hc (by simp [h0])
    obtain ⟨γ, ⟨h1, h2⟩, -⟩ := hR' _ this
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, h1, (QuotientGroup.eq.2 h2).trans c.out_eq'⟩)

end Abstract

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in

theorem heckeVec_eq_of_isCompAlong {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {U : Submodule ℂ (UA L n → ℂ)} (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 L)) {H X : Type} [Group H]
    [AddCommGroup X] [Module ℂ X] {K : Subgroup H} (hK : IsCommensurated K) (p : locU n w →* H)
    (hp : Function.Surjective p) (σ : Representation ℂ H X) (hcomp : IsCompAlong U (locU n w) p σ) {h : H → ℂ}
    (hh : h ∈ Hecke ℂ K) {lam : ℂ} (hsat : ∀ v ∈ fixed σ K, v ≠ 0 → GlobalTheory.LFun.heckeVec σ K h v = lam • v)
    {φ : UA L n → ℂ} (hφ : φ ∈ U) (hfix : ∀ x : locU n w, p x ∈ K → RU L n x.val φ = φ) :
    GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) φ = lam • φ := by
  have hfin : {c : locU n w ⧸ K.comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets hK hh.2)
  have hS : ∀ c : locU n w ⧸ K.comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) (K.comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ K.comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA L n) (locU n w) π.V X X π.rep (locU n w).subtype (σ.comp p) (σ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have hZ : ∀ i v, (∀ k ∈ (K.comap p : Set (locU n w)), (σ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ K := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [hsat v hvK hv0] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.comp p) c.out v) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ (K.comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2

end GlobalTheory.SplitTransfer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTransfer

theorem heckeVec_divInd {D : D7} [IsCMField D.host.E] {V : HSp D}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {j : UA D.host.E V.rank ≃ₜ* GA D V} {h₀ : GA D V} (hT : IsTransfer V θ j h₀)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {φ : UA D.host.E V.rank → ℂ}
    (hφ : ∀ x ∈ KP V.rank P, RU D.host.E V.rank x φ = φ) {d : List ℤ} {R : Finset (GA D V)}
    (hR : GlobalTheory.Hk3.SphOp V P d R) :
    GlobalTheory.LFun.heckeVec ((RU D.host.E V.rank).comp (locU V.rank P).subtype)
      ((GlobalTheory.LFun.KGL P V.rank).comap ((cLoc P).comp (locU V.rank P).subtype))
      (fun x => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) φ =
      ∑ γ ∈ R, RU D.host.E V.rank ((cj j h₀).symm γ) φ := by
  classical
  obtain ⟨h1, h2⟩ := hT.2.2.2.2.2.2.2 P d R hR
  let g : GA D V → locU V.rank P := fun γ =>
    if h : (cj j h₀).symm γ ∈ locU V.rank P then ⟨_, h⟩ else 1
  have hg : ∀ γ ∈ R, (g γ : UA D.host.E V.rank) = (cj j h₀).symm γ := fun γ hγ => by
    simp only [g, dif_pos (h1 γ hγ).1]
  have e : (fun x : locU V.rank P => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) =
      Set.indicator {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)} 1 := by
    funext x
    by_cases hx : HasDiv (Ov D.host.E P) d (cLoc P x.val)
    · rw [Set.indicator_of_mem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_mem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
    · rw [Set.indicator_of_notMem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_notMem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
  rw [e, heckeVec_indicator (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hφ k.val ⟨k.2, hk⟩) ?_ R g ?_ ?_]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [← hg γ hγ]
    rfl
  · intro x hx k hk
    have := GlobalTheory.SphGal.hasDiv_mul_mul hx (one_mem _) hk
    rw [one_mul] at this
    change HasDiv _ d (cLoc P (x.val * k.val))
    rw [map_mul]
    exact this
  · intro γ hγ
    change HasDiv _ d (cLoc P (g γ).val)
    rw [hg γ hγ]
    exact (h1 γ hγ).2
  · intro y hy
    obtain ⟨γ, ⟨a1, a2⟩, a3⟩ := h2 y.val y.2 hy
    refine ⟨γ, ⟨a1, ?_⟩, fun δ hδ => a3 δ ⟨hδ.1, ?_⟩⟩
    · change cLoc P ((g γ).val⁻¹ * y.val) ∈ GlobalTheory.LFun.KGL P V.rank
      rw [hg γ a1]
      exact a2.2
    · rw [← hg δ hδ.1]
      exact ⟨((g δ)⁻¹ * y).2, hδ.2⟩

end GlobalTheory.SplitTransfer

end
