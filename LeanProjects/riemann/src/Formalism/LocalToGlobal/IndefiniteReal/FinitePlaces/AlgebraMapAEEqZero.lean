import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SbHalfHalfInd
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FstACoordOfInfPart
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.VacExA

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def LatPres {S T : HSp D} (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) : Prop :=
  ∀ (g : GA D S) (h : GA D T), g ∈ GfC S → h ∈ GfC T → Lev.finE S g ∈ Formalism.L2.DIV.St βS →
    Lev.finE T h ∈ Formalism.L2.DIV.St βT → ∀ t : WO S T, actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT

def VacFixOffO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    WeilFull.SphInertAtO ψ S T χS χT om → S.rank ≠ T.rank → (Even S.rank ∨ Even T.rank) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
    Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → UnrOff e χS → UnrOff e χT →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀ →
    (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) →
    ∀ (g : GA D S) (h : GA D T), g ∈ GfC S → h ∈ GfC T → Lev.finE S g ∈ Formalism.L2.DIV.St βS →
      Lev.finE T h ∈ Formalism.L2.DIV.St βT →
      (∀ i j, (e + cA D e) * (Formalism.L2.Theta.mt S g - 1) i j = 0) →
      (∀ i j, (e + cA D e) * (Formalism.L2.Theta.mt T h - 1) i j = 0) →
      om (g, h) f₀ = f₀

theorem placeIdem_sA (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (sA v (1 : v.adicCompletion D.host.F)) :=
  ⟨sglV v 1, rfl, by classical exact Pi.single_eq_same v (1 : v.adicCompletion D.host.F),
    fun v' hv' => by classical exact Pi.single_eq_of_ne hv' (1 : v.adicCompletion D.host.F)⟩

theorem resG_inv {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) :
    (resG V ε g)⁻¹ = resG V ε g⁻¹ := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← resG_mul (V := V) (ε := ε) hε, inv_mul_cancel, resG_one (V := V) (ε := ε) hε]

theorem mt_resG' {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) :
    Formalism.L2.Theta.mt V (resG V ε g) = 1 + algebraMap (AF D.host.F) (AE D) ε • (Formalism.L2.Theta.mt V g - 1) := by
  rw [mt_resG (V := V) (ε := ε) hε]
  rfl

theorem mt_resG_sub {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) (i j : Fin V.rank) :
    (Formalism.L2.Theta.mt V (resG V ε g) - 1) i j = algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V g - 1) i j := by
  rw [mt_resG' hε, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]

theorem eps_orth {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : ∀ PP ∈ P, belowPl PP ≠ v) :
    (e + cA D e) * algebraMap (AF D.host.F) (AE D) (sA v 1) = 0 := by
  rw [he, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_eq_zero fun PP hPP => ?_
  have h1 : es PP * phiE (belowPl PP) 1 = es PP := idemAt_eps (hes PP hPP)
  have h2 : es PP + cA D (es PP) = phiE (D := D) (belowPl PP) 1 := below_of_idemAt (hes PP hPP)
  have h3 : phiE (D := D) (belowPl PP) 1 * phiE v 1 = 0 := phiE_orth (hv PP hPP)
  change (es PP + cA D (es PP)) * phiE v 1 = 0
  rw [h2, h3]

theorem eps_absorb {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP) (hc : e * cA D e = 0)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ P) :
    algebraMap (AF D.host.F) (AE D) (sA (belowPl PP) 1) * (e + cA D e) =
      algebraMap (AF D.host.F) (AE D) (sA (belowPl PP) 1) := by
  have hsum : e + cA D e = ∑ Q ∈ P, phiE (D := D) (belowPl Q) 1 := by
    rw [he, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun Q hQ => below_of_idemAt (hes Q hQ)
  change phiE (D := D) (belowPl PP) 1 * (e + cA D e) = phiE (D := D) (belowPl PP) 1
  rw [hsum, Finset.mul_sum, Finset.sum_eq_single_of_mem PP hPP]
  · rw [← phiE_mul, one_mul]
  · intro Q hQ hne
    exact phiE_orth fun h => hne (idemSum_below_inj hes he hc hPP hQ h).symm

theorem unrAtV_of_unrOff {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : (e + cA D e) * algebraMap (AF D.host.F) (AE D) (sA v 1) = 0) {χ : (AE D)ˣ →* Circle} (hU : UnrOff e χ) :
    WeilFull.UnrAtV (sA v 1) χ := by
  intro x hx hf hfi
  set a := algebraMap (AF D.host.F) (AE D) (sA v 1) with ha
  have hx' : (x : AE D) - 1 = a * ((x : AE D) - 1) := by linear_combination hx
  have hinf : infPart D a = 0 := by
    have h0 : fstA D.host.F (sA v (1 : v.adicCompletion D.host.F)) = 0 := rfl
    rw [ha]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
      (sA v (1 : v.adicCompletion D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul, h0, TensorProduct.zero_tmul]
  have hinfx : infPart D (x : AE D) = 1 := by
    have h1 := congrArg (infPart D) hx'
    rw [map_sub, map_mul, hinf, zero_mul, map_one, sub_eq_zero] at h1
    exact h1
  have hex : (e + cA D e) * (x : AE D) = e + cA D e := by
    have h2 : (e + cA D e) * ((x : AE D) - 1) = 0 := by rw [hx', ← mul_assoc, hv, zero_mul]
    linear_combination h2
  exact hU x hinfx hf hfi hex

theorem algebraMap_AE_eq_zero {a : AF D.host.F} (h : algebraMap (AF D.host.F) (AE D) a = 0) : a = 0 := by
  have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
    (A := AF D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective
  exact hinj (by rw [map_zero]; exact h)

theorem sA_one_ne_zero (v : HeightOneSpectrum (𝓞 D.host.F)) : sA v (1 : v.adicCompletion D.host.F) ≠ 0 := by
  intro h
  have h2 := congrArg (fun z => evalV D.host.F v (sndA D.host.F z)) h
  simp only [map_zero] at h2
  have h3 : evalV D.host.F v (sndA D.host.F (sA v (1 : v.adicCompletion D.host.F))) = 1 := by
    classical exact Pi.single_eq_same v (1 : v.adicCompletion D.host.F)
  exact one_ne_zero (h3.symm.trans h2)

theorem two_not_mem_of_inert {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hin : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) (sA v 1) = 0) : (2 : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro h2
  obtain ⟨e, ε, hs, hε, hse⟩ := twoSplitIdem D v h2
  rw [placeIdem_eq hε] at hse
  have h0 := hin e hs
  rw [← hse] at h0
  have he0 : e = 0 := by
    have : e * (e + cA D e) = e := by rw [mul_add, hs.1, hs.2.1, add_zero]
    rw [← this, h0]
  rw [he0, map_zero, add_zero] at hse
  exact sA_one_ne_zero v (algebraMap_AE_eq_zero hse.symm)

set_option maxHeartbeats 1000000 in

theorem loc_fix (hSL : SplitLin D) (hPM : PlaceModelAt D) (hSOI : SplitOrInert D) {ψ : AddChar (AF D.host.F) ℂ}
    {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) (hI : WeilFull.SphInertAtO ψ S T χS χT om) (hrk : S.rank ≠ T.rank)
    (hev : Even S.rank ∨ Even T.rank)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hfS : Formalism.L2.DIV.IsFrame βS ΛS) (hfT : Formalism.L2.DIV.IsFrame βT ΛT) (hLP : LatPres ΛS ΛT βS βT)
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (huS : UnrOff e χS) (huT : UnrOff e χT)
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (hlat : IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀)
    (hn : ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1)
    {g : GA D S} {h : GA D T} (hgf : g ∈ GfC S) (hhf : h ∈ GfC T) (hgS : Lev.finE S g ∈ Formalism.L2.DIV.St βS)
    (hhT : Lev.finE T h ∈ Formalism.L2.DIV.St βT)
    (hgP : ∀ i j, (e + cA D e) * (Formalism.L2.Theta.mt S g - 1) i j = 0)
    (hhP : ∀ i j, (e + cA D e) * (Formalism.L2.Theta.mt T h - 1) i j = 0) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    om (resG S (sA v 1) g, resG T (sA v 1) h) f₀ = f₀ := by
  have hε : IsIdempotentElem (sA v (1 : v.adicCompletion D.host.F)) := sA_idem v
  obtain ⟨⟨es, hes, hesum⟩, hc⟩ := he
  set s := algebraMap (AF D.host.F) (AE D) (sA v 1) with hsdef
  have hgv : Lev.finE S (resG S (sA v 1) g) ∈ Formalism.L2.DIV.St βS := finE_resG_mem_St (V := S) hε hgS
  have hhv : Lev.finE T (resG T (sA v 1) h) ∈ Formalism.L2.DIV.St βT := finE_resG_mem_St (V := T) hε hhT
  by_cases hunder : ∃ PP ∈ P, belowPl PP = v
  ·
    obtain ⟨PP, hPP, rfl⟩ := hunder
    have hab := eps_absorb hes hesum hc hPP
    have hg1 : resG S (sA (belowPl PP) 1) g = 1 := by
      apply gaExt
      rw [mtG_one]
      ext i j
      have := mt_resG_sub (V := S) hε g i j
      rw [← hab, mul_assoc, hgP i j, mul_zero] at this
      simpa [sub_eq_zero] using this
    have hh1 : resG T (sA (belowPl PP) 1) h = 1 := by
      apply gaExt
      rw [mtG_one]
      ext i j
      have := mt_resG_sub (V := T) hε h i j
      rw [← hab, mul_assoc, hhP i j, mul_zero] at this
      simpa [sub_eq_zero] using this
    rw [hg1, hh1, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  · push Not at hunder
    have horth := eps_orth hes hesum hunder
    rcases hSOI v _ (placeIdem_sA v) with ⟨PP, hPPv, hPPc⟩ | hin
    ·
      obtain ⟨e', he', ε', hε', hse'⟩ := idem_at PP hPPc v hPPv
      rw [placeIdem_eq hε'] at hse'
      have hsp : IsSplitIdem D e' := he'.1
      have hsum1 : IsIdemSum e' {PP} := ⟨⟨fun _ => e', by simpa using he', by simp⟩, hsp.2.1⟩
      have horth' : (e + cA D e) * e' = 0 := by
        have : e' = e' * (e' + cA D e') := by rw [mul_add, hsp.1, hsp.2.1, add_zero]
        rw [this, hse', mul_comm e', ← mul_assoc, horth, zero_mul]
      have hfac : splitFacO χS χT (detAt e' S (resG S (sA v 1) g)) (detAt e' T (resG T (sA v 1) h)) = 1 := by
        simp only [splitFacO, unrOff_detAt he' horth' S hgv huT, unrOff_detAt he' horth' T hhv huS, inv_one, mul_one]
      have hgvi : Lev.finE S (resG S (sA v 1) g)⁻¹ ∈ Formalism.L2.DIV.St βS := by
        rw [map_inv]; exact inv_mem hgv
      have hhvi : Lev.finE T (resG T (sA v 1) h)⁻¹ ∈ Formalism.L2.DIV.St βT := by
        rw [map_inv]; exact inv_mem hhv
      exact fix_split hSL hPM hW hsS hsT he' hf₀ hlat hn (suppAt_resG (V := S) hε g hse') (suppAt_resG (V := T) hε h hse')
        (isDetAt_detAt hsp.1 S _) (isDetAt_detAt hsp.1 T _) hfac
        (fun t _ => hLP _ _ (resG_mem_GfC (V := S) hε hgf) (resG_mem_GfC (V := T) hε hhf) hgv hhv t)
        (fun t _ => hLP _ _ (inv_mem (resG_mem_GfC (V := S) hε hgf)) (inv_mem (resG_mem_GfC (V := T) hε hhf)) hgvi hhvi t)
    ·
      have hsupp : ∀ (V : HSp D) (x : GA D V), WeilFull.SuppV (sA v 1) V (resG V (sA v 1) x) := by
        intro V x i j
        rw [mt_resG_sub (V := V) hε x i j, ← mul_assoc, algIdem hε]
      exact fix_inert hI hrk hev hsS hsT hfS hfT (placeIdem_sA v) (two_not_mem_of_inert hin) hin
        (unrAtV_of_unrOff horth huS) (unrAtV_of_unrOff horth huT) (hsupp S g) (hsupp T h) hgv hhv hf₀ hlat

theorem vacFixOff_of (hSL : SplitLin D) (hPM : PlaceModelAt D) (hSOI : SplitOrInert D)
    (hLP : ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
      (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS →
        Formalism.L2.DIV.IsFrame βT ΛT → LatPres ΛS ΛT βS βT) :
    VacFixOffO D := by
  intro ψ S T χS χT om hW hI hrk hev ΛS ΛT hsS hsT βS βT hfS hfT P e he huS huT f₀ hf₀ hlat hn g h hgf hhf hgS hhT
    hgP hhP
  have hLP' := hLP S T ΛS ΛT βS βT hsS hsT hfS hfT
  refine om_fix_of_trunc hW hf₀ hgf hhf (fun A => resG S (idemS A) g) (fun A => resG T (idemS A) h)
    (fun A => mt_resG' (idemS_idem A) g) (fun A => by rw [resG_inv (idemS_idem A)]; exact mt_resG' (idemS_idem A) g⁻¹)
    (fun A => mt_resG' (idemS_idem A) h) (fun A => by rw [resG_inv (idemS_idem A)]; exact mt_resG' (idemS_idem A) h⁻¹)
    (fun A => ?_)
  classical
  induction A using Finset.induction_on with
  | empty =>
    simp only [idemS_empty, resG_zero_eps (V := S), resG_zero_eps (V := T)]
    rw [← Prod.one_eq_mk, map_one, Module.End.one_apply]
  | insert v A hv ih =>
    have hmul : idemS (insert v A) = sA v 1 + idemS A := by rw [idemS_insert hv, add_comm]
    have horth : sA v (1 : v.adicCompletion D.host.F) * idemS A = 0 := by rw [mul_comm]; exact idemS_mul_sA hv
    simp only [hmul]
    rw [← resG_orth (V := S) (sA_idem v) (idemS_idem A) horth g, ← resG_orth (V := T) (sA_idem v) (idemS_idem A) horth h,
      ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih]
    exact loc_fix hSL hPM hSOI hW hI hrk hev hsS hsT hfS hfT hLP' he huS huT hf₀ hlat hn hgf hhf hgS hhT hgP hhP v

end Formalism.IndefR.Fin.LevelGroupLemmas

end
