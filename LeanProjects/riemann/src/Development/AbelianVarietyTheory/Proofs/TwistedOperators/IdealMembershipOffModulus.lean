import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdVLeOfLoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHost
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.DepthIdeal

open GlobalTheory.SeeSaw (FI idV dI)
open GlobalTheory.FinPlLoc (idem)
open Formalism.IndefR.Fin

variable {D : D7}

theorem phiE_one (v : GlobalTheory.FinPl.Pl D) : phiE (D := D) v 1 = idem D (· = v) := by
  classical
  have h : sglV v (1 : v.adicCompletion D.host.F) = GlobalTheory.FinPlLoc.ePl D (· = v) := by
    apply af_ext; intro u
    rw [GlobalTheory.FinPlLoc.evalV_ePl]
    by_cases hu : u = v
    · subst hu; rw [sglV_same, if_pos rfl]
    · rw [sglV_ne v _ hu, if_neg hu]
  unfold idem
  rw [← h]
  rfl

variable {T : Type} {L : LevCh D T}

theorem belowPl_w (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) : belowPl (P.w v) = v := by
  conv_rhs => rw [← P.under_w hv]
  rfl

theorem exists_idem (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) {e : AE D} (he : IsIdemSum e P.W0) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f (P.w v) ∧ (1 - e) * idem D (· = v) = cA D f := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hmem : ∀ PP, PP ∈ P.W0 ↔ ∃ u ∈ P.S0, P.w u = PP := fun PP => by
    unfold Places.W0
    convert Finset.mem_image
  have hw : P.w v ∈ P.W0 := (hmem _).2 ⟨v, hv, rfl⟩
  have heps : ∀ u ∈ P.S0, es (P.w u) + cA D (es (P.w u)) = phiE u 1 := fun u hu => by
    have := below_of_idemAt (hes _ ((hmem _).2 ⟨u, hu, rfl⟩))
    rwa [belowPl_w P hu] at this
  have hfix : ∀ u ∈ P.S0, es (P.w u) * phiE u 1 = es (P.w u) := fun u hu => by
    have h := hes _ ((hmem _).2 ⟨u, hu, rfl⟩)
    rw [← heps u hu, mul_add, h.1.1, h.1.2.1, add_zero]
  refine ⟨es (P.w v), hes _ hw, ?_⟩
  have hsum : (∑ PP ∈ P.W0, es PP) * phiE v 1 = es (P.w v) := by
    rw [Finset.sum_mul, Finset.sum_eq_single (P.w v), hfix v hv]
    · intro PP hPP hne
      obtain ⟨u, hu, rfl⟩ := (hmem _).1 hPP
      have huv : u ≠ v := fun h => hne (h ▸ rfl)
      rw [← hfix u hu, mul_assoc, phiE_orth huv, mul_zero]
    · intro h; exact absurd hw h
  rw [← phiE_one, sub_mul, one_mul, hsum, ← heps v hv, add_sub_cancel_left]

theorem exists_modul_conj (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    ∃ x ∈ P.modul sc, ∃ y : 𝓞 D.host.E, y ∉ (P.w v).asIdeal ∧ (y : D.host.E) = star (x : D.host.E) := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ a ∈ (P.w u).asIdeal, ∃ b : 𝓞 D.host.E, b ∉ (P.w v).asIdeal ∧
      (b : D.host.E) = star (a : D.host.E) := by
    intro u hu
    by_cases huv : u = v
    · subst huv
      obtain ⟨f, hf⟩ := P.w_split u hu
      have hs := idemAt_split hf
      unfold Formalism.IndefR.Lev.IsConjPl at hs
      push Not at hs
      obtain ⟨a, ha, hb⟩ := hs
      exact ⟨a, ha, starO a, fun h => hb _ h rfl, rfl⟩
    · have hne : ¬ u.asIdeal ≤ v.asIdeal := fun hle =>
        huv (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle))
      obtain ⟨t, htu, htv⟩ := Set.not_subset.1 hne
      refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, ?_⟩
      · have : t ∈ (belowPl (P.w u)).asIdeal := by rw [belowPl_w P hu]; exact htu
        exact this
      · intro h
        apply htv
        have : t ∈ (belowPl (P.w v)).asIdeal := h
        rwa [belowPl_w P hv] at this
      · rw [algebraMap_O]
        exact (D.sp.cm.sig.commutes _).symm
  choose! a ha b hb hab using hu
  refine ⟨∏ u ∈ P.S0, a u ^ P.depth sc u, ?_, ∏ u ∈ P.S0, b u ^ P.depth sc u, ?_, ?_⟩
  · exact Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow (ha u hu) _
  · intro hmem
    obtain ⟨u, hu, hmem'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (P.w v).isPrime)).1 hmem
    exact hb u hu ((P.w v).isPrime.mem_of_pow_mem _ hmem')
  · change algebraMap (𝓞 D.host.E) D.host.E _ = star (algebraMap (𝓞 D.host.E) D.host.E _)
    rw [map_prod, map_prod, star_prod]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [map_pow, map_pow, star_pow]
    exact congrArg (· ^ P.depth sc u) (hab u hu)

theorem idV_le_dI (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v ≤ idV (dI D) v := by
  refine GlobalTheory.StairLine.idV_le_of_loc fun z hz => ⟨_, GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces P hv, ?_⟩
  have e : dI D = D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) := by
    unfold dI; ring
  have e2 : algebraMap D.host.F D.host.E ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) =
      ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) := by
    rw [← algebraMap_O, map_natCast]; rfl
  rw [e, e2]
  exact FractionalIdeal.mul_mem_mul (GlobalTheory.HostClear.absNorm_mem_AA D) hz

theorem compl_mem (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) {e : AE D} (he : IsIdemSum e P.W0)
    (𝔞 : FI D) {s : AE D} (hs : s ∈ idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) v) :
    (1 - e) * idem D (· = v) * s ∈ idV 𝔞 v := by
  obtain ⟨f, hf, hfe⟩ := exists_idem P hv he
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_modul_conj P sc hv
  have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  have hx0 : (x : D.host.E) ≠ 0 := by
    intro h
    apply hy0
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [map_zero]
    change (y : D.host.E) = 0
    rw [hxy, h, star_zero]
  have hm0 : ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 (P.modul_ne_bot sc)
  have h1 : idem D (· = v) * incA D x ∈ idV ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) v := by
    unfold idem
    rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, mul_one]
    refine GlobalTheory.SeeSaw.IdVMul.gen_mem (GlobalTheory.FinPlLoc.ePl_int _) (fun w hw => ?_)
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨x, hx, rfl⟩)
    rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]
  have h2 := GlobalTheory.SeeSaw.IdVMul.mul_mem_idV h1 hs
  rw [mul_left_comm, mul_inv_cancel₀ hm0, mul_one] at h2
  have hint : finPart D (cA D f * incA D (x : D.host.E)⁻¹) ∈ intAE D := by
    have h3 : finPart D (f * incA D (y : D.host.E)⁻¹) ∈ intAE D := not_not.1 (mt (hf.2 y hy0).2 hy)
    have h4 := cF_int h3
    rwa [← finPart_cA, cA_mul_incA, hxy, star_inv₀, star_star] at h4
  have h5 : cA D f * incA D (x : D.host.E)⁻¹ ∈ idV (1 : FI D) v := by
    refine (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ⟨?_, hint⟩
    rw [← hfe]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _))
  have h6 := GlobalTheory.SeeSaw.IdVMul.mul_mem_idV h5 h2
  rw [one_mul, ← hfe] at h6
  have e1 : incA D (x : D.host.E)⁻¹ * incA D x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have e2 := GlobalTheory.FinPlLoc.idem_mul_self (D := D) (· = v)
  have e3 : (1 - e) * idem D (· = v) * incA D (x : D.host.E)⁻¹ * (idem D (· = v) * incA D x * s) =
      (1 - e) * idem D (· = v) * s := by
    calc _ = (1 - e) * (idem D (· = v) * idem D (· = v)) * (incA D (x : D.host.E)⁻¹ * incA D x) * s := by ring
      _ = _ := by rw [e1, e2, mul_one]
  rwa [e3] at h6

theorem mem_dI_of_half : All fun {D} _ _ _ {G} _ _ => ∀ v ∈ G.pl.S0, ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ s ∈ idAt D (· = v), s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D * ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → e * s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v → s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
  intro D _ T L μ0 _ sc G W M _ v hv e he s hs h1 h2
  have hA := idV_le_dI G.pl hv h2
  have hB := compl_mem G.pl sc hv he (dI D) h1
  rw [mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ s).1 hs] at hB
  have := add_mem hA hB
  rwa [← add_mul, add_sub_cancel, one_mul] at this

end GlobalTheory.DepthIdeal

end
