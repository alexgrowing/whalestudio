import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_sec_lbPow_vanishing_of_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB →
      0 < interNum k (GlobalTheory.structureModule C) ![L] →
      ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  intro k _ C _ hC L hL hpos
  have := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hC.1
  obtain ⟨hprop, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k C)).1 hC.2.1
  have := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  set O := GlobalTheory.structureModule C with hO
  set d := interNum k O ![L] with hdd
  set f := chiPic k O with hf

  have hdeg : ∀ (M : LB C) (hM : M.IsLB), interNum k O ![M] = f 0 - f (-cls M hM) := by
    intro M hM
    rw [interNum_one k O hM, chi_twistZ k O hM, hf, chiPic_zero, neg_one_zsmul]

  have hchi : ∀ m : ℕ, f ((m : ℤ) • cls L hL) = f 0 + m * d := by
    intro m
    obtain ⟨N, hN, hc⟩ := cls_surj (-((m : ℤ) • cls L hL))
    have hLm := isLB_lbPow hL m
    have e : cls _ (LB.isLB_triv C) = cls N hN + cls _ hLm := by
      rw [hc, cls_lbPow hL m hLm, cls_triv, natCast_zsmul, neg_add_cancel]
    have hadd := interNum_one_of_cls_eq_add (k := k) hH hd (LB.isLB_triv C) hN hLm e
    rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m, hdeg _ (LB.isLB_triv C), hdeg N hN, hc,
      cls_triv, neg_zero, neg_neg] at hadd
    have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
    linarith
  set m : ℕ := (f 0).natAbs + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hLm := isLB_lbPow hL m
  have hqc := Twist.isQuasicoherent_twist (F := O) hLm
  have hvan : ∀ n, 2 ≤ n → Subsingleton (coh (twist O (lbPow L m)) n) := by
    intro n hn
    refine hH.subsingleton_coh_of_dim_lt _ ?_
    rw [hd]
    exact_mod_cast (show (1 : ℕ) < n by omega)
  have hχ : chi k (twist O (lbPow L m)) = f 0 + m * d := by
    rw [← chiPic_cls k O hLm, cls_lbPow hL m hLm, ← natCast_zsmul, ← hf, hchi m]
  have hχpos : 0 < chi k (twist O (lbPow L m)) := by
    rw [hχ]
    have h1 : (1 : ℤ) ≤ d := hpos
    have h2 : -(f 0) ≤ ((f 0).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact neg_le_abs (f 0)
    have h3 : (m : ℤ) = (f 0).natAbs + 1 := by rw [hm]; push_cast; ring
    nlinarith
  have hh0 : 0 < hdim k (twist O (lbPow L m)) 0 := by
    have := chi_eq_hdim_zero_sub_hdim_one k hvan
    omega
  have hnt : Nontrivial (coh (twist O (lbPow L m)) 0) := Module.nontrivial_of_finrank_pos hh0
  obtain ⟨σ, hσ⟩ := hasNonzeroSec_iff_nontrivial.2 hnt
  refine ⟨m, σ, ?_⟩
  by_contra! hall
  have htop : Out.nonzeroLocus σ = ⊤ := top_unique fun c _ ↦ (hall c hm0 hσ)
  have h0 : cls _ hLm = 0 := (cls_eq_zero_iff hLm).2 (exists_isGen_of_nonzeroLocus_eq_top σ htop)
  have hz := interNum_eq_zero_of_cls_eq_zero k O (isLB_vecOne hLm) 0 h0
  rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m] at hz
  have : (0 : ℤ) < m * d := mul_pos (by exact_mod_cast hm0) hpos
  have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
  rw [hd'] at hz
  omega

end GlobalTheory.Nef
