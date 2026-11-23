import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFlagBasisVectorEqSingleOfNoExtra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHJsymIffJSymG
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] {N : ℕ}

theorem prXpG_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    prXpG E N ∘ₗ (sumE hN g 1).toLinearMap = (g.toLinearMap : Sp E ((N - 1) + 0) →ₗ[E] Sp E ((N - 1) + 0)) ∘ₗ prXpG E N := by
  refine LinearMap.ext fun x => funext fun i => ?_

  exact congrFun (prH_sumE hN g 1 x) i

theorem atNL_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    atNL E N (N - 1) ∘ₗ (sumE hN g 1).toLinearMap = atNL E N (N - 1) := by
  refine LinearMap.ext fun x => ?_
  have hlt : N - 1 < N := by omega

  have h := sumE_last hN g 1 x
  rw [Units.val_one, one_mul] at h
  simp only [LinearMap.comp_apply, atNL, dif_pos hlt, LinearMap.proj_apply]
  exact h

end Local

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

theorem exists_topLev_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m →
    ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z,
      GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧
        CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  intro B X I hI u a i hi b κ P
  subst hi

  rcases b with ⟨_ | b₀, hb⟩
  swap
  · exact absurd (hb.mp rfl) (lt_irrefl _)
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1

  have hq : ((qOf P.1 : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal ^ 2 :=
    Formalism.L2.Ker.mq_rowSG_unif (I.tup a) (GlobalTheory.Mem.FieldsLaws.fields_ok (B := B)) hPr hI.sel_ok P
  have hN := N_m_succ B.R
  by_cases hP : P.1 ∈ (B.primes X).vGs
  ·
    have hQn : P.1 ∉ I.Q a := QE_disj (I.tup a) hPr hI.sel_ok hI.g_mem P.1 hP
    have hmem : κ.2.1.1 ⟨P.1, hP⟩ ∈ (levGTop I.Ch I.Ps ⟨P.1, hP⟩).H := by
      have h := κ.2.1.2
      simp only [LevFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levG_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hP⟩ (Set.mem_univ _)
    obtain ⟨h₀, hh₀, hdiag⟩ := (mem_levDiag _ _ _).mp hmem
    rw [rowTyG_PsymF_H] at hh₀
    have hr : B.R.r = B.R.k + 2 * B.R.rS + 1 := by
      simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
      obtain ⟨s, hs⟩ := B.R.m_even
      have := B.R.two_le_m
      omega
    have hsym : rSym B.R.k B.R.rS = B.R.r := by rw [hr]; rfl

    have hJ := (mem_HJsym_iff_JSymG (𝓞 B.fields.E ⧸ P.1.asIdeal) (B.R.N B.R.m - 1) B.R.k B.R.r B.R.t B.R.m B.R.rS
      (r_le_X' B.R) hr B.R.t_odd.pos (rank_X'_eq B.R) h₀⁻¹).mp (Subgroup.inv_mem _ hh₀)

    obtain ⟨j, hj⟩ := redGL_surjective (E := B.fields.E) (n := B.R.N B.R.m - 1) P.1 h₀⁻¹
    have hjinv : redGL _ P.1 j⁻¹ = h₀ := by rw [map_inv, hj, inv_inv]
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      have h := GlobalTheory.Mem.LastGrp.mem_JGsym0 (fun x hx h0 => intAt_div_of_redP hq hx h0)
        (hsym.symm ▸ r_le_X' B.R) j
        (fun x y hxy => by rw [← redGL_val, hj]; exact hJ.1.1 x y hxy)
        (fun x y hxy => by rw [← redGL_val, hjinv]; simpa using hJ.2.1 x y hxy)
        (fun x hx => by rw [← redGL_val, hj]; exact hJ.1.2.1 x hx)
        (fun x y hx hy => by rw [← redGL_val, hj]; exact hJ.1.2.2.1 x y hx hy)
      have e : GlobalTheory.CongLevel.extE 0 j.1 = j.1 := LinearEquiv.ext (GlobalTheory.Mem.LastGrp.extE_zero j.1)
      rw [e, hsym] at h
      simp only [GlobalTheory.TwU.rowLevTop, if_pos hP, hI.sharp a, if_true]
      exact h
    refine ⟨sumE hN j.1 1, sumE hN j.1 1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩, ⟨?_, ?_, ?_⟩, congE_refl _ _ _⟩
    · rw [← extI_val hN j]
      exact (extI hN P.1 j).2
    · intro h x hx
      rw [← extI_val hN j, redV_redGL _ hx, redGL_extI, hj, ← hdiag, ← map_inv]
    · exact fun h => absurd h hQn
  ·
    have hQ : P.1 ∈ I.Q a := by
      classical
      have h := P.2
      simp only [SBof, rowSG, uSG, Finset.mem_union] at h
      exact h.resolve_left hP
    have hmem : κ.2.2.1 ⟨P.1, hQ⟩ ∈ (levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) ⟨P.1, hQ⟩).H := by
      have h := κ.2.2.2
      simp only [LevQFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hQ⟩ (Set.mem_univ _)
    simp only [levQTop] at hmem
    obtain ⟨j, hj, hjc⟩ := (mem_levCong _ _ _ _).mp (Subgroup.inv_mem _ hmem)
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      simp only [GlobalTheory.TwU.rowLevTop, if_neg hP]
      exact GlobalTheory.TopLaw.mem_JQ_of_red hq j ((mem_levRed _ _).mp hj)
    refine ⟨sumE hN j.1 1, ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩,
      ⟨((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h => absurd h hP, fun h => rfl⟩, ?_⟩

    have h2 : (extI hN P.1 j)⁻¹ * (κ.2.2.1 ⟨P.1, hQ⟩)⁻¹ ∈ prinCong _ P.1 (2 * (I.cst a).M) :=
      prinCong_anti (by have := two_mul_le_topDep B.R (I.cst a).M; omega) hjc
    have h3 : ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹)⁻¹ * extI hN P.1 j ∈ prinCong _ P.1 (2 * (I.cst a).M) := by
      have := Subgroup.inv_mem _ h2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have h4 := (inv_mul_mem_prinCong _ _ _).mp h3
    intro x hx
    simp only [GlobalTheory.TwU.topDep, if_neg hP]
    have := h4 x hx
    rwa [extI_val] at this

end GlobalTheory.Mem.Col2.AdT
