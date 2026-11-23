import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.DsInfCharCap

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem kspan_stb {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) :
    Stb F (Formalism.REAL.kSpan (fun _ => true) F x) := by
  intro a b y hy
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b rfl y (hy S hS)

private theorem proj_comm {n : ℕ} {N : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    {F : Fin n → Fin n → Module.End ℂ N} (hF : UF F) (S : Submodule ℂ N) [S.HasOrthogonalProjection]
    (hS : Stb F S) (a b : Fin n) (y : N) :
    S.starProjection (F a b y) = F a b (S.starProjection y) := by
  have hz : F a b (y - S.starProjection y) ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [← hF.unit b a w]
    exact Submodule.inner_right_of_mem_orthogonal (hS b a w hw)
      (Submodule.sub_starProjection_mem_orthogonal y)
  refine Submodule.eq_starProjection_of_mem_orthogonal' (hS a b _ (S.starProjection_apply_mem y)) hz ?_
  rw [← map_add, add_sub_cancel]

theorem UpperTheory.RealTr.homSurj :
    ∀ (n : ℕ) (N V : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (F : Fin n → Fin n → Module.End ℂ N) (K : Fin n → Fin n → Module.End ℂ V), UF F → UF K → LocF K → ∀ (ν : Wt n) (φ : hw F ν →ₗ[ℂ] hw K ν), ∃ t ∈ homL F K, (∀ x : hw F ν, t x = φ x) ∧ ∀ μ, μ ≠ ν → ∀ x ∈ hw F μ, t x = 0 := by
  intro n N V _ _ _ _ _ F K hF hK hL ν φ
  have hKR : Formalism.REAL.KRel (fun _ => true) F := Formalism.REAL.glRel_kRel _ F hF.gl
  have hKU : Formalism.REAL.KUnit (fun _ => true) F := fun a b _ => hF.unit a b
  obtain ⟨m, x, μ, hx, horth, hsup⟩ := Formalism.REAL.kDecomp N n (fun _ => true) F ⊤ inferInstance hKR hKU
    (fun a b _ y _ => trivial)
  obtain ⟨P, hP⟩ : ∃ P : Fin m → N →L[ℂ] N,
      ∀ i, P i = (Formalism.REAL.kSpan (fun _ => true) F (x i)).starProjection := ⟨_, fun _ => rfl⟩
  have hPmem : ∀ i y, P i y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) := by
    intro i y
    rw [hP]
    exact Submodule.starProjection_apply_mem _ y
  have hPself : ∀ i y, y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) → P i y = y := by
    intro i y hy
    rw [hP]
    exact Submodule.starProjection_eq_self_iff.mpr hy
  have hPorth : ∀ i j y, j ≠ i → y ∈ Formalism.REAL.kSpan (fun _ => true) F (x j) → P i y = 0 := by
    intro i j y hji hy
    rw [hP]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (zero_mem _) (fun w hw => ?_)
    rw [sub_zero]
    exact horth j i hji y hy w hw
  have hcomm : ∀ i a b y, P i (F a b y) = F a b (P i y) := by
    intro i a b y
    rw [hP]
    exact proj_comm hF _ (kspan_stb F (x i)) a b y
  have hcomp : ∀ (μ' : Wt n) (y : N), KHighest (fun _ => true) F μ' y →
      ∀ i, KHighest (fun _ => true) F μ' (P i y) := by
    intro μ' y hy i
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hcomm, hy.1 a, map_smul]
    · rw [← hcomm, hy.2 a b hab he, map_zero]
  have huniq : ∀ (μ' : Wt n) (y : N) i, KHighest (fun _ => true) F μ' y →
      y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) → y = 0 ∨ μ' = μ i ∧ ∃ c : ℂ, y = c • x i :=
    fun μ' y i hy hm => Formalism.REAL.kHiUniq N n _ F (μ i) μ' (x i) y hKR hKU (hx i).2.2 hm hy
  have hsum : ∀ y : N, y = ∑ i, P i y := by
    intro y
    have hy : y ∈ ⨆ i, Formalism.REAL.kSpan (fun _ => true) F (x i) := by
      rw [hsup]
      trivial
    refine Submodule.iSup_induction (motive := fun y => y = ∑ i, P i y) _ hy ?_ ?_ ?_
    · intro j z hz
      rw [Finset.sum_eq_single j (fun i _ hij => hPorth i j z (Ne.symm hij) hz)
        (fun h => absurd (Finset.mem_univ j) h), hPself j z hz]
    · simp
    · intro a b ha hb
      simp only [map_add, Finset.sum_add_distrib]
      rw [← ha, ← hb]
  have hg : ∀ i, ∃ g : N →ₗ[ℂ] V, (∀ a b (y : N), g (F a b y) = K a b (g y)) ∧
      (μ i = ν → ∀ h : x i ∈ hw F ν, g (x i) = (φ ⟨x i, h⟩ : V)) ∧ (μ i ≠ ν → g = 0) := by
    intro i
    by_cases h : μ i = ν
    · have hxi : x i ∈ hw F ν := by
        rw [← h]
        exact (hx i).2.2
      obtain ⟨S, hSf, hvS, hSstb⟩ := hL (φ ⟨x i, hxi⟩ : V)
      obtain ⟨g, hg1, hg2⟩ := GlobalTheory.CompanionTheory.TransS.InfChar.hHWMap n (fun _ => true) N V F K ν (x i)
        (φ ⟨x i, hxi⟩ : V) S (fun a b c d _ _ => hF.gl a b c d) (fun a b _ => hF.unit a b)
        (fun a b c d _ _ => hK.gl a b c d) (fun a b _ => hK.unit a b) (hx i).2.1 hxi
        (φ ⟨x i, hxi⟩).2 hSf (fun a b _ => hSstb a b) hvS
      exact ⟨g, fun a b y => hg2 a b rfl y, fun _ _ => hg1, fun hne => absurd h hne⟩
    · exact ⟨0, fun a b y => by simp, fun h' => absurd h' h, fun _ => rfl⟩
  choose g hgL hgv hg0 using hg
  have happ : ∀ y, (∑ i, (g i).comp (P i : N →ₗ[ℂ] N)) y = ∑ i, g i (P i y) := by
    intro y
    simp [LinearMap.sum_apply]
  refine ⟨∑ i, (g i).comp (P i : N →ₗ[ℂ] N), ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun i _ => ?_)
    show ∀ a b (y : N), (g i).comp (P i : N →ₗ[ℂ] N) (F a b y) = K a b ((g i).comp (P i : N →ₗ[ℂ] N) y)
    intro a b y
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hcomm i a b y]
    exact hgL i a b _
  · intro y
    have key : ∀ i, g i (P i y) = (φ ⟨P i y, hcomp ν y y.2 i⟩ : V) := by
      intro i
      rcases huniq ν (P i y) i (hcomp ν y y.2 i) (hPmem i y) with h0 | ⟨hμ, c, hc⟩
      · have e : (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν) = 0 := Subtype.ext h0
        rw [e, map_zero, Submodule.coe_zero, h0, map_zero]
      · have hxi : x i ∈ hw F ν := by
          rw [hμ]
          exact (hx i).2.2
        have e : (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν) = c • ⟨x i, hxi⟩ := Subtype.ext hc
        rw [e, map_smul, Submodule.coe_smul, hc, map_smul, hgv i hμ.symm hxi]
    have hs : (∑ i, (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν)) = y := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact (hsum y).symm
    rw [happ, Finset.sum_congr rfl (fun i _ => key i), ← Submodule.coe_sum, ← map_sum, hs]
  · intro μ' hne y hy
    rw [happ]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases h : μ i = ν
    · rcases huniq μ' (P i y) i (hcomp μ' y hy i) (hPmem i y) with h0 | ⟨hμ, _⟩
      · rw [h0, map_zero]
      · exact absurd (hμ.trans h) hne
    · rw [hg0 i h, LinearMap.zero_apply]
