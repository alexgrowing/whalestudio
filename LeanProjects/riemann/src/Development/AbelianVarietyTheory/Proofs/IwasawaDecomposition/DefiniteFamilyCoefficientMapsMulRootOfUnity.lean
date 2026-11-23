import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsLev
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

open Formalism.DivisionValues

variable {D : D7}

theorem exists_unit_of_pow (a : D.what₂.LL) (n : ℕ) (hn : n ≠ 0) (ha : a ^ n = 1) :
    ∃ u : (𝓞 D.what₂.LL)ˣ, ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = a ∧ a ∈ Formalism.DivisionValues.cmMax D.what₂.LL ∧ star a * a = 1 := by
  have hσ : ∀ σ : D.what₂.LL →+* ℂ, ‖σ a‖ = 1 := fun σ => by
    have h : (σ a) ^ n = 1 := by rw [← map_pow, ha, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one h hn
  have hconj : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun z hz => by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    simp
  have a0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at ha
    exact zero_ne_one ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 a0
  have h2 : star a * a = 1 := D.what₂.embLL.injective (by
    rw [map_mul, D.starLL_cx, hconj _ (hσ _), inv_mul_cancel₀ m0, map_one])
  have hs : star a = a⁻¹ := eq_inv_of_mul_eq_one_left h2
  have h1 : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
    change ∀ σ : D.what₂.LL →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)
    intro σ
    rw [hs, map_inv₀, hconj _ (hσ σ)]
  have hi : IsIntegral (𝓞 D.what₂.LL) a := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [ha]
    exact isIntegral_one
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hx1 : x ^ n = 1 := IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [map_pow, hx, ha, map_one])
  refine ⟨(IsUnit.of_pow_eq_one hx1 hn).unit, ?_, h1, h2⟩
  rw [IsUnit.unit_spec]
  exact hx

theorem coefMapTie_smul {V C lam c0 rho} (h : Formalism.IndefR.Bridge.CoefMapTie (D := D) V C (lam := lam) c0 rho) {μ : ℂ} (hμ : μ ≠ 0) :
    Formalism.IndefR.Bridge.CoefMapTie V C (μ • c0) rho := by
  obtain ⟨a1, a2, a3⟩ := h
  refine ⟨fun γ γE hγ v => by simp [a1 γ γE hγ v], a2.units_smul fun _ => Units.mk0 _ hμ, ?_⟩
  rw [eq_top_iff, ← a3, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have := Submodule.smul_mem _ μ⁻¹ (Submodule.subset_span (R := ℂ)
    (s := Set.range fun i => (μ • c0) (bVV D.what₂.LL lam i)) ⟨i, rfl⟩)
  exact Set.mem_of_eq_of_mem (inv_smul_smul₀ hμ (c0 _)).symm this

theorem coefTie_smul {V C S J χ P lam c0 pair nab del}
    (h : Formalism.IndefR.Bridge.CoefTie (D := D) V C (S := S) (J := J) (χ := χ) P lam c0 pair nab del)
    (l : D.what₂.LL) (u : (𝓞 D.what₂.LL)ˣ) (hu : ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = l) (h1 : l ∈ Formalism.DivisionValues.cmMax D.what₂.LL)
    (h2 : star l * l = 1) :
    Formalism.IndefR.Bridge.CoefTie V C P lam (D.what₂.embLL l • c0) pair nab del := by
  have l0 : l ≠ 0 := right_ne_zero_of_mul_eq_one h2
  have m0 : D.what₂.embLL l ≠ 0 := (map_ne_zero _).2 l0
  have li : (((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) : D.what₂.LL) = l⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← hu, ← map_mul (algebraMap (𝓞 D.what₂.LL) D.what₂.LL), Units.inv_mul, map_one])
  obtain ⟨e, a1, a2, a3, a4, a5⟩ := h
  let s := LinearEquiv.smulOfNeZero D.what₂.LL (VV D.what₂.LL lam) l⁻¹ (inv_ne_zero l0)
  have hs : ∀ x, (e.trans s) x = l⁻¹ • e x := fun _ => rfl
  have hm : ∀ N : Submodule (𝓞 D.what₂.LL) S.V,
      N.map ((e.trans s).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) =
        N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := fun N => by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      exact (map_smul e _ _).trans (congrArg (· • e v) li)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(u : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      show (e.trans s) ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL)) • v) = e v
      rw [show algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL) = l from hu]
      exact (hs _).trans ((congrArg (l⁻¹ • ·) (map_smul e l v)).trans (inv_smul_smul₀ l0 _))
  refine ⟨e.trans s, fun i j => ?_, fun x => ?_, fun x x' => ?_, fun c => (hm _).trans (a4 c), fun c => (hm _).trans (a5 c)⟩
  · rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem (inv_mem h1) (a1 i j)
  · rw [hs, LinearMap.smul_apply, map_smulₛₗ, map_inv₀, smul_inv_smul₀ m0, a2]
  · rw [hs, hs, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, a3, smul_smul, starRingEnd_apply, star_inv₀,
      ← mul_inv, mul_comm, h2, inv_one, one_smul]

end GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

namespace GlobalTheory.Mem.R3.Rw.OmExt

set_option maxHeartbeats 1000000 in

theorem coefFam_update_root : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W),
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R c0L → ∀ (i : Fin D.R.m) (a : D.what₂.LL) (n : ℕ), n ≠ 0 → a ^ n = 1 →
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R (Function.update c0L i (D.what₂.embLL a • c0L i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R c0L hc i a n hn ha
  obtain ⟨u, hu, h1, h2⟩ := RootUpd.exists_unit_of_pow a n hn ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 (right_ne_zero_of_mul_eq_one h2)
  obtain ⟨gramR, c0R, ht⟩ := hc
  refine ⟨gramR, c0R, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ht.ok, ht.gramR_eq, ht.mapR, fun j => ?_,
    ht.coefR, fun j t => ?_⟩⟩
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefMapTie_smul (ht.mapL j) m0
    · rw [Function.update_of_ne hj]
      exact ht.mapL j
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefTie_smul (ht.coefL j t) a u hu h1 h2
    · rw [Function.update_of_ne hj]
      exact ht.coefL j t

end GlobalTheory.Mem.R3.Rw.OmExt

end
