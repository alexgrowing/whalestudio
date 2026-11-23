import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.CLBGen
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.CLBAlg
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.CLBKer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto

open Pb CLB

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}}

theorem strV_appLE (q : Z ⟶ Spec (CommRingCat.of K)) (π : Y ⟶ Z) (V : Z.Opens) (U : Y.Opens) (h : U ≤ π ⁻¹ᵁ V) :
    strV (π ≫ q) U = (π.appLE V U h).hom.comp (strV q V) := by
  unfold strV
  rw [← Scheme.Hom.appLE_comp_appLE π q ⊤ V U le_top h]
  rfl

theorem strV_app (q : Z ⟶ Spec (CommRingCat.of K)) (π : Y ⟶ Z) (U : Z.Opens) :
    strV (π ≫ q) (π ⁻¹ᵁ U) = (π.app U).hom.comp (strV q U) := by
  rw [strV_appLE q π U (π ⁻¹ᵁ U) le_rfl, Scheme.Hom.app_eq_appLE]

theorem rs_appLE (π : Y ⟶ Z) (V : Z.Opens) (U U' : Y.Opens) (hU : U ≤ π ⁻¹ᵁ V) (h : U' ≤ U) (a : Γ(Z, V)) :
    rs h ((π.appLE V U hU).hom a) = (π.appLE V U' (h.trans hU)).hom a := by
  unfold rs
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem card_ne (m : ℕ) (j0 : Fin m) : Fintype.card {j : Fin m // j ≠ j0} = m - 1 := by
  simp [Fintype.card_subtype_compl]

theorem chartLaws_B : ∀ (K : Type) [Field K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
    [IsClosedImmersion i] (π : Y ⟶ Z) (d : ℕ) (V : Z.Opens) (c : BChart q i π d V),
    ∀ (k : Fin d) (D : Y.Opens) (h : D ≤ c.C k), IsAffineOpen D → Nonempty (Coord (π ≫ q) D (c.n + d)) ∧
      Nonempty (Coord (pullback.snd i π ≫ π ≫ q) (pullback.snd i π ⁻¹ᵁ D) (c.n + d - 1)) ∧
      RingHom.ker ((pullback.snd i π).app D).hom = Ideal.span {(π.appLE V D (h.trans (c.C_le k))).hom (c.t k)} ∧
      ∀ (a : ℕ) (ω : Om K (Sec (π ≫ q) D) a),
        (show Sec (π ≫ q) D from (π.appLE V D (h.trans (c.C_le k))).hom (c.t k)) • ω = 0 → ω = 0 := by
  intro K _ W Z Y q i _ π d V c k D h hD
  have hDV : D ≤ π ⁻¹ᵁ V := h.trans (c.C_le k)
  set φ := (π.appLE V (c.C k) (c.C_le k)).hom with hφ
  set yC : Fin c.n ⊕ Fin d → Γ(Y, c.C k) := Sum.elim (φ ∘ c.x) (fun j => if j = k then φ (c.t k) else c.u k j) with hyC
  have hC := chart_etale (strV q V) c.x c.t c.etale φ (c.u k) k (c.surj k) (c.rel k)
  let cC : Coord (π ≫ q) (c.C k) (c.n + d) :=
    ⟨c.C_aff k, yC ∘ finSumFinEquiv.symm, by
      rw [strV_appLE q π V (c.C k) (c.C_le k)]
      exact etale_reindex _ _ _ hC⟩
  obtain ⟨cD, hcD⟩ := coord_res cC h hD
  set j0 : Fin (c.n + d) := finSumFinEquiv (Sum.inr k) with hj0
  set τ := (π.appLE V D hDV).hom (c.t k) with hτ
  have ht : cD.t j0 = τ := by
    rw [hcD]
    change rs h (yC (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr k)))) = _
    rw [Equiv.symm_apply_apply]
    simp only [hyC, Sum.elim_inr, hφ]
    exact rs_appLE π V (c.C k) D (c.C_le k) h (c.t k)

  have hrel : ∀ j, φ (c.t j) = φ (c.t k) * c.u k j := by
    intro j
    have hm : MvPolynomial.C (c.t j) - MvPolynomial.C (c.t k) * MvPolynomial.X j ∈
        RingHom.ker (MvPolynomial.eval₂Hom φ (c.u k)) := by
      rw [c.rel k]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
    rw [RingHom.mem_ker] at hm
    simpa [sub_eq_zero] using hm
  have hker : RingHom.ker ((pullback.snd i π).app D).hom = Ideal.span {τ} := by
    rw [ker_snd i π V c.affine D hD hDV, c.ker, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_span_singleton']
      refine ⟨rs h (c.u k j), ?_⟩
      rw [hτ, ← rs_appLE π V (c.C k) D (c.C_le k) h, ← rs_appLE π V (c.C k) D (c.C_le k) h, ← map_mul, ← hφ,
        hrel j, mul_comm]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨c.t k, ⟨k, rfl⟩, rfl⟩
  refine ⟨⟨cD⟩, ?_, hker, ?_⟩
  · have hsurj := app_surj (pullback.snd i π) D hD
    have hq := quot_etale (strV (π ≫ q) D) cD.t j0 cD.etale ((pullback.snd i π).app D).hom hsurj (by rw [hker, ht])
    let e : Fin (c.n + d - 1) ≃ {j : Fin (c.n + d) // j ≠ j0} :=
      (Fintype.equivFinOfCardEq (card_ne (c.n + d) j0)).symm
    refine ⟨⟨hD.preimage (pullback.snd i π), (fun j : {j : Fin (c.n + d) // j ≠ j0} =>
      ((pullback.snd i π).app D).hom (cD.t j)) ∘ e, ?_⟩⟩
    rw [strV_app (π ≫ q) (pullback.snd i π) D]
    exact etale_reindex _ _ _ hq
  · intro a ω hω
    have hal : algebraMap K (Sec (π ≫ q) D) = strV (π ≫ q) D := rfl
    have he : (MvPolynomial.eval₂Hom (algebraMap K (Sec (π ≫ q) D)) (cD.t : Fin (c.n + d) → Sec (π ≫ q) D)).Etale := by
      rw [hal]; exact cD.etale
    have key : ∀ ω' : Om K (Sec (π ≫ q) D) a, (cD.t j0 : Sec (π ≫ q) D) • ω' = 0 → ω' = 0 :=
      coord_nzd (K := K) (B := Sec (π ≫ q) D) _ he j0 a
    apply key
    rw [ht]
    exact hω

end CrystallineSemistableComparison.Onto

end
