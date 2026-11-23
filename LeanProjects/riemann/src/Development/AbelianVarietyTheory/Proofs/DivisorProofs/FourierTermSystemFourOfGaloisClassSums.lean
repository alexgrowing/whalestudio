import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxIntegralClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SFour

theorem pow_le_map {V V' : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing V'] [IsLocalRing V']
    (io : V →+* V') (hfin : io.Finite) :
    ∃ J : ℕ, ∀ j : ℕ, maximalIdeal V' ^ (J * j) ≤ (maximalIdeal V ^ j).map io := by
  letI := io.toAlgebra
  haveI : Module.Finite V V' := hfin
  obtain ⟨E, hE⟩ := GlobalTheory.Poinc.OrbTrace.exists_pow_le (A := V) (B := V') (maximalIdeal V') (maximalIdeal.isMaximal V') 1
  have h1 : maximalIdeal V' ^ E ≤ (maximalIdeal V).map io := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hE x hx
    have hu' : IsUnit u := by
      by_contra h
      exact hu ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [pow_one] at hux
    exact (Ideal.unit_mul_mem_iff_mem _ hu').1 hux
  refine ⟨E, fun j => ?_⟩
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_right_mono h1 j

variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A]
  [IsLocalRing A]

theorem term_mem (Φ : VPre bar q W A) (y : Φ.Y) (mu : Fin s → Φ.X y) (cc : Φ.Q) (j : ℕ)
    (hj : (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) : Φ.term y mu cc ∈ maximalIdeal (Φ.V y) ^ j := by
  have hnn : ∀ i, 0 ≤ qW W (Φ.δ y i) mu := fun i => qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) mu
  have hle : j ≤ ∑ i, (qW W (Φ.δ y i) mu).toNat := by
    have e1 : ((∑ i, (qW W (Φ.δ y i) mu).toNat : ℕ) : ℤ) = ∑ i, qW W (Φ.δ y i) mu := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hnn i)
    rw [← e1] at hj
    exact_mod_cast hj
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle ?_)
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Φ.t_mem y i).1 _

end GlobalTheory.Poinc.SFour

namespace GlobalTheory.Poinc.SFour

theorem four_of_classSums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.ClassSums N₁ → Φ.Four N₁ := by
  intro O _ bar q s W A _ _ _ _ Φ N₁ hcs y₀ N₀
  classical
  obtain ⟨N, hN0, hN1, hNd, k, hk0, hk, L, _, _, _, _, _, _, 𝔷, f, hz, hf, hy, hσ⟩ := hcs y₀ N₀
  refine ⟨N, hN0, hNd, k, hk0, hk, fun l a c e => ?_⟩
  obtain ⟨C, hC1, hC2, hC3⟩ := OrbTrace.exists_classes (O := O) (N₁ := N₁) hN1 a
  set F : integralClosure A L := ∑ c' ∈ C, ∏ i, f (fun u => c' (i, u)) (c i) with hF
  have hFix : ∀ σ : L ≃ₐ[FractionRing A] L, (∀ x x' : integralClosure A L, (x' : L) = σ x → (x ∈ 𝔷 ↔ x' ∈ 𝔷)) →
      σ (F : L) = F := by
    intro σ hσ'
    obtain ⟨ga, h1, h2, h3, h4⟩ := hσ σ hσ'
    have e1 : ((F : integralClosure A L) : L) = ∑ c' ∈ C, ∏ i, (f (fun u => c' (i, u)) (c i) : L) := by
      rw [hF]; push_cast; rfl
    rw [e1, map_sum]
    simp only [map_prod, h4]
    exact OrbTrace.sum_comp_eq C hC1 hC2 hC3 ga h1 h2 h3 (fun c' => ∏ i, (f (fun u => c' (i, u)) (c i) : L))
      (fun c₁ c₂ h => Finset.prod_congr rfl fun i _ => by rw [hf _ _ _ fun u => h _])
  haveI := hz
  obtain ⟨g₀, b, hb, hbF⟩ := GlobalTheory.DecompFixed.exists_approx_integralClosure A (FractionRing A) L 𝔷 F hFix e
  refine ⟨g₀, fun y j => ?_⟩
  obtain ⟨V', _, _, io, ev', hfin, hloc, hpure, hcomm, hcomap, hcls⟩ := hy y
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  obtain ⟨J, hJ⟩ := pow_le_map io hfin
  set j' := J * j + j with hj'
  have hjj : j ≤ j' := Nat.le_add_left _ _
  have hJj : maximalIdeal V' ^ j' ≤ (maximalIdeal (Φ.V y) ^ j).map io :=
    (Ideal.pow_le_pow_right (Nat.le_add_right _ _)).trans (hJ j)
  have hmap : ∀ n, (maximalIdeal (Φ.V y) ^ n).map io ≤ maximalIdeal V' ^ n := by
    intro n
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 <|
      (IsLocalRing.mem_maximalIdeal _).2 fun h => (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit io x h)) n
  choose S₀ hSa hSb hSc using fun κ cc => hcls κ cc j'
  set T : Finset (Fin s → Φ.X y) := C.biUnion (fun c' => Finset.univ.biUnion
    (fun i => S₀ (fun u => c' (i, u)) (c i))) with hT
  have hSfin : {mu : Fin l × Fin s → Φ.X y | mu ∈ orbit O N₁ N (k y) a ∧ ∀ i, (fun u => mu (i, u)) ∈ T}.Finite := by
    refine ((Set.Finite.pi' (fun _ : Fin l => T.finite_toSet)).image (fun x j => x j.1 j.2)).subset ?_
    intro mu hmu
    exact ⟨fun i u => mu (i, u), hmu.2, rfl⟩
  refine ⟨hSfin.toFinset, fun mu hmu => (hSfin.mem_toFinset.1 hmu).1, fun mu hmu hmuS => ?_, ?_⟩
  · rw [hSfin.mem_toFinset] at hmuS
    obtain ⟨i, hi⟩ : ∃ i, (fun u => mu (i, u)) ∉ T := by
      by_contra hcon
      push_neg at hcon
      exact hmuS ⟨hmu, hcon⟩
    obtain ⟨gm, g1, g2, g3, g4⟩ := hmu
    obtain ⟨c', hc', hcc⟩ := hC3 (fun idx => gm (a idx)) ⟨gm, g1, g2, g3, fun idx => OrbTrace.cm_refl _⟩
    have hcong : ∀ v, CongMod N (mu (i, v)) (k y (c' (i, v))) := fun v =>
      OrbTrace.cm_trans (g4 _) (OrbTrace.cm_map (k y) (OrbTrace.cm_symm (hcc _)))
    have hnot : (fun u => mu (i, u)) ∉ S₀ (fun u => c' (i, u)) (c i) := fun h =>
      hi (Finset.mem_biUnion.2 ⟨c', hc', Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩⟩)
    have h1 := hSb (fun u => c' (i, u)) (c i) (fun u => mu (i, u)) hcong hnot
    have hnn : ∀ fi i', 0 ≤ qW W (Φ.δ y fi) (fun u => mu (i', u)) := fun fi i' =>
      qW_nonneg Φ.posW (Φ.bal y fi).1 (Φ.nonneg y fi) _
    calc (j : ℤ) ≤ j' := by exact_mod_cast hjj
      _ ≤ ∑ fi, qW W (Φ.δ y fi) (fun u => mu (i, u)) := h1
      _ ≤ ∑ fi, lin W mu (Φ.δ y fi) := Finset.sum_le_sum fun fi _ =>
          Finset.single_le_sum (f := fun i' => qW W (Φ.δ y fi) (fun u => mu (i', u))) (fun i' _ => hnn fi i')
            (Finset.mem_univ i)
  · have key : ∀ c' ∈ C, ∀ i (U : Finset (Fin s → Φ.X y)), S₀ (fun u => c' (i, u)) (c i) ⊆ U →
        (∀ ν ∈ U, ∀ v, CongMod N (ν v) (k y (c' (i, v)))) →
        ev' (f (fun u => c' (i, u)) (c i)) - io (∑ ν ∈ U, Φ.u y ν (c i) * mono W (Φ.t y) (Φ.δ y) ν) ∈
          maximalIdeal V' ^ j' := by
      intro c' hc' i U hU hU'
      rw [← Finset.sum_sdiff hU, map_add]
      have e2 : ∀ x y z : V', x - (y + z) = (x - z) - y := fun _ _ _ => by ring
      rw [e2]
      refine sub_mem (hSc _ _) (hmap j' (Ideal.mem_map_of_mem io (Ideal.sum_mem _ fun ν hν => ?_)))
      obtain ⟨hνU, hνS⟩ := Finset.mem_sdiff.1 hν
      exact term_mem Φ y ν (c i) j' (hSb _ _ ν (hU' ν hνU) hνS)
    have hsum := OrbTrace.sum_orbit_eq C hC1 hC2 hC3 (k y) (hk y) T hSfin.toFinset (fun mu => hSfin.mem_toFinset)
      (fun i ν => Φ.u y ν (c i) * mono W (Φ.t y) (Φ.δ y) ν)
    have hF' : ev' F - io (∑ mu ∈ hSfin.toFinset, ∏ i, Φ.u y (fun v => mu (i, v)) (c i) *
        mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v))) ∈ maximalIdeal V' ^ j' := by
      rw [hsum]
      rw [← Ideal.Quotient.eq]
      rw [hF, map_sum ev', map_sum io, map_sum (Ideal.Quotient.mk _), map_sum (Ideal.Quotient.mk _)]
      refine Finset.sum_congr rfl fun c' hc' => ?_
      rw [map_prod ev', map_prod io, map_prod (Ideal.Quotient.mk _), map_prod (Ideal.Quotient.mk _)]
      refine Finset.prod_congr rfl fun i _ => Ideal.Quotient.eq.2 (key c' hc' i _ ?_ ?_)
      · intro ν hν
        exact Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨c', hc', Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hν⟩⟩,
          hSa _ _ ν hν⟩
      · intro ν hν
        exact (Finset.mem_filter.1 hν).2
    have hD : ev' F - io (Φ.ev y g₀) ∈ ((maximalIdeal A ^ e).map (Φ.ev y)).map io := by
      have h1 := Ideal.mem_map_of_mem ev' hbF
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, map_mul, map_sub] at h1
      have hu : IsUnit (ev' b) := by
        by_contra h
        exact hb (by rw [← hcomap]; exact Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      have h2 := (Ideal.unit_mul_mem_iff_mem _ hu).1 h1
      have h3 : ev' (algebraMap A (integralClosure A L) g₀) = io (Φ.ev y g₀) := RingHom.congr_fun hcomm g₀
      rwa [h3] at h2
    rw [← hpure (maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y))]
    refine Ideal.mem_comap.2 ?_
    rw [Ideal.map_sup, map_sub]
    have h4 := sub_mem (Ideal.mem_sup_left (T := ((maximalIdeal A ^ e).map (Φ.ev y)).map io) (hJj hF'))
      (Ideal.mem_sup_right (S := (maximalIdeal (Φ.V y) ^ j).map io) hD)
    rwa [sub_sub_sub_cancel_left] at h4

end GlobalTheory.Poinc.SFour
