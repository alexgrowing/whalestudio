import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing UpperTheory.V.Alg

namespace UpperTheory.V.Ws

def Pins (l : ℕ) {G : Type} [Group G] [TopologicalSpace G] (I : Subgroup G) (S : Set G) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], (l : R) = 0 → ∀ ψ : G →* Rˣ,
    AdicCont (maximalIdeal R) (fun g => ((ψ g : Rˣ) : R)) → (∀ g ∈ I, ((ψ g : Rˣ) : R) - 1 ∈ maximalIdeal R) →
    (∀ g ∈ S, ψ g = 1) → ∀ g ∈ I, ψ g = 1

theorem eq_one_of_pow {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h0 : (l : R) = 0)
    {x : R} (hx : x - 1 ∈ maximalIdeal R) {N : ℕ} (hN : N ≠ 0) (h : x ^ N = 1) : x = 1 := by
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  obtain ⟨k, M, hlM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.out.ne_one
  have hz1 : x ^ l ^ k - 1 = (x - 1) ^ l ^ k := by rw [sub_pow_char_pow, one_pow]
  have hzM : (x ^ l ^ k) ^ M = 1 := by rw [← pow_mul]; exact h
  have hMu : IsUnit (M : R) := by
    have hu : IsUnit (M : ZMod l) := isUnit_iff_ne_zero.mpr (by rwa [Ne, ZMod.natCast_eq_zero_iff])
    simpa using hu.map (ZMod.castHom (dvd_refl l) R)
  have hzm : x ^ l ^ k - 1 ∈ maximalIdeal R := by
    rw [hz1]; exact Ideal.pow_mem_of_mem _ hx _ (pow_pos hl.out.pos _)
  have hS : IsUnit (∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i) := by
    have key : (∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i) - (M : R) ∈ maximalIdeal R := by
      have e : (∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i) - (M : R) =
          ∑ i ∈ Finset.range M, ((x ^ l ^ k) ^ i - 1) := by
        simp [Finset.sum_sub_distrib]
      rw [e]
      refine Ideal.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (x ^ l ^ k) 1 i
      rw [one_pow] at hc
      rw [hc]
      exact Ideal.mul_mem_right _ _ hzm
    by_contra hns
    have hmem : (∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i) ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; exact hns
    have hM : (M : R) ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hmem key
      simpa using this
    rw [mem_maximalIdeal, mem_nonunits_iff] at hM
    exact hM hMu
  have hz1' : x ^ l ^ k = 1 := by
    have h2 : (x ^ l ^ k - 1) * ∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i = 0 := by
      rw [mul_comm, geom_sum_mul, hzM, sub_self]
    exact sub_eq_zero.mp (hS.mul_left_eq_zero.mp h2)
  have h3 : (x - 1) ^ l ^ k = 0 := by rw [← hz1, hz1', sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero) |>.mp h3)

theorem adicCont_units {G R : Type} [TopologicalSpace G] [CommRing R] (m : Ideal R) (f : G → Rˣ) :
    AdicCont m (fun g => ((f g : Rˣ) : R)) ↔
      ∀ N, IsLocallyConstant fun g => Units.map (Ideal.Quotient.mk (m ^ N) : R →* R ⧸ m ^ N) (f g) := by
  unfold AdicCont
  refine forall_congr' fun N => ⟨fun h => ?_, fun h => ?_⟩
  · refine IsLocallyConstant.desc _ Units.val ?_ fun a b hab => Units.ext hab
    convert h using 1
    ext g
    simp
  · convert h.comp Units.val using 1
    ext g
    simp

theorem Pins.eq {l : ℕ} {G : Type} [Group G] [TopologicalSpace G] {I : Subgroup G} {S : Set G} (h : Pins l I S)
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (h0 : (l : R) = 0) (ψ ψ' : G →* Rˣ)
    (hc : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R)) (hc' : AdicCont (maximalIdeal R) fun g => ((ψ' g : Rˣ) : R))
    (h1 : ∀ g ∈ I, ((ψ g : Rˣ) : R) - 1 ∈ maximalIdeal R) (h1' : ∀ g ∈ I, ((ψ' g : Rˣ) : R) - 1 ∈ maximalIdeal R)
    (hS : ∀ g ∈ S, ψ g = ψ' g) : ∀ g ∈ I, ψ g = ψ' g := by
  intro g hg
  obtain ⟨χ, hχ⟩ : ∃ χ : G →* Rˣ, ∀ g, χ g = ψ g / ψ' g := ⟨ψ / ψ', fun g => rfl⟩
  have hres : ∀ u : Rˣ, (u : R) - 1 ∈ maximalIdeal R ↔
      Units.map (Ideal.Quotient.mk (maximalIdeal R) : R →* R ⧸ maximalIdeal R) u = 1 := by
    intro u
    rw [Units.ext_iff, ← Ideal.Quotient.eq]
    simp
  have hcχ : AdicCont (maximalIdeal R) fun g => ((χ g : Rˣ) : R) := by
    rw [adicCont_units] at hc hc' ⊢
    intro N
    have := (hc N).comp₂ (hc' N) (· / ·)
    convert this using 1
    ext g
    simp [hχ, map_div]
  have h1χ : ∀ g ∈ I, ((χ g : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    intro g hg
    rw [hres, hχ, map_div, (hres _).1 (h1 g hg), (hres _).1 (h1' g hg), div_one]
  have hSχ : ∀ g ∈ S, χ g = 1 := by
    intro g hg
    rw [hχ, hS g hg, div_self']
  have key := h R h0 χ hcχ h1χ hSχ g hg
  rw [hχ, div_eq_one] at key
  exact key

theorem isClosed_ker_of_adicCont {G R : Type} [Group G] [TopologicalSpace G] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ψ : G →* Rˣ) (hc : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R)) : IsClosed (ψ.ker : Set G) := by
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) Ideal.IsPrime.ne_top'
  have e : (ψ.ker : Set G) = ⋂ N, {g | Ideal.Quotient.mk (maximalIdeal R ^ N) ((ψ g : Rˣ) : R) =
      Ideal.Quotient.mk (maximalIdeal R ^ N) 1} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq, Ideal.Quotient.eq]
    constructor
    · intro h N
      simp [h]
    · intro h
      have hm : ((ψ g : Rˣ) : R) - 1 ∈ ⨅ N, maximalIdeal R ^ N := (Submodule.mem_iInf _).2 h
      rw [hK, Ideal.mem_bot, sub_eq_zero] at hm
      exact Units.ext hm
  rw [e]
  exact isClosed_iInter fun N => (hc N).isClosed_fiber _

end UpperTheory.V.Ws
