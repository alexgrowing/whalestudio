import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NnDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Ws

section
open UpperTheory.V.W

end

private theorem exists_pow_l_pow_eq_one_of_mem_muG {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ψ : G →* Rˣ) (hψc : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R))
    (g : G) (hg : g ∈ UpperTheory.V.W.muG l G) : ∃ n : ℕ, ψ g ^ (l ^ n) = 1 := by
  obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.1 hg
  refine ⟨n, ?_⟩
  have h1 : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hn
  have hker : (commutator G).topologicalClosure ≤ ψ.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker ψ)
      (isClosed_ker_of_adicCont ψ hψc)
  rw [← map_pow]
  exact hker h1

theorem UpperTheory.exists_pinning_elements_of_locAb :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (I : Subgroup G) (d : ℕ), UpperTheory.V.W.LocAb l G I d → ∃ s : Fin d → G, (∀ k, s k ∈ I) ∧ Pins l I (Set.range s) := by
  intro l _ G _ _ _ _ I d A
  have hlp : l.Prime := Fact.out
  have hs : ∀ k : Fin d, ∃ g ∈ I,
      A.a g = Multiplicative.ofAdd ((Pi.single k 1 : Fin d → ℤ_[l]), (0 : ℤ_[l])) :=
    fun k => (A.inertia _).2 rfl
  choose s hsI hsa using hs
  refine ⟨s, hsI, ?_⟩
  intro R _ _ _ _ hl ψ hψc hψI hψs g hg
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hlp).2 hl
  have hsk : ∀ k, ψ (s k) = 1 := fun k => hψs _ ⟨k, rfl⟩
  have hq : ∀ (N : ℕ) (u : Rˣ),
      Units.map (↑(Ideal.Quotient.mk (maximalIdeal R ^ N)) : R →* R ⧸ maximalIdeal R ^ N) u = 1 ↔
        (u : R) - 1 ∈ maximalIdeal R ^ N := by
    intro N u
    rw [Units.ext_iff]
    show Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R) = 1 ↔ _
    rw [← map_one (Ideal.Quotient.mk (maximalIdeal R ^ N)), Ideal.Quotient.eq]
  let ρN : (N : ℕ) → G →* (R ⧸ maximalIdeal R ^ N)ˣ := fun N =>
    (Units.map (↑(Ideal.Quotient.mk (maximalIdeal R ^ N)) : R →* R ⧸ maximalIdeal R ^ N)).comp ψ
  have hloc : ∀ N, IsLocallyConstant (ρN N) := fun N => (adicCont_units _ _).1 hψc N
  haveI hfin1 : Finite (ρN 1).range := (hloc 1).range_finite.to_subtype
  set M := Nat.card (ρN 1).range with hMdef
  have hM0 : M ≠ 0 := Nat.card_pos.ne'
  have hres : ∀ g, ((ψ g ^ M : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    intro g
    have h1 := congrArg (fun u : (ρN 1).range => (u : (R ⧸ maximalIdeal R ^ 1)ˣ))
      (pow_card_eq_one' (G := (ρN 1).range) (x := ⟨ρN 1 g, g, rfl⟩))
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, ← hMdef] at h1
    rw [← map_pow] at h1
    simpa using (hq 1 _).1 h1
  have hmu : ∀ g ∈ UpperTheory.V.W.muG l G, ψ g ^ M = 1 := by
    intro g hg
    obtain ⟨n, hn⟩ := exists_pow_l_pow_eq_one_of_mem_muG ψ hψc g hg
    apply Units.ext
    refine eq_one_of_pow hl (hres g) (pow_ne_zero n hlp.ne_zero) ?_
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hn, one_pow, Units.val_one]
  let φN : (N : ℕ) → G →* (R ⧸ maximalIdeal R ^ N)ˣ := fun N => (powMonoidHom M).comp (ρN N)
  have hφloc : ∀ N, IsLocallyConstant (φN N) := fun N => (hloc N).comp (fun u => u ^ M)
  have hφ : ∀ N g, φN N g = 1 ↔ ((ψ g ^ M : Rˣ) : R) - 1 ∈ maximalIdeal R ^ N := by
    intro N g
    rw [← hq]
    rw [map_pow]
    exact Iff.rfl
  have hφp : ∀ N g, (φN N g) ^ (l ^ N) = 1 := by
    intro N g
    rw [← map_pow, hφ]
    set y := ((ψ g ^ M : Rˣ) : R) - 1 with hy
    have hym : y ∈ maximalIdeal R := hres g
    have : (((ψ g ^ M) ^ (l ^ N) : Rˣ) : R) = 1 + y ^ (l ^ N) := by
      rw [Units.val_pow_eq_pow_val, show ((ψ g ^ M : Rˣ) : R) = 1 + y by rw [hy]; ring,
        add_pow_char_pow, one_pow]
    rw [map_pow, ← pow_mul, mul_comm (l ^ N) M, pow_mul, this, add_sub_cancel_left]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self hlp.one_lt).le (Ideal.pow_mem_pow hym _)
  have hK : ∀ N, A.a.ker ≤ (φN N).ker := by
    intro N
    haveI : Finite (φN N).range := (hφloc N).range_finite.to_subtype
    have hP : IsPGroup l (φN N).range := by
      rintro ⟨x, g, rfl⟩
      exact ⟨N, Subtype.ext (hφp N g)⟩
    have := A.univ (φN N).range hP (φN N).rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact (hφloc N).isOpen_fiber 1)
      (by
        intro g hg
        rw [MonoidHom.ker_rangeRestrict]
        exact (hφ N g).2 (by rw [hmu g hg, Units.val_one, sub_self]; exact zero_mem _))
    rwa [MonoidHom.ker_rangeRestrict] at this
  have hclosed : ∀ N, IsClosed ((Subgroup.map A.a (φN N).ker : Subgroup _) :
      Set (Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]))) := by
    intro N
    rw [Subgroup.coe_map]
    exact (((hφloc N).isClosed_fiber 1).isCompact.image A.cont).isClosed
  have hmem : ∀ N (x : Fin d → ℤ_[l]),
      Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ Subgroup.map A.a (φN N).ker := by
    intro N
    have hint : ∀ z : Fin d → ℤ, Multiplicative.ofAdd ((fun k => (z k : ℤ_[l])), (0 : ℤ_[l])) ∈
        Subgroup.map A.a (φN N).ker := by
      intro z
      have he : ((fun k => (z k : ℤ_[l])), (0 : ℤ_[l])) =
          ∑ k, z k • ((Pi.single k 1 : Fin d → ℤ_[l]), (0 : ℤ_[l])) := by
        refine Prod.ext ?_ ?_
        · funext j
          rw [Prod.fst_sum, Finset.sum_apply]
          simp [Pi.single_apply]
        · rw [Prod.snd_sum]
          simp
      rw [he, ofAdd_sum]
      refine Subgroup.prod_mem _ fun k _ => ?_
      rw [ofAdd_zsmul]
      refine Subgroup.zpow_mem _ ?_ _
      refine ⟨s k, ?_, hsa k⟩
      exact (hφ N (s k)).2 (by rw [hsk, one_pow, Units.val_one, sub_self]; exact zero_mem _)
    have hT : IsClosed {x : Fin d → ℤ_[l] |
        Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ Subgroup.map A.a (φN N).ker} :=
      (hclosed N).preimage (continuous_ofAdd.comp (continuous_id.prodMk continuous_const))
    have hD : DenseRange (Pi.map fun (_ : Fin d) (z : ℤ) => (z : ℤ_[l])) :=
      DenseRange.piMap fun _ => PadicInt.denseRange_intCast
    intro x
    have hx : x ∈ closure (Set.range (Pi.map fun (_ : Fin d) (z : ℤ) => (z : ℤ_[l]))) := by
      rw [hD.closure_eq]
      exact Set.mem_univ x
    exact hT.closure_subset_iff.2 (by rintro _ ⟨z, rfl⟩; exact hint z) hx
  have hgN : ∀ N, φN N g = 1 := by
    intro N
    obtain ⟨x, hx⟩ : ∃ x, A.a g = Multiplicative.ofAdd x := ⟨Multiplicative.toAdd (A.a g), rfl⟩
    have hx2 : x.2 = 0 := (A.inertia x).1 ⟨g, hg, hx⟩
    obtain ⟨h, hh, hah⟩ := hmem N x.1
    have hk : h⁻¹ * g ∈ A.a.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hah, hx, inv_mul_eq_one, ← hx2]
    have := hK N hk
    rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 hh, inv_one, one_mul] at this
    exact this
  have hzero : ((ψ g ^ M : Rˣ) : R) - 1 = 0 := by
    have : ((ψ g ^ M : Rˣ) : R) - 1 ∈ ⨅ N, maximalIdeal R ^ N :=
      Ideal.mem_iInf.2 fun N => (hφ N g).1 (hgN N)
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
      Ideal.mem_bot] at this
  apply Units.ext
  refine eq_one_of_pow hl (hψI g hg) hM0 ?_
  rw [← Units.val_pow_eq_pow_val]
  exact sub_eq_zero.1 hzero
