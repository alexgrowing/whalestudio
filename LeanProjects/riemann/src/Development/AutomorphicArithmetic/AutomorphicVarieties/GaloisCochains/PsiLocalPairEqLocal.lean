import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.StrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

open scoped Pointwise in
private theorem ine_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (v : G F Ω)
    (B : ValuationSubring Ω) (g : G F Ω) (hg : g ∈ Ine (F := F) (v • B)) : v⁻¹ * g * v ∈ Ine (F := F) B := by
  have hl : IsLift (RingEquiv.refl F) v.toRingEquiv := fun y => v.commutes y
  have hA : ∀ x : Ω, v.toRingEquiv x ∈ v • B ↔ x ∈ B := fun x => by
    show v • x ∈ v • B ↔ x ∈ B
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have e : v⁻¹ * g * v = conjGal hl g := AlgEquiv.ext fun _ => rfl
  rw [e]
  exact conjGal_mem_Ine hl hA hg

private theorem not_dvd_ker_index {H : Type} [Group H] (l : ℕ) [hl : Fact l.Prime] (χ : H →* (ZMod (l ^ 1))ˣ) :
    ¬ l ∣ χ.ker.index := by
  intro h
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  rw [Subgroup.index_ker] at h
  have h2 := h.trans (Subgroup.card_subgroup_dvd_card χ.range)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h2
  have h3 := hl.out.two_le
  have := Nat.le_of_dvd (by omega) h2
  omega

private theorem Psi_local_pair_eq_local {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (Φ : Fr.Frame l k) (p : Φ.V × Bool)
    (s : Φ.Gv p.1) : Φ.Ψ (Φ.loc2 p s).1 = Φ.Ψ (Φ.loc p.1 s) := by
  obtain ⟨v, b⟩ := p
  cases b
  · rfl
  · show Φ.Ψ (Φ.c * Φ.loc v s * Φ.c⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem UpperTheory.V.GC.b1 :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) → ∀ C₀ : ℕ, clRk l (K ⊓ (cycMod F Ω l 1).ker) ≤ C₀ → Module.rank k (H1C (k := k) (W := k) Φ.loc2 (chRep (Φ.Ψ⁻¹.comp Φ.del.ker.subtype)) fun _ => ⊥) ≤ C₀ := by
  intro F Ω _ _ _ _ _ l hl k _ _ Φ S K π ι A pl e c h hΨ C₀ hC
  haveI := h.g.normal
  let U : Subgroup (G F Ω) := Φ.del.ker.comap π
  let π' : U →* Φ.del.ker := π.subgroupComap Φ.del.ker
  have hπ' : ∀ u : U, (π' u).1 = π u.1 := fun _ => rfl
  have hKU : K ≤ U := fun g hg => h.K_del g hg
  have hω : IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) :=
    by
      haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
      have e1 : ((cycMod F Ω l 1).ker : Set (G F Ω)) =
          (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - 1) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-(1 : ℕ) : ℤ)) := by
        ext g
        rw [Set.mem_preimage, mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
          RingHom.mem_ker, map_sub, map_one, sub_eq_zero, SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff]
        rfl
      rw [e1]
      refine (IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))).preimage ?_
      exact (Units.continuous_val.comp (continuous_cycZ F Ω l)).sub continuous_const
  have hidx : ¬ l ∣ (K ⊓ (cycMod F Ω l 1).ker).relIndex U := by
    intro hd
    have h1 := hd.trans (Subgroup.relIndex_dvd_index_of_le (inf_le_left.trans hKU : K ⊓ (cycMod F Ω l 1).ker ≤ U))
    rw [← Subgroup.relIndex_mul_index (inf_le_left : K ⊓ (cycMod F Ω l 1).ker ≤ K), Subgroup.inf_relIndex_left] at h1
    rcases (Nat.Prime.dvd_mul hl.out).1 h1 with h2 | h2
    · exact not_dvd_ker_index l _ (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
    · exact h.g.idx h2
  have key := strGen F Ω l k U (K ⊓ (cycMod F Ω l 1).ker) (inf_le_left.trans hKU) (h.g.isOpen.inter hω) hidx
    Φ.del.ker π' ((h.g.cont.comp continuous_subtype_val).subtype_mk _)
    (π.subgroupComap_surjective_of_surjective _ h.g.onto) (Φ.V × Bool) (fun p => Φ.Gv p.1) Φ.loc2
    (Φ.Ψ⁻¹.comp Φ.del.ker.subtype) (fun u hu => by
      show (Φ.Ψ (π u.1))⁻¹ = 1
      rw [h.K_Ψ _ hu.1, inv_one]) (fun B u hu huK => by
      by_cases hB : B = ⊤
      · left
        rw [((Base.places F Ω l B).2.1 hB).1, Subgroup.mem_bot] at hu
        exact Subtype.ext (by rw [hπ', hu, map_one]; rfl)
      obtain ⟨w, hw⟩ := (Base.places F Ω l B).1 hB
      by_cases hS : w ∈ S
      · right
        obtain ⟨v, rfl⟩ := (h.loc.mem w).2 (h.only w hS)
        obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (h.loc.isOver v) hw
        have h1 := Ine_le_Dec _ (ine_conj g _ _ hu)
        rw [← h.loc.range v] at h1
        obtain ⟨s, hs⟩ := h1
        have h2 : π u.1 = π g * Φ.loc v s * (π g)⁻¹ := by
          rw [h.loc_eq, hs, ← map_inv, ← map_mul, ← map_mul]
          congr 1
          group
        rcases Int.units_eq_one_or (Φ.del (π g)) with h3 | h3
        · exact ⟨(v, false), s, ⟨π g, h3⟩, Subtype.ext h2⟩
        · refine ⟨(v, true), s, ⟨π g * Φ.c⁻¹, ?_⟩, Subtype.ext (h2.trans ?_)⟩
          · rw [MonoidHom.mem_ker, map_mul, map_inv, h3, h.del_c, mul_inv_cancel]
          · show _ = π g * Φ.c⁻¹ * (Φ.c * Φ.loc v s * Φ.c⁻¹) * (π g * Φ.c⁻¹)⁻¹
            group
      · left
        refine Subtype.ext ?_
        show π u.1 = 1
        rw [← MonoidHom.mem_ker, h.g.ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨w, hS, B, hw, hu, huK.1⟩)
  haveI : IsEmpty {p : Φ.V × Bool // ∀ s, (Φ.Ψ⁻¹.comp Φ.del.ker.subtype) (Φ.loc2 p s) = 1} := ⟨fun p => by
    obtain ⟨s, hs⟩ := hΨ p.1.1
    have h1 : (Φ.Ψ (Φ.loc2 p.1 s).1)⁻¹ = 1 := p.2 s
    rw [Psi_local_pair_eq_local, inv_eq_one] at h1
    exact hs (by rw [h1, one_pow])⟩
  rw [Nat.card_of_isEmpty, Nat.cast_zero, add_zero, Cardinal.lift_id] at key
  exact key.trans hC
