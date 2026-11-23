import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.StrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC
open scoped Pointwise

private theorem exists_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A₀ A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h₀ : IsPlaceOver A₀ v) (hA : IsPlaceOver A v) :
    ∃ u : G F Ω, ∀ x ∈ Ine (F := F) A, u⁻¹ * x * u ∈ Dec (F := F) A₀ := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) h₀ hA
  have h : IsLift (RingEquiv.refl F) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ A ↔ x ∈ A₀ := fun x => by
    show g • x ∈ A ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  exact ⟨g, fun x hx => conjGal_mem_Dec h hm hx.1⟩

theorem UpperTheory.V.GC.b1p :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) → ∀ C₀ : ℕ, clRk l (K ⊓ (cycMod F Ω l 1).ker) ≤ C₀ → Module.rank k (H1C (k := k) (W := k) Φ.loc (chRep (Φ.Ψ⁻¹ ^ 2 * Φ.delK k)) fun _ => ⊥) ≤ C₀ := by
  intro F Ω _ _ _ _ _ l hl k _ _ Φ S K π ι A pl e c L h3 C₀ hC
  haveI := L.g.normal
  have hω : IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) :=
    (isOpen_discrete {(1 : (ZMod (l ^ 1))ˣ)}).preimage GlobalTheory.Published.PoitouTate.continuous_cycMod
  have hidx : ¬ l ∣ (K ⊓ (cycMod F Ω l 1).ker).relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]
    intro h
    have h1 : (K ⊓ (cycMod F Ω l 1).ker).index ∣ K.index * (cycMod F Ω l 1).ker.index := by
      rw [← Subgroup.relIndex_mul_index (inf_le_left : K ⊓ (cycMod F Ω l 1).ker ≤ K), mul_comm,
        Subgroup.inf_relIndex_left]
      exact Nat.mul_dvd_mul_left _ (Subgroup.relIndex_dvd_index_of_normal _ _)
    rcases (hl.out.dvd_mul).1 (h.trans h1) with h2 | h2
    · exact L.g.idx h2
    · rw [Subgroup.index_ker] at h2
      have h4 := h2.trans (Subgroup.card_subgroup_dvd_card _)
      haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h4
      have h5 := hl.out.two_le
      have := Nat.le_of_dvd (by omega) h4
      omega
  have key := strGen F Ω l k ⊤ (K ⊓ (cycMod F Ω l 1).ker) le_top (L.g.isOpen.inter hω) hidx Φ.Γ
    (π.comp (Subgroup.subtype ⊤)) (L.g.cont.comp continuous_subtype_val)
    (fun y => by
      obtain ⟨x, hx⟩ := L.g.onto y
      exact ⟨⟨x, trivial⟩, hx⟩)
    Φ.V Φ.Gv Φ.loc (Φ.Ψ⁻¹ ^ 2 * Φ.delK k)
    (fun u hu => by
      have h1 := L.K_del _ hu.1
      have h2 := L.K_Ψ _ hu.1
      simp [Frame.delK, h1, h2])
    (fun B u hu hK => by
      obtain ⟨p1, p2, -⟩ := Kum.placeDict F Ω
      by_cases hB : B = ⊤
      · left
        rw [hB, p1, Subgroup.mem_bot] at hu
        simp [hu]
      obtain ⟨w, hw⟩ := p2 B hB
      by_cases hS : w ∈ S
      · right
        obtain ⟨v, rfl⟩ := (L.loc.mem w).2 (L.only w hS)
        obtain ⟨g, hg⟩ := exists_conj (L.loc.isOver v) hw
        have h1 := hg _ hu
        rw [← L.loc.range v] at h1
        obtain ⟨s, hs⟩ := h1
        refine ⟨v, s, π g, ?_⟩
        rw [L.loc_eq, hs]
        simp [mul_assoc]
      · left
        have : u.1 ∈ π.ker := by
          rw [L.g.ker]
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          simp only [Set.mem_iUnion]
          exact ⟨w, hS, B, hw, hu, hK.1⟩
        exact this)
  haveI : IsEmpty {v // ∀ s, (Φ.Ψ⁻¹ ^ 2 * Φ.delK k) (Φ.loc v s) = 1} := ⟨fun ⟨v, hv⟩ => by
    obtain ⟨g, hg⟩ := h3 v
    have h1 : Φ.del (Φ.loc v g) = 1 := (Φ.loc0 v g).2
    have h2 := hv g
    apply hg
    simpa [Frame.delK, h1] using h2⟩
  rw [Nat.card_of_isEmpty, Nat.cast_zero, add_zero, Cardinal.lift_id] at key
  exact key.trans hC
