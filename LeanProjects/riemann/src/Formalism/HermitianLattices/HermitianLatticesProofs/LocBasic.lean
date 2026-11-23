import Mathlib
import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace Formalism.HermitianLatticesTheory

section LocS

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem locBasic_mem_locS {S : Submonoid R} {L : Submodule R W} {x : W} :
    x ∈ locS S L ↔ ∃ s ∈ S, s • x ∈ L := Iff.rfl

theorem locBasic_le_locS (S : Submonoid R) (L : Submodule R W) : L ≤ locS S L := by
  intro x hx
  exact locBasic_mem_locS.mpr ⟨1, S.one_mem, by rwa [one_smul]⟩

theorem locBasic_locS_mono (S : Submonoid R) {L M : Submodule R W} (h : L ≤ M) :
    locS S L ≤ locS S M := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
  exact locBasic_mem_locS.mpr ⟨s, hs, h hsx⟩

theorem locBasic_locS_le_of_le {S T : Submonoid R} (hST : S ≤ T) (L : Submodule R W) :
    locS S L ≤ locS T L := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
  exact locBasic_mem_locS.mpr ⟨s, hST hs, hsx⟩

theorem locBasic_locS_idem (S : Submonoid R) (L : Submodule R W) :
    locS S (locS S L) = locS S L := by
  refine le_antisymm ?_ (locBasic_le_locS S _)
  intro x hx
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
  obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.mp hsx
  exact locBasic_mem_locS.mpr ⟨t * s, S.mul_mem ht hs, by rwa [mul_smul]⟩

theorem locBasic_locS_inf (S : Submonoid R) (L M : Submodule R W) :
    locS S (L ⊓ M) = locS S L ⊓ locS S M := by
  apply le_antisymm
  · exact le_inf (locBasic_locS_mono S inf_le_left) (locBasic_locS_mono S inf_le_right)
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp (Submodule.mem_inf.mp hx).1
    obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.mp (Submodule.mem_inf.mp hx).2
    refine locBasic_mem_locS.mpr ⟨s * t, S.mul_mem hs ht, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_comm, mul_smul]
      exact L.smul_mem t hsx
    · rw [mul_smul]
      exact M.smul_mem s htx

theorem locBasic_lg (S : Ideal R → Submonoid R)
    (hS : ∀ p : Ideal R, p.IsMaximal → ∀ s ∈ S p, s ∉ p) (L : Submodule R W) (x : W)
    (hx : ∀ p : Ideal R, p.IsMaximal → x ∈ locS (S p) L) : x ∈ L := by
  let I : Ideal R := L.comap (LinearMap.toSpanSingleton R W x)
  have hI : ∀ r, r ∈ I ↔ r • x ∈ L := fun r => by simp [I]
  by_contra hxL
  have hne : I ≠ ⊤ := by
    intro h
    apply hxL
    have h1 : (1 : R) ∈ I := by
      rw [h]
      exact Submodule.mem_top
    simpa using (hI 1).mp h1
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp (hx p hp)
  exact hS p hp s hs (hIp ((hI s).mpr hsx))

end LocS

section LocK

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem locBasic_locS_sup (S : Submonoid R) (hS : ∀ s ∈ S, algebraMap R K s ≠ 0)
    (L M : Submodule R V) : locS S (L ⊔ M) = locS S L ⊔ locS S M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
    obtain ⟨l, hl, m, hm, hlm⟩ := Submodule.mem_sup.mp hsx
    have ha := hS s hs
    have key : ∀ v : V, s • ((algebraMap R K s)⁻¹ • v) = v := fun v => by
      rw [← algebraMap_smul K s ((algebraMap R K s)⁻¹ • v), smul_smul, mul_inv_cancel₀ ha,
        one_smul]
    have hx' : x = (algebraMap R K s)⁻¹ • l + (algebraMap R K s)⁻¹ • m := by
      rw [← smul_add, hlm, ← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hx']
    refine Submodule.add_mem_sup ?_ ?_
    · exact locBasic_mem_locS.mpr ⟨s, hs, by rw [key]; exact hl⟩
    · exact locBasic_mem_locS.mpr ⟨s, hs, by rw [key]; exact hm⟩
  · exact sup_le (locBasic_locS_mono S le_sup_left) (locBasic_locS_mono S le_sup_right)

end LocK

section Herm

variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]

theorem locBasic_hcompl_le (p : Ideal R) [p.IsPrime] :
    hcompl (K := K) p ≤ p.primeCompl := by
  unfold hcompl
  rw [Submonoid.closure_le]
  intro s hs
  exact hs.1

theorem locBasic_hcompl_not_mem (p : Ideal R) [p.IsPrime] (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := Ideal.mem_primeCompl_iff.mp (locBasic_hcompl_le (K := K) p hs)

theorem locBasic_mem_hcompl (p : Ideal R) (u : R) (hu : u ∉ p) (hu' : u ∉ conjIdeal (K := K) p) :
    u ∈ hcompl (K := K) p := by
  unfold hcompl
  apply Submonoid.subset_closure
  refine ⟨hu, fun t ht htp => hu' ?_⟩
  unfold conjIdeal
  apply Ideal.subset_span
  exact ⟨t, htp, by rw [ht, star_star]⟩

def locBasic_sigma (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) : R →+* R where
  toFun r := (hstar r).choose
  map_one' := hinj (by rw [(hstar 1).choose_spec, map_one, star_one])
  map_mul' a b := hinj (by
    rw [(hstar (a * b)).choose_spec, map_mul, map_mul, (hstar a).choose_spec,
      (hstar b).choose_spec, star_mul'])
  map_zero' := hinj (by rw [(hstar 0).choose_spec, map_zero, star_zero])
  map_add' a b := hinj (by
    rw [(hstar (a + b)).choose_spec, map_add, map_add, (hstar a).choose_spec,
      (hstar b).choose_spec, star_add])

theorem locBasic_sigma_spec (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (r : R) :
    algebraMap R K (locBasic_sigma hinj hstar r) = star (algebraMap R K r) := (hstar r).choose_spec

theorem locBasic_conj_eq (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R) :
    conjIdeal (K := K) p = p.comap (locBasic_sigma hinj hstar) := by
  have hσ := locBasic_sigma_spec hinj hstar
  have hσσ : ∀ r, locBasic_sigma hinj hstar (locBasic_sigma hinj hstar r) = r := fun r =>
    hinj (by rw [hσ, hσ, star_star])
  apply le_antisymm
  · unfold conjIdeal
    rw [Ideal.span_le]
    rintro r ⟨s, hs, hrs⟩
    have e : r = locBasic_sigma hinj hstar s := hinj (by rw [hrs, hσ])
    rw [SetLike.mem_coe, Ideal.mem_comap, e, hσσ]
    exact hs
  · intro r hr
    unfold conjIdeal
    apply Ideal.subset_span
    exact ⟨locBasic_sigma hinj hstar r, Ideal.mem_comap.mp hr, by rw [hσ, star_star]⟩

theorem locBasic_hcompl_le_conj (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R)
    [(conjIdeal (K := K) p).IsPrime] :
    hcompl (K := K) p ≤ (conjIdeal (K := K) p).primeCompl := by
  unfold hcompl
  rw [Submonoid.closure_le]
  rintro s ⟨_, hs2⟩
  rw [SetLike.mem_coe, Ideal.mem_primeCompl_iff, locBasic_conj_eq hinj hstar p, Ideal.mem_comap]
  exact hs2 _ (locBasic_sigma_spec hinj hstar s)

end Herm

theorem locBasic : LocBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ hinj
  unfold loc localization₂
  have hne : ∀ (p : Ideal R), p.IsPrime → ∀ s ∈ hcompl (K := K) p, algebraMap R K s ≠ 0 := by
    intro p hp s hs h0
    haveI := hp
    apply locBasic_hcompl_not_mem (K := K) p s hs
    rw [← map_zero (algebraMap R K)] at h0
    rw [hinj h0]
    exact p.zero_mem
  have hnm : ∀ (p : Ideal R), p.IsMaximal → ∀ s ∈ hcompl (K := K) p, s ∉ p := by
    intro p hp s hs
    haveI := hp.isPrime
    exact locBasic_hcompl_not_mem (K := K) p s hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp L M
    haveI := hp
    exact ⟨locBasic_le_locS _ L, fun h => locBasic_locS_mono _ h, locBasic_locS_idem _ L,
      locBasic_locS_inf _ L M, locBasic_locS_sup (K := K) _ (hne p hp) L M⟩
  · intro L
    apply le_antisymm
    · intro x hx
      simp only [Submodule.mem_iInf] at hx
      exact locBasic_lg (fun p => hcompl (K := K) p) hnm L x hx
    · exact le_iInf₂ fun p _ => locBasic_le_locS _ L
  · intro L M h x hx
    exact locBasic_lg (fun p => hcompl (K := K) p) hnm M x
      (fun p hp => h p hp (locBasic_le_locS _ L hx))
  · intro p _ L
    exact locBasic_locS_le_of_le (locBasic_hcompl_le (K := K) p) L
  · intro hstar p _
    have hc := locBasic_conj_eq hinj hstar p
    haveI hpc : (conjIdeal (K := K) p).IsPrime := by
      rw [hc]
      exact Ideal.comap_isPrime _ _
    refine ⟨hpc, fun L => ?_⟩
    apply le_antisymm
    · exact le_inf (locBasic_locS_le_of_le (locBasic_hcompl_le (K := K) p) L)
        (locBasic_locS_le_of_le (locBasic_hcompl_le_conj hinj hstar p) L)
    · intro x hx
      obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp (Submodule.mem_inf.mp hx).1
      obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.mp (Submodule.mem_inf.mp hx).2
      have hs' : s ∉ p := Ideal.mem_primeCompl_iff.mp hs
      have ht' : locBasic_sigma hinj hstar t ∉ p := by
        have h1 := Ideal.mem_primeCompl_iff.mp ht
        rwa [hc, Ideal.mem_comap] at h1
      have key : ∀ u, u • x ∈ L → u ∉ p → locBasic_sigma hinj hstar u ∉ p →
          x ∈ locS (hcompl (K := K) p) L := by
        intro u hux hu1 hu2
        refine locBasic_mem_locS.mpr ⟨u, locBasic_mem_hcompl (K := K) p u hu1 ?_, hux⟩
        rw [hc, Ideal.mem_comap]
        exact hu2
      by_cases h1 : locBasic_sigma hinj hstar s ∈ p
      · by_cases h2 : t ∈ p
        · refine key (s + t) (by rw [add_smul]; exact L.add_mem hsx htx) ?_ ?_
          · intro h
            exact hs' (by simpa using p.sub_mem h h2)
          · rw [map_add]
            intro h
            exact ht' (by simpa using p.sub_mem h h1)
        · exact key t htx h2 ht'
      · exact key s hsx hs' h1

end Formalism.HermitianLatticesTheory
