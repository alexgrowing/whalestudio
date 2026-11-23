import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Generate

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

open KStar.TotallyRealRoots in
private theorem eg_pow_mem {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 1 ≤ a) {u : ℤ_[l]ˣ} (hu : u ∈ princ l a) :
    u ^ l ∈ princ l (a + 1) := by
  rw [mem_princ] at hu ⊢
  obtain ⟨c, hc⟩ := hu
  obtain ⟨f, hf⟩ := sq_dvd_add_pow_sub_sub ((l : ℤ_[l]) ^ a * c) 1 l
  have hw : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ a * c := by rw [← hc]; ring
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  refine ⟨c + (l : ℤ_[l]) ^ m * c ^ 2 * f, ?_⟩
  rw [Units.val_pow_eq_pow_val, hw]
  simp only [one_pow, one_mul] at hf
  linear_combination hf

open KStar.TotallyRealRoots in
private theorem eg_exists_not_mem {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ≠ 1) :
    ∃ a, u ∉ princ l a := by
  by_contra h
  push Not at h
  apply hu
  have hb : IsClosed ((⊥ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  have := mem_of_isClosed hb (x := u) fun b => ⟨1, Subgroup.one_mem _, by
    rw [map_one]; exact (MonoidHom.mem_ker.1 (h b)).symm⟩
  exact Subgroup.mem_bot.1 this

theorem UpperTheory.V.Kum.existsGen :
    ∀ (l : ℕ) [Fact l.Prime] (V : Subgroup ℤ_[l]ˣ), IsClosed (V : Set ℤ_[l]ˣ) → (l ≠ 2 ∨ V ≤ KStar.TotallyRealRoots.princ l 2) → ∃ γ ∈ V, V ≤ (Subgroup.zpowers γ).topologicalClosure := by
  classical
  intro l _ V _ hl
  have hp : l.Prime := Fact.out
  obtain ⟨⟨_, g, hg, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := V.map (KStar.TotallyRealRoots.red l))
  have key : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g →
      V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ (Subgroup.zpowers γ).topologicalClosure →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨_, Subgroup.mem_map_of_mem _ hv⟩)
    have hk' : KStar.TotallyRealRoots.red l g ^ k = KStar.TotallyRealRoots.red l v := congrArg Subtype.val hk
    have h1 : v * (γ ^ k)⁻¹ ∈ V ⊓ KStar.TotallyRealRoots.princ l 1 := by
      refine Subgroup.mem_inf.2 ⟨V.mul_mem hv (V.inv_mem (V.zpow_mem hγ k)), ?_⟩
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, e, hk',
        mul_inv_cancel]
    have h2 : γ ^ k ∈ (Subgroup.zpowers γ).topologicalClosure :=
      Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k)
    simpa using Subgroup.mul_mem _ (h h1) h2
  by_cases hW : V ⊓ KStar.TotallyRealRoots.princ l 1 = ⊥
  · exact ⟨g, hg, key g hg rfl (by rw [hW]; exact bot_le)⟩
  have hex : ∃ b, ¬ V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l b := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
    obtain ⟨b, hb⟩ := eg_exists_not_mem (u := w) (fun h => hw1 (Subtype.ext h))
    exact ⟨b, fun h => hb (h hw)⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l m :=
    fun m hm => not_not.1 (Nat.find_min hex hm)
  have h1 : 1 < Nat.find hex := by
    by_contra h
    exact hspec (inf_le_right.trans (KStar.TotallyRealRoots.princ_anti (by omega)))
  have h2 : l = 2 → 2 < Nat.find hex := by
    intro h2
    by_contra h
    exact hspec (inf_le_left.trans ((hl.resolve_left (not_not.2 h2)).trans (KStar.TotallyRealRoots.princ_anti (by omega))))
  obtain ⟨a, ha⟩ : ∃ a, Nat.find hex = a + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ha] at hspec hmin h1 h2
  have hle := hmin a (Nat.lt_succ_self a)
  obtain ⟨u, hu, hua⟩ := SetLike.not_le_iff_exists.1 hspec
  have fin : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g → γ ^ (l - 1) ∉ KStar.TotallyRealRoots.princ l (a + 1) →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h
    refine key γ hγ e (hle.trans ?_)
    have hm : γ ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l a := by
      refine hle (Subgroup.mem_inf.2 ⟨V.pow_mem hγ _, ?_⟩)
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_pow, ZMod.units_pow_card_sub_one_eq_one]
    refine KStar.TotallyRealRoots.princ_le_of_isClosed (u := γ ^ (l - 1)) (by omega) (fun h => by have := h2 h; omega)
      (Subgroup.isClosed_topologicalClosure _)
      (Subgroup.le_topologicalClosure _ (Subgroup.npow_mem_zpowers γ _)) ?_
    exact emultiplicity_eq_coe.2 ⟨KStar.TotallyRealRoots.mem_princ.1 hm, fun h' => h (KStar.TotallyRealRoots.mem_princ.2 h')⟩
  by_cases hga : g ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l (a + 1)
  · refine ⟨g * u, V.mul_mem hg hu.1, fin _ (V.mul_mem hg hu.1) ?_ ?_⟩
    · have : u ∈ (KStar.TotallyRealRoots.red l).ker := by
        rw [← KStar.TotallyRealRoots.princ_one_eq_ker]
        exact (Subgroup.mem_inf.1 hu).2
      rw [map_mul, MonoidHom.mem_ker.1 this, mul_one]
    · intro h
      rw [mul_pow] at h
      have h3 := (mul_mem_cancel_left hga).1 h
      have h4 := eg_pow_mem (by omega) (hle hu)
      have h5 : u ^ l = u ^ (l - 1) * u := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      rw [h5] at h4
      exact hua ((mul_mem_cancel_left h3).1 h4)
  · exact ⟨g, hg, fin g hg rfl hga⟩
