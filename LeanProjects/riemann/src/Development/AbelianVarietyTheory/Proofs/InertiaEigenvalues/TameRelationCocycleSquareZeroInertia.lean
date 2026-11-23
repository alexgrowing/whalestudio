import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.OneAddPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.TameRelation

open GlobalTheory.TameQuot

theorem eq_one_of_index_coprime {J N : Type} [Group J] [AddCommGroup N] {l k : ℕ}
    (hN : ∀ m : N, (l ^ k) • m = 0) (θ : J →* Multiplicative N) (h : θ.ker.index.Coprime l)
    (σ : J) : θ σ = 1 := by
  have h1 : θ σ ^ θ.ker.index = 1 := by
    rw [← map_pow]; exact θ.ker.pow_index_mem σ
  have h2 : θ σ ^ l ^ k = 1 := hN (θ σ).toAdd
  exact (pow_eq_one_iff_of_coprime (h.pow_right k)).1 ⟨h1, h2⟩

theorem pow_formula {Γ R W : Type} [Group Γ] [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : Representation R Γ W) {b : R} (hb : b * b = 0) {γ : Γ} (hγ : ∀ m, ρ γ m = m + b • m)
    (z : Γ → W) (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) (k : ℕ) :
    (∀ m, ρ (γ ^ k) m = m + k • b • m) ∧ z (γ ^ k) = k • z γ + k.choose 2 • b • z γ := by
  have hbb : ∀ m : W, b • b • m = 0 := fun m => by rw [← mul_smul, hb, zero_smul]
  induction k with
  | zero => simpa using hz 1 1
  | succ k ih =>
    refine ⟨fun m => ?_, ?_⟩
    · rw [pow_succ', map_mul, Module.End.mul_apply, ih.1, hγ, smul_add, smul_comm b k, hbb,
        smul_zero, add_zero, succ_nsmul]
      abel
    · rw [pow_succ', hz, ih.2, hγ, smul_add, smul_comm b k, smul_comm b (k.choose 2), hbb,
        smul_zero, add_zero, succ_nsmul, Nat.choose_succ_succ' k 1, Nat.choose_one_right, add_smul]
      abel

theorem tame_relation : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (k : ℕ), normV v % (2 * l ^ k) = 1 → ∀ (M : ℕ) (d : G F Ω →* Multiplicative (ZMod (l ^ M))) (γ σ : G F Ω), 1 ≤ M → IsOpen (d.ker : Set (G F Ω)) → γ ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) σ → ∀ (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R (G F Ω) W) (a b : R), (∀ m : W, (l ^ k) • m = 0) → b * b = 0 → (∀ τ ∈ Ine (F := F) A, ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m) → (∀ m, ρ σ m = m + a • m) → ∀ z : Z1 ρ, a • z.1 γ = b • z.1 σ ∧ (b = 0 → z.1 γ = 0 → ∀ τ ∈ Ine (F := F) A, z.1 τ = 0) := by
  intro hT F Ω _ _ _ _ _ l hlp A v hA hl k hq M d γ σ hM hd hγ hdγ hσ R _ W _ _ _ _ ρ a b h4 hb hI hρ z
  obtain ⟨-, -, hco, ⟨t, tc, ts, hk⟩, -, -⟩ := hT F Ω l A v hA hl
  haveI : Fact (1 < l ^ M) := ⟨one_lt_pow₀ hlp.out.one_lt (by omega)⟩
  have hdJ : ∀ τ ∈ ineKer F A l, d τ = 1 := fun τ hτ =>
    eq_one_of_index_coprime (l := l) (k := M) (fun m => by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
      (d.comp (ineKer F A l).subtype) (hco _ inferInstance (hd.preimage continuous_subtype_val)) ⟨τ, hτ⟩
  have hρJ : ∀ τ ∈ ineKer F A l, ∀ m, ρ τ m = m := fun τ hτ m => by
    rw [hI τ (ineKer_le_Ine A l hτ), hdJ τ hτ]; simp
  have hzJ : ∀ τ ∈ ineKer F A l, z.1 τ = 0 := fun τ hτ => by
    let θ : ineKer F A l →* Multiplicative W :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
        have := z.2.2 (g : G F Ω) h
        rw [hρJ _ g.2] at this
        exact congrArg Multiplicative.ofAdd this
    have ho : IsOpen (θ.ker : Set (ineKer F A l)) :=
      (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
    exact eq_one_of_index_coprime (l := l) (k := k) h4 θ
      (hco _ inferInstance ho) ⟨τ, hτ⟩
  refine ⟨?_, fun hb0 h0 τ hτ => ?_⟩
  · have hj := tame_rel hA hl hσ hγ
    have hγ' : ∀ m, ρ γ m = m + b • m := fun m => by
      rw [hI γ hγ, hdγ, toAdd_ofAdd, ZMod.val_one, Nat.cast_one, one_mul]
    obtain ⟨p1, p2⟩ := pow_formula ρ hb hγ' z.1 z.2.2 (normV v)
    have hqs : ∀ m : W, normV v • m = m := KStar.Tree.nsmul_eq_self_of_mod hq h4
    obtain ⟨c, hc⟩ := KStar.Tree.dvd_choose_two hq
    rw [hc, mul_comm (l ^ k), mul_smul, h4, smul_zero, add_zero, hqs] at p2
    have e : σ * γ = γ ^ normV v * (((γ ^ normV v)⁻¹ * (σ * γ * σ⁻¹)) * σ) := by group
    have h1 := z.2.2 σ γ
    rw [e, z.2.2, z.2.2 _ σ, hzJ _ hj, hρJ _ hj, zero_add, p1, p2, hqs, hρ, ← add_assoc,
      ← add_assoc, add_comm (z.1 γ)] at h1
    exact (add_left_cancel h1).symm
  · have hg : IsProGen F A l γ := by
      refine (isProGen_iff_isUnit F Ω l A t tc ts hk ⟨γ, hγ⟩).2 ?_
      by_contra hu
      obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.mem_nonunits.1 hu)
      obtain ⟨g, hg⟩ := ts (Multiplicative.ofAdd y)
      have h1 : t ((g ^ l)⁻¹ * ⟨γ, hγ⟩) = 1 := by
        rw [map_mul, map_inv, map_pow, inv_mul_eq_one, hg]
        refine Multiplicative.toAdd.injective ?_
        rw [hy, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul]
      have h2 : d (((g : G F Ω) ^ l)⁻¹ * γ) = 1 := hdJ _ ((hk _).1 h1)
      rw [map_mul, map_inv, map_pow, inv_mul_eq_one, hdγ] at h2
      have h3 := congrArg (fun x => ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) (ZMod l)
        (Multiplicative.toAdd x)) h2
      simp only [toAdd_pow, toAdd_ofAdd, map_one, nsmul_eq_mul, map_mul, map_natCast,
        ZMod.natCast_self, zero_mul] at h3
      exact zero_ne_one h3
    let θ : Ine (F := F) A →* Multiplicative W :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
        have := z.2.2 (g : G F Ω) h
        rw [hI _ g.2, hb0, mul_zero, zero_smul, add_zero] at this
        exact congrArg Multiplicative.ofAdd this
    have ho : IsOpen (θ.ker : Set (Ine (F := F) A)) :=
      (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
    have hc : IsClosed ((θ.ker.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (θ.ker.isClosed_of_isOpen ho)
    have h1 : Subgroup.zpowers γ ⊔ ineKer F A l ≤ θ.ker.map (Ine (F := F) A).subtype :=
      sup_le (Subgroup.zpowers_le.2 ⟨⟨γ, hγ⟩, h0, rfl⟩) fun τ hτ =>
        ⟨⟨τ, ineKer_le_Ine A l hτ⟩, hzJ τ hτ, rfl⟩
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hg.2 hτ)
    exact hτ'

end GlobalTheory.TameRelation
