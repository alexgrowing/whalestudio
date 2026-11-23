import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CrysSlopes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.IntCrit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem norm_normV {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (l : ℕ) [Fact l.Prime]
    (hw : (l : 𝓞 F) ∉ w.asIdeal) : ‖((normV w : ℕ) : Qbar l)‖ = 1 := by
  classical
  have hl : l.Prime := Fact.out
  have hN : ¬ l ∣ normV w := by
    intro hdvd
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 F ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
    obtain ⟨p, hchar⟩ := CharP.exists (𝓞 F ⧸ w.asIdeal)
    have hp : p.Prime := CharP.char_is_prime (𝓞 F ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 F ⧸ w.asIdeal) p
    have hcard : normV w = p ^ (n : ℕ) := by rw [normV, Nat.card_eq_fintype_card, hn]
    rw [hcard] at hdvd
    have hlp : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow hdvd)
    apply hw
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hlp]
    exact CharP.cast_eq_zero _ p
  have h1 : ‖((normV w : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hN
  rw [← h1, ← map_natCast (algebraMap ℚ_[l] (Qbar l))]
  exact norm_algebraMap' _ _

private theorem frob_unit {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (w : HeightOneSpectrum (𝓞 F))
    (B : Multiset ℂ) (h : FrobEig ι r w B) : ∀ b ∈ B, ‖ι.symm b‖ = 1 := by
  intro b hb
  have hA := isPlaceOver_placeOf Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := (h _ hA).2 σ hσ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  refine Lib.norm_root_eq_one r hr σ⁻¹ _ ?_
  apply ι.injective
  have h2 : ((r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).eval b = 0 := by
    rw [e, Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map]
    exact Multiset.mem_map.2 ⟨b, hb, by simp⟩
  have h3 := Polynomial.eval₂_at_apply (p := (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) ι.toRingHom (ι.symm b)
  rw [map_zero]
  rw [Polynomial.eval_map] at h2
  refine h3.symm.trans ?_
  rwa [show ι.toRingHom (ι.symm b) = b from ι.apply_symm_apply b]

theorem slopesOf (hP : Hypotheses₂) {F : Type} [Field F] [NumberField F] {n : ℕ} (m : Fin n → ℤ) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 F)) (hw : (p : 𝓞 F) ∈ w.asIdeal) (hd : ¬ (p : ℤ) ∣ discr F)
    (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (H : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r : G F (AlgebraicClosure F) →* GL (Fin n) (Qbar l), Continuous r ∧
      ((l : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring (AlgebraicClosure F)) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → IsWDOf ι r (rc (algNorm σ))) ∧
      ∀ (A : ValuationSubring (AlgebraicClosure F)) (h : IsPlaceOver A w)
        (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l F (AlgebraicClosure F) (Dec (F := F) A) O) (hj : Induces Bw),
        (GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype)) ∧
        (∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ (Finset.univ.val.map fun i => -m i)) ∧
        (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ → ∀ rc, IsRec h rc →
          wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype) = rc (algNorm σ))) :
    SlopesIn (normV w) m (algSat n (normV w) B) := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  obtain ⟨x, hx0, hx, -⟩ := hB.exists_vec
  have hfix : ∀ U, U ≤ GlobalTheory.LFun.KGL w n → GlobalTheory.PRep.fixed σ.ρ U ≠ ⊥ := fun U hU =>
    (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k (hU hk), hx0⟩
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := hfix _ hK.le
  have hiw := hfix _ ((GlobalTheory.SmGL.iwahori_le_KO _ _).trans hK.le)
  have key : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∀ b ∈ algSat n (normV w) B,
      (∀ a : ℤ, (∀ i, -a ≤ m i) → ‖ι.symm ((normV w : ℂ) ^ a * b⁻¹)‖ ≤ 1) ∧
        ∀ a : ℤ, (∀ i, m i ≤ a) → ‖ι.symm ((normV w : ℂ) ^ a * b)‖ ≤ 1 := by
    intro l _ ι
    obtain ⟨r, hr, h1, h2⟩ := H l ι
    by_cases hl : (l : 𝓞 F) ∈ w.asIdeal
    · obtain rfl : l = p := by
        by_contra hne
        have hc : IsCoprime (l : 𝓞 F) (p : 𝓞 F) :=
          Nat.Coprime.cast ((Nat.coprime_primes Fact.out hp).2 hne)
        obtain ⟨a, b, e⟩ := hc
        exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
          (e ▸ add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hw)))
      have hA := isPlaceOver_placeOf (AlgebraicClosure F) w
      obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l F (AlgebraicClosure F) w _ hl hA
      obtain ⟨Bw, hBj, -⟩ := hLL L0 le_rfl
      have hI : Induces Bw := fun x => by rw [hBj]; exact hj x
      obtain ⟨c1, c2, c3⟩ := h2 _ hA _ Bw hI
      have L := hP.litN.loc
      obtain ⟨rc, hrc⟩ := L.llc F _ _ w hA
      have hrc' := GlobalTheory.LocLanglands.isRec_of_isRecLit L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F _ _ w hA rc hrc
      exact crysSlopes hP F _ l hd ι n m r hr w _ hA _ Bw hI (c1 hsph) c2 σ B hB rc hrc' (c3 hiw rc hrc')
    · intro b hb
      have hu := frob_unit ι r hr w _ (satFrob hP F _ l ι n r hr w hl σ B hB (h1 hl)) b hb
      have hq := norm_normV w l hl
      constructor <;> intro a _ <;> simp [hu, hq]
  intro b hb
  exact ⟨fun a ha => Lib.isIntegral_of_norm_le _ fun l _ ι => (key l ι b hb).1 a ha, fun a ha => Lib.isIntegral_of_norm_le _ fun l _ ι => (key l ι b hb).2 a ha⟩

end UpperTheory.V.Af
