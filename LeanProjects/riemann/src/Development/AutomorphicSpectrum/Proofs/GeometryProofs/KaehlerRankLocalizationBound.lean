import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseIsLocalizationAwayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationKaehlerPrimeIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisTowerStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionFieldStatement

namespace GlobalTheory.CompanionTheory.Ar.LocalStep

theorem exists_away_basis (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] [Algebra ℚ S] [Algebra.Smooth S T] [Algebra.Smooth ℚ S]
    (e r : ℕ) (hr : Module.finrank L (KaehlerDifferential K L) = r) (z : Fin e → S)
    (hli : LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)))
    (hsp : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤)
    (P : Ideal T) [P.IsPrime] :
    ∃ g : T, g ∉ P ∧ ∀ (T' : Type) [CommRing T'] [IsDomain T'] [Algebra T T'] [IsLocalization.Away g T']
      [Algebra ℚ T'] [Algebra T' L] [IsScalarTower T T' L],
      Algebra.Smooth ℚ T' ∧ ∃ z' : Fin (e + r) → T',
        (∀ i, z' (Fin.castAdd r i) = algebraMap T T' (algebraMap S T (z i))) ∧
        LinearIndependent T' (fun i => KaehlerDifferential.D ℚ T' (z' i)) ∧
        Submodule.span T' (Set.range fun i => KaehlerDifferential.D ℚ T' (z' i)) = ⊤ := by
  haveI : Algebra.IsSmoothAt S P := inferInstance
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth S P
  refine ⟨g, hg, ?_⟩
  intro T' _ _ _ _ _ _ _
  letI : Algebra S T' := ((algebraMap T T').comp (algebraMap S T)).toAlgebra
  haveI : IsScalarTower S T T' := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℚ S T' := .of_algebraMap_eq fun x =>
    DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ T') ((algebraMap S T').comp (algebraMap ℚ S))) x
  haveI : IsScalarTower S T' L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply S T L, IsScalarTower.algebraMap_apply S T T',
      ← IsScalarTower.algebraMap_apply T T' L]
  let f : Localization.Away g ≃ₐ[T] T' := IsLocalization.algEquiv (Submonoid.powers g) _ _
  haveI : Algebra.IsStandardSmooth S T' := Algebra.IsStandardSmooth.of_algEquiv (f.restrictScalars S)
  haveI : Algebra.Smooth S T' := inferInstance
  have hsm : Algebra.Smooth ℚ T' := Algebra.Smooth.comp ℚ S T'
  refine ⟨hsm, ?_⟩
  obtain ⟨m, w, hli', hsp'⟩ : ∃ (m : ℕ) (w : Fin m → T'),
      LinearIndependent T' (fun i => KaehlerDifferential.D S T' (w i)) ∧
      Submodule.span T' (Set.range fun i => KaehlerDifferential.D S T' (w i)) = ⊤ := by
    obtain ⟨-, I, b, hb⟩ := (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
      (R := S) (S := T')).1 inferInstance
    haveI : Finite I := Module.Finite.finite_basis b
    cases nonempty_fintype I
    let b' := b.reindex (Fintype.equivFin I)
    have hb' : ∀ i, ∃ x, KaehlerDifferential.D S T' x = b' i := fun i => by
      obtain ⟨x, hx⟩ := hb ⟨(Fintype.equivFin I).symm i, rfl⟩
      exact ⟨x, by simpa [b'] using hx⟩
    choose w hw using hb'
    refine ⟨_, w, ?_, ?_⟩
    · simpa only [hw] using b'.linearIndependent
    · simpa only [hw] using b'.span_eq
  haveI : IsDomain T := (IsFractionRing.injective T L).isDomain (algebraMap T L)
  haveI : IsFractionRing T' L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g) T' L
  have hm : Module.finrank L (KaehlerDifferential K L) = m := GlobalTheory.T.kaehler_finrank_fraction_field S T' K L m w hli' hsp'
  obtain rfl : r = m := hr.symm.trans hm
  obtain ⟨h1, h2⟩ := GlobalTheory.T.kaehler_basis_tower_alt ℚ S T' e r z w hli hsp hli' hsp'
  exact ⟨_, fun i => by rw [Fin.append_left]; rfl, h1, h2⟩

theorem local_step : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type) [Finite σ']
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (e r : ℕ) (bd : Ideal (MvPolynomial σ ℤ)), Module.finrank Ω (KaehlerDifferential Ω₀ Ω) = r →
    ∀ (h : Ω₀), h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert h⁻¹ (Set.range r₀)) →
    T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (Set.range r₁)) →
    ∀ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) → ψ.Smooth →
    IsFractionRing S Ω₀ → IsFractionRing T Ω → Algebra.Smooth ℚ S →
    ∀ (z : Fin e → S) (n : ℕ), n ≤ e → LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) →
    ∀ (P : Ideal (Algebra.adjoin ℚ (Set.range r₁))), P.IsPrime →
    ∀ h₁ : Algebra.adjoin ℚ (Set.range r₁), (h₁ : Ω) = algebraMap Ω₀ Ω h → h₁ ∉ P →
    ∃ t : Algebra.adjoin ℚ (Set.range r₁), t ∉ P ∧ ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range r₁)) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + r) → S') (n' : ℕ), n' ≤ e + r ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
            ∃ i : Fin (e + r), (i : ℕ) < n' ∧ z' i ∈ q) := by
  intro Ω₀ Ω _ _ _ _ _ σ σ' _ r₀ r₁ v hv e r bd hr h hh S T hS hT ψ hψ hsm hfS hfT hsS z n hn hli hsp hq
    P hP h₁ hh₁ hh₁P
  letI : Algebra S T := ψ.toAlgebra
  haveI : Algebra.Smooth S T := hsm
  haveI : IsScalarTower S T Ω := .of_algebraMap_eq fun s => (hψ s).symm
  haveI : IsScalarTower S Ω₀ Ω := .of_algebraMap_eq fun s => rfl
  have hr₁T : ∀ p, r₁ p ∈ T := fun p => by
    rw [hT]; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hle₁ : Algebra.adjoin ℚ (Set.range r₁) ≤ T := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr₁T p)
  letI : Algebra (Algebra.adjoin ℚ (Set.range r₁)) T := (Subalgebra.inclusion hle₁).toRingHom.toAlgebra
  have hne₁ : h₁ ≠ 0 := fun h0 => hh₁P (h0 ▸ P.zero_mem)
  haveI : IsLocalization.Away h₁ T :=
    GlobalTheory.T.adjoin_inverse_is_localization_away Ω _ T (Set.range r₁) rfl h₁ hne₁ (by rw [hT, hh₁]) hle₁
  have hdisj : Disjoint ((Submonoid.powers h₁ : Submonoid (Algebra.adjoin ℚ (Set.range r₁))) :
      Set (Algebra.adjoin ℚ (Set.range r₁))) (↑P : Set (Algebra.adjoin ℚ (Set.range r₁))) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  haveI hPT : (P.map (algebraMap _ T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers h₁) T P hP hdisj
  have hcomap : (P.map (algebraMap _ T)).comap (algebraMap _ T) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint (.powers h₁) T hP hdisj
  obtain ⟨g, hgP, Hg⟩ := exists_away_basis S T Ω₀ Ω e r hr z hli hsp (P.map (algebraMap _ T))
  obtain ⟨k, g₀, hk⟩ := IsLocalization.Away.surj h₁ g
  have hg₀ : g₀ ∉ P := by
    intro hmem
    have h1 := Ideal.mem_map_of_mem (algebraMap _ T) hmem
    rw [← hk] at h1
    rcases hPT.mem_or_mem h1 with h2 | h2
    · exact hgP h2
    · have h3 := hPT.mem_of_pow_mem _ h2
      have h4 : h₁ ∈ (P.map (algebraMap _ T)).comap (algebraMap _ T) := h3
      rw [hcomap] at h4
      exact hh₁P h4
  refine ⟨g₀ * h₁, hP.mul_notMem hg₀ hh₁P, ?_⟩
  intro S' hS'
  have hk' : (g : Ω) * (h₁ : Ω) ^ k = (g₀ : Ω) := congrArg T.val hk
  have hg0 : g ≠ 0 := fun h0 => hgP (h0 ▸ Ideal.zero_mem _)
  have hgΩ : (g : Ω) ≠ 0 := fun h0 => hg0 (Subtype.ext h0)
  have hHΩ : (h₁ : Ω) ≠ 0 := fun h0 => hne₁ (Subtype.ext h0)
  have hg₀Ω : (g₀ : Ω) ≠ 0 := by rw [← hk']; exact mul_ne_zero hgΩ (pow_ne_zero _ hHΩ)
  have ht : (((g₀ * h₁ : Algebra.adjoin ℚ (Set.range r₁)) : _) : Ω) = (g₀ : Ω) * h₁ := rfl
  have hr₁S' : ∀ p, r₁ p ∈ S' := fun p => by
    rw [hS']; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hle' : Algebra.adjoin ℚ (Set.range r₁) ≤ S' := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr₁S' p)
  have htS' : ((g₀ : Ω) * h₁)⁻¹ ∈ S' := by
    rw [hS', ht]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have hTS' : T ≤ S' := by
    rw [hT]
    refine Algebra.adjoin_le (Set.insert_subset ?_ (by rintro _ ⟨p, rfl⟩; exact hr₁S' p))
    have : (algebraMap Ω₀ Ω h)⁻¹ = ((g₀ : Ω) * h₁)⁻¹ * (g₀ : Ω) := by
      rw [← hh₁]; field_simp
    rw [SetLike.mem_coe, this]
    exact S'.mul_mem htS' (hle' g₀.2)
  have hEq : S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ (T : Set Ω)) := by
    refine le_antisymm ?_ (Algebra.adjoin_le (Set.insert_subset ?_ hTS'))
    · rw [hS']
      refine Algebra.adjoin_le (Set.insert_subset ?_ ?_)
      · have hinv : (h₁ : Ω)⁻¹ ∈ T := by
          rw [hT, hh₁]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
        have : (((g₀ * h₁ : Algebra.adjoin ℚ (Set.range r₁)) : _) : Ω)⁻¹ = (g : Ω)⁻¹ * ((h₁ : Ω)⁻¹) ^ (k + 1) := by
          rw [ht, ← hk', inv_pow, ← mul_inv, mul_assoc, ← pow_succ]
        rw [SetLike.mem_coe, this]
        exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _))
          (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hinv)) _)
      · rintro _ ⟨p, rfl⟩
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (hr₁T p))
    · have : (g : Ω)⁻¹ = ((g₀ : Ω) * h₁)⁻¹ * (h₁ : Ω) ^ (k + 1) := by
        rw [← hk', mul_assoc, ← pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hHΩ), mul_one]
      rw [SetLike.mem_coe, this]
      exact S'.mul_mem htS' (S'.pow_mem (hle' h₁.2) _)
  letI : Algebra T S' := (Subalgebra.inclusion hTS').toRingHom.toAlgebra
  haveI : IsLocalization.Away g S' := GlobalTheory.T.adjoin_inverse_is_localization_away Ω T S' (T : Set Ω) (Algebra.adjoin_eq T).symm g hg0 hEq hTS'
  haveI : IsScalarTower T S' Ω := .of_algebraMap_eq fun _ => rfl
  obtain ⟨hsm', z', hz', hli', hsp'⟩ := Hg S'
  refine ⟨hsm', z', n, by omega, hli', hsp', ?_⟩
  intro q hq'
  let θ : S →+* S' := (algebraMap T S').comp ψ
  have hθ : ∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s := fun s => hψ s
  have hr₀S : ∀ p, r₀ p ∈ S := fun p => by
    rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  rw [GlobalTheory.T.localization_kaehler_prime_ideal Ω₀ Ω σ σ' r₀ r₁ v hv bd S S' θ hθ hr₀S hr₁S' q, hq (q.comap θ) (hq'.comap θ)]
  constructor
  · rintro ⟨i, hi, hmem⟩
    refine ⟨Fin.castAdd r i, by simpa using hi, ?_⟩
    rw [hz']; exact hmem
  · rintro ⟨j, hj, hmem⟩
    have hje : (j : ℕ) < e := by omega
    refine ⟨⟨j, hje⟩, hj, ?_⟩
    have : j = Fin.castAdd r ⟨j, hje⟩ := Fin.ext rfl
    rw [this, hz'] at hmem
    exact hmem

end GlobalTheory.CompanionTheory.Ar.LocalStep
