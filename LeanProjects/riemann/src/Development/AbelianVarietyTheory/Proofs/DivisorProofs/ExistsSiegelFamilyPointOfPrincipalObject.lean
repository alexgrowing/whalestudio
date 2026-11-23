import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyCyclotomicAwayOddLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusPointMemRangeSiegelModuliOpenImmersi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem dense_asIdeal_eq_bot_spMap (n : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) : Dense {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
  let p₀ : Sp V₁ := ⟨⊥, Ideal.isPrime_bot⟩
  let K := FractionRing V₁
  have hinj : Function.Injective (algebraMap V₁ K) := IsFractionRing.injective V₁ K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hmem : p₀ ∈ {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
    let q : Sp K := ⟨⊥, Ideal.isPrime_bot⟩
    have h := GlobalTheory.AbChart.asIdeal_eq_bot_of_charZero n K (spMap ((algebraMap V₁ K).comp b₁)) q
    show Ideal.comap b₁ (⊥ : Ideal V₁) = ⊥
    have hc : Ideal.comap (algebraMap V₁ K) (⊥ : Ideal K) = ⊥ :=
      (RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => hinj (by rw [ha, map_zero])
    rw [← hc, Ideal.comap_comap]
    exact h
  have hcl : closure ({p₀} : Set (Sp V₁)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    exact (PrimeSpectrum.le_iff_mem_closure (R := V₁) p₀ x).1 bot_le
  refine Dense.mono (Set.singleton_subset_iff.2 hmem) ?_
  exact dense_iff_closure_eq.2 hcl

theorem exists_sFam_point : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) (s : SiegPre h n (zetaAway n) (spMap b₁)), s.Principal →
    ∃ (F : SFam h n (zetaAway n)) (x : Sp V₁ ⟶ F.X), x ≫ F.s = spMap b₁ ∧ SiegPB s F.univ x := by
  intro n hn hodd h V₁ _ _ _ b₁ s hs
  obtain ⟨F⟩ : Nonempty (SFam h n (zetaAway n)) := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exact ⟨zeroFam n hn⟩
    · exact GlobalTheory.SiegelTor.exists_sFam_cycAway h n hh hn hodd
  obtain ⟨x, hx, hpb⟩ := F.rep (Sp V₁) (spMap b₁) s inferInstance (dense_asIdeal_eq_bot_spMap n V₁ b₁) hs
  exact ⟨F, x, hx, hpb⟩

end GlobalTheory.LowChart
