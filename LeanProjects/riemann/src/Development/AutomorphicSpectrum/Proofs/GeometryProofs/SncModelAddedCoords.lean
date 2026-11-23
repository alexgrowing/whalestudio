import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGeneratedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankLocalizationBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SncPull
open GlobalTheory.CompanionTheory.Ar.SncRefine

theorem adjoin_insert_eq {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) :
    Algebra.adjoin ℚ (insert t ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω) : Set Ω)) =
      Algebra.adjoin ℚ (insert t (Set.range (bratio y c))) := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro b (rfl | hb)
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · have h : Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) ≤
          (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).restrictScalars ℤ := Algebra.adjoin_le (by
        rintro _ ⟨d, rfl⟩
        exact seg_ratio_mem y c (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).toSubring
          (fun p => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)) d)
      exact h hb
  · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
    rintro _ ⟨p, rfl⟩
    obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩

theorem map_mem_adjoin {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    {W : Set Ω₀} {W' : Set Ω} (hW : ∀ w ∈ W, algebraMap Ω₀ Ω w ∈ W') {b : Ω₀} (hb : b ∈ Algebra.adjoin ℚ W) :
    algebraMap Ω₀ Ω b ∈ Algebra.adjoin ℚ W' := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hW x hx)
  | algebraMap r =>
    have : algebraMap Ω₀ Ω (algebraMap ℚ Ω₀ r) = algebraMap ℚ Ω r := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_cover {R : Type} [CommRing R] (G : R → Prop) (h : ∀ P : Ideal R, P.IsPrime → ∃ t, t ∉ P ∧ G t) :
    ∃ (m : ℕ) (f a : Fin m → R), ∑ l, a l * f l = 1 ∧ ∀ l, G (f l) := by
  classical
  have hs : Ideal.span {t | G t} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht, hG⟩ := h M hM.isPrime
    exact ht (hle (Ideal.subset_span hG))
  have h1 : (1 : R) ∈ Ideal.span {t | G t} := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : R), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x • (x : R)

theorem isSncModel_pull : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (e : ℕ) (bd : Ideal (MRing J)) (I : Type) [Fintype I] (u : I → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) → Smooth f →
    AlgebraicIndependent Ω₀ u → IntermediateField.adjoin Ω₀ (Set.range u) = ⊤ →
    Cmp.IsSncModel y e bd →
    Cmp.IsSncModel (addY y x') (e + Fintype.card I) (bd.map (MvPolynomial.rename (addV J N))) := by
  classical
  intro X X' Ω₀ Ω _ _ _ _ _ ξ ξ' f K _ J _ y N x' e bd I _ u hq hq' tie tie' hd hsm hu hadj hsnc c₁ hc₁
  let c : (k : K) → J k := fun k => c₁ (Sum.inr k)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h =>
    hc₁ (Sum.inr k) (show algebraMap Ω₀ Ω (y ⟨k, c k⟩) = 0 by rw [h, map_zero])
  have hv : ∀ p, algebraMap Ω₀ Ω (bratio y c p) = bratio (addY y x') c₁ (addV J N p) := fun p => map_div₀ _ _ _
  have hxc : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hxc₁ : seg (addY y x') c₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc₁ k
  have hblk : ∀ p, bratio (addY y x') c₁ p ∈
      Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁) := fun p => by
    obtain ⟨d, hd⟩ := exists_seg_ratio (addY y x') c₁ hc₁ p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩
  obtain ⟨φ, hφ, hφs⟩ := GlobalTheory.T.dominant_smooth_map_coords X X' Ω₀ Ω ξ ξ' f (algebraMap Ω₀ Ω) _ _ (seg y) (seg (addY y x'))
    hq hq' tie tie' hd hsm c c₁ hxc hxc₁ (fun d => by
      have e1 : seg y d / seg y c = ∏ k, bratio y c ⟨k, d k⟩ := (Finset.prod_div_distrib _ _).symm
      rw [e1, map_prod]
      refine prod_mem fun k _ => ?_
      rw [hv]
      exact hblk _)
  obtain ⟨m, f₀, a₀, hf, ha, hsum, H⟩ := hsnc c hc
  have hfin := GlobalTheory.T.kaehler_rank_transcendence_degree Ω₀ Ω I u hu hadj
  have hW : ∀ w ∈ Set.range (bratio y c), algebraMap Ω₀ Ω w ∈ Set.range (bratio (addY y x') c₁) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (hv p).symm⟩
  let R₁ := Algebra.adjoin ℚ (Set.range (bratio (addY y x') c₁))
  have hfr : ∀ (A : Subalgebra ℤ Ω₀) (S : Subalgebra ℚ Ω₀), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω₀, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω₀ := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hfr₁ : ∀ (A : Subalgebra ℤ Ω) (S : Subalgebra ℚ Ω), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hloc : ∀ P : Ideal R₁, P.IsPrime → ∃ t : R₁, t ∉ P ∧ ((t : Ω) ≠ 0 → ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range (bratio (addY y x') c₁))) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + Fintype.card I) → S') (n' : ℕ), n' ≤ e + Fintype.card I ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename (addV J N)), ∀ s : S',
              (s : Ω) = MvPolynomial.aeval (bratio (addY y x') c₁) g → s ∈ q) ↔
            ∃ i : Fin (e + Fintype.card I), (i : ℕ) < n' ∧ z' i ∈ q)) := by
    intro P hP
    let fl : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (f₀ l), map_mem_adjoin hW (hf l)⟩
    let al : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (a₀ l), map_mem_adjoin hW (ha l)⟩
    have hone : ∑ l, al l * fl l = 1 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      show ∑ l, algebraMap Ω₀ Ω (a₀ l) * algebraMap Ω₀ Ω (f₀ l) = 1
      simp only [← map_mul]
      rw [← map_sum, hsum, map_one]
    obtain ⟨l, hl⟩ : ∃ l, fl l ∉ P := by
      by_contra hcon
      push_neg at hcon
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hcon l)))
    have h0 : f₀ l ≠ 0 := fun h => hl (by
      have : fl l = 0 := Subtype.ext (by show algebraMap Ω₀ Ω (f₀ l) = 0; rw [h, map_zero])
      rw [this]
      exact P.zero_mem)
    obtain ⟨hSm, z, n, hn, hli, hspan, hbd⟩ := H l h0 _ rfl
    have hle₀ : Algebra.adjoin ℚ (Set.range (bratio y c)) ≤ Algebra.adjoin ℚ
        ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω₀) : Set Ω₀) :=
      Algebra.adjoin_le (by
        rintro _ ⟨p, rfl⟩
        obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
        rw [hd]
        exact Algebra.subset_adjoin (Algebra.subset_adjoin ⟨d, rfl⟩))
    obtain ⟨ψ, hψ, hψs⟩ := GlobalTheory.T.smooth_map_localization_compat Ω₀ Ω _ _ φ hφ hφs (f₀ l) (hle₀ (hf l)) h0
      (Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))))
      (Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))))
      (adjoin_insert_eq y c hc _).symm (adjoin_insert_eq (addY y x') c₁ hc₁ _).symm
    have hA₀ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c),
        a ∈ Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))) := fun a ha' => by
      rw [← adjoin_insert_eq y c hc]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    have hA₁ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁),
        a ∈ Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))) := fun a ha' => by
      rw [← adjoin_insert_eq (addY y x') c₁ hc₁]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    obtain ⟨t, ht, hG⟩ := GlobalTheory.T.kaehler_rank_localization_bound Ω₀ Ω _ _ (bratio y c) (bratio (addY y x') c₁) (addV J N) hv e _ bd hfin (f₀ l) h0 _ _ rfl rfl
      ψ hψ hψs (hfr _ _ hA₀ (GlobalTheory.T.fraction_field_coords_generated X Ω₀ ξ _ (seg y) tie c hxc))
      (hfr₁ _ _ hA₁ (GlobalTheory.T.fraction_field_coords_generated X' Ω ξ' _ (seg (addY y x')) tie' c₁ hxc₁)) hSm z n hn hli hspan hbd P hP (fl l) rfl hl
    exact ⟨t, ht, fun _ => hG⟩
  obtain ⟨m', f', a', hs', hG⟩ := exists_cover _ hloc
  refine ⟨m', fun l => (f' l : Ω), fun l => (a' l : Ω), fun l => (f' l).2, fun l => (a' l).2, ?_, fun l hl S' hS' => ?_⟩
  · have := congrArg (Subtype.val) hs'
    rw [AddSubmonoidClass.coe_finset_sum] at this
    exact this
  · obtain ⟨h1, z', n', h2, h3, h4, h5⟩ := hG l hl S' hS'
    exact ⟨h1, z', n', h2, h3, h4, h5⟩

end GlobalTheory.CompanionTheory.Ar.SncPull
