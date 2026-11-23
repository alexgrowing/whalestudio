import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionTargetGenericCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCorrespondenceExtendSourceDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceFstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceSndStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ExtT

theorem exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → IsDominant i → i ≫ s = s₀ → IsFinite s → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → Flat (s ≫ M.s) → IsLocallyNoetherian Y → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → ∃ t : Y ⟶ M.X, i ≫ t = t₀ ∧ t ≫ M.s = s ≫ M.s ∧ IsFinite t := by
  intro p _ D R _ _ _ _ b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs
    hes hft het hiso htj Y s i hio hid his hsf hnorm hflat hln hfac
  have hred : IsReduced Y := GlobalTheory.T.isReduced_normalModel_generic_correspondence p D R b N hpm M Y₀ s₀ gs hgs hes Y s i hio his hflat hfac
  have hval : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i →
      ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
    intro V K _ _ _ _ _ _ y x hy
    exact GlobalTheory.T.exists_dvr_extension_target_generic_correspondence p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj V K (y ≫ s) x (by rw [← Category.assoc, hy, Category.assoc, his])
  have hqf : ∀ y : Y, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ M.X)
      (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
    intro y
    refine (GlobalTheory.T.finite_points_closure_genericCorrespondence_fst p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj (s y)).subset ?_
    rintro z ⟨V, K, i1, i2, i3, i4, i5, i6, y', z', x, h1, h2, h3, h4⟩
    exact ⟨V, K, i1, i2, i3, i4, i5, i6, y' ≫ s, z', x, by rw [← Category.assoc, h1, Category.assoc, his], h2,
      by rw [← h3]; rfl, h4⟩
  obtain ⟨t, hit, htσ⟩ := GlobalTheory.T.extension_over_normal_quasi_projective_base R Y₀ Y M.X i (s ≫ M.s) M.s t₀ hio hid hln hred hnorm M.qproj
    (by rw [reassoc_of% his, hst]) hval hqf
  have hP : IsProper t := GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence R M.X Y₀ Y M.s s t i M.qproj hsf hio hid htσ (fun V K _ _ _ _ _ _ y x hy => by
    obtain ⟨z, hz⟩ := GlobalTheory.T.harrisTaylor_correspondence_extend_source_dvr p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj V K y x (by rw [hy, hit])
    exact ⟨z, by rw [hz, his]⟩)
  have hC : ∀ z : M.X, {y : Y | t y = z}.Finite := GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first M.X Y₀ Y s t i hsf hio hid hln (fun z => by
    simpa only [his, hit] using GlobalTheory.T.finite_points_closure_genericCorrespondence_snd p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj z)
  haveI : LocallyQuasiFinite t := LocallyQuasiFinite.of_finite_preimage_singleton t hC
  exact ⟨t, hit, htσ, IsFinite.of_isProper_of_locallyQuasiFinite t⟩

end GlobalTheory.ExtT
