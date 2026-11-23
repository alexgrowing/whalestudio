import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem isIntegral_of_pow_eq_one {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) :
    IsIntegral ℤ z := by
  refine IsIntegral.of_pow hN ?_
  rw [hz]
  exact isIntegral_one

theorem isIntegral_zpow_of_pow_eq_one {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) (a : ℤ) :
    IsIntegral ℤ (z ^ a) := by

  refine GlobalTheory.PlaceInt.isIntegral_of_pow_eq_one hN ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm a, zpow_mul, zpow_natCast, hz, one_zpow]

private theorem isIntegral_int_ringHom_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a : A}
    (h : IsIntegral ℤ a) : IsIntegral ℤ (f a) :=
  h.map f.toIntAlgHom

theorem datum_isIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ ph ψ x₀, d.PhiPin ph ψ x₀ → ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ x₀ hpin x0 q
  obtain ⟨-, hM, -, -, hII, -⟩ := id hd
  obtain ⟨hloc, hsupp, hequi, hone, hspan0, hsum⟩ := hpin
  have hpd : 0 < d.pd := by
    rcases Nat.eq_zero_or_pos d.pd with h | h
    · have h3 := d.l₂.three_le
      rw [hM, h, mul_zero] at h3
      omega
    · exact h

  have hI : d.I ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot, sup_bot_eq] at hII
    exact bot_ne_top hII
  have : Finite (𝓞 E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot d.I hI
  have := Dw.fin
  have := Dw.proj
  obtain ⟨eI⟩ := GlobalTheory.HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I (Dw.p + Dw.q) Dw.rank
  have : Finite (LaI Xo c d) := Finite.of_equiv _ eI.symm.toEquiv
  have : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :=
    Finite.of_injective (fun e : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (e : LaI Xo c d → LaI Xo c d))
      (fun a b h => LinearEquiv.ext (congrFun h))

  have hph : ∀ x, IsIntegral ℤ (ph x) := by
    intro x
    by_cases h0 : ph x = 0
    · rw [h0]
      exact isIntegral_zero
    have hspan := hsupp x h0
    obtain ⟨-, htrans, adj, -, hadj⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
    let pad : (Fin n → LaJ Xo c d) → Fin (Dw.p + Dw.q) → LaJ Xo c d :=
      fun z i => if h : i.val < n then z ⟨i.val, h⟩ else 0
    have hpadv : ∀ z i (h : i.val < n), pad z i = z ⟨i.val, h⟩ := fun z i h => dif_pos h
    have hpad : ∀ z : Fin n → LaJ Xo c d, Submodule.span (𝓞 E) (z '' {b | b.val < Dw.p + Dw.q}) = ⊤ →
        Submodule.span (𝓞 E) (Set.range (pad z)) = ⊤ := by
      intro z hz
      rw [eq_top_iff, ← hz]
      apply Submodule.span_mono
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, hpadv z _ b.isLt⟩
    obtain ⟨g, hg, -⟩ := htrans (pad x₀) (pad x) (hpad x₀ hspan0) (hpad x hspan)
    have h1 := hequi (adj g) g ((hadj (adj g) g).mpr rfl) x₀
    rw [hone, _root_.mul_one] at h1
    have h2 : ph x = ph (fun b => g (x₀ b)) := by
      apply hloc
      intro b hb
      have hb' := hg ⟨b.val, hb⟩
      rw [hpadv x₀ _ b.isLt, hpadv x _ b.isLt] at hb'
      exact hb'.symm
    rw [h2, h1]
    obtain ⟨m, hm, hpow⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp (ψ.isOfFinOrder (isOfFinOrder_of_finite (adj g))).inv
    refine GlobalTheory.PlaceInt.isIntegral_of_pow_eq_one hm ?_
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]

  have hz : IsIntegral ℤ (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))) :=
    GlobalTheory.PlaceInt.isIntegral_zpow_of_pow_eq_one (N := l.M) (by have := l.three_le; omega)
      (GlobalTheory.DatumInverseCharacter.root_pow c dvd_rfl) _

  have hφ : IsIntegral ℤ (d.φδ q) := by
    have he : IsIntegral ℤ (d.eF (d.φδ q)) := by
      rw [hsum q]
      refine finsum_induction (fun y => IsIntegral ℤ y) isIntegral_zero
        (fun a b ha hb => ha.add hb) (fun x => ?_)
      refine (isIntegral_int_ringHom_apply d.eF.toRingHom (hph x)).mul ?_
      exact GlobalTheory.PlaceInt.isIntegral_zpow_of_pow_eq_one hpd
        (GlobalTheory.DatumInverseCharacter.root_pow d.c₂ (Dvd.intro_left _ hM.symm)) _
    have hb := isIntegral_int_ringHom_apply d.eF.symm.toRingHom he
    simpa using hb
  exact isIntegral_int_ringHom_apply d.eF.toRingHom (hz.mul hφ)

end GlobalTheory.PlaceInt
