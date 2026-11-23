import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFibreUniformisedTripleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DatumCommensurablePeriod
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifFibreLatticeEqOfPullbackStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplexStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisedQuotientOfCommensurable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpaceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonemptyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem GlobalTheory.all_classes_occur :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ ga : GL (Fin r) E, ∀ x y, FD.herm G ((ga : Matrix (Fin r) (Fin r) E) *ᵥ x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty), l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (f l.M a) = U.t i a + l.M • e := by
  intro hL hN hLaw hQ E _ _ _ H D l Xo σ g ty U hA hσ hty D' f hp hq hf hE
  let i₀ : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨hp₀, hq₀⟩ := U.sig i₀
  have hξ : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
      simpa using this
    have h3 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, h2, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
    · exfalso
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h4 : starRingEnd ℂ (τ (H.rt : E)) = τ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj]
        exact congrArg τ h
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h4
      have h5 := congrArg τ h2
      rw [map_pow, hr, map_neg, map_natCast] at h5
      have h6 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h5
      have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg r]
    · exact h
  have hξ0 : (H.rt : E) ≠ 0 := by
    intro h
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simp only [h, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast] at this
    have h2 : (H.d : E) = 0 := by
      simpa using this
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H (U.Di i₀) (H.rt : E) hξ hξ0 _ rfl
  obtain ⟨φ', hφ'⟩ := GlobalTheory.T.hermitian_forms_same_signature_same_space hL hN E H (U.Di i₀) D' _ _ Gm φ (hp.trans hp₀.symm) (hq.trans hq₀.symm) hξ hφ
  obtain ⟨hg, P₀, hP₀⟩ := (GlobalTheory.T.typeFn_period_exist_moduli_nonempty E H (U.Di i₀)).2.1 g ty (by rw [hp₀, hq₀]; exact hty)
  rw [hp₀, hq₀] at hg
  obtain ⟨N, j, j', P', hj, hP', h₁, h₂⟩ :=
    GlobalTheory.datum_commensurable_period E H (U.Di i₀) D' _ _ Gm φ φ' g ty hξ hφ hφ' P₀ hP₀
  obtain ⟨t₀, e₀, -, -, ht₀⟩ := GlobalTheory.T.exists_universal_fibre_uniformised_triple E H D l Xo σ g ty U i₀ P₀ hσ hg hP₀
  obtain ⟨t, e, ht⟩ := GlobalTheory.exists_uniformised_quotient_of_commensurable hLaw hQ E H (U.Di i₀) D' g ty P₀ P' N j j' t₀ e₀
    (hp.trans hp₀.symm) (hq.trans hq₀.symm) hj hP₀ hP' h₁ h₂ ht₀
  obtain ⟨o, m, hm⟩ := GlobalTheory.T.exists_obj_of_uniformised_triple_complex hLaw E H D D' l σ g ty P' t e f hA hσ hp hq hP' ht hf hE
  obtain ⟨y, ⟨hy, ⟨om⟩⟩, -⟩ := Xo.rep (Sp ℂ) (spMap σ) inferInstance o
  obtain ⟨i, P, hP, rfl⟩ := U.onto y hy
  obtain ⟨n, hn⟩ : ∃ n : SABMap t Xo.univ.t (U.u i P), n.φ = m.φ ≫ om.toSABMap.φ := by
    have := sabComp pullCubComp E H _ _ _ _ _ _ _ _ om.toSABMap m
    rwa [Category.id_comp] at this
  obtain ⟨h, gam, hh, hgam, hiso⟩ := GlobalTheory.T.familyUnif_fibre_lattice_eq_of_pullback E H D l Xo σ g ty U i P D' P' t e n hP hP' ht
  refine ⟨i, gam, hiso, fun a ha => ?_⟩
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact_mod_cast (by omega : l.M ≠ 0)
  have k₁ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a))) = U.ex i P ((l.M : ℂ)⁻¹ • P (U.t i a)) := by
    apply Over.OverMorphism.ext
    rw [← U.ex_eta i P hP a ha, hgam, ← map_smul, ← hh, hn, ← Category.assoc, hm a ha, om.eta, Over.comp_left]
    congr 1
  have k₂ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a)) = 1 := by
    have := U.ex_add i P hP ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a))
      ((l.M : ℂ)⁻¹ • P (U.t i a))
    rw [sub_add_cancel, k₁] at this
    exact (right_eq_mul.1 this)
  obtain ⟨b, hb⟩ := (U.ex_ker i P hP _).1 k₂
  refine ⟨b, hP.2.1 ?_⟩
  rw [map_add, map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hM, one_smul]
  abel
