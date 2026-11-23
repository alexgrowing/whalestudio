import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory.ShortValueLinear

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    P.IsHomogeneous (∑ σ : T, ∑ i : Fin (r σ), a σ i) := by
  classical
  intro m hm
  have hmS : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hm
  have key : ∀ (σ : T) (i : Fin (r σ)), a σ (i : ℕ) = ∑ b, m ⟨σ, (i, b)⟩ :=
    fun σ i => (hP m hmS σ i).symm
  simp only [key]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Fintype.sum_prod_type _

theorem sum_support_eq_constr {ι F S : Type} [Field F] [CommRing S] [Algebra F S]
    (G : (ι →₀ ℕ) → S) (P : MvPolynomial ι F) :
    ∑ m ∈ P.support, algebraMap F S (P.coeff m) * G m =
      (MvPolynomial.basisMonomials ι F).constr F G P := by
  classical
  rw [Module.Basis.constr_apply, Finsupp.sum]
  refine Finset.sum_congr ?_ fun μ _ => ?_
  · ext μ
    simp [MvPolynomial.basisMonomials]
    exact Iff.rfl
  · simp [MvPolynomial.basisMonomials, Algebra.smul_def]
    rfl

theorem formula_linear {ι F S Qt J : Type} [Field F] [CommRing S] [Algebra F S] [Finite Qt] [Fintype J]
    (k N : F) (w : Qt → F) (G : Qt → J → (ι →₀ ℕ) → S) (d m : ℕ) (cf : Fin m → F)
    (Q : Fin m → MvPolynomial ι F) (hQ : ∀ i, (Q i).IsHomogeneous d) :
    algebraMap F S (k * (N ^ (∑ i, cf i • Q i).totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ μ ∈ (∑ i, cf i • Q i).support,
          algebraMap F S ((∑ i, cf i • Q i).coeff μ) * G q j μ =
      ∑ i, algebraMap F S (cf i) * (algebraMap F S (k * (N ^ (Q i).totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ μ ∈ (Q i).support,
          algebraMap F S ((Q i).coeff μ) * G q j μ) := by
  classical
  have := Fintype.ofFinite Qt
  set B := MvPolynomial.basisMonomials ι F
  have hsum : ∀ (P : MvPolynomial ι F) (q : Qt) (j : J),
      ∑ μ ∈ P.support, algebraMap F S (P.coeff μ) * G q j μ = B.constr F (G q j) P :=
    fun P q j => sum_support_eq_constr (G q j) P
  simp only [hsum, finsum_eq_sum_of_fintype]
  have hpre : ∀ P : MvPolynomial ι F, P.IsHomogeneous d →
      algebraMap F S (k * (N ^ P.totalDegree)⁻¹) *
          ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) P =
        algebraMap F S (k * (N ^ d)⁻¹) * ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) P := by
    intro P hP
    by_cases hP0 : P = 0
    · simp [hP0]
    · rw [hP.totalDegree hP0]
  have hQs : (∑ i, cf i • Q i).IsHomogeneous d := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hQ i))
  have hR : ∀ i, algebraMap F S (cf i) * (algebraMap F S (k * (N ^ (Q i).totalDegree)⁻¹) *
        ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) (Q i)) =
      algebraMap F S (cf i) * (algebraMap F S (k * (N ^ d)⁻¹) *
        ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) (Q i)) :=
    fun i => by rw [hpre _ (hQ i)]
  have hlin : ∀ (q : Qt) (j : J), B.constr F (G q j) (∑ i, cf i • Q i) =
      ∑ i, algebraMap F S (cf i) * B.constr F (G q j) (Q i) := by
    intro q j
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
  rw [hpre _ hQs]
  simp only [hR]
  simp only [hlin, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.ShortValueLinear

namespace GlobalTheory

theorem shortThetaValue_linear : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, Q i ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (u : Fin m → S), ShortValAt Xo c nab w Λ β N (∑ i, cf i • Q i) y v → (∀ i, ShortValAt Xo c nab w Λ β N (Q i) y (u i)) → v = ∑ i, algebraMap c.F S (cf i) * u i := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hL a w β m cf Q hQ S _ _ y v u hv hu
  classical
  have : Finite (LevQ Dw l) := GlobalTheory.ShortValue.finite_levelQuotient Dw l
  have hEU := fun i => GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l
    Xo c nab hnab n Λ N hU hT hL a (Q i) (hQ i) w β
  have hRow : ∀ i, RowDeg Dw.mult n c.F (fun τ j => a (τ, j)) (Q i) := by
    intro i
    have h := hQ i
    unfold HHa at h
    simp only [Set.mem_setOf_eq] at h
    exact h.2.2
  have hQd := fun i => GlobalTheory.ShortValueLinear.isHomogeneous_of_rowDeg (hRow i)
  unfold ShortValAt at hv
  obtain ⟨S', _i1, _i2, φ, y', z, tp, F, hff, hfr, hz, hgeo, htp, huu, hφv⟩ := hv
  have hnat : ∀ i, φ (u i) = algebraMap c.F S' (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ (Q i).totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S' (w q) *
        ∑ j, ∑ μ ∈ (Q i).support, algebraMap c.F S' ((Q i).coeff μ) *
          ∏ b, nab y' ((N : ℤ) ^ 2) (F q j b) (colOf μ b) := by
    intro i
    refine (hEU i).2 S S' φ y y' hfr (u i) _ (hu i) ?_
    unfold ShortValAt
    exact ⟨S', _i1, _i2, AlgHom.id c.F S', y', z, tp, F,
      RingHom.FaithfullyFlat.of_bijective ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩,
      GlobalTheory.Frames.frMapUniq_refl y', hz, hgeo, htp, huu, rfl⟩
  have hlin := GlobalTheory.ShortValueLinear.formula_linear (S := S')
    (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹) (N : c.F) w
    (fun q j μ => ∏ b, nab y' ((N : ℤ) ^ 2) (F q j b) (colOf μ b)) _ m cf Q hQd
  apply RingHom.FaithfullyFlat.injective hff
  change φ v = φ (∑ i, algebraMap c.F S (cf i) * u i)
  rw [hφv]
  refine hlin.trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul φ, AlgHom.commutes, hnat i]

end GlobalTheory
