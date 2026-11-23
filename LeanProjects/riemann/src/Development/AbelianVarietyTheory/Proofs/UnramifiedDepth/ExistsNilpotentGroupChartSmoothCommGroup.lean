import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfNaturalOnNilpotent
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GroupLawPowerSeries
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBasicNEvalSubCoeffMem
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSeriesEqOfEvalAtNilpotentPointsEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma nv_eq_nEval {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n d : ℕ} (f : PS R n d)
    (a : Fin n → Fin d → S) :
    nv (algebraMap R S) f a = nEval f (fun q : Fin n × Fin d => a q.1 q.2) := by
  unfold nv nEval tEval
  rfl

private lemma sep_nil {R : Type} [CommRing R] {n d : ℕ} (f f' : PS R n d)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) →
      nv (algebraMap R S) f a = nv (algebraMap R S) f' a) : f = f' :=
  GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq R ⊥ inferInstance n d f f' (fun S _ _ _ _ _ a ha => h S a ha)

private lemma nv_ev {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n m d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (b : Fin m → Fin d → PS R n d) (f : PS R m d)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) :
    nv s (ev b f) a = nv s f (fun i j => nv s (b i j) a) :=
  (nv_calculus R S s n d a ha).2.2.1 m d b f hb

private lemma nv_X {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) (j : Fin d) :
    nv s (MvPowerSeries.X (i, j)) a = a i j := by
  obtain ⟨ψ, h1, -, h3⟩ := (nv_calculus R S s n d a ha).1
  rw [← h1, h3]

private lemma nv_zero {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) :
    nv s (0 : PS R n d) a = 0 := by
  obtain ⟨ψ, h1, -, -⟩ := (nv_calculus R S s n d a ha).1
  rw [← h1, map_zero]

private lemma nilpotent_eval_subst_pair {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (b c : Fin d → PS R n d) (f : PS R 2 d)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) :
    nv s (ev ![b, c] f) a = nv s f ![fun j => nv s (b j) a, fun j => nv s (c j) a] := by
  rw [nv_ev s a ha _ f (by intro i j; fin_cases i; exacts [hb j, hc j])]
  congr 1
  funext i j
  fin_cases i <;> rfl

private lemma const_pt {R : Type} [CommRing R] {n d : ℕ} (i : Fin n) (j : Fin d) :
    MvPowerSeries.constantCoeff (pt R d i j) = 0 := by
  simp [pt]

private lemma nv_pt {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) :
    (fun j => nv s (pt R d i j) a) = a i := funext fun j => nv_X s a ha i j

private lemma nv_at_zero {R : Type} [CommRing R] {n d : ℕ} (f : PS R n d) :
    nv (algebraMap R R) f (0 : Fin n → Fin d → R) = MvPowerSeries.constantCoeff f := by
  have := (nv_calculus R R (algebraMap R R) n d 0 (fun _ _ => IsNilpotent.zero)).2.2.2.2.2
    (fun _ _ _ _ => by simp) f
  simpa using this

private lemma constantCoeff_germEvalTwo_eq_zero {R : Type} [CommRing R] {n d : ℕ} (b c : Fin d → PS R n d) (f : PS R 2 d)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![b, c] f) = 0 := by
  rw [← nv_at_zero, nilpotent_eval_subst_pair _ _ (fun _ _ => IsNilpotent.zero) _ _ _ hb hc, ← hf, ← nv_at_zero]
  congr 1
  funext i j
  fin_cases i
  · exact (nv_at_zero _).trans (hb j)
  · exact (nv_at_zero _).trans (hc j)

theorem exists_nilChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∃ (F : FGLaw R g) (X : Fam G g), NilChart G F.F X := by
  intro R _ _ G _ _ g hG
  classical
  obtain ⟨x, h0, hnat, hinj, hsur⟩ := GlobalTheory.NilCoord.nilpotent_coordinates G g hG
  have hser := @GlobalTheory.exists_series_of_natural_on_nilpotent (@GlobalTheory.nEval_basic)
  obtain ⟨F0, hF0⟩ := GlobalTheory.ChLaw.groupLaw_powerSeries (@GlobalTheory.nEval_basic) (@hser) G g x ⟨h0, hnat, hinj, hsur⟩
  have hF : ∀ k : Fin g, ∃ f : PS R 2 g, ∀ (S : Type) [CommRing S] [Algebra R S] (u : Fin 2 × Fin g → S),
      (∀ i, IsNilpotent (u i)) → fAdd F0 (fun j => u (0, j)) (fun j => u (1, j)) k = nEval f u := by
    intro k
    refine hser (fun S _ _ u => fAdd F0 (fun j => u (0, j)) (fun j => u (1, j)) k) ?_
    intro S _ _ S' _ _ φ u hu
    unfold fAdd
    rw [((GlobalTheory.nEval_basic (F0 k) S _).2 (by rintro (i | i) <;> exact hu _)).1 S' φ]
    congr 1
    funext i
    rcases i with i | i <;> rfl
  choose F hF using hF
  have hFe : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → fAdd F0 a b = fun k => nv (algebraMap R S) (F k) ![a, b] := by
    intro S _ _ a b ha hb
    funext k
    rw [nv_eq_nEval, ← hF k S _ (by rintro ⟨i, j⟩; fin_cases i; exacts [ha j, hb j])]
    rfl
  have law : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → x S a * x S b = x S (fun k => nv (algebraMap R S) (F k) ![a, b]) := by
    intro S _ _ a b ha hb
    rw [← hFe S a b ha hb]
    exact (hF0 S a b ha hb).2
  have nil : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (nv (algebraMap R S) (F k) ![a, b]) := by
    intro S _ _ a b ha hb k
    have h1 := (hF0 S a b ha hb).1 k
    rw [hFe S a b ha hb] at h1
    have h : Ideal.span (Set.range a ∪ Set.range b) ≤ nilradical S := Ideal.span_le.2 (by
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      exacts [mem_nilradical.2 (ha i), mem_nilradical.2 (hb i)])
    exact mem_nilradical.1 (h h1)
  have hz : ∀ (S : Type) [CommRing S] (i : Fin g), IsNilpotent ((0 : Fin g → S) i) :=
    fun S _ i => IsNilpotent.zero
  have unitL : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (fun k => nv (algebraMap R S) (F k) ![0, a]) = a := by
    intro S _ _ a ha
    refine hinj S _ _ (nil S _ _ (hz S) ha) ha ?_
    rw [← law S _ _ (hz S) ha, h0, _root_.one_mul]
  have const : ∀ k, MvPowerSeries.constantCoeff (F k) = 0 := by
    intro k
    have h := congrFun (unitL R 0 (hz R)) k
    rw [← nv_at_zero]
    refine Eq.trans ?_ h
    congr 1
    funext i j
    fin_cases i <;> rfl
  refine ⟨⟨F, const, ?_, ?_, ?_⟩, x, ⟨h0, hnat, hinj, ?_, law⟩⟩
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha (0 : Fin g → PS R 1 g) _ _ (fun _ => map_zero _) (const_pt _), nv_pt _ a ha, nv_X _ a ha]
    have e : (fun j => nv (algebraMap R S) ((0 : Fin g → PS R 1 g) j) a) = 0 :=
      funext fun j => nv_zero _ a ha
    rw [e]
    exact congrFun (unitL S (a 0) (ha 0)) k
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (const_pt _), nv_pt _ a ha, nv_pt _ a ha]
    have e : a = ![a 0, a 1] := by
      funext i
      fin_cases i <;> rfl
    conv_rhs => rw [e]
    refine congrFun (hinj S _ _ (nil S _ _ (ha 1) (ha 0)) (nil S _ _ (ha 0) (ha 1)) ?_) k
    rw [← law S _ _ (ha 1) (ha 0), ← law S _ _ (ha 0) (ha 1), _root_.mul_comm]
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha _ _ _ (fun l => constantCoeff_germEvalTwo_eq_zero _ _ _ (const_pt _) (const_pt _) (const l)) (const_pt _),
      nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (fun l => constantCoeff_germEvalTwo_eq_zero _ _ _ (const_pt _) (const_pt _) (const l))]
    simp only [nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (const_pt _), nv_pt _ a ha]
    refine congrFun (hinj S _ _ (nil S _ _ (nil S _ _ (ha 0) (ha 1)) (ha 2))
      (nil S _ _ (ha 0) (nil S _ _ (ha 1) (ha 2))) ?_) k
    rw [← law S _ _ (nil S _ _ (ha 0) (ha 1)) (ha 2), ← law S _ _ (ha 0) (nil S _ _ (ha 1) (ha 2)),
      ← law S _ _ (ha 0) (ha 1), ← law S _ _ (ha 1) (ha 2), _root_.mul_assoc]
  · intro S _ _ S' _ _ ρ σ hρσ hn z hz'
    refine hsur S S' ρ (fun y => ⟨σ y, AlgHom.congr_fun hρσ y⟩) ?_ z hz'
    intro c hc
    obtain ⟨N, hN⟩ := hn
    have := Ideal.pow_mem_pow hc N
    rw [hN] at this
    exact ⟨N, by simpa using this⟩

end GlobalTheory.ChF
