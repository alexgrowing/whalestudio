import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqB

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1

namespace GlobalTheory.ChartCmp.FrameRatio

theorem exists_corr_scaled {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ φ' : K → (Y ⟶ X)) (h : φ = φ') (ε : K → ℤ) (g : LB.Gen (LB.LinComb L φ ε))
    (g' : LB.Gen (LB.LinComb L φ' ε)) (hg : g.IsGen) (hg' : g'.IsGen) :
    ∃ U : Γ(Y, ⊤)ˣ, LB.Gen.Corr L φ ε φ' ε g
      (⟨fun j => res le_top U * g'.s j⟩ : LB.Gen (LB.LinComb L φ' ε)) := by
  subst h
  obtain ⟨U, hU⟩ := GaugeR.ratio_of_gen L hL φ ε g' g hg' hg
  refine ⟨U, fun j j' _ _ hx => ?_⟩
  obtain rfl : j = j' := funext fun k => hx k k rfl
  rw [hU j]

theorem comp_psum' {S : Scheme.{0}} (G : Over S) [GrpObj G] {T T' : Over S} (f : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) : f ≫ psum G x I = psum G (fun k => f ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    simp only [List.foldr_cons, padd]
    rw [← Category.assoc, comp_lift]
    congr 2

theorem unitΓ_surj {A : Type} [CommRing A] (U : Γ(Sp A, ⊤)ˣ) : ∃ u : Aˣ, unitΓ u = U := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom U, Units.ext ?_⟩
  simp [unitΓ, toΓ]

theorem psJet_surj {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ) (a : Jet R κ m) :
    ∃ f : MvPowerSeries κ R, psJet m f = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨(p : MvPowerSeries κ R), GaugeR.psJet_eq_mk m _ p fun e _ => (MvPolynomial.coeff_coe p e).symm⟩

theorem copy_subst {V : Type} [CommRing V] (d m : ℕ) (φ : Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (ψ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) (i : Fin 2)
    (hψ : ∀ j, ψ i j = psIn d m ![i] (φ j)) :
    (jetCopy d m i).comp (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) =
      (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2).comp (jetCopy d m i) := by
  apply GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  simp only [AlgHom.comp_apply, jetCopy, jetSubstP, GaugeR.jetMap_mk, MvPolynomial.aeval_X, hψ, psIn,
    MvPolynomial.constantCoeff_rename, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  congr 2
  generalize psTrunc m (φ j) = P
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    obtain ⟨a, b⟩ := k
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → ∀ m, ∃ ε : PS V 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧ FrRel t x x' e e' φ m ε := by
  intro E _ _ _ H V _ t d x x' e e' φ _ hc he he' m
  let ψ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V :=
    ![fun j => psIn d m ![0] (φ j), fun j => psIn d m ![1] (φ j)]
  have hpt : ∀ i : Fin 2, (∀ j, ψ i j = psIn d m ![i] (φ j)) → jptG t (𝟙 (Sp V)) d x' m i =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2) ≫ jptG t (𝟙 (Sp V)) d x m i := by
    intro i hi
    rw [jptG, jptG, hc m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp,
      copy_subst d m φ ψ i hi]
  have hfam : cφG t ![jptG t (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x' m (1 : Fin 2)] =
      fun I => (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2)).left ≫
        cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I := by
    funext I
    rw [cφG, cφG, ← Over.comp_left, comp_psum']
    congr 2
    funext k
    fin_cases k
    · exact hpt 0 fun _ => rfl
    · exact hpt 1 fun _ => rfl
  obtain ⟨U, hU⟩ := exists_corr_scaled t.PP.L t.PP.isLB _ _ hfam (cε 2) (e' m)
    (peG t (𝟙 (Sp V)) d x e m ψ) (he' m) (DVR.pullGen_isGen _ _ _ _ (he m) _)
  obtain ⟨u, rfl⟩ := unitΓ_surj U
  obtain ⟨ε, hε⟩ := psJet_surj m (u : Jet V (Fin 2 × Fin d) m)
  refine ⟨ε, ?_, u, hε.symm, hU⟩
  rw [← GaugeR.jetAug_psJet m ε, hε]
  exact u.isUnit.map _

end GlobalTheory.ChartCmp.FrameRatio
