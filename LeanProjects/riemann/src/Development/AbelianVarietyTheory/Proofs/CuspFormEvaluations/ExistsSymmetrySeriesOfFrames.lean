import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameSymmetry

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

section Pts

variable {S : Type} [CommRing S] (d : ℕ)

private theorem jetMap_mk_lemma (m : ℕ) {κ κ' : Type} (f : κ → MvPolynomial κ' S) (hf : ∀ i, f i ∈ orig S κ')
    (q : MvPolynomial κ S) :
    jetMap (m := m) f hf (Ideal.Quotient.mk (orig S κ ^ (m + 1)) q : Jet S κ m) =
      (Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (MvPolynomial.bind₁ f q) : Jet S κ' m) := by
  rfl

theorem subst_comp_copy (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) =
      jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2) := by
  refine AlgHom.ext fun p => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S _ ^ (m + 1)) p
  simp only [jetCopy, jetSubstP, AlgHom.comp_apply, jetMap_mk_lemma m, MvPolynomial.bind₁_bind₁,
    MvPolynomial.bind₁_X_right]

theorem subst_X_eq_copy (m : ℕ) {n : ℕ} (k : Fin n) :
    jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S)) =
      jetCopy d m k := by
  refine AlgHom.ext fun p => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S _ ^ (m + 1)) p
  simp only [jetCopy, jetSubstP, jetMap_mk_lemma m, MvPolynomial.constantCoeff_X, map_zero, sub_zero]

end Pts

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}

theorem pt_sub (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    homAt x0 (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)) ≫ jptG t x0 d x m i =
      homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2)) ≫ x m := by
  unfold jptG
  rw [← Category.assoc, ← subst_comp_copy]
  congr 1
  apply Over.OverMorphism.ext
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left]
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem pt_X (m : ℕ) {n : ℕ} (k : Fin n) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S))) ≫ x m =
      jptG t x0 d x m k := by
  rw [subst_X_eq_copy]
  rfl

private theorem comp_foldr_padd_eq_foldr_padd_comp {T T' : Over X0} (f : T' ⟶ T) (xs : Fin 2 → (T ⟶ t.G)) (L : List (Fin 2)) :
    f ≫ L.foldr (fun k acc => padd t.G (xs k) acc) (pzero t.G T) =
      L.foldr (fun k acc => padd t.G (f ≫ xs k) acc) (pzero t.G T') := by
  induction L with
  | nil => simp [pzero]
  | cons k L ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    simp only [padd]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]

theorem pe_pt (m : ℕ) {n : ℕ} (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) (I : ULift.{0} (Finset (Fin 2))) :
    (homAt x0 σ).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I =
      (psum t.G ![homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2), homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2)] I.down).left := by
  unfold cφG
  rw [← Over.comp_left]
  congr 1
  unfold psum
  rw [comp_foldr_padd_eq_foldr_padd_comp]
  congr 1
  funext k acc
  fin_cases k <;> rfl

theorem ofMul_eq {M : Type} [CommGroup M] {a b : M} (h : Additive.ofMul a = Additive.ofMul b) : a = b :=
  by exact Additive.ofMul.injective h

private theorem univ_ulift_finset_fin_two :
    (Finset.univ : Finset (ULift (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by
  decide

theorem prod_cube2_swap {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (xs : Fin 2 → (T ⟶ t.G)) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G xs I.down) ^ cε 2 I =
      h 1 * (h (xs 0 * 1))⁻¹ * (h (xs 1 * 1))⁻¹ * h (xs 1 * (xs 0 * 1)) := by
  have e0 : psum t.G xs ∅ = 1 := by rfl
  have e1 : psum t.G xs {0} = xs 0 * 1 := by rfl
  have e2 : psum t.G xs {1} = xs 1 * 1 := by rfl
  have e3 : psum t.G xs {0, 1} = xs 0 * (xs 1 * 1) := by rfl
  rw [univ_ulift_finset_fin_two, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [e0, e1, e2, e3]
  rw [show xs 0 * (xs 1 * 1) = xs 1 * (xs 0 * 1) by rw [_root_.mul_one, _root_.mul_one, _root_.mul_comm]]
  have c01 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [cε, Finset.card_empty, Finset.card_singleton, c01]
  norm_num [zpow_neg, _root_.mul_assoc]

end Chart

end GlobalTheory.FrameSymmetry

namespace GlobalTheory

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameSymmetry in
set_option maxHeartbeats 4000000 in

theorem exists_symmetry_series_of_frames :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ sy : PS S 2 d, ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (e m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])) := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ _ e he htr _
  have hBt : ∀ m y J, Good t.PP.L y J →
      val (peG t x0 d x e (m + 1) ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]) (ρn x0 d 2 m).left y J =
        val (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]) (𝟙 _) y J :=
    fun m y J hJ => pe_trunc t x0 d htr (fun _ => ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])
      (fun _ _ _ => by rw [sub_self]; exact zero_mem _) m y J hJ
  have hAt : ∀ m y J, Good t.PP.L y J → val (e (m + 1)) (ρn x0 d 2 m).left y J = val (e m) (𝟙 _) y J := by
    intro m y J hJ
    have h1 := val_corr hJ (htr m) (𝟙 _)
    have h2 := val_pull hJ (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left (𝟙 _)
    rw [Category.id_comp] at h2
    exact h2.symm.trans h1
  have hF : ∀ m, FormEq (fun I : ULift.{0} (Finset (Fin 2)) =>
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) (cε 2)
      (fun I => (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
          p.1 p.2)).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) (cε 2) := by
    intro m U _ h
    have hs0 : homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
          p.1 p.2) ≫ jptG t x0 d x m (0 : Fin 2) = jptG t x0 d x m (1 : Fin 2) :=
      (pt_sub m _ 0).trans (pt_X m 1)
    have hs1 : homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
          p.1 p.2) ≫ jptG t x0 d x m (1 : Fin 2) = jptG t x0 d x m (0 : Fin 2) :=
      (pt_sub m _ 1).trans (pt_X m 0)
    simp only [pe_pt]
    refine ((prod_cube2_swap (fun g : jOG x0 d m 2 ⟶ t.G => h g.left)
      ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]).trans ?_).trans
      (prod_cube2_swap (fun g : jOG x0 d m 2 ⟶ t.G => h g.left) _).symm
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hs0, hs1, _root_.mul_one]
    rw [_root_.mul_comm (jptG t x0 d x m 0) (jptG t x0 d x m 1)]
    ac_rfl
  obtain ⟨ph, hph⟩ := exists_series t x0 d _ (cε 2) _ (cε 2)
    (fun m => peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (he m) _) e he (fun m U _ h => (hF m U h).symm) hBt hAt
  refine ⟨ph, fun m => ?_⟩
  obtain ⟨u, hu, hc⟩ := hph m
  refine ⟨u, hu, corr_of_val t.PP.isLB fun y J hJ => ?_⟩
  rw [val_scale t _ _ _ _ _ _ _ hJ, val_corr hJ hc (𝟙 _)]
  have k1 := val_scale t _ _ (unitΓ u) (e m) (𝟙 (jOG x0 d m 2).left) y J hJ
  refine Eq.trans ?_ (congrArg (fun v => gm (𝟙 (jOG x0 d m 2).left) y ⊤ (unitΓ u⁻¹) * v) k1.symm)
  have k2 : unitΓ u⁻¹ * unitΓ u = 1 := by
    unfold unitΓ
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [← _root_.mul_assoc, ← map_mul]
  simp only [k2, map_one, _root_.one_mul]

end GlobalTheory
