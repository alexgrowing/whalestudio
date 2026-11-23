import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RawChartBC

open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem psTrunc_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (f : MvPowerSeries κ S) :
    psTrunc m (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psTrunc m f) := by
  unfold psTrunc
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem basis_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {σ κ : Type} [Fintype σ] [Fintype κ]
    (U : σ → κ → S) (h : ∀ v : κ → S, ∃! a : σ → S, ∀ j, ∑ ℓ, a ℓ * U ℓ j = v j) (v : κ → S') :
    ∃! a : σ → S', ∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j := by
  classical
  choose N hN hNu using fun k : κ => h (Pi.single k 1)
  let M : Matrix σ κ S := Matrix.of U
  let P : Matrix κ σ S := Matrix.of N
  have h1 : P * M = 1 := by
    ext k j
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine (hN k j).trans ?_
    simp [Pi.single_apply, eq_comm]
  have h2 : M * P = 1 := by
    ext ℓ ℓ'
    have e : (fun i => (M * P) ℓ i) = fun i => (1 : Matrix σ σ S) ℓ i := by
      refine (h (U ℓ)).unique (fun j => ?_) (fun j => ?_)
      · have : (M * P * M) ℓ j = M ℓ j := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
        rw [Matrix.mul_apply] at this
        exact this
      · have : ((1 : Matrix σ σ S) * M) ℓ j = M ℓ j := by rw [Matrix.one_mul]
        rw [Matrix.mul_apply] at this
        exact this
    exact congrFun e ℓ'
  have h1' : P.map ψ * M.map ψ = 1 := by rw [← Matrix.map_mul, h1]; simp
  have h2' : M.map ψ * P.map ψ = 1 := by rw [← Matrix.map_mul, h2]; simp
  have key : ∀ a : σ → S', (∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j) ↔ Matrix.vecMul a (M.map ψ) = v := by
    intro a
    rw [funext_iff]
    rfl
  refine ⟨Matrix.vecMul v (P.map ψ), (key _).2 ?_, fun a ha => ?_⟩
  · rw [Matrix.vecMul_vecMul, h1', Matrix.vecMul_one]
  · rw [← (key a).1 ha, Matrix.vecMul_vecMul, h2', Matrix.vecMul_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

section Maps

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)

def baseMap : overAt (spMap ψ ≫ x0) S' ⟶ overAt x0 S :=
  Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap S S) ≫ x0 = spMap (algebraMap S' S') ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]
    first | done | rfl)

def dualPtMap : overAt (spMap ψ ≫ x0) (DualNumber S') ⟶ overAt x0 (DualNumber S) :=
  Over.homMk (spMap (dualMap ψ)) (by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap, dualMap_alg])

theorem sq_aug (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ rjBC ψ x0 d m 1 =
      baseMap ψ x0 ≫ homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap ψ ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetAug_comp_jetBC ψ _ m)

theorem sq_trunc (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetTrunc : Jet S' (Fin 1 × Fin d) (m + 1) →ₐ[S'] Jet S' (Fin 1 × Fin d) m) ≫
        rjBC ψ x0 d (m + 1) 1 =
      rjBC ψ x0 d m 1 ≫ homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ (m + 1)) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetTrunc_comp_jetBC ψ _ m)

theorem sq_subst {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ rjBC ψ x0 d m n =
      rjBC ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetSubstP_comp_jetBC ψ m φ)

theorem sq_tan (d : ℕ) (ℓ : Fin 1 × Fin d) :
    homAt (spMap ψ ≫ x0) (jetTan ℓ : Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S') ≫ rjBC ψ x0 d 1 1 =
      dualPtMap ψ x0 ≫ homAt x0 (jetTan ℓ : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ (0 + 1)) = spMap (dualMap ψ) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetTan_comp_jetBC ψ ℓ 0)

theorem jetMap_congr_fun {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem sq_copy (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        rjBC ψ x0 d m 1 =
      rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  have e := jetMap_comp_jetBC ψ m
    (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (fun _ => X_mem_orig _) (fun p => by rw [MvPolynomial.map_X]; exact X_mem_orig _)
  rw [jetMap_congr_fun (show (fun p : Fin 1 × Fin d =>
      MvPolynomial.map ψ (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) =
    fun p => MvPolynomial.X (i, p.2) from funext fun p => MvPolynomial.map_X ψ _) _ (fun _ => X_mem_orig _)] at e
  exact congrArg spMap e

theorem list_prod_comp {T T' : Over Xo.X} (f : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

theorem isCombAt_map {k : ℕ} {v : Fin k → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin k → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x0 v cf w) :
    IsCombAt (spMap ψ ≫ x0) (fun i => spMap (dualMap ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun i => dualPtMap ψ x0 ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, spMap_spMap, dualMap_epsMul, ← spMap_spMap, Category.assoc]
  · have e : List.ofFn (fun i => dualPtMap ψ x0 ≫ u i) = (List.ofFn u).map (dualPtMap ψ x0 ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, list_prod_comp, Over.comp_left, hp]
    rfl

end Maps

theorem rIsChart_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (uvec : Lt1 Dw → Fin d → S), RIsChart x0 u d F act uvec x → RIsChart (spMap ψ ≫ x0) (fun τ i => spMap (dualMap ψ) ≫ u τ i) d (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (fun ℓ j => ψ (uvec ℓ j)) x' := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx' u uvec hX
  obtain rfl : x' = fun m => rjBC ψ x0 d m 1 ≫ x m := funext hx'
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun ℓ => ?_, basis_map ψ uvec hX.basis⟩
  · rw [← Category.assoc, sq_aug, Category.assoc, hX.zero m]
    simp [Hom.one_def]
  · rw [← Category.assoc, sq_trunc, Category.assoc, hX.trunc m]
  · simp only [psTrunc_map]
    rw [← Category.assoc, sq_subst, Category.assoc, hX.law m]
    simp only [rjpt, Hom.mul_def, comp_lift_assoc]
    rw [← Category.assoc (homAt _ _) (rjBC _ _ _ _ _), ← Category.assoc (homAt _ _) (rjBC _ _ _ _ _), sq_copy,
      sq_copy, Category.assoc, Category.assoc]
  · simp only [psTrunc_map]
    rw [← Category.assoc (homAt _ _), sq_subst, Category.assoc, Category.assoc, hX.act m a]
  · have hv : (fun j : Fin d => (homAt (spMap ψ ≫ x0) (jetTan ((0 : Fin 1), j) :
        Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S') ≫ (rjBC ψ x0 d 1 1 ≫ x 1)).left) =
        fun j => spMap (dualMap ψ) ≫ (homAt x0 (jetTan ((0 : Fin 1), j) :
          Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left := by
      funext j
      rw [← Category.assoc, sq_tan, Category.assoc]
      rfl
    have := isCombAt_map ψ x0 (hX.tan ℓ)
    rw [← hv] at this
    exact this

end GlobalTheory.RawChartBC
