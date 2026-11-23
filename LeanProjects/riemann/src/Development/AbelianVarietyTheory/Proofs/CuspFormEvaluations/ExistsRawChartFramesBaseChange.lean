import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RawFrameBC

private theorem pull2_lemma_9 {Z' Y' Z Y : Scheme.{0}} (a : Z' ⟶ Y') (g : Y' ⟶ Y) (r : Z' ⟶ Z) (b : Z ⟶ Y)
    (hab : a ≫ g = r ≫ b) (U : Y.Opens) (V : Y'.Opens) (hV : V ≤ g ⁻¹ᵁ U) (W1 : Z'.Opens) (hW1 : W1 ≤ a ⁻¹ᵁ V)
    (V' : Z.Opens) (hV' : V' ≤ b ⁻¹ᵁ U) (W1' : Z'.Opens) (hW1' : W1' ≤ r ⁻¹ᵁ V') (W2 : Z'.Opens)
    (h12 : W2 ≤ W1) (h12' : W2 ≤ W1') (u : Γ(Y, U)ˣ) :
    Units.map (Z'.presheaf.map (homOfLE h12).op).hom.toMonoidHom (Units.map (Z'.presheaf.map (homOfLE hW1).op).hom.toMonoidHom
      (Units.map (a.app V).hom.toMonoidHom (Units.map (Y'.presheaf.map (homOfLE hV).op).hom.toMonoidHom (Units.map (g.app U).hom.toMonoidHom u)))) =
    Units.map (Z'.presheaf.map (homOfLE h12').op).hom.toMonoidHom (Units.map (Z'.presheaf.map (homOfLE hW1').op).hom.toMonoidHom
      (Units.map (r.app V').hom.toMonoidHom (Units.map (Z.presheaf.map (homOfLE hV').op).hom.toMonoidHom (Units.map (b.app U).hom.toMonoidHom u)))) := by
  have hW : W2 ≤ (a ≫ g) ⁻¹ᵁ U := fun z hz => hV (hW1 (h12 hz))
  have hW' : W2 ≤ (r ≫ b) ⁻¹ᵁ U := fun z hz => hV' (hW1' (h12' hz))
  have e1 : g.app U ≫ Y'.presheaf.map (homOfLE hV).op ≫ a.app V ≫ Z'.presheaf.map (homOfLE hW1).op ≫
      Z'.presheaf.map (homOfLE h12).op = (a ≫ g).appLE U W2 hW := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Hom.naturality_assoc, ← Functor.map_comp]
    rfl
  have e2 : b.app U ≫ Z.presheaf.map (homOfLE hV').op ≫ r.app V' ≫ Z'.presheaf.map (homOfLE hW1').op ≫
      Z'.presheaf.map (homOfLE h12').op = (r ≫ b).appLE U W2 hW' := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Hom.naturality_assoc, ← Functor.map_comp]
    rfl
  have e3 : ∀ (f f' : Z' ⟶ Y) (hf : f = f') (h : W2 ≤ f ⁻¹ᵁ U) (h' : W2 ≤ f' ⁻¹ᵁ U),
      f.appLE U W2 h = f'.appLE U W2 h' := by
    intro f f' hf h h'
    subst hf
    rfl
  have key := congrArg (fun F => F.hom (u : Γ(Y, U))) (e1.trans ((e3 _ _ hab hW hW').trans e2.symm))
  apply Units.ext
  simpa using key

theorem exists_reindexed_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) (g : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (h : φ' = fun k => g ≫ φ k) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L _ _ _ _ c' (LB.pullGen L φ ε c g) ∧
      ∀ (Z Z' : Scheme.{0}) (a : Z' ⟶ Y') (b : Z ⟶ Y) (r : Z' ⟶ Z), a ≫ g = r ≫ b →
        LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ' ε c' a) (LB.pullGen L _ _ (LB.pullGen L φ ε c b) r) := by
  subst h
  refine ⟨LB.pullGen L φ ε c g, DVR.pullGen_isGen L φ ε c hc g, corr_of_val hL fun y J => congrFun rfl, ?_⟩
  intro Z Z' a b r hab j j' hj hj' hjj
  have hjj' : j = j' := funext fun k => hjj k k (by
    show a ≫ g ≫ φ k = r ≫ b ≫ φ k
    rw [← Category.assoc, hab, Category.assoc])
  subst hjj'
  simp only [LB.pullGen]
  unfold pullU res
  exact pull2_lemma_9 a g r b hab _ _ _ _ _ _ _ _ _ _ _ _ (c.s j)

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, ← Spec.map_comp]
  rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)

theorem sq_of_ring {m n n' : ℕ} (f : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m)
    (f' : Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m)
    (h : f'.toRingHom.comp (jetBC ψ _ m) = (jetBC ψ _ m).comp f.toRingHom) :
    homAt (spMap ψ ≫ x0) f' ≫ rjBC ψ x0 d m n = rjBC ψ x0 d m n' ≫ homAt x0 f := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Formalism.L2.Pj.homAt, rjBC, Over.homMk_left]
  rw [spMap_comp_eq, spMap_comp_eq]
  congr 1

private theorem jetCopy_eq_lemma {R : Type} [CommRing R] {d n : ℕ} (m : ℕ) (i : Fin n) :
    (jetCopy d m i : Jet R (Fin 1 × Fin d) m →ₐ[R] Jet R (Fin n × Fin d) m) =
      jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) R)) := by
  unfold jetCopy jetSubstP
  congr 1
  funext p
  simp

theorem sq_copy {n : ℕ} (m : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i) ≫ rjBC ψ x0 d m 1 = rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i) := by
  rw [jetCopy_eq_lemma, jetCopy_eq_lemma]
  have := sq_of_ring ψ x0 d _ _
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC ψ m
      (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S)))
  simpa only [MvPolynomial.map_X] using this

theorem sq_subst {n n' : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m fun p => MvPolynomial.map ψ (φ p)) ≫ rjBC ψ x0 d m n =
      rjBC ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ) := sq_of_ring ψ x0 d _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem rjpt_bc (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G)
    (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    rjpt (spMap ψ ≫ x0) d x' m i = rjBC ψ x0 d m n ≫ rjpt x0 d x m i := by
  unfold rjpt
  rw [hx, ← Category.assoc, sq_copy, Category.assoc]

private theorem padd_lemma_2 {T T' : Over Xo.X} (ρ : T' ⟶ T) (a b : T ⟶ Xo.univ.t.G) :
    ρ ≫ padd Xo.univ.t.G a b = padd Xo.univ.t.G (ρ ≫ a) (ρ ≫ b) := by
  unfold padd
  rw [← Category.assoc, comp_lift]

private theorem pzero_lemma_3 {T T' : Over Xo.X} (ρ : T' ⟶ T) :
    ρ ≫ pzero Xo.univ.t.G T = pzero Xo.univ.t.G T' := by
  unfold pzero
  rw [← Category.assoc]
  congr 1
  exact toUnit_unique _ _

private theorem foldr_lemma_4 {T T' : Over Xo.X} (ρ : T' ⟶ T) {n : ℕ} (v : Fin n → (T ⟶ Xo.univ.t.G))
    (v' : Fin n → (T' ⟶ Xo.univ.t.G)) (hv : ∀ k, v' k = ρ ≫ v k) (l : List (Fin n)) :
    ρ ≫ l.foldr (fun k acc => padd Xo.univ.t.G (v k) acc) (pzero Xo.univ.t.G T) =
      l.foldr (fun k acc => padd Xo.univ.t.G (v' k) acc) (pzero Xo.univ.t.G T') := by
  induction l with
  | nil => exact pzero_lemma_3 ρ
  | cons k l ih => simp only [List.foldr_cons]; rw [padd_lemma_2, ih, hv]

theorem cφ_comp {T T' : Over Xo.X} (ρ : T' ⟶ T) (a b : T ⟶ Xo.univ.t.G) :
    cφ ![ρ ≫ a, ρ ≫ b] = fun I => ρ.left ≫ cφ ![a, b] I := by
  funext I
  unfold cφ psum
  exact (congrArg Over.Hom.left (foldr_lemma_4 ρ ![a, b] ![ρ ≫ a, ρ ≫ b] (fun k => by fin_cases k <;> rfl) _)).symm

end

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m), (∀ m, (e m).IsGen) → ∃ e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) ∧ ∀ (m n' : ℕ) (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S), LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (rpe (spMap ψ ≫ x0) d x' e' m (fun i j => MvPolynomial.map ψ (φ i j))) (LB.pullGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m φ) (rjBC ψ x0 d m n').left) := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx e he
  have hφ : ∀ m, cφ ![rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2), rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2)] =
      fun k => (rjBC ψ x0 d m 2).left ≫ cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)] k := by
    intro m
    rw [rjpt_bc ψ x0 d x x' hx m 0, rjpt_bc ψ x0 d x x' hx m 1, cφ_comp]
  choose e' he' hcorr hnat using fun m =>
    exists_reindexed_pull Xo.univ.t.PP.isLB (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2)
      (e m) (he m) (rjBC ψ x0 d m 2).left _ (hφ m)
  refine ⟨e', he', fun m => hcorr m, fun m n' φ => ?_⟩
  have hab := congrArg Over.Hom.left (sq_subst ψ x0 d m (fun p : Fin 2 × Fin d => φ p.1 p.2))
  simp only [Over.comp_left] at hab
  unfold rpe
  exact hnat m _ _ _ _ _ hab

end GlobalTheory.RawFrameBC
