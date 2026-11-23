import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

attribute [local instance] Over.cartesianMonoidalCategory

section Pt

variable {S Idx : Type} [CommRing S]

instance jetAug_isLocalHom (m : ℕ) : IsLocalHom ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := @jet_exists_nil S Idx _ m a
  have hn : IsNilpotent ((jetAug : Jet S Idx m →ₐ[S] S) (a - algebraMap S _ c)) := hc.map _
  rw [map_sub, AlgHom.commutes] at hn
  have hcu : IsUnit c := by
    have := hn.neg.isUnit_add_left_of_commute ha (Commute.all _ _)
    simpa using this
  have := hc.isUnit_add_left_of_commute (hcu.map (algebraMap S (Jet S Idx m))) (Commute.all _ _)
  simpa using this

theorem pre_top [IsLocalRing S] (m : ℕ) {X : Scheme.{0}} (U : X.Opens) (ψ : Sp (Jet S Idx m) ⟶ X) (e : Sp S ⟶ X)
    (he : spMap ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S) ≫ ψ = e) (hU : e ⁻¹ᵁ U = ⊤) : ψ ⁻¹ᵁ U = ⊤ := by
  apply ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem
  have h1 : (IsLocalRing.closedPoint S : Sp S) ∈ e ⁻¹ᵁ U := by rw [hU]; trivial
  have h2 : (spMap ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S)).base (IsLocalRing.closedPoint S) =
      IsLocalRing.closedPoint (Jet S Idx m) :=
    IsLocalRing.comap_closedPoint ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S)
  rw [← he] at h1
  show ψ.base (IsLocalRing.closedPoint (Jet S Idx m)) ∈ U
  rw [← h2]
  exact h1

theorem psum_one {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {n : ℕ}
    (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons k l ih => exact (congrArg (padd G 1) ih).trans (_root_.one_mul (1 : T ⟶ G))

theorem aug_copy {d n : ℕ} (m : ℕ) (i : Fin n) :
    (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S).comp (jetCopy d m i) = jetAug := by
  apply jet_hom_ext
  intro p
  show MvPolynomial.aeval (fun _ => (0 : S))
      (MvPolynomial.aeval (fun q : Fin 1 × Fin d => (MvPolynomial.X (i, q.2) : MvPolynomial (Fin n × Fin d) S))
        (MvPolynomial.X p)) = MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X p)
  simp

end Pt

section Axes

theorem prod_cube2 {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {M : Type} [CommGroup M]
    (h : (T ⟶ G) → M) (xs : Fin 2 → (T ⟶ G)) :
    ∏ I : ULift (Finset (Fin 2)), h (psum G xs I.down) ^ cε 2 I =
      h 1 * (h (xs 0 * 1))⁻¹ * (h (xs 1 * 1))⁻¹ * h (xs 0 * (xs 1 * 1)) := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => h (psum G xs I) ^ cε 2 ⟨I⟩) (fun _ => rfl)).trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have c0 : cε 2 ⟨(∅ : Finset (Fin 2))⟩ = 1 := rfl
  have c1 : cε 2 ⟨({0} : Finset (Fin 2))⟩ = -1 := rfl
  have c2 : cε 2 ⟨({1} : Finset (Fin 2))⟩ = -1 := rfl
  have c3 : cε 2 ⟨({0, 1} : Finset (Fin 2))⟩ = 1 := rfl
  have p0 : psum G xs ∅ = 1 := rfl
  have p1 : psum G xs {0} = xs 0 * 1 := rfl
  have p2 : psum G xs {1} = xs 1 * 1 := rfl
  have p3 : psum G xs {0, 1} = xs 0 * (xs 1 * 1) := rfl
  rw [c0, c1, c2, c3, p0, p1, p2, p3]
  simp only [zpow_one, zpow_neg, _root_.mul_assoc]

variable {S : Type} [CommRing S]

theorem jetAug_X {Idx : Type} (m : ℕ) (q : Idx) :
    (jetAug : Jet S Idx m →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 := by
  show MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X q) = 0
  simp

variable (d : ℕ)

abbrev axis0 (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

abbrev axis1 (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

theorem first_axis_at_first_copy (m : ℕ) : (axis0 (S := S) d m).comp (jetCopy d m (0 : Fin 2)) =
    (Algebra.ofId S (Jet S (Fin 1 × Fin d) m)).comp jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk, jetAug_X]

theorem first_axis_at_second_copy (m : ℕ) : (axis0 (S := S) d m).comp (jetCopy d m (1 : Fin 2)) = AlgHom.id S _ := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk]

theorem second_axis_at_first_copy (m : ℕ) : (axis1 (S := S) d m).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id S _ := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk]

theorem second_axis_at_second_copy (m : ℕ) : (axis1 (S := S) d m).comp (jetCopy d m (1 : Fin 2)) =
    (Algebra.ofId S (Jet S (Fin 1 × Fin d) m)).comp jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetSubstP, jetCopy, jetMap_mk, jetAug_X]

end Axes

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev e0 : Sp S ⟶ t.G.left := (1 : overAt x0 S ⟶ t.G).left

theorem exists_chart_covering_index : ∃ i0 : t.PP.L.ι, (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤ := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_chart_top (V := S) t.PP.L t.PP.isLB (fun _ : Fin 1 => e0 t x0)
    (fun _ => 1)
  exact ⟨j 0, top_unique (by rw [← hj]; exact LB.wchart_le _ _ j 0)⟩

theorem vec2 {α : Type*} (f : Fin 2 → α) : (![f 0, f 1] : Fin 2 → α) = f := by
  funext i
  fin_cases i <;> rfl

variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

variable {t x0 d x} in
theorem jpt_aug (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ jptG t x0 d x m i = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, aug_copy, hch.zero m]

variable {t x0 d x} in
theorem jpt_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by
  have hc : (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) := by
    apply jet_hom_ext
    intro p
    rfl
  rw [jptG, jptG, ← Category.assoc, homAt_comp, hc, ← homAt_comp, Category.assoc, hch.trunc m]

theorem psum_aug {m n : ℕ} (xs : Fin n → (jOG x0 d m n ⟶ t.G))
    (hxs : ∀ i, homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ xs i = 1) (I : Finset (Fin n)) :
    homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ psum t.G xs I = 1 :=
  (psum_hom (preHom (homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S))) xs I).trans
    ((congrArg (fun f => psum t.G f I) (funext hxs)).trans (psum_one t.G I))

theorem wchart_top (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) {m n : ℕ}
    (xs : Fin n → (jOG x0 d m n ⟶ t.G))
    (hxs : ∀ i, homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ xs i = 1) :
    LB.wchart t.PP.L (cφG t xs) (fun _ => i0) = ⊤ := by
  refine top_unique fun y _ => Set.mem_iInter.2 fun I => ?_
  have h := pre_top m (t.PP.L.U i0) (cφG t xs I) (e0 t x0)
    (congrArg Over.Hom.left (psum_aug t x0 d xs hxs I.down)) hi0
  have : y ∈ (cφG t xs I) ⁻¹ᵁ t.PP.L.U i0 := by rw [h]; trivial
  exact this

variable {t x0 d x} in

def fr (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) (m : ℕ) :
    LB.Gen (LB.LinComb t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2)) :=
  cgen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (fun _ => i0)
    (wchart_top t x0 d i0 hi0 _ fun i => by rw [vec2 (fun i => jptG t x0 d x m i)]; exact jpt_aug hch m i)

variable {t x0 d x} in
theorem fr_trunc (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    FrTrunc t x0 d x (fr hch i0 hi0) := fun m => corr_of_val t.PP.isLB fun y J hJ => by
  have hmor : ∀ I : ULift (Finset (Fin 2)),
      (𝟙 _ ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) ≫
        cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] I =
      𝟙 _ ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
    intro I
    rw [Category.id_comp, Category.id_comp, vec2 (fun i => jptG t x0 d x (m + 1) i),
      vec2 (fun i => jptG t x0 d x m i)]
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    exact congrArg (fun f => psum t.G f I.down) (funext fun i => jpt_trunc hch m i)
  exact (val_pull hJ _ _ _).trans ((val_cgen _ _ _ _ _ _ y J hJ).trans
    (Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun ψ => cv t.PP.L i0 y J ψ ^ cε 2 I) (hmor I))
      (val_cgen _ _ _ _ _ _ y J hJ).symm))

variable {t x0 d x} in
theorem fr_axes (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    FrAxes t x0 d x (fr hch i0 hi0) := by
  have hL := t.PP.isLB
  have key : ∀ (m : ℕ) (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m) (a b : jOG x0 d m 1 ⟶ t.G),
      homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2) = a → homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2) = b → (a = 1 ∨ b = 1) →
      LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)])
        (cε 2) (fr hch i0 hi0 m) (homAt x0 σ).left) (LB.oneGen t.PP.L) := by
    intro m σ a b ha hb hab
    refine corr_of_val hL fun y J hJ => ?_
    refine (val_pull hJ _ _ _).trans ((val_cgen _ _ _ _ _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    have hI : ∀ I : ULift (Finset (Fin 2)), (𝟙 _ ≫ (homAt x0 σ).left) ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I = (psum t.G ![a, b] I.down).left := by
      intro I
      rw [Category.id_comp]
      simp only [cφG, ← Over.comp_left]
      refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
      refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
      fin_cases i
      · exact ha
      · exact hb
    rw [Finset.prod_congr rfl fun I _ => congrArg (fun ψ => cv t.PP.L i0 y J ψ ^ cε 2 I) (hI I)]
    have hc := prod_cube2 t.G (fun p : jOG x0 d m 1 ⟶ t.G => cv t.PP.L i0 y J p.left) ![a, b]
    rw [hc]
    rcases hab with rfl | rfl <;> simp
  intro m
  refine ⟨key m (axis0 d m) 1 (x m) ?_ ?_ (Or.inl rfl), key m (axis1 d m) (x m) 1 ?_ ?_ (Or.inr rfl)⟩
  · rw [jptG, ← Category.assoc, homAt_comp, first_axis_at_first_copy, ← homAt_comp, Category.assoc, hch.zero m]
    exact map_one (preHom (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) m))))
  · rw [jptG, ← Category.assoc, homAt_comp, first_axis_at_second_copy, homAt_id, Category.id_comp]
  · rw [jptG, ← Category.assoc, homAt_comp, second_axis_at_first_copy, homAt_id, Category.id_comp]
  · rw [jptG, ← Category.assoc, homAt_comp, second_axis_at_second_copy, ← homAt_comp, Category.assoc, hch.zero m]
    exact map_one (preHom (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) m))))

end Frames

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
