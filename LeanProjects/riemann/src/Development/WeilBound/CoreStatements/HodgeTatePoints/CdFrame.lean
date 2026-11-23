import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPf
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero

set_option autoImplicit false

noncomputable section

namespace PositivityTheory.HtPt.Cd

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

attribute [local instance] Over.cartesianMonoidalCategory

theorem pre_topA {S Idx : Type} [CommRing S] (m : ℕ) {X : Scheme.{0}} (U : X.Opens) (ψ : Sp (Jet S Idx m) ⟶ X)
    (e : Sp S ⟶ X) (he : spMap ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S) ≫ ψ = e) (hU : e ⁻¹ᵁ U = ⊤) :
    ψ ⁻¹ᵁ U = ⊤ := by
  refine top_unique fun y _ => ?_
  let s : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (Jet S Idx m)) y
  have h1 : (s : Sp S) ∈ e ⁻¹ᵁ U := by rw [hU]; trivial
  have h2 : PrimeSpectrum.comap ((jetAug : Jet S Idx m →ₐ[S] S) : Jet S Idx m →+* S) s = y := by
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    have hk : a - algebraMap S _ ((jetAug : Jet S Idx m →ₐ[S] S) a) ∈
        RingHom.ker (jetAug : Jet S Idx m →ₐ[S] S) := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
    have hn : (a - algebraMap S _ ((jetAug : Jet S Idx m →ₐ[S] S) a)) ^ (m + 1) = 0 := by
      have := Ideal.pow_mem_pow hk (m + 1)
      have e0 : RingHom.ker (jetAug : Jet S Idx m →ₐ[S] S) ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow (R := S) Idx m
      rwa [e0] at this
    have hm : a - algebraMap S _ ((jetAug : Jet S Idx m →ₐ[S] S) a) ∈ PrimeSpectrum.asIdeal y :=
      y.isPrime.mem_of_pow_mem (m + 1) (by rw [hn]; exact Ideal.zero_mem _)
    change algebraMap S _ ((jetAug : Jet S Idx m →ₐ[S] S) a) ∈ PrimeSpectrum.asIdeal y ↔ a ∈ PrimeSpectrum.asIdeal y
    constructor
    · intro h; simpa using Ideal.add_mem _ hm h
    · intro h; simpa using Ideal.sub_mem _ h hm
  rw [← he] at h1
  show ψ.base y ∈ U
  rw [← h2]
  exact h1

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

variable {t x0 d x} in
theorem jpt_augA (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ jptG t x0 d x m i = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, aug_copy, hch.zero m]

variable {t x0 d x} in
theorem jpt_truncA (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by
  have hc : (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) := by
    apply jet_hom_ext
    intro p
    rfl
  rw [jptG, jptG, ← Category.assoc, homAt_comp, hc, ← homAt_comp, Category.assoc, hch.trunc m]

theorem psum_augA {m n : ℕ} (xs : Fin n → (jOG x0 d m n ⟶ t.G))
    (hxs : ∀ i, homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ xs i = 1) (I : Finset (Fin n)) :
    homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ psum t.G xs I = 1 :=
  (psum_hom (preHom (homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S))) xs I).trans
    ((congrArg (fun f => psum t.G f I) (funext hxs)).trans (psum_one t.G I))

theorem wchart_topA (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) {m n : ℕ}
    (xs : Fin n → (jOG x0 d m n ⟶ t.G))
    (hxs : ∀ i, homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) ≫ xs i = 1) :
    LB.wchart t.PP.L (cφG t xs) (fun _ => i0) = ⊤ := by
  refine top_unique fun y _ => Set.mem_iInter.2 fun I => ?_
  have h := pre_topA m (t.PP.L.U i0) (cφG t xs I) (e0 t x0)
    (congrArg Over.Hom.left (psum_augA t x0 d xs hxs I.down)) hi0
  have : y ∈ (cφG t xs I) ⁻¹ᵁ t.PP.L.U i0 := by rw [h]; trivial
  exact this

variable {t x0 d x} in

def frA (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) (m : ℕ) :
    LB.Gen (LB.LinComb t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2)) :=
  cgen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (fun _ => i0)
    (wchart_topA t x0 d i0 hi0 _ fun i => by rw [vec2 (fun i => jptG t x0 d x m i)]; exact jpt_augA hch m i)

variable {t x0 d x} in
theorem fr_truncA (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    FrTrunc t x0 d x (frA hch i0 hi0) := fun m => corr_of_val t.PP.isLB fun y J hJ => by
  have hmor : ∀ I : ULift (Finset (Fin 2)),
      (𝟙 _ ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) ≫
        cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] I =
      𝟙 _ ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
    intro I
    rw [Category.id_comp, Category.id_comp, vec2 (fun i => jptG t x0 d x (m + 1) i),
      vec2 (fun i => jptG t x0 d x m i)]
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    exact congrArg (fun f => psum t.G f I.down) (funext fun i => jpt_truncA hch m i)
  exact (val_pull hJ _ _ _).trans ((val_cgen _ _ _ _ _ _ y J hJ).trans
    (Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun ψ => cv t.PP.L i0 y J ψ ^ cε 2 I) (hmor I))
      (val_cgen _ _ _ _ _ _ y J hJ).symm))

variable {t x0 d x} in
theorem fr_axesA (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    FrAxes t x0 d x (frA hch i0 hi0) := by
  have hL := t.PP.isLB
  have key : ∀ (m : ℕ) (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m) (a b : jOG x0 d m 1 ⟶ t.G),
      homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2) = a → homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2) = b → (a = 1 ∨ b = 1) →
      LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)])
        (cε 2) (frA hch i0 hi0 m) (homAt x0 σ).left) (LB.oneGen t.PP.L) := by
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

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem triple_point_truncation_alt (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (i j k : Fin 3) :
    (ρn x0 d 3 m).left ≫ (P3 (x := x) (m + 1) i j k).left = 𝟙 _ ≫ (P3 (x := x) m i j k).left := by
  rw [← Over.comp_left, Category.id_comp, P3, P3, comp_lift, comp_lift, jpt_truncA hch, jpt_truncA hch, jpt_truncA hch]

theorem pair_point_truncation_alt (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) :
    (ρn x0 d 2 m).left ≫ (lift (jptG t x0 d x (m + 1) (0 : Fin 2)) (jptG t x0 d x (m + 1) (1 : Fin 2))).left =
      𝟙 _ ≫ (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left := by
  rw [← Over.comp_left, Category.id_comp, comp_lift, jpt_truncA hch, jpt_truncA hch]

end Main

section Ex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem val_fr_oneA (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤)
    (m : ℕ) {T : Over X0} (ρ : T ⟶ jOG x0 d m 2) (a b : T ⟶ t.G)
    (ha : ρ ≫ jptG t x0 d x m (0 : Fin 2) = a) (hb : ρ ≫ jptG t x0 d x m (1 : Fin 2) = b) (hab : a = 1 ∨ b = 1)
    (z : T.left) (J : (T.left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L z J) :
    val (frA hch i0 hi0 m) ρ.left z J = 1 := by
  refine (val_cgen _ _ _ _ _ _ z J hJ).trans ?_
  have hI : ∀ I : ULift.{0} (Finset (Fin 2)), ρ.left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I = (psum t.G ![a, b] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact ha
    · exact hb
  rw [Finset.prod_congr rfl fun I _ => congrArg (fun ψ => cv t.PP.L i0 z J ψ ^ cε 2 I) (hI I)]
  rcases hab with rfl | rfl
  · exact cube_one_left t (fun p : T ⟶ t.G => cv t.PP.L i0 z J p.left) b
  · exact cube_one_right t (fun p : T ⟶ t.G => cv t.PP.L i0 z J p.left) a

set_option maxHeartbeats 4000000 in
theorem ex_ph1A (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    ∃ ph : MvPowerSeries (Fin 3 × Fin d) S, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ,
      (u : Jet S (Fin 3 × Fin d) m) = psJet m ph ∧ LB.Gen.Corr t.PP.L _ _ _ _
        (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
          (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3))
            (jptG t x0 d x m (2 : Fin 3)))).left)
        (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (frA hch i0 hi0) m ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  have hL := t.PP.isLB
  have heg : ∀ m, (frA hch i0 hi0 m).IsGen := fun m => cgen_isGen t.PP.L hL _ _ _ _
  have htr := fr_truncA hch i0 hi0
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x (frA hch i0 hi0) m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp

  have hB3 : ∀ (φ1 φ2 φ3 : ℕ → Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S),
      (∀ m i j, φ1 (m + 1) i j - φ1 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ2 (m + 1) i j - φ2 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ3 (m + 1) i j - φ3 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      ∀ m y J, Good t.PP.L y J →
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (frA hch i0 hi0) (m + 1) (φ1 (m + 1)))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) (m + 1) (φ2 (m + 1))))
            (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) (m + 1) (φ3 (m + 1)))))) (ρn x0 d 3 m).left y J =
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (frA hch i0 hi0) m (φ1 m))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m (φ2 m)))
            (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m (φ3 m))))) (𝟙 _) y J := by
    intro φ1 φ2 φ3 h1 h2 h3 m y J hJ
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, val_mul hJ, val_mul hJ, val_inv, val_inv,
      pe_trunc t x0 d htr φ1 h1 m y J hJ, pe_trunc t x0 d htr φ2 h2 m y J hJ, pe_trunc t x0 d htr φ3 h3 m y J hJ]
  obtain ⟨ph1, hph1⟩ := exists_series t x0 d (n := 3) _ _ _ _
    (fun m => LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (P3 (x := x) m 0 1 2).left)
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ t.cub.isGen _)
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (peG t x0 d x (frA hch i0 hi0) m ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (LB.mulGen t.PP.L _ _ _ _
        (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))
        (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m
          ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hpe m _) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _)) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _))))
    (fun m U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, th_pt, pe_pt, pt_sub, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_law hch, zpow_neg, Finset.prod_inv_distrib]
      erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      rw [prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
        prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      have ha : jptG t x0 d x m (0 : Fin 3) * jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) =
          jptG t x0 d x m (0 : Fin 3) * (jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3)) := _root_.mul_assoc _ _ _
      apply ofMul_eq
      simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
      erw [ha]
      abel!)
    (fun m y J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J) (triple_point_truncation_alt hch m 0 1 2)).trans
      (val_pull hJ _ _ _).symm))
    (fun m y J hJ => hB3 (fun m => ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX m _ j])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
  exact ⟨_, hph1⟩

set_option maxHeartbeats 4000000 in
theorem ex_ph2A (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    ∃ ph : MvPowerSeries (Fin 3 × Fin d) S, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ,
      (u : Jet S (Fin 3 × Fin d) m) = psJet m ph ∧ LB.Gen.Corr t.PP.L _ _ _ _
        (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
          (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3))
            (jptG t x0 d x m (0 : Fin 3)))).left)
        (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (frA hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  have hL := t.PP.isLB
  have heg : ∀ m, (frA hch i0 hi0 m).IsGen := fun m => cgen_isGen t.PP.L hL _ _ _ _
  have htr := fr_truncA hch i0 hi0
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x (frA hch i0 hi0) m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp

  have hB3 : ∀ (φ1 φ2 φ3 : ℕ → Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S),
      (∀ m i j, φ1 (m + 1) i j - φ1 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ2 (m + 1) i j - φ2 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ3 (m + 1) i j - φ3 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      ∀ m y J, Good t.PP.L y J →
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (frA hch i0 hi0) (m + 1) (φ1 (m + 1)))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) (m + 1) (φ2 (m + 1))))
            (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) (m + 1) (φ3 (m + 1)))))) (ρn x0 d 3 m).left y J =
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (frA hch i0 hi0) m (φ1 m))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m (φ2 m)))
            (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m (φ3 m))))) (𝟙 _) y J := by
    intro φ1 φ2 φ3 h1 h2 h3 m y J hJ
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, val_mul hJ, val_mul hJ, val_inv, val_inv,
      pe_trunc t x0 d htr φ1 h1 m y J hJ, pe_trunc t x0 d htr φ2 h2 m y J hJ, pe_trunc t x0 d htr φ3 h3 m y J hJ]
  obtain ⟨ph2, hph2⟩ := exists_series t x0 d (n := 3) _ _ _ _
    (fun m => LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (P3 (x := x) m 1 2 0).left)
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ t.cub.isGen _)
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (peG t x0 d x (frA hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
      (LB.mulGen t.PP.L _ _ _ _
        (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)]))
        (LB.invGen t.PP.L _ _ (peG t x0 d x (frA hch i0 hi0) m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hpe m _) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _)) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _))))
    (fun m U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, th_pt, pe_pt, pt_sub, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_law hch, zpow_neg, Finset.prod_inv_distrib]
      erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      rw [prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
        prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      have ha2 : jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3) =
          jptG t x0 d x m (1 : Fin 3) * (jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3)) := _root_.mul_assoc _ _ _
      apply ofMul_eq
      simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
      erw [ha2]
      abel!)
    (fun m y J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J) (triple_point_truncation_alt hch m 1 2 0)).trans
      (val_pull hJ _ _ _).symm))
    (fun m y J hJ => hB3 (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m i j => by fin_cases i; exacts [hXX m _ j, psIn_succ_sub m _ _])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
  exact ⟨_, hph2⟩

set_option maxHeartbeats 4000000 in
theorem ex_syA (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    ∃ sy : MvPowerSeries (Fin 2 × Fin d) S, ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ,
      (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (frA hch i0 hi0 m)
        (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x (frA hch i0 hi0) m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  have hL := t.PP.isLB
  have heg : ∀ m, (frA hch i0 hi0 m).IsGen := fun m => cgen_isGen t.PP.L hL _ _ _ _
  have htr := fr_truncA hch i0 hi0
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x (frA hch i0 hi0) m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  obtain ⟨sy, hsy⟩ := exists_series t x0 d (n := 2) _ _ _ _
    (fun m => peG t x0 d x (frA hch i0 hi0) m
      ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])
    (fun m => hpe m _) (fun m => frA hch i0 hi0 m) heg
    (fun m U _ h => by
      try simp only [pe_pt, pt_sub, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pt_X]
      try simp only [cφG]
      rw [prod_cube2_swap (fun p : jOG x0 d m 2 ⟶ t.G => h p.left)]
      erw [prod_cube2 t.G (fun p : jOG x0 d m 2 ⟶ t.G => h p.left)]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      apply ofMul_eq
      simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
      abel!)
    (fun m y J hJ => pe_trunc t x0 d htr
      (fun _ => ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
    (fun m y J hJ => (congrArg (fun r => val (frA hch i0 hi0 (m + 1)) r y J) (Category.id_comp _).symm).trans
      ((val_pull hJ _ _ _).symm.trans (val_corr hJ (htr m) _)))
  have uinv : ∀ {m : ℕ} (u : (Jet S (Fin 2 × Fin d) m)ˣ), unitΓ u⁻¹ = (unitΓ u)⁻¹ := fun u => map_inv _ u
  have hsy' : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
      LB.Gen.Corr t.PP.L _ _ _ _ (frA hch i0 hi0 m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x (frA hch i0 hi0) m
        ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
    intro m
    obtain ⟨u, hu, hc⟩ := hsy m
    refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
    have e1 := (val_corr hJ hc (𝟙 _)).trans (val_scale t _ _ _ _ _ y J hJ)
    refine Eq.trans ?_ (val_scale t _ _ _ _ _ y J hJ).symm
    rw [e1, uinv, map_inv, inv_mul_cancel_left]
  exact ⟨sy, hsy'⟩

set_option maxHeartbeats 4000000 in
theorem ex_adA (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) (a : 𝓞 E)
    (wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I))) (hwLg : wL.IsGen)
    (hwL0 : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over X0)).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val wL (r ≫ (zz t).left) z J = 1) :
    ∃ ad : MvPowerSeries (Fin 2 × Fin d) S, MvPowerSeries.constantCoeff ad = 1 ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ,
      (u : Jet S (Fin 2 × Fin d) m) = psJet m ad ∧ LB.Gen.Corr t.PP.L _ _ _ _
        (LB.mulGen t.PP.L _ _ _ _
          (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
          (peG t x0 d x (frA hch i0 hi0) m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
        (scaleGenG t _ _ (unitΓ u) (peG t x0 d x (frA hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])) := by
  have hL := t.PP.isLB
  have heg : ∀ m, (frA hch i0 hi0 m).IsGen := fun m => cgen_isGen t.PP.L hL _ _ _ _
  have htr := fr_truncA hch i0 hi0
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x (frA hch i0 hi0) m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  obtain ⟨ad, had⟩ := exists_series t x0 d (n := 2) _ _ _ _
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
      (peG t x0 d x (frA hch i0 hi0) m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwLg _)
      (hpe m _))
    (fun m => peG t x0 d x (frA hch i0 hi0) m
      ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])
    (fun m => hpe m _)
    (fun m U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_act hch, zpow_neg, Finset.prod_inv_distrib]
      simp only [inv_mul_cancel_right])
    (fun m y J hJ => (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans ((congrArg (fun r => val wL r y J) (pair_point_truncation_alt hch m)).trans (val_pull hJ _ _ _).symm))
      (pe_trunc t x0 d htr
        (fun m => ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
        (fun m i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX m _ j]) m y J hJ))
      (val_mul hJ _ _ _).symm))
    (fun m y J hJ => pe_trunc t x0 d htr
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])
      (fun m i j => by fin_cases i; exacts [hXX m _ j, psIn_succ_sub m _ _]) m y J hJ)
  have hx0 : x 0 = 1 := frame_origin_jet_one hch
  have hj0 : ∀ {n : ℕ} (i : Fin n), jptG t x0 d x 0 i = 1 := fun i => by
    rw [jptG, hx0]
    exact map_one (preHom _)
  have hadc : MvPowerSeries.constantCoeff ad = 1 := by
    obtain ⟨u, hu, hc⟩ := had 0
    have hU : unitΓ u = 1 := by
      refine unit_ext (V := ⊤) fun y _ => ?_
      choose I hI using fun χ : (jOG x0 d 0 2).left ⟶ t.G.left => exists_chart hL (χ y)
      have e1 := (val_corr hI hc (𝟙 _)).trans (val_scale t _ _ _ _ _ y I hI)
      have hl : (𝟙 _ ≫ (lift (jptG t x0 d x 0 (0 : Fin 2)) (jptG t x0 d x 0 (1 : Fin 2))).left) =
          ((𝟙 _ ≫ (toUnit (jOG x0 d 0 2)).left) ≫ (zz t).left) := by
        rw [Category.id_comp, Category.id_comp, ← Over.comp_left, comp_lift, hj0, hj0]
        rfl
      have hA1 : val (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x 0 (0 : Fin 2)) (jptG t x0 d x 0 (1 : Fin 2))).left)
          (𝟙 _) y I = 1 := by
        refine (val_pull hI _ _ _).trans ?_
        rw [hl]
        exact hwL0 _ _ y I hI
      have hA2 : val (peG t x0 d x (frA hch i0 hi0) 0
          ![fun j => psIn d 0 ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (𝟙 _) y I = 1 :=
        (val_pull hI _ _ _).trans ((congrArg (fun r => val (frA hch i0 hi0 0) r y I) (Category.id_comp _)).trans
          (val_fr_oneA hch i0 hi0 0 (T := jOG x0 d 0 2) _ (1 ≫ t.act.act a) 1
            (by rw [pt_sub]; simp only [Matrix.cons_val_zero]; rw [pt_act hch, hj0])
            (by rw [pt_sub]; simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]; rw [pt_X, hj0]) (Or.inr rfl) y I hI))
      have hB : val (peG t x0 d x (frA hch i0 hi0) 0
          ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 0 ![1] (act (H.bar a) j)]) (𝟙 _) y I = 1 :=
        (val_pull hI _ _ _).trans ((congrArg (fun r => val (frA hch i0 hi0 0) r y I) (Category.id_comp _)).trans
          (val_fr_oneA hch i0 hi0 0 (T := jOG x0 d 0 2) _ 1 (1 ≫ t.act.act (H.bar a))
            (by rw [pt_sub]; simp only [Matrix.cons_val_zero]; rw [pt_X, hj0])
            (by rw [pt_sub]; simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]; rw [pt_act hch, hj0]) (Or.inl rfl)
            y I hI))
      rw [val_mul hI, hA1, hA2, hB, _root_.one_mul, _root_.mul_one] at e1
      rw [map_one]
      exact e1.symm
    have hu1 : (u : Jet S (Fin 2 × Fin d) 0) = 1 := by
      apply toΓ_injective
      rw [map_one]
      exact congrArg Units.val hU
    show MvPowerSeries.coeff 0 ad = 1
    rw [← coeff_psTrunc 0 ad 0 le_rfl]
    have h0 := hu.symm.trans hu1
    rw [psJet, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at h0
    have h1 := coeff_eq_zero_of_mem h0 (e := 0) (by simp)
    rw [MvPolynomial.coeff_sub, sub_eq_zero, MvPolynomial.coeff_one, if_pos rfl] at h1
    exact h1
  exact ⟨ad, hadc, had⟩

end Ex

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem frame_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : Germ.FGLaw S d) (A : Germ.OAct (𝓞 E) G) (tg : Fin d → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : Fin d → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (c : t.PP.L.ι), IsChartG t x0 d G.F A.act tg uvec x → Set.range (x0 ≫ eSec t.G) ⊆ (t.PP.L.U c : Set t.G.left) → ∃ (e : ∀ m, FrTyG t x0 d x m) (ph1 ph2 : Germ.PS S 3 d) (sy : Germ.PS S 2 d) (ad : 𝓞 E → Germ.PS S 2 d), IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e ∧ ∀ a, MvPowerSeries.constantCoeff (ad a) = 1 := by
  intro E _ _ _ H X0 t S _ x0 d G A tg uvec x i0 hch hc
  have hi0 : (GermB.e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤ := by
    have e : GermB.e0 t x0 = x0 ≫ eSec t.G := by
      show (spMap (algebraMap S S) ≫ x0) ≫ eSec t.G = _
      simp [spMap]
    rw [e]
    exact top_unique fun y _ => hc ⟨y, rfl⟩
  choose wL hwLg hwL0 using fun a => GermB.exists_wL t a
  obtain ⟨ph1, hph1⟩ := ex_ph1A hch i0 hi0
  obtain ⟨ph2, hph2⟩ := ex_ph2A hch i0 hi0
  obtain ⟨sy, hsy⟩ := ex_syA hch i0 hi0
  choose ad hadc had using fun a => ex_adA hch i0 hi0 a (wL a) (hwLg a) (hwL0 a)
  exact ⟨frA hch i0 hi0, ph1, ph2, sy, ad,
    ⟨fun m => GermB.cgen_isGen t.PP.L t.PP.isLB _ _ _ _, hph1, hph2, hsy, fun a => ⟨wL a, hwLg a, had a⟩⟩,
    fr_truncA hch i0 hi0, fr_axesA hch i0 hi0, hadc⟩

end PositivityTheory.HtPt.Cd
