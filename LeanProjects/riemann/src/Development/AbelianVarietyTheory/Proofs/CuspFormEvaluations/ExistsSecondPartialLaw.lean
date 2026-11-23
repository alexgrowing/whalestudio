import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

noncomputable section

namespace GlobalTheory.SecondPartialLaw

theorem prod_cube3 {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {M : Type} [CommGroup M]
    (h : (T ⟶ G) → M) (xs : Fin 3 → (T ⟶ G)) :
    ∏ I : thK, h (psum G xs I.down) ^ thε I =
      (h 1)⁻¹ * h (xs 0 * 1) * h (xs 1 * 1) * h (xs 2 * 1) * (h (xs 0 * (xs 1 * 1)))⁻¹ * (h (xs 0 * (xs 2 * 1)))⁻¹ *
        (h (xs 1 * (xs 2 * 1)))⁻¹ * h (xs 0 * (xs 1 * (xs 2 * 1))) := by
  refine (Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _
    (fun I : Finset (Fin 3) => h (psum G xs I) ^ thε ⟨I⟩) (fun _ => rfl)).trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  have c0 : thε (⟨∅⟩ : thK) = -1 := rfl
  have c1 : thε (⟨{0}⟩ : thK) = 1 := rfl
  have c2 : thε (⟨{1}⟩ : thK) = 1 := rfl
  have c3 : thε (⟨{2}⟩ : thK) = 1 := rfl
  have c4 : thε (⟨{0, 1}⟩ : thK) = -1 := rfl
  have c5 : thε (⟨{0, 2}⟩ : thK) = -1 := rfl
  have c6 : thε (⟨{1, 2}⟩ : thK) = -1 := rfl
  have c7 : thε (⟨{0, 1, 2}⟩ : thK) = 1 := rfl
  have p0 : psum G xs ∅ = 1 := rfl
  have p1 : psum G xs {0} = xs 0 * 1 := rfl
  have p2 : psum G xs {1} = xs 1 * 1 := rfl
  have p3 : psum G xs {2} = xs 2 * 1 := rfl
  have p4 : psum G xs {0, 1} = xs 0 * (xs 1 * 1) := rfl
  have p5 : psum G xs {0, 2} = xs 0 * (xs 2 * 1) := rfl
  have p6 : psum G xs {1, 2} = xs 1 * (xs 2 * 1) := rfl
  have p7 : psum G xs {0, 1, 2} = xs 0 * (xs 1 * (xs 2 * 1)) := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7, p0, p1, p2, p3, p4, p5, p6, p7]
  simp only [zpow_one, zpow_neg, _root_.mul_assoc]

section Pts

variable {S : Type} [CommRing S] (d : ℕ)

theorem subst_copy (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) =
      jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2) := by
  apply jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetSubstP, jetCopy, jetMap_mk, MvPolynomial.aeval_X]

theorem substX (m : ℕ) {n : ℕ} (k : Fin n) :
    jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S)) =
      jetCopy d m k := by
  apply jet_hom_ext
  intro p
  simp [jetSubstP, jetCopy, jetMap_mk]

def jetRen (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m :=
  jetMap (fun q : Fin n × Fin d => MvPolynomial.X (r q.1, q.2)) fun _ => X_mem_orig _

theorem ren_copy (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (i : Fin n) :
    (jetRen (S := S) d m r).comp (jetCopy d m i) = jetCopy d m (r i) := by
  apply jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetRen, jetCopy, jetMap_mk, MvPolynomial.aeval_X]

theorem ren_one (m : ℕ) {n' : ℕ} (r : Fin 1 → Fin n') : jetRen (S := S) d m r = jetCopy d m (r 0) := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [jetRen, jetCopy, jetMap_mk, MvPolynomial.aeval_X]

theorem subst_psIn (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (g : Fin d → MvPowerSeries (Fin n × Fin d) S) :
    jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (g p.2)) =
      (jetRen d m r).comp (jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (g p.2))) := by
  have hr : (MvPolynomial.aeval fun q : Fin n × Fin d => (MvPolynomial.X (r q.1, q.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.rename fun p : Fin n × Fin d => (r p.1, p.2) := MvPolynomial.algHom_ext fun q => by simp
  apply jet_hom_ext
  intro p
  simp only [jetSubstP, jetRen, AlgHom.comp_apply, jetMap_mk, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, psIn, MvPolynomial.constantCoeff_rename, hr, MvPolynomial.rename_C]

end Pts

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem pt_sub (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    homAt x0 (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)) ≫ jptG t x0 d x m i =
      homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2)) ≫ x m := by
  rw [jptG, ← Category.assoc, homAt_comp, subst_copy]

theorem pt_X (m : ℕ) {n : ℕ} (k : Fin n) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S))) ≫ x m =
      jptG t x0 d x m k := by
  rw [substX]
  try rfl

theorem pt_law (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (r : Fin 2 → Fin n) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (F p.2))) ≫ x m =
      jptG t x0 d x m (r 0) * jptG t x0 d x m (r 1) := by
  have hk : ∀ i, homAt x0 (jetRen d m r) ≫ jptG t x0 d x m i = jptG t x0 d x m (r i) := fun i => by
    rw [jptG, jptG, ← Category.assoc, homAt_comp, ren_copy]
  rw [subst_psIn, ← homAt_comp, Category.assoc, hch.law m, MonObj.comp_mul, hk, hk]

theorem pe_pt (m : ℕ) {n : ℕ} (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) (I : ULift.{0} (Finset (Fin 2))) :
    (homAt x0 σ).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I =
      (psum t.G ![homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2), homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2)] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i <;> rfl

theorem th_pt {T : Over X0} (a b c : T ⟶ t.G) (I : thK) :
    (lift a (lift b c)).left ≫ thφ t.G (x3 t.G) I = (psum t.G ![a, b, c] I.down).left := by
  simp only [thφ, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a (lift b c) ≫ fst t.G (t.G ⊗ t.G) = a
    exact lift_fst _ _
  · show lift a (lift b c) ≫ (snd t.G (t.G ⊗ t.G) ≫ fst t.G t.G) = b
    rw [lift_snd_assoc, lift_fst]
  · show lift a (lift b c) ≫ (snd t.G (t.G ⊗ t.G) ≫ snd t.G t.G) = c
    rw [lift_snd_assoc, lift_snd]

theorem ofMul_eq {M : Type} [CommGroup M] {a b : M} (h : Additive.ofMul a = Additive.ofMul b) : a = b :=
  Additive.ofMul.injective h

theorem prod_cube2_swap {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (xs : Fin 2 → (T ⟶ t.G)) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G xs I.down) ^ cε 2 I =
      h 1 * (h (xs 0 * 1))⁻¹ * (h (xs 1 * 1))⁻¹ * h (xs 1 * (xs 0 * 1)) := by
  rw [prod_cube2]
  simp only [_root_.mul_one]
  rw [_root_.mul_comm (xs 0) (xs 1)]

theorem jpt_trunc_ring (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by
  have hc : (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) := by
    apply jet_hom_ext
    intro p
    rfl
  rw [jptG, jptG, ← Category.assoc, homAt_comp, hc, ← homAt_comp, Category.assoc, hch.trunc m]

end Chart

theorem triplePt_trunc_second {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
    {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
    {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
    (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (i j k : Fin 3) :
    (ρn x0 d 3 m).left ≫ (lift (jptG t x0 d x (m + 1) i) (lift (jptG t x0 d x (m + 1) j) (jptG t x0 d x (m + 1) k))).left =
      𝟙 _ ≫ (lift (jptG t x0 d x m i) (lift (jptG t x0 d x m j) (jptG t x0 d x m k))).left := by
  rw [← Over.comp_left, Category.id_comp, comp_lift, comp_lift, jpt_trunc_ring hch, jpt_trunc_ring hch, jpt_trunc_ring hch]

set_option maxHeartbeats 4000000 in

theorem exists_second_partial_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ph2 : PS S 3 d, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))) := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch e heg htr _
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x e m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  have hB3 : ∀ (φ1 φ2 φ3 : ℕ → Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S),
      (∀ m i j, φ1 (m + 1) i j - φ1 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ2 (m + 1) i j - φ2 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ3 (m + 1) i j - φ3 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      ∀ m y J, Good t.PP.L y J →
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e (m + 1) (φ1 (m + 1)))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e (m + 1) (φ2 (m + 1))))
            (LB.invGen t.PP.L _ _ (peG t x0 d x e (m + 1) (φ3 (m + 1)))))) (ρn x0 d 3 m).left y J =
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m (φ1 m))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m (φ2 m)))
            (LB.invGen t.PP.L _ _ (peG t x0 d x e m (φ3 m))))) (𝟙 _) y J := by
    intro φ1 φ2 φ3 h1 h2 h3 m y J hJ
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, val_mul hJ, val_mul hJ, val_inv, val_inv,
      pe_trunc t x0 d htr φ1 h1 m y J hJ, pe_trunc t x0 d htr φ2 h2 m y J hJ, pe_trunc t x0 d htr φ3 h3 m y J hJ]
  obtain ⟨ph2, hph2⟩ := exists_series t x0 d (n := 3) _ _ _ _
    (fun m => LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
      (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left)
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ t.cub.isGen _)
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
      (LB.mulGen t.PP.L _ _ _ _
        (LB.invGen t.PP.L _ _ (peG t x0 d x e m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)]))
        (LB.invGen t.PP.L _ _ (peG t x0 d x e m
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
    (fun m y J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J) (triplePt_trunc_second hch m 1 2 0)).trans
      (val_pull hJ _ _ _).symm))
    (fun m y J hJ => hB3 (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m i j => by fin_cases i; exacts [hXX m _ j, psIn_succ_sub m _ _])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
  exact ⟨_, hph2⟩

end GlobalTheory.SecondPartialLaw
