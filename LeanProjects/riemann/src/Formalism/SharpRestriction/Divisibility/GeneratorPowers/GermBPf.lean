import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

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

theorem pt_act (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (r : Fin 1 → Fin n) (a : 𝓞 E) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (act a p.2))) ≫ x m =
      jptG t x0 d x m (r 0) ≫ t.act.act a := by
  rw [subst_psIn, ← homAt_comp, Category.assoc, ← hch.act m a, ← Category.assoc, ren_one]
  try rfl

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

theorem wl_pt {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act c] I =
      (psum t.G ![a, b ≫ t.act.act c] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ fst t.G t.G = a
    exact lift_fst _ _
  · show lift a b ≫ (snd t.G t.G ≫ t.act.act c) = b ≫ t.act.act c
    exact lift_snd_assoc _ _ _

theorem wl_pt' {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G ≫ t.act.act c, snd t.G t.G] I =
      (psum t.G ![a ≫ t.act.act c, b] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ (fst t.G t.G ≫ t.act.act c) = a ≫ t.act.act c
    exact lift_fst_assoc _ _ _
  · show lift a b ≫ snd t.G t.G = b
    exact lift_snd _ _

end Chart

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] [IsLocalRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem ofMul_eq {M : Type} [CommGroup M] {a b : M} (h : Additive.ofMul a = Additive.ofMul b) : a = b :=
  Additive.ofMul.injective h

abbrev P3 (m : ℕ) (i j k : Fin 3) : jOG x0 d m 3 ⟶ t.G ⊗ t.G ⊗ t.G :=
  lift (jptG t x0 d x m i) (lift (jptG t x0 d x m j) (jptG t x0 d x m k))

theorem triple_point_truncation (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (i j k : Fin 3) :
    (ρn x0 d 3 m).left ≫ (P3 (x := x) (m + 1) i j k).left = 𝟙 _ ≫ (P3 (x := x) m i j k).left := by
  rw [← Over.comp_left, Category.id_comp, P3, P3, comp_lift, comp_lift, jpt_trunc hch, jpt_trunc hch, jpt_trunc hch]

theorem pair_point_truncation (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) :
    (ρn x0 d 2 m).left ≫ (lift (jptG t x0 d x (m + 1) (0 : Fin 2)) (jptG t x0 d x (m + 1) (1 : Fin 2))).left =
      𝟙 _ ≫ (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left := by
  rw [← Over.comp_left, Category.id_comp, comp_lift, jpt_trunc hch, jpt_trunc hch]

theorem prod_cube2_swap {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (xs : Fin 2 → (T ⟶ t.G)) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G xs I.down) ^ cε 2 I =
      h 1 * (h (xs 0 * 1))⁻¹ * (h (xs 1 * 1))⁻¹ * h (xs 1 * (xs 0 * 1)) := by
  rw [prod_cube2]
  simp only [_root_.mul_one]
  rw [_root_.mul_comm (xs 0) (xs 1)]

end Main

section X0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem frame_origin_jet_one (hch : IsChartG t x0 d F act tg uvec x) : x 0 = 1 := by
  have hj : (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)).comp jetAug = AlgHom.id S _ := by
    apply jet_hom_ext
    intro p
    rw [AlgHom.comp_apply, jetAug_X, map_zero, AlgHom.id_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using X_mem_orig (R := S) p)).symm
  calc x 0 = 𝟙 _ ≫ x 0 := (Category.id_comp _).symm
    _ = (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)) ≫ homAt x0 jetAug) ≫ x 0 := by
        rw [homAt_comp, hj, homAt_id]
    _ = homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)) ≫ 1 := by rw [Category.assoc, hch.zero 0]
    _ = 1 := map_one (preHom _)

end X0

section Ex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] [IsLocalRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem val_fr_one (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤)
    (m : ℕ) {T : Over X0} (ρ : T ⟶ jOG x0 d m 2) (a b : T ⟶ t.G)
    (ha : ρ ≫ jptG t x0 d x m (0 : Fin 2) = a) (hb : ρ ≫ jptG t x0 d x m (1 : Fin 2) = b) (hab : a = 1 ∨ b = 1)
    (z : T.left) (J : (T.left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L z J) :
    val (fr hch i0 hi0 m) ρ.left z J = 1 := by
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
theorem exists_first_face_unit (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    ∃ ph : MvPowerSeries (Fin 3 × Fin d) S, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ,
      (u : Jet S (Fin 3 × Fin d) m) = psJet m ph ∧ LB.Gen.Corr t.PP.L _ _ _ _
        (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
          (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3))
            (jptG t x0 d x m (2 : Fin 3)))).left)
        (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (fr hch i0 hi0) m ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  have hL := t.PP.isLB
  have heg : ∀ m, (fr hch i0 hi0 m).IsGen := fun m => cgen_isGen t.PP.L hL _ _ _ _
  have htr := fr_trunc hch i0 hi0
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x (fr hch i0 hi0) m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp

  have hB3 : ∀ (φ1 φ2 φ3 : ℕ → Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S),
      (∀ m i j, φ1 (m + 1) i j - φ1 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ2 (m + 1) i j - φ2 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ3 (m + 1) i j - φ3 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      ∀ m y J, Good t.PP.L y J →
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (fr hch i0 hi0) (m + 1) (φ1 (m + 1)))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) (m + 1) (φ2 (m + 1))))
            (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) (m + 1) (φ3 (m + 1)))))) (ρn x0 d 3 m).left y J =
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (fr hch i0 hi0) m (φ1 m))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m (φ2 m)))
            (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m (φ3 m))))) (𝟙 _) y J := by
    intro φ1 φ2 φ3 h1 h2 h3 m y J hJ
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, val_mul hJ, val_mul hJ, val_inv, val_inv,
      pe_trunc t x0 d htr φ1 h1 m y J hJ, pe_trunc t x0 d htr φ2 h2 m y J hJ, pe_trunc t x0 d htr φ3 h3 m y J hJ]
  obtain ⟨ph1, hph1⟩ := exists_series t x0 d (n := 3) _ _ _ _
    (fun m => LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (P3 (x := x) m 0 1 2).left)
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ t.cub.isGen _)
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (peG t x0 d x (fr hch i0 hi0) m ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (LB.mulGen t.PP.L _ _ _ _
        (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))
        (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m
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
    (fun m y J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J) (triple_point_truncation hch m 0 1 2)).trans
      (val_pull hJ _ _ _).symm))
    (fun m y J hJ => hB3 (fun m => ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX m _ j])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
  exact ⟨_, hph1⟩

set_option maxHeartbeats 4000000 in
theorem exists_second_face_unit (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    ∃ ph : MvPowerSeries (Fin 3 × Fin d) S, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ,
      (u : Jet S (Fin 3 × Fin d) m) = psJet m ph ∧ LB.Gen.Corr t.PP.L _ _ _ _
        (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
          (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3))
            (jptG t x0 d x m (0 : Fin 3)))).left)
        (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (fr hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  have hL := t.PP.isLB
  have heg : ∀ m, (fr hch i0 hi0 m).IsGen := fun m => cgen_isGen t.PP.L hL _ _ _ _
  have htr := fr_trunc hch i0 hi0
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x (fr hch i0 hi0) m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp

  have hB3 : ∀ (φ1 φ2 φ3 : ℕ → Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S),
      (∀ m i j, φ1 (m + 1) i j - φ1 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ2 (m + 1) i j - φ2 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ3 (m + 1) i j - φ3 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      ∀ m y J, Good t.PP.L y J →
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (fr hch i0 hi0) (m + 1) (φ1 (m + 1)))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) (m + 1) (φ2 (m + 1))))
            (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) (m + 1) (φ3 (m + 1)))))) (ρn x0 d 3 m).left y J =
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x (fr hch i0 hi0) m (φ1 m))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m (φ2 m)))
            (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m (φ3 m))))) (𝟙 _) y J := by
    intro φ1 φ2 φ3 h1 h2 h3 m y J hJ
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, val_mul hJ, val_mul hJ, val_inv, val_inv,
      pe_trunc t x0 d htr φ1 h1 m y J hJ, pe_trunc t x0 d htr φ2 h2 m y J hJ, pe_trunc t x0 d htr φ3 h3 m y J hJ]
  obtain ⟨ph2, hph2⟩ := exists_series t x0 d (n := 3) _ _ _ _
    (fun m => LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (P3 (x := x) m 1 2 0).left)
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ t.cub.isGen _)
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (peG t x0 d x (fr hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
      (LB.mulGen t.PP.L _ _ _ _
        (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)]))
        (LB.invGen t.PP.L _ _ (peG t x0 d x (fr hch i0 hi0) m
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
    (fun m y J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J) (triple_point_truncation hch m 1 2 0)).trans
      (val_pull hJ _ _ _).symm))
    (fun m y J hJ => hB3 (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m i j => by fin_cases i; exacts [hXX m _ j, psIn_succ_sub m _ _])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
  exact ⟨_, hph2⟩

set_option maxHeartbeats 4000000 in
theorem ex_sy (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    ∃ sy : MvPowerSeries (Fin 2 × Fin d) S, ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ,
      (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (fr hch i0 hi0 m)
        (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x (fr hch i0 hi0) m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  have hL := t.PP.isLB
  have heg : ∀ m, (fr hch i0 hi0 m).IsGen := fun m => cgen_isGen t.PP.L hL _ _ _ _
  have htr := fr_trunc hch i0 hi0
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x (fr hch i0 hi0) m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  obtain ⟨sy, hsy⟩ := exists_series t x0 d (n := 2) _ _ _ _
    (fun m => peG t x0 d x (fr hch i0 hi0) m
      ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])
    (fun m => hpe m _) (fun m => fr hch i0 hi0 m) heg
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
    (fun m y J hJ => (congrArg (fun r => val (fr hch i0 hi0 (m + 1)) r y J) (Category.id_comp _).symm).trans
      ((val_pull hJ _ _ _).symm.trans (val_corr hJ (htr m) _)))
  have uinv : ∀ {m : ℕ} (u : (Jet S (Fin 2 × Fin d) m)ˣ), unitΓ u⁻¹ = (unitΓ u)⁻¹ := fun u => map_inv _ u
  have hsy' : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
      LB.Gen.Corr t.PP.L _ _ _ _ (fr hch i0 hi0 m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x (fr hch i0 hi0) m
        ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
    intro m
    obtain ⟨u, hu, hc⟩ := hsy m
    refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
    have e1 := (val_corr hJ hc (𝟙 _)).trans (val_scale t _ _ _ _ _ y J hJ)
    refine Eq.trans ?_ (val_scale t _ _ _ _ _ y J hJ).symm
    rw [e1, uinv, map_inv, inv_mul_cancel_left]
  exact ⟨sy, hsy'⟩

set_option maxHeartbeats 4000000 in
theorem ex_ad (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) (a : 𝓞 E)
    (wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I))) (hwLg : wL.IsGen)
    (hwL0 : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over X0)).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val wL (r ≫ (zz t).left) z J = 1) :
    ∃ ad : MvPowerSeries (Fin 2 × Fin d) S, MvPowerSeries.constantCoeff ad = 1 ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ,
      (u : Jet S (Fin 2 × Fin d) m) = psJet m ad ∧ LB.Gen.Corr t.PP.L _ _ _ _
        (LB.mulGen t.PP.L _ _ _ _
          (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
          (peG t x0 d x (fr hch i0 hi0) m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
        (scaleGenG t _ _ (unitΓ u) (peG t x0 d x (fr hch i0 hi0) m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])) := by
  have hL := t.PP.isLB
  have heg : ∀ m, (fr hch i0 hi0 m).IsGen := fun m => cgen_isGen t.PP.L hL _ _ _ _
  have htr := fr_trunc hch i0 hi0
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x (fr hch i0 hi0) m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  obtain ⟨ad, had⟩ := exists_series t x0 d (n := 2) _ _ _ _
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
      (peG t x0 d x (fr hch i0 hi0) m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwLg _)
      (hpe m _))
    (fun m => peG t x0 d x (fr hch i0 hi0) m
      ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])
    (fun m => hpe m _)
    (fun m U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_act hch, zpow_neg, Finset.prod_inv_distrib]
      simp only [inv_mul_cancel_right])
    (fun m y J hJ => (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans ((congrArg (fun r => val wL r y J) (pair_point_truncation hch m)).trans (val_pull hJ _ _ _).symm))
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
      have hA2 : val (peG t x0 d x (fr hch i0 hi0) 0
          ![fun j => psIn d 0 ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (𝟙 _) y I = 1 :=
        (val_pull hI _ _ _).trans ((congrArg (fun r => val (fr hch i0 hi0 0) r y I) (Category.id_comp _)).trans
          (val_fr_one hch i0 hi0 0 (T := jOG x0 d 0 2) _ (1 ≫ t.act.act a) 1
            (by rw [pt_sub]; simp only [Matrix.cons_val_zero]; rw [pt_act hch, hj0])
            (by rw [pt_sub]; simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]; rw [pt_X, hj0]) (Or.inr rfl) y I hI))
      have hB : val (peG t x0 d x (fr hch i0 hi0) 0
          ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 0 ![1] (act (H.bar a) j)]) (𝟙 _) y I = 1 :=
        (val_pull hI _ _ _).trans ((congrArg (fun r => val (fr hch i0 hi0 0) r y I) (Category.id_comp _)).trans
          (val_fr_one hch i0 hi0 0 (T := jOG x0 d 0 2) _ 1 (1 ≫ t.act.act (H.bar a))
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

set_option maxHeartbeats 4000000 in
theorem ex_rig (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) (wP : PrimTyG t) (hwP : IsPrimG t wP) : Rig0G t x0 d x act (fr hch i0 hi0) wP := by
  have hL := t.PP.isLB
  have hx0 : x 0 = 1 := frame_origin_jet_one hch
  have hj0 : ∀ {n : ℕ} (i : Fin n), jptG t x0 d x 0 i = 1 := fun i => by
    rw [jptG, hx0]
    exact map_one (preHom _)
  have hrig : Rig0G t x0 d x act (fr hch i0 hi0) wP := corr_of_val hL fun y J hJ => by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_rigT t.G t.PP.L t.PP.rig _ _ y J hJ).symm)
    refine (val_mul hJ _ _ _).trans ?_
    have h2 : val (peG t x0 d x (fr hch i0 hi0) 0
        ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d 0 ![0] (act H.w0 j)])
        (𝟙 _ ≫ (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) y J = 1 := by
      refine (val_pull hJ _ _ _).trans ((congrArg (fun r => val (fr hch i0 hi0 0) r y J)
        (by rw [Category.id_comp, ← Over.comp_left])).trans ?_)
      refine val_fr_one hch i0 hi0 0 (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ homAt x0 (sL 0 (act H.w0)))
        1 _ ?_ rfl (Or.inl rfl) y J hJ
      rw [Category.assoc, pt_sub]
      simp only [Matrix.cons_val_zero]
      rw [pt_X, hj0]
      exact map_one (preHom _)
    have hpt : (𝟙 _ ≫ (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) ≫ (x 0).left =
        (𝟙 _ ≫ (overAt x0 S).hom) ≫ eSec t.G := by
      rw [Category.id_comp, Category.id_comp, ← Over.comp_left, hch.zero 0]
      rfl
    rw [val_pull hJ, h2, _root_.mul_one, hpt]
    exact (val_pull hJ wP _ _).symm.trans (val_corr hJ hwP.2 _)
  exact hrig

end Ex

open Formalism.MainNotions.ModuliIntegralCharts.H1 in

theorem frameSt_holds : FrameSt := by
  intro E _ _ _ H X0 t S _ _ x0 d G A κ _ tg uvec x hch
  obtain ⟨i0, hi0⟩ := exists_chart_covering_index t x0
  obtain ⟨wP, hwP⟩ := exists_wP t
  choose wL hwLg hwL0 using fun a => exists_wL t a
  obtain ⟨ph1, hph1⟩ := exists_first_face_unit hch i0 hi0
  obtain ⟨ph2, hph2⟩ := exists_second_face_unit hch i0 hi0
  obtain ⟨sy, hsy⟩ := ex_sy hch i0 hi0
  choose ad hadc had using fun a => ex_ad hch i0 hi0 a (wL a) (hwLg a) (hwL0 a)
  exact ⟨fr hch i0 hi0, wP, ph1, ph2, sy, ad,
    ⟨fun m => cgen_isGen t.PP.L t.PP.isLB _ _ _ _, hph1, hph2, hsy, fun a => ⟨wL a, hwLg a, had a⟩⟩, hwP,
    fr_trunc hch i0 hi0, fr_axes hch i0 hi0, hadc, ex_rig hch i0 hi0 wP hwP⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
