import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.PsiMono
variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def fracPt (ρ : V →+* V₁) (hρ : Function.Injective ρ) : (TK V₁).left ⟶ (TK V).left :=
  spMap (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ)

theorem fracPt_comp (ρ : V →+* V₁) (hρ : Function.Injective ρ) : fracPt ρ hρ ≫ jK V = jK V₁ ≫ spMap ρ := by
  simp only [fracPt, spMap, jK, TK, Over.mk_hom, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem gm_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (z : Sp R') (k : Rˣ) :
    gm (spMap f) z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn (Units.map f.toMonoidHom k)) := by
  have h := gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn k)
  rw [Category.id_comp] at h
  refine h.symm.trans (congrArg _ ?_)
  ext
  have e := congrArg (fun g => g.hom (k : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact e.symm

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen t c) r z J = gm r z ⊤ c * val t r z J :=
  gm_scaleGen t c r z _ (hJ.mem φ r)

theorem prod_zpow_swap {F : Type} [Field F] {I C : Type} [Fintype I] [Fintype C] (x : I → F) (e : C → I → ℤ)
    (w : C → ℤ) (h : ∀ c, ∏ i, x i ^ e c i ≠ 0) :
    ∏ c, (∏ i, x i ^ e c i) ^ w c = ∏ i, x i ^ ∑ c, w c * e c i := by
  classical
  have hz : ∀ i, x i = 0 → ∀ c, e c i = 0 := by
    intro i hi c
    by_contra hne
    exact h c (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, zero_zpow _ hne]))
  set y : I → F := fun i => if x i = 0 then 1 else x i with hy
  have hy0 : ∀ i, y i ≠ 0 := fun i => by
    by_cases hi : x i = 0 <;> simp [hy, hi]
  have hxy : ∀ i (n : ℤ), (x i = 0 → n = 0) → x i ^ n = y i ^ n := by
    intro i n hn
    by_cases hi : x i = 0
    · rw [hn hi]; simp
    · simp [hy, hi]
  have l1 : ∀ c, ∏ i, x i ^ e c i = ∏ i, y i ^ e c i :=
    fun c => Finset.prod_congr rfl fun i _ => hxy i _ fun hi => hz i hi c
  have l2 : ∀ i, x i ^ ∑ c, w c * e c i = y i ^ ∑ c, w c * e c i := fun i => hxy i _ fun hi => by
    simp [hz i hi]
  simp_rw [l1, l2, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  have key : ∀ (a : F), a ≠ 0 → ∀ (s : Finset C) (n : C → ℤ), ∏ c ∈ s, a ^ n c = a ^ ∑ c ∈ s, n c := by
    intro a ha s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert c s hc ih => rw [Finset.prod_insert hc, Finset.sum_insert hc, ih, zpow_add₀ ha]
  rw [key _ (hy0 i)]
  exact congrArg _ (Finset.sum_congr rfl fun c _ => mul_comm _ _)

abbrev fracOver (ρ : V →+* V₁) (hρ : Function.Injective ρ) : Over (Sp V) := Over.mk (fracPt ρ hρ ≫ jK V)

theorem psi_val (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b)
    (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V) (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε)
    {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left)
    (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂))
    (h₀ : ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J)
    (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
    (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι)
    (hJ : Good Q.M.L z J) (hJ' : Good D.P.L z J') (hJ₀ : Good M₀ z J₀) :
    ∃ u : (FractionRing V₁)ˣ, (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
              z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
          gm (𝟙 _) z ⊤ (unitOn u) := by
  classical
  have hL : Q.M.L.IsLB := Q.M.isLB
  choose k hk hkv using fun a b => (hτ a b).2
  have htau : ∀ a b, val (Q.tau a b) (fracPt ρ hρ) z J =
      gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) * val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J := by
    intro a b
    let t₁ := scaleGen (LB.pullGen Q.M.L (lamPts (Q.c a) (Q.c b)) negε (τ₀ a b) (toUnit (TK V)).left) (unitOn (k a b))
    have hc : LB.Gen.Corr Q.M.L _ _ _ _ (Q.tau a b) t₁ := corr_of_val hL fun y J₁ hJ₁ => by
      rw [val_scaleGen _ _ _ _ hJ₁, val_pull hJ₁, Category.id_comp]
      exact hkv a b y J₁ hJ₁
    rw [val_corr hJ hc (fracPt ρ hρ), val_scaleGen _ _ _ _ hJ, val_pull hJ]
    rfl
  have hunit : ∀ a b, gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
        (k a b))) := fun a b => gm_spMap_unitOn _ z _
  have hbase : ∀ a b, val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J =
      lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c a) (toUnit (fracOver ρ hρ) ≫ Q.c b)).left z J₀ J *
        val (τ₁ a b) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀ := fun a b => h₀ (fracOver ρ hρ) a b z J₀ J hJ₀ hJ
  have hfk : ∀ a b, ((Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k a b) : (FractionRing V₁)ˣ) : FractionRing V₁) =
        ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i a b := by
    intro a b
    show IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ (k a b : FractionRing V) = _
    rw [hk a b, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀]
    simp [IsFractionRing.map, IsLocalization.map_eq]
  refine ⟨∏ a, ∏ b, Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k (mu a) (mu b)) ^ W a b, ?_, ?_⟩
  · simp_rw [Units.coe_prod, Units.val_zpow_eq_zpow_val, hfk]
    have hne : ∀ c : Fin 8 × Fin 8, ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i (mu c.1) (mu c.2) ≠ 0 :=
      fun c => by rw [← hfk]; exact Units.ne_zero _
    have e := prod_zpow_swap (fun i => algebraMap V₁ (FractionRing V₁) (ρ (s i)))
      (fun (c : Fin 8 × Fin 8) i => ε i (mu c.1) (mu c.2)) (fun (c : Fin 8 × Fin 8) => W c.1 c.2) hne
    rw [Fintype.prod_prod_type] at e
    simp only [Fintype.sum_prod_type] at e
    rw [e]
    rfl
  · rw [hw (fracPt ρ hρ) (fracPt_comp ρ hρ) mu z J J' hJ hJ', _root_.mul_assoc]
    congr 1
    clear hw h₀ hkv hk hτ hfk
    simp only [htau, hunit, hbase]
    simp only [unitOn, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib]
    exact _root_.mul_comm _ _

theorem psi_val_of (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (hS : SharpRef W Q ρ D e) (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V)
    (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε) {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V)
    (hB : FromBase Q τ₀ ib) :
    ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
      (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
      (∀ a, IsMonHom (pr a)) ∧
      (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
      w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
      ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
        (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
        (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
        (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
        IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ib) β ∧ IsSquare β β₂ ∧ w₀.IsGen ∧
        (∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
        (∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
          val (τ₀ a b) (toUnit T).left z J' =
            lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J) ∧
        ∀ (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
          (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι),
          Good Q.M.L z J → Good D.P.L z J' → Good M₀ z J₀ →
          ∃ u : (FractionRing V₁)ˣ,
            (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
            val (D.psi (e mu)) (𝟙 _) z J' =
              gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
                  pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
                (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀
                    (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
                    z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
                gm (𝟙 _) z ⊤ (unitOn u) := by
  obtain ⟨pr, w, h1, h2, h3, h4, hw⟩ := hS
  obtain ⟨B₀, _, _, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀⟩ := hB
  exact ⟨pr, w, h1, h2, h3, h4, B₀, inferInstance, inferInstance, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀,
    fun mu z J J' J₀ hJ hJ' hJ₀ => psi_val W Q ρ hρ D e pr w hw τ₀ s ε hτ ib B₀ M₀ c₀ τ₁ β₂ w₀ h₀ mu z J J' J₀ hJ hJ' hJ₀⟩

end GlobalTheory.Poinc.PsiMono

end
