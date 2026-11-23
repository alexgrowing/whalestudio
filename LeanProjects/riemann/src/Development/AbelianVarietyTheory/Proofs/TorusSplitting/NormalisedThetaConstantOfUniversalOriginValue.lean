import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal.NullMove

open GlobalTheory.TranslMove GlobalTheory.VVRank

theorem map_gm {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm g (r z) U a) = gm (r ≫ g) z U a := by
  symm
  by_cases h : g (r z) ∈ U
  · refine Units.ext ((gs_unit (r ≫ g) z U h a).symm.trans (Eq.trans ?_
      (congrArg (r.stalkMap z).hom (gs_unit g (r z) U h a))))
    rw [← gs_pull r g z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) g (r z) U h, Category.id_comp]
  · have h' : (r ≫ g) z ∉ U := h
    rw [gm, dif_neg h', gm, dif_neg h]
    exact (map_one _).symm

section General

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} {L₀ : LB G.left} {L₁ : LB A.left}

theorem pmaps_of_stalks (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {w : LB.Iso L₁ (L₀.pull φ)}
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ : LB.Gen (L₁.pull (eSec A))} (he : eSec A ≫ φ = f ≫ eSec G)
    (h : ∀ (z : S') (JA) (J), Good L₁ z JA → Good L₀ z J →
      gw w (eSec A) z (J (f ≫ eSec G)) (JA (eSec A)) *
        val (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ (𝟙 _) z JA =
      val (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ f z J) :
    PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) ρ ρ₀ f := by
  intro Z r z p q hp hq
  obtain ⟨J, hJ, e₀⟩ := exists_good L₀ hL₀ (Z := S') (r z) (fun _ : PUnit => f ≫ eSec G) p
    (fun _ _ _ => rfl) (fun k => by rw [← he]; exact hp k)
  obtain ⟨JA, hJA, e₁⟩ := exists_good L₁ hL₁ (Z := S') (r z) (fun _ : PUnit => eSec A) q
    (fun _ _ _ => rfl) hq
  have a := h (r z) JA J hJA hJ
  rw [val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ f (r z) J p e₀,
    val_of (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ (𝟙 _) (r z) JA q
      (fun k => by rw [Category.id_comp]; exact e₁ k), e₀ PUnit.unit, e₁ PUnit.unit] at a
  have b := congrArg (Units.map (r.stalkMap z).hom.toMonoidHom) a
  rw [Fintype.prod_unique, zpow_one]
  refine (map_gm r f z _ _).symm.trans (b.symm.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (map_gm r _ z _ _) ?_)))
  exact (map_gm r (𝟙 _) z _ _).trans (by rw [Category.comp_id])

theorem one_comm (hp : IsGrpPullback A G f φ) {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left}
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) : τ ≫ (1 : T₀ ⟶ G).left = (1 : T ⟶ A).left ≫ φ :=
  (pt_iff hp hτ 1 1).2 (by rw [map_one, map_one])

theorem eSec_comm (hp : IsGrpPullback A G f φ) : eSec A ≫ φ = f ≫ eSec G := by
  have h := one_comm hp (T := 𝟙_ (Over S')) (T₀ := 𝟙_ (Over S)) (τ := f)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have a : (η[A] : 𝟙_ (Over S') ⟶ A) = 1 := by simp [Hom.one_def]
  have b : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by simp [Hom.one_def]
  rw [← a, ← b] at h
  exact h.symm

theorem sv_valueAt {T : Over S'} {a : ℤ} {s : LB.Sec (LPow A L₁ a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L₁ (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L₁ a s x τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good L₁ z J) :
    sv A s (r ≫ (ptSecT A x).left) z J = gs r z ⊤ v * (val τ r z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) r
  refine (sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (ptSecT A x).left) z J
    (fun _ => J (r ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])).trans ?_
  refine Eq.trans ?_ ((congrArg (gs r z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull r (ptSecT A x).left z
    (LB.wchart L₁ (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ x.left))) (val_le A L₁ x _ hy) _)).symm

theorem val_rigT_pow (rig : LB.Gen (L₁.pull (eSec A))) (T : Over S') (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) {z : Z}
    {J} (hJ : Good L₁ z J) : val (rigT A L₁ rig T k) r z J =
      val (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J ^ k := by
  rw [val_of (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => congrArg J (Category.assoc _ _ _))]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (rigT_le A L₁ _ hm) _

theorem exists_move [IsCommMonObj G] [IsCommMonObj A] (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left} {M₀ : RigLB G} (hL₁ : L₁.IsLB)
    {ρ : LB.Gen (L₁.pull (eSec A))} {w : LB.Iso L₁ (M₀.L.pull φ)} (hw : w.IsGen)
    {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (h₁ : Ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ)
    (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    (hρ : PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) ρ M₀.rig f) (N : ℕ)
    (hk : ∀ θ : ThetaGrp A L₁ ((N : ℤ) ^ 2) T, θ.pt ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow G M₀.L 1 T₀)} {s : LB.Sec (LPow A L₁ 1 T)} (hs : SecRel w Ψ s₀ s)
    {x : T ⟶ A} {y y' : T₀ ⟶ G} (hx : τ ≫ y.left = x.left ≫ φ)
    {F₀ : LB.Sec (LPow G M₀.L ((N : ℤ) ^ 2) T₀)} (H : IsVtOver G M₀ N (fun t => t = y) s₀ y' F₀)
    {v : Γ(T₀.left, ⊤)} (hv : IsValueAt G M₀.L ((N : ℤ) ^ 2) F₀ 1 (rigT G M₀.L M₀.rig T₀ ((N : ℤ) ^ 2)) v)
    {k : ℤ} (hN : (N : ℤ) ^ 2 = k) :
    ∃ (t : LB.Sec (LPow A L₁ k T))
      (α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![k, -1]))
      (s₁ : LB.Sec (LPow A L₁ k T)) (θ : ThetaGrp A L₁ k T),
      α.IsGen ∧ LB.Gen.Corr L₁ _ _ _ _ (LB.pullGen L₁ _ _ α (ptSecT A 1).left) (rigT A L₁ ρ T (k - 1)) ∧
      IsTwistPull A L₁ (mulT A T N) (snd T A ^ N) (lift_snd _ _) k 1 α s s₁ ∧
      SymLift A L₁ k (N ^ 2) x θ ∧ IsActOf A L₁ k θ s₁ t ∧
      ∀ z J, Good L₁ z J → sv A t (ptSecT A 1).left z J = gs τ z ⊤ v * (val (rigT A L₁ ρ T k) (𝟙 _) z J).val := by
  subst hN
  have he := eSec_comm hp
  have hτ := base_comm hp hx
  obtain ⟨_, β₀, β, r₁, V, -, rfl, g₀, n₀, cβ, tw, sl, ac⟩ := H
  obtain ⟨α₀, gα₀, nα₀, v₀⟩ := exists_normMul hp M₀.isLB hL₁ hw he hρ N g₀ n₀
  obtain ⟨α, gα, cα⟩ := NormMulUniv.exists_pull hL₁ α₀ gα₀ T
  have vα : GenRel w Ψ β α := fun Z r z J₀ J hJ₀ hJ => by
    rw [val_corr hJ₀ cβ, val_pull hJ₀, val_corr hJ cα, val_pull hJ, Category.assoc, h₂, ← Category.assoc,
      v₀ Z _ z J₀ J hJ₀ hJ, Category.comp_id, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨s₁, tw'⟩ := VVRank.exists_isTwistPull A (ψ := mulT A T N) (hm := lift_snd _ _) (b := 1) hL₁ gα s
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow hp h₂ N) h₂) vα tw tw' hs
  obtain ⟨U, l₁, a₁⟩ := exists_symLift hp M₀.isLB hL₁ hw h₁ h₂ hk hx sl
  obtain ⟨t, b₁, R₂⟩ := a₁ _ _ _ ac R₁
  have o₁ : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
    rw [← Over.comp_left, ptSecT, lift_snd]; rfl
  refine ⟨t, α, s₁, U, gα, corr_of_val hL₁ fun z J hJ => ?_, tw', l₁, b₁, fun z J hJ => ?_⟩
  · have a := (val_pull hJ α₀ (eSec A) T.hom).symm.trans ((val_corr hJ nα₀ T.hom).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_rigPow _ _ _ _ _) (val_inv _ _))))
    refine (val_pull hJ _ _ _).trans ((val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans
      (Eq.trans ?_ (val_rigT_pow ρ T _ _ hJ).symm)))
    rw [Category.id_comp, Category.id_comp, o₁, zpow_sub_one]
    exact a
  · obtain ⟨J₀, hJ₀⟩ := exists_good_pt M₀.isLB z
    have o₂ : (ptSecT A (1 : T ⟶ A)).left ≫ Ψ = τ ≫ (ptSecT G (1 : T₀ ⟶ G)).left := by
      have e₁ : ((ptSecT A (1 : T ⟶ A)).left ≫ Ψ) ≫ (fst T₀ G).left =
          (τ ≫ (ptSecT G (1 : T₀ ⟶ G)).left) ≫ (fst T₀ G).left := by
        rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
          lift_fst, lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
      have e₂ : ((ptSecT A (1 : T ⟶ A)).left ≫ Ψ) ≫ (snd T₀ G).left =
          (τ ≫ (ptSecT G (1 : T₀ ⟶ G)).left) ≫ (snd T₀ G).left := by
        rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
          lift_snd, lift_snd, one_comm hp hτ]
      exact pullback.hom_ext e₁ e₂
    have a₁ := R₂ _ (ptSecT A 1).left z J₀ J hJ₀ hJ
    have a₂ := (sv_valueAt hv τ hJ₀).trans
      (congrArg (fun u => gs τ z ⊤ v * Units.val u) (val_rigT_pow M₀.rig T₀ _ τ hJ₀))
    have a₃ := val_move (fun _ => he) hρ T.hom hJ₀ hJ
    rw [Fintype.prod_unique, zpow_one] at a₃
    rw [o₂, a₂, hτ, o₁] at a₁
    have a₄ := a₁.symm.trans (congrArg (fun u => gs τ z ⊤ v * Units.val (u ^ ((N : ℤ) ^ 2))) a₃)
    rw [mul_zpow, Units.val_mul, _root_.mul_left_comm] at a₄
    rw [val_rigT_pow ρ T _ _ hJ, Category.id_comp]
    exact (Units.mul_right_inj _).1 a₄

end General

theorem thC_of_isNullVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra c.F F] (z : FrPt Xo c F), z.x = spMap (algebraMap (FractionRing R) F) ≫ x → ∀ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie z.x z.s th → ∀ (m : ℕ), Odd m → ∀ (p : ptO Xo z.x ⟶ Xo.univ.t.G) (p' : TFK (R := R) F ⟶ A.A) (w : F), p ^ (m ^ 2) = 1 → p'.left ≫ Φ.φ = p.left → IsNullVal Xo c m z p w → ∃ t, GlobalTheory.UT.ThC A Φ.ρ m th p' t w := by
  intro E _ _ _ H Dw l Xo c R _ _ _ x A Φ F _ _ _ z hz th hth m _ p p' w _ hp hw
  obtain ⟨F₀, hV, hv⟩ := hw
  have := A.isAb.comm
  have hc : (fst (TFK (R := R) F) A.A).left ≫ z.x =
      ((snd (TFK (R := R) F) A.A).left ≫ Φ.φ) ≫ Xo.univ.t.G.hom := by
    rw [Category.assoc, Φ.cart.1.w, ← Category.assoc, Over.w (snd (TFK (R := R) F) A.A),
      ← Over.w (fst (TFK (R := R) F) A.A), hz, Category.assoc]
    rfl
  let Ψ : (TFK (R := R) F ⊗ A.A).left ⟶ (ptO Xo z.x ⊗ Xo.univ.t.G).left := pullback.lift _ _ hc
  have h₁ : Ψ ≫ (fst (ptO Xo z.x) Xo.univ.t.G).left = (fst (TFK (R := R) F) A.A).left := pullback.lift_fst _ _ _
  have h₂ : Ψ ≫ (snd (ptO Xo z.x) Xo.univ.t.G).left = (snd (TFK (R := R) F) A.A).left ≫ Φ.φ := pullback.lift_snd _ _ _
  have hs : SecRel (G := Xo.univ.t.G) (T₀ := ptO Xo z.x) (a := 1) Φ.ω Ψ z.s th := fun Z r y J₀ J hJ₀ hJ => by
    have e : (r ≫ Ψ) ≫ (snd (ptO Xo z.x) Xo.univ.t.G).left = (r ≫ (snd (TFK (R := R) F) A.A).left) ≫ Φ.φ := by
      rw [Category.assoc, h₂, Category.assoc]
    have a := hth.2 Z r (r ≫ Ψ) (e.trans (Category.assoc _ _ _)) (by rw [Category.assoc, h₁]) y J J₀ hJ hJ₀
    rw [zpow_one]
    unfold TranslMove.wv
    rw [← e]
    exact a
  obtain ⟨t, α, s₁, θ, h⟩ := exists_move Φ.cart (T := TFK (R := R) F) (T₀ := ptO Xo z.x) (τ := 𝟙 (Sp F)) A.isLB Φ.ωgen
    (h₁.trans (Category.comp_id _).symm) h₂
    (pmaps_of_stalks Xo.univ.t.PP.isLB A.isLB (eSec_comm Φ.cart) Φ.rig) m
    (fun θ => pt_pow_eq_one GlobalTheory.firstFiveLaws.1.kerPow A (m ^ 2) (Nat.cast_pow m 2).symm θ) hs
    ((Category.id_comp _).trans hp.symm) hV hv (Nat.cast_pow m 2).symm
  exact ⟨t, α, s₁, θ, h⟩

end GlobalTheory.EtaVal.NullMove
