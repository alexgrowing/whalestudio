import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.PairingOfForm

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing PrimNorm AdjointOfPairing

def chartUnflat {X Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (L : LB X) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
    ChartPull (LB.LinComb L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1))
      (LB.LinComb (LB.LinComb L φ ε) ψ δ) (𝟙 Z) :=
  have le : ∀ j : K' × K → L.ι, LB.wchart L (fun p : K' × K => ψ p.1 ≫ φ p.2) j ≤
      LB.wchart (LB.LinComb L φ ε) ψ (fun a b => j (a, b)) := fun j y hy =>
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => Set.mem_iInter.1 hy (a, b)
  { idx := fun j a b => j (a, b)
    le := le
    g := fun y p q hp hq => by
      refine (gm_linComb L _ _ (𝟙 Z) y p q hp hq).trans (Eq.trans ?_
        (gm_linComb (LB.LinComb L φ ε) ψ δ (𝟙 Z) y _ _ (le p hp) (le q hq)).symm)
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun k _ => Eq.symm ?_
      refine (congrArg (· ^ δ k) (gm_linComb L φ ε (𝟙 Z ≫ ψ k) y (fun b => p (k, b)) (fun b => q (k, b))
        (Set.mem_iInter.1 (le p hp) k) (Set.mem_iInter.1 (le q hq) k))).trans ?_
      simp only [← Finset.prod_zpow, zpow_mul, Category.assoc] }

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem weilIs_swap {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : WeilIs A L k x y c) : WeilIs A L k y x c⁻¹ := by
  intro p
  obtain ⟨V, hp, ⟨θx, θy, h1, h2⟩, h3⟩ := h p
  refine ⟨V, hp, ⟨θy, θx, h2, h1⟩, fun θ₁ θ₂ e₁ e₂ => ?_⟩
  have H := h3 θ₂ θ₁ e₂ e₁
  unfold CommIsOf at H ⊢
  refine corr_of_val hL fun q J hJ => ?_
  have e := val_corr hJ H (𝟙 _)
  simp only [val_mul hJ, H1.val_constGen, unitRes, map_inv] at e ⊢
  rw [e, mul_inv_cancel_right]

abbrev fr {X Y : Scheme.{0}} (ψ : Y ⟶ X) : Abelianization (FreeGroup (Y ⟶ X)) := Abelianization.of (FreeGroup.of ψ)

def charSums (L : LB A.left) (hL : L.IsLB) {T : Over S} (x : T ⟶ A) :
    Subgroup (Abelianization (FreeGroup ((T ⊗ A).left ⟶ A.left)) × Γ(T.left, ⊤)ˣ) where
  carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → ((T ⊗ A).left ⟶ A.left)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L φ ε)), u.IsGen ∧ ∏ k, fr (φ k) ^ ε k = s.1 ∧
      ∀ (Z : Over S) (t : Z ⟶ T) (w : Z ⟶ A) (z : Z.left) (J), Good L z J →
        val u (lift t ((t ≫ x) * w)).left z J = val u (lift t w).left z J * gm t.left z ⊤ s.2}
  one_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, fun _ _ => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    Fintype.prod_empty _, fun Z t w z J _ => by rw [val_one, val_one, Prod.snd_one, map_one, _root_.mul_one]⟩
  mul_mem' := by
    rintro ⟨_, c⟩ ⟨_, c'⟩ ⟨K, _, φ, ε, u, hu, rfl, h⟩ ⟨K', _, φ', ε', u', hu', rfl, h'⟩
    refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ u u', DVR.mulGen_isGen _ _ _ _ _ _ _ hu hu',
      Fintype.prod_sum_type _, fun Z t w z J hJ => ?_⟩
    rw [val_mul hJ, val_mul hJ, h Z t w z J hJ, h' Z t w z J hJ, Prod.snd_mul, map_mul, _root_.mul_mul_mul_comm]
  inv_mem' := by
    rintro ⟨_, c⟩ ⟨K, _, φ, ε, u, hu, rfl, h⟩
    refine ⟨K, inferInstance, _, _, LB.invGen L _ _ u, DVR.invGen_isGen _ _ _ _ hu,
      by simp only [zpow_neg, Finset.prod_inv_distrib, Prod.fst_inv], fun Z t w z J hJ => ?_⟩
    rw [val_inv, val_inv, h Z t w z J hJ, Prod.snd_inv, map_inv, mul_inv]

variable {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)

theorem eq_one_of_mem (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {c : Γ(T.left, ⊤)ˣ}
    (h : (1, c) ∈ charSums L hL x) : c = 1 := by
  obtain ⟨K, _, φ, ε, u, hu, hs, ht⟩ := h
  have key : ∀ (U : Type) [CommGroup U] (f : ((T ⊗ A).left ⟶ A.left) → U), ∏ k, f (φ k) ^ ε k = 1 := by
    intro U _ f
    have e := congrArg (Abelianization.lift (FreeGroup.lift f)) hs
    simpa [map_prod, map_zpow] using e
  set p := (fst T A).left with hp_def
  set e := (lift (𝟙 T) (1 : T ⟶ A)).left with he_def
  have hl : ∀ w : T ⟶ A, (lift (𝟙 T) w).left ≫ p = 𝟙 _ := fun w => by
    rw [hp_def, ← Over.comp_left, lift_fst, Over.id_left]
  have hfe : FormEq (fun k => (p ≫ e) ≫ φ k) ε φ ε := by
    intro U _ f
    rw [key U f]
    simpa using key U (fun ψ => f ((p ≫ e) ≫ ψ))
  obtain ⟨u', hu', hv⟩ := exists_gen hL hfe (LB.pullGen L φ ε u (p ≫ e)) (LB.isGen_pullGen L φ ε u hu _)
  have hall : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      val u r z J = val u (r ≫ p ≫ e) z J := by
    intro Z r z J hJ
    rw [gen_unique hL p e (hl 1) (GlobalTheory.CommutatorPairing.surj_fst hG hA T) hu hu' ?_ Z r z J hJ,
      hv Z r z J hJ, val_pull hJ]
    intro y J' hJ'
    rw [hv _ e y J' hJ', val_pull hJ', ← Category.assoc, hl 1, Category.id_comp]
  have hz : ∀ z : T.left, gm (𝟙 T.left) z ⊤ c = 1 := by
    intro z
    obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
    have h1 := ht T (𝟙 T) 1 z J hJ
    rw [hall _ _ z J hJ, hall _ (lift (𝟙 T) 1).left z J hJ, ← Category.assoc, hl, ← Category.assoc, hl,
      Over.id_left] at h1
    exact mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)
  apply Units.ext
  apply fn_ext
  intro z _
  rw [gs_unit _ z ⊤ (by simp) c, gs_unit _ z ⊤ (by simp) 1, hz z, map_one]

theorem pull_mem {B : Over S} {K : Type} [Fintype K] {φ : K → (B.left ⟶ A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb L φ ε)) (hu : u.IsGen) (ρ : T ⊗ A ⟶ B) (c : Γ(T.left, ⊤)ˣ)
    (h : ∀ (Z : Over S) (t : Z ⟶ T) (w : Z ⟶ A) (z : Z.left) (J), Good L z J →
      val u (lift t ((t ≫ x) * w) ≫ ρ).left z J = val u (lift t w ≫ ρ).left z J * gm t.left z ⊤ c) :
    (∏ k, fr (ρ.left ≫ φ k) ^ ε k, c) ∈ charSums L hL x := by
  refine ⟨K, inferInstance, fun k => ρ.left ≫ φ k, ε, LB.pullGen L φ ε u ρ.left,
    LB.isGen_pullGen L φ ε u hu ρ.left, rfl, fun Z t w z J hJ => ?_⟩
  rw [val_pull hJ, val_pull hJ]
  simpa only [Over.comp_left] using h Z t w z J hJ

private theorem gm_res_pullU_eq_gm_comp' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (a : Y ⟶ X) (z : Z) (U : X.Opens)
    (W : Y.Opens) (h : W ≤ a ⁻¹ᵁ U) (hz : r z ∈ W) (u : Γ(X, U)ˣ) :
    gm r z W (res h (pullU a U u)) = gm (r ≫ a) z U u := by
  rw [← gm_id_pull r z W hz, pullU_res₂, gm_rp₂ r a z U _ _ hz]

theorem const_mem (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a : T ⟶ A) :
    (fr (fst T A ≫ a).left, 1) ∈ charSums L hL x := by
  obtain ⟨j₀, hj₀⟩ := LB.mem_of_cover hL (a.left p₀)
  set ψ := (fst T A ≫ a).left with hψ_def
  have hψ : ∀ y, ψ y ∈ L.U j₀ := fun y => by
    have e : (fst T A).left y = p₀ := hT _
    show a.left ((fst T A).left y) ∈ L.U j₀
    rw [e]
    exact hj₀
  have hle : ∀ i : PUnit → L.ι,
      (LB.LinComb L (fun _ : PUnit => ψ) (fun _ => (1 : ℤ))).U i ≤ ψ ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U j₀) :=
    fun i y hy => ⟨Set.mem_iInter.1 hy PUnit.unit, hψ y⟩
  have h0 : ∀ y, y ∈ LB.wchart L (fun _ : PUnit => ψ) (fun _ => j₀) :=
    fun y => Set.mem_iInter.2 fun _ => hψ y
  refine ⟨PUnit, inferInstance, fun _ => ψ, fun _ => 1,
    ⟨fun i => res (hle i) (pullU ψ _ (L.g (i PUnit.unit) j₀))⟩, ?_, by simp, ?_⟩
  · intro i i'
    apply Units.ext
    apply fn_ext
    intro y hy
    rw [gs_unit _ y _ hy, gs_unit _ y _ hy]
    congr 1
    rw [map_mul]
    dsimp only
    rw [LB.res_res, LB.res_res, gm_rp₁ _ _ _ _ _ hy, gm_rp₁ _ _ _ _ _ hy]
    have g : gm (𝟙 _) y ((LB.LinComb L (fun _ : PUnit => ψ) (fun _ => (1 : ℤ))).U i ⊓
        (LB.LinComb L (fun _ : PUnit => ψ) (fun _ => (1 : ℤ))).U i')
        ((LB.LinComb L (fun _ : PUnit => ψ) (fun _ => (1 : ℤ))).g i i') =
        ∏ k : PUnit, gm (𝟙 _ ≫ ψ) y (L.U (i k) ⊓ L.U (i' k)) (L.g (i k) (i' k)) ^ (1 : ℤ) :=
      gm_linComb L _ _ (𝟙 _) y i i' hy.1 hy.2
    rw [g]
    have e := trF_trans hL (fun _ : PUnit => ψ) (fun _ => (1 : ℤ)) (𝟙 _) y hy.1 hy.2 (h0 y)
    simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp] at e ⊢
    exact e.symm
  · intro Z t' w z J hJ
    have key : ∀ r : Z.left ⟶ (T ⊗ A).left,
        val (⟨fun i => res (hle i) (pullU ψ _ (L.g (i PUnit.unit) j₀))⟩ :
          LB.Gen (LB.LinComb L (fun _ : PUnit => ψ) (fun _ => 1))) r z J =
        gm (r ≫ ψ) z (L.U (J (r ≫ ψ)) ⊓ L.U j₀) (L.g (J (r ≫ ψ)) j₀) := by
      intro r
      unfold val
      exact gm_res_pullU_eq_gm_comp' r ψ z _ _ _ (Good.mem hJ (fun _ : PUnit => ψ) r) _
    rw [key, key]
    have e : ∀ v : Z ⟶ A, (lift t' v).left ≫ ψ = (t' ≫ a).left := fun v => by
      rw [hψ_def, ← Over.comp_left, lift_fst_assoc]
    rw [e, e]
    simp

variable [IsCommMonObj A]

theorem diff_mem (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} (cb : CubicalStr A L)
    (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (hx : x ^ n = 1) (f : A ⟶ A) [IsMonHom f] (b : T ⟶ A)
    (hb : b ^ n = 1) (c : Γ(T.left, ⊤)ˣ) (hc : WeilIs A L.L n b (x ≫ f) c) :
    (diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ f) (fst T A ≫ b), c) ∈ charSums L.L L.isLB x := by
  obtain ⟨u, hu, hU⟩ := AdjointOfPairing.exists_gen_pairing hG hA cb p₀ hT n b hb
  have hxf : (x ≫ f) ^ n = 1 := by
    rw [← show postHom f T x = x ≫ f from rfl, ← map_pow, hx, map_one]
  have h1 := pull_mem L.isLB x u hu (lift (fst T A) (snd T A ≫ f)) c (fun Z t w z J hJ => by
    have e := hU (x ≫ f) c hxf hc Z t (w ≫ f) z J hJ
    have l : ∀ v : Z ⟶ A, lift t v ≫ lift (fst T A) (snd T A ≫ f) = lift t (v ≫ f) := fun v => by
      rw [comp_lift, lift_fst, lift_snd_assoc]
    rw [l, l, MonObj.mul_comp, Category.assoc]
    exact e)
  have h2 := const_mem L.isLB x p₀ hT 1
  have h3 := const_mem L.isLB x p₀ hT b
  have h4 := (charSums L.L L.isLB x).mul_mem ((charSums L.L L.isLB x).mul_mem h1 h2)
    ((charSums L.L L.isLB x).inv_mem h3)
  convert h4 using 1
  refine Prod.ext ?_ (by simp)
  have hp : (snd T A ≫ f) ^ n = (snd T A ^ n) ≫ f := (map_pow (postHom f (T ⊗ A)) (snd T A) n).symm
  have h1' : fst T A ≫ (1 : T ⟶ A) = 1 := by simp
  simp only [Prod.fst_mul, Prod.fst_inv]
  rw [AdjointOfPairing.prod_mulT n b (fst T A) (snd T A ≫ f) (h := fr), hp, h1', mul_comm (fst T A ≫ b)]
  simp only [diff₂]
  exact mul_right_comm _ _ _

theorem eq_prod (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} (cb : CubicalStr A L)
    (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (hx : x ^ n = 1) (y : T ⟶ A) (hy : y ^ n = 1)
    {I : Type} [Fintype I] (φ : I → (A ⟶ A)) (hφ : ∀ i, IsMonHom (φ i)) (ε : I → ℤ) (s : A ⟶ A) [IsMonHom s]
    (hs : LBIso (abelian₂ A (LB.LinComb L.L (fun i => (φ i).left) ε)) (cubeLB A ![fst A A, snd A A ≫ s] L.L))
    (c : I → Γ(T.left, ⊤)ˣ) (hc : ∀ i, WeilIs A L.L n (x ≫ φ i) (y ≫ φ i) (c i)) (d : Γ(T.left, ⊤)ˣ)
    (hd : WeilIs A L.L n x (y ≫ s) d) : d = ∏ i, c i ^ ε i := by
  have hE : ∀ i, (diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ φ i) (fst T A ≫ y ≫ φ i), (c i)⁻¹) ∈
      charSums L.L L.isLB x := by
    intro i
    haveI := hφ i
    have hb : (y ≫ φ i) ^ n = 1 := by
      rw [← show postHom (φ i) T y = y ≫ φ i from rfl, ← map_pow, hy, map_one]
    exact diff_mem x hG hA cb p₀ hT n hx (φ i) (y ≫ φ i) hb (c i)⁻¹ (weilIs_swap L.isLB (hc i))
  have hEd : (diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ 𝟙 A) (fst T A ≫ y ≫ s), d⁻¹) ∈
      charSums L.L L.isLB x := by
    have hb : (y ≫ s) ^ n = 1 := by
      rw [← show postHom s T y = y ≫ s from rfl, ← map_pow, hy, map_one]
    have hw := weilIs_swap L.isLB hd
    rw [← Category.comp_id x] at hw
    exact diff_mem x hG hA cb p₀ hT n hx (𝟙 A) (y ≫ s) hb d⁻¹ hw
  have hflat : LBIso (LB.LinComb L.L (fun p : ULift.{0} (Finset (Fin 2)) × I =>
        (psum A (x2 A) p.1.down).left ≫ (φ p.2).left) (fun p => ε p.2 * (-1) ^ (2 - p.1.down.card)))
      (LB.LinComb L.L (fun J : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A, snd A A ≫ s] J.down).left)
        (fun J => (-1) ^ (2 - J.down.card))) := by
    have hN : LBIso (abelian₂ A (LB.LinComb L.L (fun i => (φ i).left) ε))
        (LB.LinComb L.L (fun p : ULift.{0} (Finset (Fin 2)) × I =>
          (psum A (x2 A) p.1.down).left ≫ (φ p.2).left) (fun p => ε p.2 * (-1) ^ (2 - p.1.down.card))) :=
      lbIso_nested L.isLB _ _ _ _ _ _ (prod_flat _ _ _ _).symm
    exact LBIso.trans (LB.isLB_linComb L.isLB _ _) (LB.isLB_linComb (LB.isLB_linComb L.isLB _ _) _ _)
      (LB.isLB_linComb L.isLB _ _) hN.symm hs
  obtain ⟨u, hu⟩ := NormRos.exists_gen_of_lbIso hflat
  have hF := pull_mem L.isLB x u hu (lift (snd T A ^ n) (fst T A ≫ y)) 1 (fun Z t w z J hJ => by
    have e : ∀ v : Z ⟶ A, lift t v ≫ lift (snd T A ^ n) (fst T A ≫ y) = lift (v ^ n) (t ≫ y) := fun v => by
      rw [comp_lift, lift_fst_assoc, comp_pow, lift_snd]
    have c1 : t ≫ (1 : T ⟶ A) = 1 := by simpa using comp_pow (1 : T ⟶ A) 0 t
    rw [e, e, mul_pow, ← comp_pow, hx, c1, _root_.one_mul, map_one, _root_.mul_one])
  have cubeP : ∏ J : ULift.{0} (Finset (Fin 2)), fr ((lift (snd T A ^ n) (fst T A ≫ y)).left ≫
      (psum A ![fst A A, snd A A ≫ s] J.down).left) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ 𝟙 A) (fst T A ≫ y ≫ s) := by
    rw [prod_square (lift (snd T A ^ n) (fst T A ≫ y)) (fst A A) (snd A A ≫ s) (h := fr), lift_fst,
      lift_snd_assoc, Category.comp_id, Category.assoc]
  have flatP : ∀ i, ∏ J : ULift.{0} (Finset (Fin 2)), fr ((lift (snd T A ^ n) (fst T A ≫ y)).left ≫
      (psum A (x2 A) J.down).left ≫ (φ i).left) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ φ i) (fst T A ≫ y ≫ φ i) := by
    intro i
    have := hφ i
    have e := prod_square (lift (snd T A ^ n) (fst T A ≫ y)) (fst A A) (snd A A)
      (h := fun ψ => fr (ψ ≫ (φ i).left))
    simp only [Category.assoc] at e
    rw [show x2 A = ![fst A A, snd A A] from rfl, e, lift_fst, lift_snd]
    simp only [diff₂, ← Over.comp_left, MonObj.mul_comp, one_comp, Category.assoc]
  have hQ := (charSums L.L L.isLB x).mul_mem ((charSums L.L L.isLB x).mul_mem hEd
    ((charSums L.L L.isLB x).inv_mem ((charSums L.L L.isLB x).prod_mem
      (fun i (_ : i ∈ (Finset.univ : Finset I)) => (charSums L.L L.isLB x).zpow_mem (hE i) (ε i))))) ((charSums L.L L.isLB x).inv_mem hF)
  have hz1 : ∀ (a : Abelianization (FreeGroup ((T ⊗ A).left ⟶ A.left)) × (Γ(T.left, ⊤))ˣ) (m : ℤ),
      (a ^ m).1 = a.1 ^ m := fun _ _ => rfl
  have h1 := eq_one_of_mem L.isLB x hG hA (c := d⁻¹ * ∏ i, c i ^ ε i) (by
    convert hQ using 1
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.fst_inv, Prod.fst_prod, hz1]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [cubeP, Fintype.prod_prod_type, Finset.prod_comm]
      simp only [zpow_neg, Finset.prod_inv_distrib, zpow_mul', Finset.prod_zpow, flatP]
      exact (mul_inv_cancel _).symm
    · simp [Prod.snd_prod, Finset.prod_inv_distrib])
  rw [inv_mul_eq_one] at h1
  exact h1

end GlobalTheory.PairingOfForm

namespace GlobalTheory

open PairingOfForm in

theorem weilIs_of_formIs_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A ⟶ P.A)) (ε : I → ℤ) (s : P.A ⟶ P.A) (k : ℕ) (x y : Out.baseOver (Sp K) ⟶ P.A) (c : I → Kˣ), (k : K) ≠ 0 → (∀ i, IsMonHom (φ i)) → FormIs P (LB.LinComb P.L (fun i => (φ i).left) ε) s → x ^ k = 1 → y ^ k = 1 → (∀ i, Out.WeilIs P.A P.L k (x ≫ φ i) (y ≫ φ i) (unitOn (c i))) → Out.WeilIs P.A P.L k x (y ≫ s) (unitOn (∏ i, c i ^ ε i)) := by
  intro hl hl2 K _ _ P I _ φ ε s k x y c hk hφ hF hx hy hc
  obtain ⟨t, ht⟩ := P.rigid
  letI := P.isAb.comm
  have := hF.1
  obtain ⟨cb⟩ := (hl.cube (Sp K) P (RigLB.mk P.L t P.isLB ht) rfl).1
  obtain ⟨d, hd, -⟩ := (hl.weil (Sp K) P k (Out.baseOver (Sp K))).1 x (y ≫ s) hx (by
    rw [← show PrimNorm.postHom s _ y = y ≫ s from rfl, ← map_pow, hy, map_one])
  have hsub : Subsingleton (Out.baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Out.baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have e := PairingOfForm.eq_prod x hl.globalFns P.isAb cb p₀ (fun p => Subsingleton.elim p p₀) k hx y hy φ hφ
    ε s hF.2 (fun i => unitOn (c i)) hc d hd
  have hu : unitOn (∏ i, c i ^ ε i) = ∏ i, unitOn (c i) ^ ε i := by
    unfold unitOn
    simp [map_prod, map_zpow]
  rw [hu, ← e]
  exact hd

end GlobalTheory
