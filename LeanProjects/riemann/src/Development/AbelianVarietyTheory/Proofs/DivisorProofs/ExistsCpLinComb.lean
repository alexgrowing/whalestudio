import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LinCombCP

variable {X Y Y' Z : Scheme.{0}} {L : LB X}

section Prod
variable {K I : Type} [Fintype K] [Fintype I] (φ : K → I → (Y ⟶ X)) (ε : I → ℤ) (n : K → ℤ)

theorem prod_le (j : K × I → L.ι) (k : K) :
    LB.wchart L (fun p : K × I => φ p.1 p.2) j ≤ LB.wchart L (φ k) (fun i => j (k, i)) := fun _ hy =>
  Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)

def prodGen (t : ∀ k, LB.Gen (LB.LinComb L (φ k) ε)) :
    LB.Gen (LB.LinComb L (fun p : K × I => φ p.1 p.2) (fun p => n p.1 * ε p.2)) :=
  ⟨fun j => ∏ k, res (prod_le φ j k) ((t k).s (fun i => j (k, i))) ^ n k⟩

theorem gm_prodGen (t : ∀ k, LB.Gen (LB.LinComb L (φ k) ε)) (r : Z ⟶ Y) (z : Z) (j : K × I → L.ι)
    (hj : r z ∈ LB.wchart L (fun p : K × I => φ p.1 p.2) j) :
    gm r z (LB.wchart L (fun p : K × I => φ p.1 p.2) j) ((prodGen φ ε n t).s j) =
      ∏ k, gm r z (LB.wchart L (φ k) (fun i => j (k, i))) ((t k).s (fun i => j (k, i))) ^ n k :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ n k) (gm_res r z _ hj _)))

theorem prodGen_isGen (t : ∀ k, LB.Gen (LB.LinComb L (φ k) ε)) (ht : ∀ k, (t k).IsGen) :
    (prodGen φ ε n t).IsGen := by
  refine isGen_of_gm _ fun y j j' h h' => ?_
  rw [gm_prodGen φ ε n t _ y j h, gm_prodGen φ ε n t _ y j' h', trF, Fintype.prod_prod_type,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gen_trans (ht k) (𝟙 Y) y (prod_le φ j k h) (prod_le φ j' k h'), mul_zpow, trF, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, mul_comm (ε i)]

theorem val_prodGen (t : ∀ k, LB.Gen (LB.LinComb L (φ k) ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (prodGen φ ε n t) r z J = ∏ k, val (t k) r z J ^ n k :=
  gm_prodGen φ ε n t r z _ (hJ.mem _ r)

end Prod

section Nest
variable {K I : Type} [Fintype K] [Fintype I] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : I → (Y' ⟶ Y)) (δ : I → ℤ)

theorem nest_le (jj : I → K → L.ι) :
    LB.wchart (LB.LinComb L φ ε) ψ jj ≤
      LB.wchart L (fun p : I × K => ψ p.1 ≫ φ p.2) (fun p => jj p.1 p.2) := fun _ hy =>
  Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2

def nestGen (v : LB.Gen (LB.LinComb L (fun p : I × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1))) :
    LB.Gen (LB.LinComb (LB.LinComb L φ ε) ψ δ) :=
  ⟨fun jj => res (nest_le φ ε ψ jj) (v.s (fun p => jj p.1 p.2))⟩

theorem nestGen_isGen (v : LB.Gen (LB.LinComb L (fun p : I × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1)))
    (hv : v.IsGen) : (nestGen φ ε ψ δ v).IsGen := by
  refine isGen_of_gm _ fun y jj jj' h h' => ?_
  refine (gm_res (𝟙 _) y _ h _).trans ((gen_trans hv (𝟙 _) y (nest_le φ ε ψ jj h) (nest_le φ ε ψ jj' h')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 _) y _ h' _).symm))
  unfold trF
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  refine Eq.trans ?_ (congrArg (· ^ δ a) (gm_linComb L φ ε (𝟙 _ ≫ ψ a) y (jj a) (jj' a)
    (Set.mem_iInter.1 h a) (Set.mem_iInter.1 h' a))).symm
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, Category.assoc]

def chg (JM : (Z ⟶ Y) → (K → L.ι)) (J : (Z ⟶ X) → L.ι) (z : Z) (χ : Z ⟶ Y) : (Z.presheaf.stalk z)ˣ :=
  ∏ k, gm (χ ≫ φ k) z _ (L.g (JM χ k) (J (χ ≫ φ k))) ^ ε k

theorem val_nestGen (v : LB.Gen (LB.LinComb L (fun p : I × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1)))
    (hv : v.IsGen) (r : Z ⟶ Y') (z : Z) {JM : (Z ⟶ Y) → (K → L.ι)} {J : (Z ⟶ X) → L.ι}
    (hM : Good (LB.LinComb L φ ε) z JM) (hJ : Good L z J) :
    val (nestGen φ ε ψ δ v) r z JM = (∏ i, chg φ ε JM J z (r ≫ ψ i) ^ δ i) * val v r z J := by
  have h₁ : r z ∈ LB.wchart (LB.LinComb L φ ε) ψ (fun i => JM (r ≫ ψ i)) := hM.mem ψ r
  have h₂ := hJ.mem (fun p : I × K => ψ p.1 ≫ φ p.2) r
  refine (gm_res r z _ h₁ _).trans ((gen_trans hv r z (nest_le φ ε ψ _ h₁) h₂).trans (congrArg (· * _) ?_))
  unfold trF chg
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, Category.assoc]

end Nest

section Cub
variable {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U]

theorem isCub_comp {θ : A → A → A → U} (h : IsCub θ) (β : A' →* A) :
    IsCub (fun a b c => θ (β a) (β b) (β c)) :=
  ⟨fun x y => by simp only [map_one, h.face], fun x y z => h.s01 _ _ _, fun x y z => h.s12 _ _ _,
    fun x x' x'' y => by simp only [map_mul]; exact h.coc _ _ _ _⟩

theorem isCub_prod {K : Type} [Fintype K] {θ : K → A → A → A → U} (h : ∀ k, IsCub (θ k)) (n : K → ℤ) :
    IsCub (fun a b c => ∏ k, θ k a b c ^ n k) :=
  ⟨fun x y => Finset.prod_eq_one fun k _ => by rw [(h k).face, one_zpow],
    fun x y z => Finset.prod_congr rfl fun k _ => by rw [(h k).s01],
    fun x y z => Finset.prod_congr rfl fun k _ => by rw [(h k).s12],
    fun x x' x'' y => by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [← mul_zpow, ← mul_zpow, (h k).coc]⟩

end Cub

end GlobalTheory.LinCombCP
end

noncomputable section
namespace GlobalTheory.LinCombCP

section Main
variable {S : Scheme.{0}} {G₀ H : Over S} [GrpObj G₀] [IsCommMonObj G₀] [GrpObj H] [IsCommMonObj H]

def postHom (g : H ⟶ G₀) [IsMonHom g] (T : Over S) : (T ⟶ H) →* (T ⟶ G₀) :=
  MonoidHom.mk' (· ≫ g) fun x y => MonObj.mul_comp x y g

theorem formEq_swap {X Y : Scheme.{0}} {K I : Type} [Fintype K] [Fintype I] {α β : K → I → (Y ⟶ X)}
    (e : ∀ k i, α k i = β k i) (n : K → ℤ) (ε : I → ℤ) :
    FormEq (fun p : K × I => α p.1 p.2) (fun p => n p.1 * ε p.2) (fun p : I × K => β p.2 p.1)
      (fun p => n p.2 * ε p.1) := by
  intro U _ h
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type_right]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => by simp only [e]

abbrev cpLB (P : UU.CP G₀) {K : Type} [Fintype K] (f : K → (H ⟶ G₀)) (ε : K → ℤ) : LB H.left :=
  LB.LinComb P.L.L (fun k => (f k).left) ε

theorem exists_cp_linComb (P : UU.CP G₀) {K : Type} [Fintype K] (f : K → (H ⟶ G₀)) [∀ k, IsMonHom (f k)]
    (ε : K → ℤ) : ∃ Q : UU.CP H, Q.L.L = cpLB P f ε := by
  have hM : (cpLB P f ε).IsLB := LB.isLB_linComb P.L.isLB _ _

  have he : ∀ k, eSec H ≫ (f k).left = eSec G₀ := fun k => by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨vr, hvr, -⟩ := exists_gen P.L.isLB
    (formEq_swap (α := fun (_ : K) (_ : PUnit) => eSec G₀) (β := fun k _ => eSec H ≫ (f k).left)
      (fun k _ => (he k).symm) ε (fun _ => 1))
    (prodGen (fun (_ : K) (_ : PUnit) => eSec G₀) (fun _ => 1) ε (fun _ => P.L.rig))
    (prodGen_isGen _ _ _ _ fun _ => P.L.rigGen)
  let rig : LB.Gen (LB.LinComb (cpLB P f ε) (fun _ : PUnit => eSec H) (fun _ => 1)) :=
    nestGen (fun k => (f k).left) ε (fun _ : PUnit => eSec H) (fun _ => 1) vr
  have rigGen : rig.IsGen := nestGen_isGen (fun k => (f k).left) ε (fun _ : PUnit => eSec H) (fun _ => 1) vr hvr
  let L' : RigLB H := ⟨cpLB P f ε, rig, hM, rigGen⟩

  have hc : ∀ k (I : thK.{0}), (f k ⊗ₘ f k ⊗ₘ f k).left ≫ thφ G₀ (x3 G₀) I = thφ H (x3 H) I ≫ (f k).left :=
    fun k I => ((CubeMap.ofHom (f k)).psum_comm I.down).symm
  obtain ⟨vc, hvc, Hvc⟩ := exists_gen P.L.isLB (formEq_swap hc ε thε)
    (prodGen (fun k I => (f k ⊗ₘ f k ⊗ₘ f k).left ≫ thφ G₀ (x3 G₀) I) thε ε
      (fun k => LB.pullGen P.L.L _ _ P.c.t (f k ⊗ₘ f k ⊗ₘ f k).left))
    (prodGen_isGen _ _ _ _ fun k => DVR.pullGen_isGen _ _ _ _ P.c.isGen _)
  have vcub : ∀ {T : Over S} {z : T.left} {JL}, Good P.L.L z JL → ∀ k (a b d : T ⟶ H),
      val (LB.pullGen P.L.L (thφ G₀ (x3 G₀)) thε P.c.t (f k ⊗ₘ f k ⊗ₘ f k).left) (lift a (lift b d)).left z JL =
        cubV P.c z JL (a ≫ f k) (b ≫ f k) (d ≫ f k) := fun hJL k a b d => by
    refine (val_pull hJL _ _ _).trans ?_
    rw [← Over.comp_left, lift_map, lift_map]; rfl
  obtain ⟨t, ht, vt⟩ : ∃ t : LB.Gen (Theta H (cpLB P f ε)), t.IsGen ∧ ∀ (T : Over S) (z : T.left) (J JL),
      Good (cpLB P f ε) z J → Good P.L.L z JL → ∀ a b d : T ⟶ H,
      val (L := cpLB P f ε) (φ := thφ H (x3 H)) (ε := thε) t (lift a (lift b d)).left z J =
        (chg (fun k => (f k).left) ε J JL z (a * b * d).left * (chg (fun k => (f k).left) ε J JL z (a * b).left)⁻¹ *
          (chg (fun k => (f k).left) ε J JL z (a * d).left)⁻¹ * (chg (fun k => (f k).left) ε J JL z (b * d).left)⁻¹ *
          chg (fun k => (f k).left) ε J JL z a.left * chg (fun k => (f k).left) ε J JL z b.left *
          chg (fun k => (f k).left) ε J JL z d.left * (chg (fun k => (f k).left) ε J JL z (1 : T ⟶ H).left)⁻¹) *
        ∏ k, cubV P.c z JL (a ≫ f k) (b ≫ f k) (d ≫ f k) ^ ε k :=
    ⟨nestGen (fun k => (f k).left) ε (thφ H (x3 H)) thε vc,
      nestGen_isGen (fun k => (f k).left) ε (thφ H (x3 H)) thε vc hvc, fun T z J JL hJ hJL a b d => by
        refine (val_nestGen (fun k => (f k).left) ε (thφ H (x3 H)) thε vc hvc (lift a (lift b d)).left z hJ hJL).trans
          (congrArg₂ (· * ·) (prod_cub a b d (chg (fun k => (f k).left) ε J JL z))
            ((Hvc _ _ z JL hJL).trans ((val_prodGen (fun k I => (f k ⊗ₘ f k ⊗ₘ f k).left ≫ thφ G₀ (x3 G₀) I) thε ε
              (fun k => LB.pullGen P.L.L _ _ P.c.t (f k ⊗ₘ f k ⊗ₘ f k).left) _ z hJL).trans
              (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (vcub hJL k a b d)))))⟩

  have hι : ∀ k (i : Fin 2), (f k).left ≫ ![(ι[G₀]).left, 𝟙 G₀.left] i = ![(ι[H]).left, 𝟙 H.left] i ≫ (f k).left := by
    intro k i
    fin_cases i
    · show (f k).left ≫ (ι[G₀]).left = (ι[H]).left ≫ (f k).left
      rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
    · show (f k).left ≫ 𝟙 _ = 𝟙 _ ≫ (f k).left
      rw [Category.comp_id, Category.id_comp]
  obtain ⟨vs, hvs, Hvs⟩ := exists_gen P.L.isLB (formEq_swap hι ε ![1, -1])
    (prodGen (fun k i => (f k).left ≫ ![(ι[G₀]).left, 𝟙 G₀.left] i) ![1, -1] ε
      (fun k => LB.pullGen P.L.L _ _ P.sym (f k).left))
    (prodGen_isGen (fun k i => (f k).left ≫ ![(ι[G₀]).left, 𝟙 G₀.left] i) ![1, -1] ε _
      fun k => DVR.pullGen_isGen _ _ _ _ P.sym_gen _)
  let sym : LB.Gen (LB.LinComb (cpLB P f ε) (K := Fin 2) ![(ι[H]).left, 𝟙 H.left] ![1, -1]) :=
    nestGen (fun k => (f k).left) ε ![(ι[H]).left, 𝟙 H.left] ![1, -1] vs
  have symGen : sym.IsGen := nestGen_isGen (fun k => (f k).left) ε ![(ι[H]).left, 𝟙 H.left] ![1, -1] vs hvs
  have vsym : ∀ {Z : Scheme.{0}} (r : Z ⟶ H.left) (z : Z) (J JL), Good (cpLB P f ε) z J → Good P.L.L z JL →
      val sym r z J = (chg (fun k => (f k).left) ε J JL z (r ≫ (ι[H]).left) *
        (chg (fun k => (f k).left) ε J JL z r)⁻¹) * ∏ k, val P.sym (r ≫ (f k).left) z JL ^ ε k :=
    fun r z J JL hJ hJL =>
    (val_nestGen (fun k => (f k).left) ε ![(ι[H]).left, 𝟙 H.left] ![1, -1] vs hvs r z hJ hJL).trans
      (congrArg₂ (· * ·) (by simp [Fin.prod_univ_two])
        ((Hvs _ _ z JL hJL).trans ((val_prodGen (fun k i => (f k).left ≫ ![(ι[G₀]).left, 𝟙 G₀.left] i) ![1, -1] ε
          (fun k => LB.pullGen P.L.L _ _ P.sym (f k).left) _ z hJL).trans
          (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (val_pull hJL _ _ _)))))

  have hcub : ∀ (T : Over S) (z : T.left) (J), Good L'.L z J → IsCub (CubTransport.thV (L := L') t z J) := by
    intro T z J hJ
    obtain ⟨JL, hJL⟩ := UU.exists_good_pt P.L.isLB z
    refine CubTransport.isCub_of_twist (isCub_prod (fun k => isCub_comp (isCub_cubV P.c hJL) (postHom (f k) T)) ε)
      (MonoidHom.id _) (fun p => (chg (fun k => (f k).left) ε J JL z p.left)⁻¹) fun a b d => ?_
    rw [show CubTransport.thV (L := L') t z J a b d = _ from vt T z J JL hJ hJL a b d]
    simp only [MonoidHom.id_apply, postHom, MonoidHom.mk'_apply]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  let c : CubicalStr H L' := CubTransport.cubicalOfVal t ht hcub
  refine ⟨⟨L', c, sym, symGen, ?_, ?_⟩, rfl⟩
  · refine corr_of_val hM fun y J hJ => ?_
    obtain ⟨JL, hJL⟩ := UU.exists_good_pt P.L.isLB y
    refine (val_pull hJ _ _ _).trans ((vsym _ y J JL hJ hJL).trans (Eq.trans ?_ (val_one _).symm))
    have e₂ : eSec H ≫ (ι[H]).left = eSec H := by rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    have s1 : val P.sym (eSec G₀) y JL = 1 := by
      have := (val_pull hJL P.sym (eSec G₀) (𝟙 _)).symm.trans ((val_corr hJL P.sym_rig (𝟙 _)).trans (val_one _))
      rwa [Category.id_comp] at this
    simp only [Category.id_comp, Category.assoc, e₂, he, s1, one_zpow, Finset.prod_const_one, mul_inv_cancel,
      _root_.mul_one]
  · intro T x y u z J hJ
    obtain ⟨JL, hJL⟩ := UU.exists_good_pt P.L.isLB z
    have hC : ∀ a b d : T ⟶ H, cubV c z J a b d =
        (chg (fun k => (f k).left) ε J JL z (a * b * d).left * (chg (fun k => (f k).left) ε J JL z (a * b).left)⁻¹ *
          (chg (fun k => (f k).left) ε J JL z (a * d).left)⁻¹ * (chg (fun k => (f k).left) ε J JL z (b * d).left)⁻¹ *
          chg (fun k => (f k).left) ε J JL z a.left * chg (fun k => (f k).left) ε J JL z b.left *
          chg (fun k => (f k).left) ε J JL z d.left * (chg (fun k => (f k).left) ε J JL z (1 : T ⟶ H).left)⁻¹) *
        ∏ k, cubV P.c z JL (a ≫ f k) (b ≫ f k) (d ≫ f k) ^ ε k := fun a b d => vt T z J JL hJ hJL a b d
    have hinv : ∀ a : T ⟶ H, a.left ≫ (ι[H]).left = (a⁻¹).left := fun a => by rw [Hom.inv_def]; rfl
    have hS : ∀ a : T ⟶ H, val sym a.left z J = (chg (fun k => (f k).left) ε J JL z (a⁻¹).left *
        (chg (fun k => (f k).left) ε J JL z a.left)⁻¹) * ∏ k, val P.sym (a ≫ f k).left z JL ^ ε k := fun a =>
      (vsym a.left z J JL hJ hJL).trans (by rw [hinv]; rfl)
    have hP : (∏ k, cubV P.c z JL (x⁻¹ ≫ f k) (y⁻¹ ≫ f k) (u⁻¹ ≫ f k) ^ ε k) *
        (∏ k, val P.sym ((x * y) ≫ f k).left z JL ^ ε k) * (∏ k, val P.sym ((x * u) ≫ f k).left z JL ^ ε k) *
        (∏ k, val P.sym ((y * u) ≫ f k).left z JL ^ ε k) =
        (∏ k, cubV P.c z JL (x ≫ f k) (y ≫ f k) (u ≫ f k) ^ ε k) *
        (∏ k, val P.sym ((x * y * u) ≫ f k).left z JL ^ ε k) * (∏ k, val P.sym (x ≫ f k).left z JL ^ ε k) *
        (∏ k, val P.sym (y ≫ f k).left z JL ^ ε k) * (∏ k, val P.sym (u ≫ f k).left z JL ^ ε k) := by
      simp only [← Finset.prod_mul_distrib, ← mul_zpow]
      refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
      have m : ∀ a b : T ⟶ H, (a * b) ≫ f k = (a ≫ f k) * (b ≫ f k) := fun a b => MonObj.mul_comp a b (f k)
      have i : ∀ a : T ⟶ H, a⁻¹ ≫ f k = (a ≫ f k)⁻¹ := fun a => map_inv (postHom (f k) T) a
      simp only [m, i]
      exact P.sym_cub T (x ≫ f k) (y ≫ f k) (u ≫ f k) z JL hJL
    rw [hC, hC, hS, hS, hS, hS, hS, hS, hS]
    have p4 : x⁻¹ * y⁻¹ * u⁻¹ = (x * y * u)⁻¹ := by rw [mul_inv, mul_inv]
    have p1 : x⁻¹ * y⁻¹ = (x * y)⁻¹ := (mul_inv x y).symm
    have p2 : x⁻¹ * u⁻¹ = (x * u)⁻¹ := (mul_inv x u).symm
    have p3 : y⁻¹ * u⁻¹ = (y * u)⁻¹ := (mul_inv y u).symm
    rw [p4, p1, p2, p3]
    apply Additive.ofMul.injective
    have hP' := congrArg Additive.ofMul hP
    simp only [ofMul_mul, ofMul_inv] at hP' ⊢
    linear_combination (norm := abel) hP'

end Main
end GlobalTheory.LinCombCP
end
