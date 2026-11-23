import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.TwCompare

open GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam

section Move

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P₀ : PolAV S'} {a : P₀.A.left ⟶ P.A.left}
  (hp : IsGrpPullback P₀.A P.A f a) {w : LB.Iso P₀.L (P.L.pull a)} (hw : w.IsGen)

include hp hw in

theorem exists_frames {T : Over S} {T' : Over S'} {g : T'.left ⟶ T.left}
    {rig : LB.Gen (P.L.pull (eSec P.A))} (hrig : rig.IsGen) {I : Type} {x : I → (T ⟶ P.A)} {x' : I → (T' ⟶ P₀.A)}
    (hx : ∀ i, (x' i).left ≫ a = g ≫ (x i).left) {n : ℕ}
    {τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => 1))}
    (H : ∀ i, IsTorsFrame P rig n (x i) (τ i)) :
    ∃ (rig' : LB.Gen (P₀.L.pull (eSec P₀.A)))
      (τ' : ∀ i, LB.Gen (LB.LinComb P₀.L (Y := T'.left) (K := Fin 1) (fun _ => (x' i).left) (fun _ => 1))),
      GenThrough w (fun _ : PUnit => eSec P₀.A) (fun _ : PUnit => eSec P.A) (fun _ => 1) rig' rig f ∧
      (∀ i, IsTorsFrame P₀ rig' n (x' i) (τ' i)) ∧
      ∀ i, GenThrough w (fun _ : Fin 1 => (x' i).left) (fun _ : Fin 1 => (x i).left) (fun _ => 1) (τ' i) (τ i) g := by
  obtain ⟨rig', -, Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P₀.A) (φ := fun _ => eSec P.A)
    (ε := fun _ => 1) (h := f) hw P.isLB P₀.isLB (fun _ => PolBaseChange.eSec_comm hp) rig hrig
  choose τ' hτ' Hτ using fun i => exists_gen_through (φ' := fun _ : Fin 1 => (x' i).left) (h := g) hw P.isLB P₀.isLB
    (fun _ => hx i) (τ i) (H i).2.1
  refine ⟨rig', τ', Hr, fun i => FrameMove.isTorsFrame_move hp hw (fun Z r z J J' hJ hJ' =>
    (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))) (hx i) (H i) (hτ' i)
    (fun z J J' hJ hJ' => ?_), Hτ⟩
  have := Hτ i _ (𝟙 _) z J J' hJ hJ'
  rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this

include hw in

theorem isTwVal_move {T T₀ : Over S} {T' : Over S'} {σ : T'.left ⟶ T.left} (hσ : σ ≫ T.hom = T'.hom ≫ f)
    {β : T ⟶ T₀} {g : T'.left ⟶ T₀.left} (hg : g ≫ T₀.hom = T'.hom ≫ f) (hβ : σ ≫ β.left = g)
    {θ : LB.Sec (LPow P.A P.L 1 T₀)} {θ₁ : LB.Sec (LPow P₀.A P₀.L 1 T')} (hθ : SecRel hp g hg w θ₁ θ)
    {z₀ : T₀ ⟶ P.A} {y : T' ⟶ P₀.A} {τ τ₁}
    (hτ : GenThrough w (fun _ : Fin 1 => y.left) (fun _ : Fin 1 => z₀.left) (fun _ => 1) τ₁ τ g)
    {N m : ℕ} {X H : T' ⟶ P₀.A} {x h : T ⟶ P.A} (hN : X ^ N = 1) (hx : σ ≫ x.left = X.left ≫ a)
    (hh : σ ≫ h.left = H.left ≫ a) (hy : H ^ m = y) {v : Γ(T.left, ⊤)} (E : IsTwVal P N m θ τ β x h v) :
    ∃ (α : LB.Gen (LB.LinComb P₀.L (K := Fin 2) ![(snd T' P₀.A).left, (snd T' P₀.A ^ m).left] ![(N : ℤ), -1]))
      (U : ThetaGrp P₀.A P₀.L N T'), α.IsGen ∧ SymLift P₀.A P₀.L N N X U ∧ ∀ (z : T'.left) J, Good P₀.L z J →
        gs σ z ⊤ v * (val α (ptSecT P₀.A H).left z J * val τ₁ (𝟙 _) z J).val =
          (tval U (ptSecT P₀.A H).left z J).val * ((val α (ptSecT P₀.A (X * H)).left z J).val *
            VVRank.sv P₀.A θ₁ (ptSecT P₀.A ((X * H) ^ m)).left z J) := by
  have := P₀.isAb.comm
  have hL₀ := P.isLB
  have hL₁ := P₀.isLB
  obtain ⟨α₀, U₀, hα₀, hU₀, E⟩ := E
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp σ hσ hw hL₀ hL₁ (psi_pow hp σ hσ m) α₀ hα₀
  obtain ⟨U, hU, hU'⟩ := symLift_move hp σ hσ hw hL₀ hL₁ hx hN hU₀
  have e : psi hp σ hσ ≫ (β ▷ P.A).left = psi hp g hg := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  have hθ' : SecRel hp σ hσ w θ₁ (VVRank.pullS P.A 1 β θ) := fun Z r z J J' hJ hJ' => by
    rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc, e]
    exact hθ Z r z J J' hJ hJ'
  obtain ⟨s₀, hs₀⟩ := VVRank.exists_isTwistPull P.A (ψ := mulT P.A T m) (m := snd T P.A ^ m) (hm := lift_snd _ _)
    (a := N) (b := 1) hL₀ hα₀ (VVRank.pullS P.A 1 β θ)
  obtain ⟨s, hs⟩ := exists_secRel hp σ hσ hw hL₀ hL₁ s₀
  have h₁ : IsTwistPull P₀.A P₀.L (mulT P₀.A T' m) (snd T' P₀.A ^ m) (lift_snd _ _) N 1 α θ₁ s :=
    isTwistPull_move hp σ hσ hL₀ hL₁ (psi_pow hp σ hσ m) hα vα hθ' hs hs₀
  obtain ⟨s₀', hs₀'⟩ : ∃ t, IsActOf P.A P.L (N : ℤ) U₀ s₀ t := VVRank.exists_isTwistPull P.A hL₀ U₀.isGen s₀
  obtain ⟨s', hs'⟩ := exists_secRel hp σ hσ hw hL₀ hL₁ s₀'
  have h₂ := hU' _ _ _ _ hs hs' hs₀'
  refine ⟨α, U, hα, hU, fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL₀ z
  have E' := E _ σ z J hJ
  have a₀ := VVRank.sv_of_isTwistPull P.A hs₀' (σ ≫ (ptSecT P.A h).left) z hJ
  have a₁ := VVRank.sv_of_isTwistPull P.A hs₀ (σ ≫ (ptSecT P.A (x * h)).left) z hJ
  have b₀ := VVRank.sv_of_isTwistPull P₀.A h₂ (ptSecT P₀.A H).left z hJ'
  have b₁ := VVRank.sv_of_isTwistPull P₀.A h₁ (ptSecT P₀.A (X * H)).left z hJ'
  rw [Category.assoc, ThetaCompare.pt_mulT, VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc] at a₁
  rw [Category.assoc, ThetaCompare.pt_translT, congrArg (fun q => ptSecT P.A (q * h)) hU₀.pt_eq, a₁] at a₀
  rw [ThetaCompare.pt_mulT] at b₁
  rw [ThetaCompare.pt_translT, congrArg (fun q => ptSecT P₀.A (q * H)) hU.pt_eq, b₁] at b₀
  have c₀ := hs' _ (ptSecT P₀.A H).left z J J' hJ hJ'
  have c₁ := vα _ (ptSecT P₀.A H).left z J J' hJ hJ'
  have c₂ := hτ _ (𝟙 _) z J J' hJ hJ'
  have e₂ : (ptSecT P₀.A H).left ≫ (snd T' P₀.A ^ m).left = y.left := by
    rw [← Over.comp_left, SymLiftOdd.comp_pow', ThetaCompare.pt_snd, hy]
  rw [psi_ptSec hp σ hσ hh] at c₀ c₁
  rw [e₂] at c₁
  rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at c₂
  have E₂ : gs σ z ⊤ v * (val α₀ (σ ≫ (ptSecT P.A h).left) z J * val τ g z J).val =
      VVRank.sv P.A s₀' (σ ≫ (ptSecT P.A h).left) z J := by
    rw [← hβ, a₀, ← _root_.mul_assoc, ← Units.val_mul]
    exact E'
  rw [c₀, b₀, c₁, c₂] at E₂
  refine (Units.mul_right_inj _).1 (Eq.trans ?_ E₂)
  rw [mul_left_comm, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

end Move

theorem frame_ratio_pow {S : Scheme.{0}} (P : PolAV S) {T : Over S} {N M m : ℕ} {rig : LB.Gen (P.L.pull (eSec P.A))}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1])}
    (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L rig T ((N : ℤ) - 1)))
    {h w : T ⟶ P.A} (hw : w = h ^ m) {τ τ'} (hτ : IsTorsFrame P rig M h τ) (hτ' : IsTorsFrame P rig M w τ')
    {y : T.left} {J} (hJ : Good P.L y J) :
    (val α (ptSecT P.A h).left y J * val τ' (𝟙 _) y J * (val τ (𝟙 _) y J ^ N)⁻¹) ^ (M ^ 2) = 1 := by
  subst hw
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨β, hβ⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P M T
  have rα := ThetaCompare.Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rβ := ThetaCompare.Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ M) rfl rfl
  have c := (((rα.pow hJ (M ^ 2)).mul hJ (rβ.pull hJ (snd T P.A ^ m))).mul hJ
    ((rβ.pow hJ N).mul hJ (rα.pull hJ (snd T P.A ^ M))).inv).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, mul_comm m M]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) h 1
  simp only [SymLiftOdd.comp_pow', ThetaCompare.pt_snd, hτ.1, one_pow] at c
  have a₂ := ThetaCompare.torsFrame_pow hG P hβ hτ hJ
  have a₃ := ThetaCompare.torsFrame_pow hG P hβ hτ' hJ
  have a₄ := val_corr hJ hn (𝟙 T.left)
  rw [val_pull hJ, ThetaCompare.val_rigT _ _ hJ, Category.id_comp] at a₄
  apply Additive.ofMul.injective
  replace c := congrArg Additive.ofMul c
  replace a₂ := congrArg Additive.ofMul a₂
  replace a₃ := congrArg Additive.ofMul a₃
  replace a₄ := congrArg Additive.ofMul a₄
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one] at c a₂ a₃ a₄ ⊢
  linear_combination (norm := module) c + a₃ - N • a₂ + (M ^ 2) • a₄

theorem sv_cross {K : Type} [Field K] (P : PolAV (Sp K)) (θ θ' : LB.Sec (LPow P.A P.L 1 (baseOver (Sp K))))
    (p q : baseOver (Sp K) ⟶ P.A) (z : (baseOver (Sp K)).left) {J} (hJ : Good P.L z J) :
    VVRank.sv P.A θ (ptSecT P.A p).left z J * VVRank.sv P.A θ' (ptSecT P.A q).left z J =
      VVRank.sv P.A θ' (ptSecT P.A p).left z J * VVRank.sv P.A θ (ptSecT P.A q).left z J := by
  obtain ⟨V, hV, hθ⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny P z
  obtain ⟨t, ht⟩ := hθ K (𝟙 _) (by
    rintro _ ⟨v, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) v z]
    exact hV)
  obtain ⟨r, hr⟩ := ht θ
  obtain ⟨r', hr'⟩ := ht θ'
  have a₁ := ThetaCompare.sval_smul (T := baseOver (Sp K)) hr p hJ
  have a₂ := ThetaCompare.sval_smul (T := baseOver (Sp K)) hr q hJ
  have a₃ := ThetaCompare.sval_smul (T := baseOver (Sp K)) hr' p hJ
  have a₄ := ThetaCompare.sval_smul (T := baseOver (Sp K)) hr' q hJ
  refine (congrArg₂ (· * ·) a₁ a₄).trans (Eq.trans ?_ (congrArg₂ (· * ·) a₃ a₂).symm)
  ring

theorem exists_cst_bij {K : Type} [Field K] (z : (baseOver (Sp K)).left) :
    ∃ c : K →+* (baseOver (Sp K)).left.presheaf.stalk z, Function.Bijective c ∧
      ∀ a, gs (𝟙 (baseOver (Sp K)).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = c a := by
  refine ⟨((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom,
    ⟨RingHom.injective _, fun s => ?_⟩, fun _ => gs_eq (𝟙 _) z ⊤ trivial _⟩
  obtain ⟨U, hU, t, rfl⟩ := (Sp K).presheaf.germ_exist s
  obtain rfl : U = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim (α := PrimeSpectrum K) q z]
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 t
  exact ⟨b, rfl⟩

theorem isValueAt_act {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (t h : S.Gam) {σ}
    (H : IsActOf ρ.P.A ρ.P.L S.N (ρ.U t) (ρ.s ρ.i₀) σ) :
    IsValueAt ρ.P.A ρ.P.L S.N σ (ρ.pt h) (powFrame ρ.P.A ρ.P.L (ρ.pt h) (ρ.fr h) S.N)
      (fn (∑ l, algebraMap o S.R (S.ρ t l ρ.i₀) * ⟨S.ev h l, S.ev_mem h l⟩ : S.R)) := by
  refine isValueAt_of_sv ρ.P.isLB fun y J hJ => ?_
  let g : S.R →+* (baseOver (Sp S.R)).left.presheaf.stalk y :=
    ((Sp S.R).presheaf.germ ⊤ y trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom
  have hgs : ∀ b : S.R, gs (𝟙 (baseOver (Sp S.R)).left) y ⊤ (fn b) = g b := fun b => gs_eq _ y ⊤ trivial _
  have b₂ := EvCrd.sval_sum (ρ.U_act t ρ.i₀ σ H) (ρ.pt h) hJ
  simp only [fun l => ThetaCompare.sval_valueAt (ρ.ev_val l h) hJ, hgs, ← _root_.mul_assoc, ← Finset.sum_mul] at b₂
  rw [Category.id_comp, hgs, map_sum]
  simp only [map_mul]
  exact b₂

theorem exists_generic_data {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {P₀ : PolAV (Sp Ω)} {a : P₀.A.left ⟶ ρ.P.A.left} (hp : IsGrpPullback P₀.A ρ.P.A (spMap S.R.val.toRingHom) a)
    (lb : LBIso P₀.L (ρ.P.L.pull a)) {X : S.Gam → (baseOver (Sp Ω) ⟶ P₀.A)}
    (hX : ∀ b, (X b).left ≫ a = spMap S.R.val.toRingHom ≫ (ρ.pt b).left) (hpow : ∀ (n : ℕ) b, X (n • b) = X b ^ n) :
    ∃ (rig : LB.Gen (P₀.L.pull (eSec P₀.A)))
      (τ : ∀ b, LB.Gen (LB.LinComb P₀.L (Y := (baseOver (Sp Ω)).left) (K := Fin 1) (fun _ => (X b).left) (fun _ => 1)))
      (θ : LB.Sec (LPow P₀.A P₀.L 1 (baseOver (Sp Ω))))
      (α : LB.Gen (LB.LinComb P₀.L (K := Fin 2)
        ![(snd (baseOver (Sp Ω)) P₀.A).left, (snd (baseOver (Sp Ω)) P₀.A ^ (ρ.n ^ ρ.k)).left] ![(S.N : ℤ), -1])),
      α.IsGen ∧ (∀ b, IsTorsFrame P₀ rig (S.r * S.N) (X b) (τ b)) ∧
      (∀ b, IsValueAt P₀.A P₀.L 1 θ (X b) (τ b) (fn (S.th b))) ∧
      LB.Gen.Corr P₀.L _ _ _ _ (LB.pullGen P₀.L _ _ α (ptSecT P₀.A 1).left)
        (rigT P₀.A P₀.L rig (baseOver (Sp Ω)) ((S.N : ℤ) - 1)) ∧
      ∀ (t : S.Gam) (U : ThetaGrp P₀.A P₀.L S.N (baseOver (Sp Ω))), SymLift P₀.A P₀.L S.N S.N (X (S.r • t)) U →
        ∀ (h : S.Gam) (z : (baseOver (Sp Ω)).left) J, Good P₀.L z J →
          (tval U (ptSecT P₀.A (X h)).left z J).val * ((val α (ptSecT P₀.A (X (S.r • t) * X h)).left z J).val *
            VVRank.sv P₀.A θ (ptSecT P₀.A ((X (S.r • t) * X h) ^ (ρ.n ^ ρ.k))).left z J) =
          gs (𝟙 _) z ⊤ (fn (∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j)) * (val (τ h) (𝟙 _) z J ^ S.N).val := by
  obtain ⟨w, hw⟩ := lb
  have hL₀ := ρ.P.isLB
  have hL₁ := P₀.isLB
  have := P₀.isAb.comm
  let g : (baseOver (Sp Ω)).left ⟶ (baseOver (Sp S.R)).left := spMap S.R.val.toRingHom
  have hg : g ≫ (baseOver (Sp S.R)).hom = (baseOver (Sp Ω)).hom ≫ spMap S.R.val.toRingHom :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  obtain ⟨rig, τ, vrig, hτ, vτ⟩ := exists_frames hp hw (T := baseOver (Sp S.R)) (g := g) ρ.rig_gen hX ρ.fr_tors
  obtain ⟨θ, hθ⟩ := exists_secRel hp g hg hw hL₀ hL₁ ρ.th₁
  obtain ⟨s, hs⟩ := exists_secRel hp g hg hw hL₀ hL₁ (ρ.s ρ.i₀)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp g hg hw hL₀ hL₁ (psi_pow hp g hg (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have h₁ : IsTwistPull P₀.A P₀.L (mulT P₀.A _ (ρ.n ^ ρ.k)) (snd _ P₀.A ^ (ρ.n ^ ρ.k)) (lift_snd _ _) S.N 1 α θ s :=
    isTwistPull_move hp g hg hL₀ hL₁ (psi_pow hp g hg (ρ.n ^ ρ.k)) hα vα hθ hs ρ.s_zero
  refine ⟨rig, τ, θ, α, hα, hτ, fun b => ?_, ThetaGeom.norm_move hp g hg hL₀ hL₁ vrig vα ρ.α_norm,
    fun t U hU h z J hJ => ?_⟩
  · have q := isValueAt_move hp g hg hL₀ hL₁ (hX b).symm (vτ b) hθ (ρ.th_val b)
    rw [spMap_appTop_fn] at q
    exact q
  · have hN : X (S.r • t) ^ S.N = 1 := by
      rw [hpow, ← pow_mul]
      exact (hτ t).1
    have hodd : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
    obtain ⟨U₂, hU₂, hU'⟩ := symLift_move hp g hg hw hL₀ hL₁ (hX (S.r • t)).symm hN (ρ.U_sym t)
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ, IsActOf ρ.P.A ρ.P.L (S.N : ℤ) (ρ.U t) (ρ.s ρ.i₀) σ :=
      VVRank.exists_isTwistPull ρ.P.A hL₀ (ρ.U t).isGen _
    obtain ⟨σ, hσ⟩ := exists_secRel hp g hg hw hL₀ hL₁ σ₀
    have q := isValueAt_move hp g hg hL₀ hL₁ (hX h).symm (ThetaGeom.genThrough_pow g (vτ h) S.N) hσ
      (isValueAt_act ρ t h hσ₀)
    rw [spMap_appTop_fn, map_sum] at q
    have q' := sv_of_isValueAt q (𝟙 _) z hJ
    have b₀ := VVRank.sv_of_isTwistPull P₀.A (hU' _ _ _ _ hs hσ hσ₀) (ptSecT P₀.A (X h)).left z hJ
    have b₁ := VVRank.sv_of_isTwistPull P₀.A h₁ (ptSecT P₀.A (X (S.r • t) * X h)).left z hJ
    rw [ThetaCompare.pt_mulT] at b₁
    rw [ThetaCompare.pt_translT, congrArg (fun q => ptSecT P₀.A (q * X h)) hU₂.pt_eq, b₁] at b₀
    rw [Category.id_comp, ThetaGeom.val_powFrame, zpow_natCast, b₀] at q'
    have u : tval U (ptSecT P₀.A (X h)).left z J = tval U₂ (ptSecT P₀.A (X h)).left z J :=
      val_corr hJ (SymLiftOdd.symLift_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns P₀.isAb hL₁ hodd U U₂ hU hU₂) _
    rw [u]
    exact q'

theorem twVal_eq_root_mul : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] [ArithBase o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left) (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)), IsGenLab ρ ρ' lab φ P₀ a a' x → ∀ (m : ℕ), S'.N = m ^ 2 → ∀ (κ x₀ : S.Gam) (h : S'.Gam), m • h = lab κ → ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (t : S'.Gam) (v : Ω'), IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h) ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom v) → v * S'.th (lab x₀) = ξ * φ (S.th x₀) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := by
  intro o Ω o' Ω' _ _ _ _ _ _ _ _ S S' ρ ρ' lab φ P₀ a a' x hgen m hm κ x₀ h hκ
  obtain ⟨hp, hp', ⟨w, hw⟩, lb', hpt, hlab⟩ := hgen
  obtain rfl : m = ρ'.n ^ ρ'.k := Nat.pow_left_injective two_ne_zero (hm.symm.trans ρ'.N_eq)
  choose u hu hua hua' using hpt
  have := P₀.isAb.comm
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨X, hX, hX'⟩ : ∃ X : S'.Gam → (baseOver (Sp Ω') ⟶ P₀.A), (∀ b, (X b).left ≫ a = (x b).left) ∧
      ∀ b, (X b).left ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt b).left := ⟨fun b => Over.homMk (u b) (hu b), hua, hua'⟩
  have hadd : ∀ b c, X (b + c) = X b * X c := fun b c => by
    refine Over.OverMorphism.ext (hp'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [hX', ρ'.pt_add]
    exact over_mul hp' (T := baseOver (Sp Ω')) (T₀ := baseOver (Sp S'.R)) _
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hX' b).symm (hX' c).symm
  have hpow : ∀ (n : ℕ) b, X (n • b) = X b ^ n := fun n b => by
    induction n with
    | zero =>
      have h := hadd 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  obtain ⟨rig₂, τ₂, θ₂, α₂, hα₂, hτ₂, hθ₂, hn₂, hact⟩ := exists_generic_data ρ' hp' lb' hX' hpow
  let g : (baseOver (Sp Ω')).left ⟶ (baseOver (Sp S.R)).left := spMap (φ.comp S.R.val.toRingHom)
  have hg : g ≫ (baseOver (Sp S.R)).hom = (baseOver (Sp Ω')).hom ≫ spMap (φ.comp S.R.val.toRingHom) :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  have hy : ∀ k, (X (lab k)).left ≫ a = g ≫ (ρ.pt k).left := fun k => by
    rw [hX, hlab]
    rfl
  obtain ⟨rig₁, τ₁, -, hτ₁, vτ₁⟩ := exists_frames hp hw (T := baseOver (Sp S.R)) (g := g) ρ.rig_gen
    (x' := fun k => X (lab k)) hy ρ.fr_tors
  obtain ⟨θ₁, hθ₁⟩ := exists_secRel hp g hg hw ρ.P.isLB P₀.isLB ρ.th₁
  have hv₁ := isValueAt_move hp g hg ρ.P.isLB P₀.isLB (hy x₀).symm (vτ₁ x₀) hθ₁ (ρ.th_val x₀)
  rw [spMap_appTop_fn] at hv₁
  let z : (baseOver (Sp Ω')).left := IsLocalRing.closedPoint Ω'
  obtain ⟨J, hJ⟩ := exists_good' P₀.isLB z
  obtain ⟨c, hc, hcv⟩ := exists_cst_bij z
  have hh : X (lab κ) = X h ^ (ρ'.n ^ ρ'.k) := by rw [← hκ, hpow]
  have r₁ := frame_ratio_pow P₀ hα₂ hn₂ hh (hτ₂ h) (hτ₂ (lab κ)) hJ
  have r₂ := (DivDeep.torsFrame_two_levels P₀ (hτ₁ κ) (hτ₂ (lab κ)) hJ).trans
    (DivDeep.torsFrame_two_levels P₀ (hτ₁ x₀) (hτ₂ (lab x₀)) hJ).symm
  obtain ⟨ξ, hξ⟩ := hc.2 (val (τ₂ h) (𝟙 _) z J ^ S'.N * val (τ₁ x₀) (𝟙 _) z J *
    (val α₂ (ptSecT P₀.A (X h)).left z J * val (τ₁ κ) (𝟙 _) z J * val (τ₂ (lab x₀)) (𝟙 _) z J)⁻¹).val
  have p₁ : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have p₂ : 0 < S'.r * S'.N := Nat.mul_pos S'.r_pos (by have := S'.N_ge; omega)
  refine ⟨ξ, ⟨(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2, by positivity, hc.1 ?_⟩, fun t v E => hc.1 ?_⟩
  · rw [map_pow, hξ, map_one, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
    apply Additive.ofMul.injective
    replace r₁ := congrArg Additive.ofMul r₁
    replace r₂ := congrArg Additive.ofMul r₂
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div, ofMul_one] at r₁ r₂ ⊢
    linear_combination (norm := module) -((S.r * S.N) ^ 2 • r₁) - r₂
  · have hN : X (S'.r • t) ^ S'.N = 1 := by
      rw [hpow, ← pow_mul]
      exact (hτ₂ t).1
    obtain ⟨α, U, hα, hU, e₁⟩ := isTwVal_move hp hw (T := genPt (φ.comp S.R.val.toRingHom)) (T' := baseOver (Sp Ω'))
      (σ := 𝟙 (Sp Ω')) rfl hg (Category.id_comp _) hθ₁ (vτ₁ κ) hN ((Category.id_comp _).trans (hX _).symm)
      ((Category.id_comp _).trans (hX _).symm) hh.symm E
    replace e₁ := (congrArg (· * _) (hcv v)).symm.trans (e₁ z J hJ)
    have e₂ := (hact t U hU h z J hJ).trans (congrArg (· * _) (hcv _))
    have e₃ := sv_cross P₀ θ₁ θ₂ ((X (S'.r • t) * X h) ^ (ρ'.n ^ ρ'.k)) (X (lab x₀)) z hJ
    have e₄ : VVRank.sv P₀.A θ₁ (ptSecT P₀.A (X (lab x₀))).left z J = c (φ (S.th x₀)) * (val (τ₁ x₀) (𝟙 _) z J).val :=
      (ThetaCompare.sval_valueAt hv₁ hJ).trans (congrArg (· * _) (hcv _))
    have e₅ : VVRank.sv P₀.A θ₂ (ptSecT P₀.A (X (lab x₀))).left z J =
        c (S'.th (lab x₀)) * (val (τ₂ (lab x₀)) (𝟙 _) z J).val :=
      (ThetaCompare.sval_valueAt (hθ₂ _) hJ).trans (congrArg (· * _) (hcv _))
    have e₆ := ((ThetaCompare.Reg.two (y := z) (J := J) α hα _ _ rfl rfl).mul hJ
      (ThetaCompare.Reg.two (y := z) (J := J) α₂ hα₂ _ _ rfl rfl).inv).const hG P₀.isAb P₀.isLB hJ
      (fun U _ h => mul_inv_cancel _) (X (S'.r • t) * X h) (X h)
    rw [e₄, e₅] at e₃
    rw [map_mul, map_mul, map_mul, hξ]
    have key : ∀ {R : Type} [CommRing R] (v th th' E s₁ s₂ : R) (aH aX bH bX u tk t0 t0' tN : Rˣ),
        v * (aH * tk).val = u.val * (aX.val * s₁) → u.val * (bX.val * s₂) = E * tN.val →
        s₁ * (th' * t0'.val) = s₂ * (th * t0.val) → aX * bX⁻¹ = aH * bH⁻¹ →
        v * th' = (tN * t0 * (bH * tk * t0')⁻¹).val * th * E := by
      intro R _ v th th' E s₁ s₂ aH aX bH bX u tk t0 t0' tN h₁ h₂ h₃ h₄
      obtain rfl : aX = aH * bH⁻¹ * bX := by rw [← h₄, inv_mul_cancel_right]
      have k₁ := tk.mul_inv
      have k₂ := t0'.mul_inv
      refine (Units.mul_left_inj (aH * tk * t0')).1 ?_
      simp only [mul_inv, Units.val_mul] at h₁ ⊢
      linear_combination (th' * t0'.val) * h₁ + (u.val * aH.val * bH⁻¹.val * bX.val) * h₃ +
        (aH.val * bH⁻¹.val * th * t0.val) * h₂ -
        (tN.val * t0.val * bH⁻¹.val * th * E * aH.val) * (t0'.val * t0'⁻¹.val) * k₁ -
        (tN.val * t0.val * bH⁻¹.val * th * E * aH.val) * k₂
    exact key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ e₃ e₆

end GlobalTheory.UPoinc.TwCompare
