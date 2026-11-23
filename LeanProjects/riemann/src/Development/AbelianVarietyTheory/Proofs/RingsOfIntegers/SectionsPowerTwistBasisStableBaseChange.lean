import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gm gs_eq gs_res gs_pull gs_mul gs_unit fn_ext sec_trans ChartPull chartPullSame
  gm_pull_g gm_linComb gm_div mem_pull LBIso Good val sval FormEq exists_sec exists_gen pullMulSec sval_pullMulSec
  val_pull val_inv exists_chart trF gen_chartPull chartPullId)
open GlobalTheory.AbLaw.SecBC

noncomputable section
namespace GlobalTheory.TwistBC

section General

variable {X Y Y' Y'' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def Comb {M : LB Y} {m : ℕ} (s : LB.Sec M) (a : Fin m → Γ(Y, ⊤)) (b : Fin m → LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, rs Y le_top (a i) * (b i).f j

theorem exists_comb {M : LB Y} {m : ℕ} (a : Fin m → Γ(Y, ⊤)) (b : Fin m → LB.Sec M) : ∃ s, Comb s a b :=
  ⟨⟨fun j => ∑ i, rs Y le_top (a i) * (b i).f j, fun i j => by
    have h := fun l => (b l).compat i j
    change ∀ l, rs Y _ _ = _ * rs Y _ _ at h
    change rs Y _ _ = _ * rs Y _ _
    simp only [map_sum, map_mul, rs_rs, h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring⟩, fun _ => rfl⟩

theorem comb_iff (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {m : ℕ} (s : LB.Sec (LB.LinComb L φ ε))
    (a : Fin m → Γ(Y, ⊤)) (b : Fin m → LB.Sec (LB.LinComb L φ ε)) :
    Comb s a b ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s r z J = ∑ i, gs r z ⊤ (a i) * sval (b i) r z J := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j) (∑ i, rs Y le_top (a i) * (b i).f j) =
        ∑ i, gs r z ⊤ (a i) * gs r z (LB.wchart L φ j) ((b i).f j) := fun Z r z j hm => by
    rw [gs_sum r z _ hm]
    exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm _))
  constructor
  · intro h Z r z J hJ
    exact (congrArg (gs r z _) (h _)).trans (key Z r z _ (hJ.mem φ r))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    have hI' : Good L y I := hI
    refine (sec_trans s (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))).trans (Eq.trans ?_ (key _ (𝟙 Y) y j hy).symm)
    refine (congrArg (_ * ·) (h _ (𝟙 Y) y I hI')).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (b i) (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))]
    exact mul_left_comm _ _ _

def chartQuot (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    ChartPull (LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε))
      (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) (𝟙 Y) :=
  have le : ∀ p : (K' → L.ι) × (K → L.ι), LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤
      LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := fun p y hy => Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  { idx := fun p => Sum.elim p.1 p.2
    le := le
    g := fun y p q hp hq => by
      refine (gm_div _ _ (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans ?_
        (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm)
      refine (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y p.1 q.1 hp.1 hq.1)
        (gm_linComb L φ ε (𝟙 Y) y p.2 q.2 hp.2 hq.2)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rfl }

def chartTwice (L : LB X) (a : Y ⟶ X) (b : Y' ⟶ Y) (c : Y' ⟶ X) (h : c = b ≫ a) :
    ChartPull ((L.pull a).pull b) (L.pull c) (𝟙 Y') :=
  have le : ∀ J : PUnit → PUnit → L.ι, ((L.pull a).pull b).U J ≤ (L.pull c).U (J PUnit.unit) := fun J y hy => by
    subst h
    exact (mem_pull (L := L) (F := b ≫ a)).2 ((mem_pull (L := L) (F := a)).1 ((mem_pull (L := L.pull a)).1 hy))
  { idx := fun J => J PUnit.unit
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (L.pull a) b (𝟙 Y') y J J' hj hj').trans ((gm_pull_g L a _ y _ _
        ((mem_pull (L := L.pull a)).1 hj) ((mem_pull (L := L.pull a)).1 hj')).trans
        (Eq.trans ?_ (gm_pull_g L c (𝟙 Y') y _ _ (le J hj) (le J' hj')).symm))
      subst h
      rfl }

variable {ψ : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {τ σ : Y ⟶ Y}
  (u : LB.Gen (LB.LinComb L (Sum.elim ψ fun k => τ ≫ φ k) (Sum.elim ε' fun k => -ε k)))

def Tr (s' : LB.Sec (LB.LinComb L ψ ε')) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s' r z J = sval s (r ≫ τ) z J * (val u r z J).val

theorem exists_tr (hL : L.IsLB) (hu : u.IsGen) (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s', Tr u s' s := by
  obtain ⟨s', hs'⟩ := exists_sec (φ' := ψ) (ε' := ε') hL (fun U _ h => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec s τ u hu)
  exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (sval_pullMulSec s τ u hu r z hJ)⟩

theorem exists_tr' (hL : L.IsLB) (hu : u.IsGen) (h₁ : σ ≫ τ = 𝟙 Y) (h₂ : τ ≫ σ = 𝟙 Y)
    (s' : LB.Sec (LB.LinComb L ψ ε')) : ∃ s, Tr u s' s := by
  have hv := DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _ hu) σ
  obtain ⟨s, hs⟩ := exists_sec (φ' := φ) (ε' := ε) hL (fun U _ h => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, inv_inv,
      reassoc_of% h₁]
    rw [mul_inv, inv_inv, mul_inv_cancel_left]) (pullMulSec s' σ _ hv)
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, sval_pullMulSec s' σ _ hv _ z hJ, val_pull hJ, val_inv, Category.assoc, h₂, Category.comp_id,
    Units.inv_mul_cancel_right]

theorem Tr.comb_iff (hL : L.IsLB) (h₁ : σ ≫ τ = 𝟙 Y) {m : ℕ} {a : Fin m → Γ(Y, ⊤)}
    (ha : ∀ i, τ.appTop.hom (a i) = a i) {s' : LB.Sec (LB.LinComb L ψ ε')} {s : LB.Sec (LB.LinComb L φ ε)}
    (hs : Tr u s' s) {b' : Fin m → LB.Sec (LB.LinComb L ψ ε')} {b : Fin m → LB.Sec (LB.LinComb L φ ε)}
    (hb : ∀ i, Tr u (b' i) (b i)) : Comb s' a b' ↔ Comb s a b := by
  have e : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, gs r z ⊤ (a i) = gs (r ≫ τ) z ⊤ (a i) := fun Z r z i =>
    (congrArg (gs r z ⊤) (ha i)).symm.trans (gs_pull r τ z ⊤ trivial _)
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      ((sval s' r z J = ∑ i, gs r z ⊤ (a i) * sval (b' i) r z J) ↔
        sval s (r ≫ τ) z J = ∑ i, gs (r ≫ τ) z ⊤ (a i) * sval (b i) (r ≫ τ) z J) := fun Z r z J hJ => by
    simp only [hs Z r z J hJ, fun i => hb i Z r z J hJ, e Z r z, ← _root_.mul_assoc, ← Finset.sum_mul,
      Units.mul_left_inj]
  rw [TwistBC.comb_iff hL, TwistBC.comb_iff hL]
  refine ⟨fun h Z r z J hJ => ?_, fun h Z r z J hJ => (key Z r z J hJ).2 (h Z _ z J hJ)⟩
  have := (key Z (r ≫ σ) z J hJ).1 (h Z _ z J hJ)
  rwa [Category.assoc, h₁, Category.comp_id] at this

end General

section Fibre

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

def trEnd (d : T ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (translPt A d)

theorem trEnd_comp {d d' : T ⟶ A} (h : d' * d = 1) : (trEnd d).left ≫ (trEnd d').left = 𝟙 _ := by
  rw [← Over.comp_left, ← Over.id_left]
  congr 1
  have e : ∀ x : T ⟶ A, translPt A x = (fst T A ≫ x) * snd T A := fun x => rfl
  ext
  · simp [trEnd]
  · rw [trEnd, trEnd, Category.assoc, lift_snd, e d', MonObj.comp_mul, lift_fst_assoc, lift_snd, e d,
      ← _root_.mul_assoc, ← MonObj.comp_mul, h, MonObj.comp_one, _root_.one_mul, Category.id_comp]

theorem trEnd_fst (d : T ⟶ A) : (trEnd d).left ≫ (fst T A).left = (fst T A).left := by
  rw [← Over.comp_left, trEnd, lift_fst]

theorem trEnd_snd (d : T ⟶ A) : (trEnd d).left ≫ (snd T A).left = (translPt A d).left := by
  rw [← Over.comp_left, trEnd, lift_snd]

theorem finrank_of_isSecBasis [Nontrivial Γ(T.left, ⊤)] {L : LB A.left} {n : ℤ} {m : ℕ}
    {b : Fin m → LB.Sec (LPow A L n T)} (hb : IsSecBasis (LPow A L n T) b) :
    Module.finrank Γ(T.left, ⊤) (SecM A L n T) = m := by
  have e : ∀ (z : Fin m → Γ(T.left, ⊤)) j, (SecM.toSec A (∑ i, z i • (SecM.ofSec A (b i) : SecM A L n T))).f j =
      ∑ l, rs (T ⊗ A).left le_top ((fst T A).left.appTop.hom (z l)) * (b l).f j := by
    intro z j
    change (∑ i, z i • (SecM.ofSec A (b i) : SecM A L n T)).1 j = _
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have li : LinearIndependent Γ(T.left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L n T)) := by
    rw [Fintype.linearIndependent_iff]
    intro z hz
    have r₁ := e z
    have r₀ := e 0
    rw [hz] at r₁
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at r₀
    exact congrFun ((hb (SecM.toSec A 0)).unique (y₂ := 0) r₁ r₀)
  have sp : ⊤ ≤ Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L n T)) := fun s _ => by
    obtain ⟨z, hz, -⟩ := hb (SecM.toSec A s)
    have e' : s = ∑ i, z i • (SecM.ofSec A (b i) : SecM A L n T) :=
      congrArg (SecM.ofSec A) (sec_ext fun j => (hz j).trans (e z j).symm)
    rw [e']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [Module.finrank_eq_card_basis (Module.Basis.mk li sp), Fintype.card_fin]

variable {L : LB A.left} {K' : Type} [Fintype K'] {ψ : K' → ((T ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ} {n : ℤ}
  {d : T ⟶ A}

theorem exists_basis_pow (hL : L.IsLB)
    (u : LB.Gen (LB.LinComb L (Sum.elim ψ fun _ : Fin 1 => (trEnd d).left ≫ (snd T A).left)
      (Sum.elim ε' fun _ => -n))) (hu : u.IsGen) {m : ℕ} {b' : Fin m → LB.Sec (LB.LinComb L ψ ε')}
    (hb' : IsSecBasis (LB.LinComb L ψ ε') b') : ∃ b : Fin m → LB.Sec (LPow A L n T), IsSecBasis (LPow A L n T) b := by
  have h₁ := trEnd_comp (mul_inv_cancel d)
  have h₂ := trEnd_comp (inv_mul_cancel d)
  choose b hb using fun i => exists_tr' (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n) u hL hu h₁ h₂ (b' i)
  refine ⟨b, fun s => ?_⟩
  obtain ⟨s', hs⟩ := exists_tr (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n) u hL hu s
  refine (existsUnique_congr fun a => ?_).1 (hb' s')
  exact Tr.comb_iff u hL h₁ (a := fun i => (fst T A).left.appTop.hom (a i))
    (fun i => congrArg (fun q => q.appTop.hom (a i)) (trEnd_fst d)) hs hb

end Fibre

section Complex

variable {X X' Y : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ} {R : Type} [CommRing R]
  {f : X ⟶ Spec (CommRingCat.of R)} {F : Perf f (LB.LinComb L φ ε)}

def cstTop (f : X ⟶ Spec (CommRingCat.of R)) : R →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem cstTop_pull {R' : Type} [CommRing R'] (g : R →+* R') {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (r : R) : cstTop f' (g r) = π.appTop.hom (cstTop f r) := by
  have e₁ := congrArg (fun Q => Q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  have e₂ := congrArg (fun q => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) w
  exact (congrArg f'.appTop.hom e₁).trans e₂.symm

theorem existsUnique_comb {R' : Type} [CommRing R'] (g : R →+* R') {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {ψ : K → (X' ⟶ Y)} (e : ∀ k, ψ k = π ≫ φ k) {m : ℕ} (B : Matrix (Fin F.a) (Fin m) R) (hB : F.D₀ * B = 0)
    (hu : ∀ v : Fin F.a → R', (F.D₀.map g).mulVec v = 0 → ∃! z : Fin m → R', (B.map g).mulVec z = v)
    (b : Fin m → LB.Sec (LB.LinComb L ψ ε)) (hb : ∀ i, Rep π ψ F (cstTop f') (fun k => g (B k i)) (b i).f)
    (s : LB.Sec (LB.LinComb L ψ ε)) : ∃! z : Fin m → R', Comb s (fun i => cstTop f' (z i)) b := by
  obtain ⟨-, h₂, h₃⟩ := rep_main (F := F) e g f' H (cstTop f') fun _ => rfl
  have ker : ∀ z, (F.D₀.map g).mulVec ((B.map g).mulVec z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
  have rep : ∀ (z : Fin m → R') (s : LB.Sec (LB.LinComb L ψ ε)), Comb s (fun i => cstTop f' (z i)) b →
      Rep π ψ F (cstTop f') ((B.map g).mulVec z) s.f := fun z s hs => by
    have := Rep.sum e hb z
    rw [show s.f = _ from funext hs]
    exact this
  obtain ⟨v, hv, hr⟩ := h₂ s
  obtain ⟨z, rfl, hz⟩ := hu v hv
  refine ⟨z, ?_, fun z' hz' => hz z' (h₃ _ _ s (ker z') hv (rep z' s hz') hr)⟩
  obtain ⟨s₁, hs₁⟩ := exists_comb (fun i => cstTop f' (z i)) b
  rw [Rep.sec_eq e hr (rep z s₁ hs₁)]
  exact hs₁

end Complex

section Twist

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α : D.X)

theorem exists_gen_translate {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {d : Over.mk t ⟶ D.P.A}
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 3) ![(snd (Over.mk t) D.P.A).left,
      (translPt D.P.A (toUnit _ ≫ D.c α : Over.mk t ⟶ D.P.A)).left, (translPt D.P.A d).left]
      ![(k : ℤ) - 1, 1, -(k : ℤ)])) (hw : w.IsGen) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (fun i => (snd (Over.mk t) D.P.A).left ≫ D.famφB α i)
      fun _ : Fin 1 => (trEnd d).left ≫ (snd (Over.mk t) D.P.A).left)
      (Sum.elim (DegPre.famε k) fun _ => -(k : ℤ))), u.IsGen := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := K) D.P.L D.P.isLB (K := Fin 2)
    ![(toUnit _ ≫ D.c α : Over.mk t ⟶ D.P.A).left, (toUnit _ ≫ η[D.P.A] : Over.mk t ⟶ D.P.A).left] ![-1, 1]
  have hm := DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ he (fst (Over.mk t) D.P.A).left)
  have c₁ : ∀ x : 𝟙_ _ ⟶ D.P.A, fst (Over.mk t) D.P.A ≫ toUnit _ ≫ x = snd (Over.mk t) D.P.A ≫ toUnit _ ≫ x :=
    fun x => by rw [comp_toUnit_assoc, comp_toUnit_assoc]
  have c₂ : ∀ x : 𝟙_ _ ⟶ D.P.A, (fst (Over.mk t) D.P.A).left ≫ (toUnit _ ≫ x).left =
      (snd (Over.mk t) D.P.A).left ≫ (toUnit _ ≫ x).left := fun x => congrArg (·.left) (c₁ x)
  have c₃ : (translPt D.P.A (toUnit _ ≫ D.c α : Over.mk t ⟶ D.P.A)).left =
      (snd (Over.mk t) D.P.A).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left := by
    rw [← Over.comp_left]
    congr 1
    change (fst _ _ ≫ toUnit _ ≫ D.c α) * snd _ _ = snd _ _ ≫ (𝟙 D.P.A * (toUnit _ ≫ D.c α))
    rw [MonObj.comp_mul, Category.comp_id, c₁, mul_comm]
  obtain ⟨u, hu, -⟩ := exists_gen (φ' := Sum.elim (fun i => (snd (Over.mk t) D.P.A).left ≫ D.famφB α i)
      fun _ : Fin 1 => (trEnd d).left ≫ (snd (Over.mk t) D.P.A).left)
    (ε' := Sum.elim (DegPre.famε k) fun _ => -(k : ℤ)) D.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_three, Fin.prod_univ_two,
        Fin.prod_univ_four, Fin.prod_univ_one, DegPre.famφB, DegPre.famε, trEnd_snd, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Category.comp_id, c₃]
      erw [c₂, c₂]
      ac_rfl) _ hm
  exact ⟨u, hu⟩

end Twist

theorem main : (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), 1 ≤ n → FirstCohomologyVanishes (pw P.L n)) → (∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e → M.IsLB → M'.IsLB → (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M') → (∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v) → PolBaseChangeSt → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left, (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen) → DVR.TwistBaseChangeStatement := by
  intro hPerf hProj hV hI hM hP h0 hT R _ _ _ _ D k hk α
  have hL := D.P.isLB
  have hpr : IsProjBy (R := R) D.P.A.hom := by
    obtain ⟨N, -, m, s, h₁, h₂⟩ := hProj _ D.P R (𝟙 _) _ (𝟙 _) D.P.A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
    exact ⟨_, h₁, m, s, h₂⟩
  obtain ⟨F⟩ := hPerf R _ D.P.A.hom D.P.isAb.smooth hpr _ (LB.isLB_linComb hL (D.famφB α) (DegPre.famε k))
  obtain ⟨K, _, _, g₀, hg₀⟩ := exists_geomPoint (R := R) (IsLocalRing.closedPoint R)
  let t := Spec.map (CommRingCat.ofHom g₀)
  obtain ⟨d, -, w, hw⟩ := hT _ D.P K t k hk (toUnit _ ≫ D.c α)
  obtain ⟨u, hu⟩ := exists_gen_translate D k α t w hw
  have hH : FirstCohomologyVanishes ((LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)).pull (snd (Over.mk t) D.P.A).left) := by
    obtain ⟨X', π, f', hX', hH⟩ := exists_h1Zero hV hI hP D.P k hk (Over.mk t) K (𝟙 _)
    have : IsIso π := hX'.isIso_fst_of_isIso
    have : IsIso (trEnd d).left := ⟨_, trEnd_comp (inv_mul_cancel d), trEnd_comp (mul_inv_cancel d)⟩
    refine hI _ _ ((trEnd d).left ≫ inv π) _ _ inferInstance (LB.isLB_pull (LB.isLB_linComb hL _ _) π)
      (LB.isLB_pull (LB.isLB_linComb hL _ _) _) ?_ hH
    have i₁ : LBIso _ _ := gen_chartPull (chartQuot D.P.L
      (fun _ : Fin 1 => (trEnd d).left ≫ (snd (Over.mk t) D.P.A).left) (fun _ => (k : ℤ))
      (fun i => (snd (Over.mk t) D.P.A).left ≫ D.famφB α i) (DegPre.famε k)) u hu
    exact (i₁.symm.chartPull (chartOut D.P.L _ _ _ _ fun _ => rfl) (chartOut D.P.L _ _ _ _ fun _ => rfl)).chartPull
      (chartPullId _) (chartTwice _ π _ (trEnd d).left (by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]))
  obtain ⟨r, m, B, hr, hB, hU⟩ := hM R K g₀ _ _ _ F.D₀ F.D₁ F.comp
    (F.exact K g₀ _ _ _ (isPullback_snd D.P.A (Over.mk t)) hH)
  have hr' : IsUnit r := by
    by_contra hn
    exact hr (hg₀ r hn)
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  choose b hb using fun i => (rep_main (F := F) (ψ := D.famφB α) (fun _ => (Category.id_comp _).symm) (RingHom.id R)
    D.P.A.hom H₀ (cstTop D.P.A.hom) fun _ => rfl).1 (fun l => B l i) (by
      funext l
      exact congrFun (congrFun hB l) i)
  have key : ∀ (R' : Type) [CommRing R'] (f : R →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b' := by
    intro R' _ g b' hb' s
    have H := isPullback_snd D.P.A (Over.mk (Spec.map (CommRingCat.ofHom g)))
    have h := existsUnique_comb (F := F) g H (fun _ => rfl) B hB (hU R' g (hr'.map g)) b' (fun i =>
      Rep.pull (fun _ => (Category.id_comp _).symm) (hb i) _ (Category.comp_id _).symm (fun _ => rfl)
        (fun l => cstTop_pull g H.w _) _ (hb' i)) s
    exact (Equiv.existsUnique_congr (Equiv.piCongrRight fun _ : Fin m =>
      (Scheme.ΓSpecIso (CommRingCat.of R')).symm.commRingCatIsoToRingEquiv.toEquiv) fun _ => Iff.rfl).1 h
  refine ⟨m, b, ?_, key⟩
  obtain ⟨bK, hbK⟩ := exists_basis_pow hL u hu
    (key K g₀ (fun i => DVR.pullSec D.P.L _ _ (b i) _) fun _ _ => rfl)
  have : Nontrivial Γ((Over.mk t).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  rw [← h0 _ D.P K t k hk, finrank_of_isSecBasis hbK]

end GlobalTheory.TwistBC
