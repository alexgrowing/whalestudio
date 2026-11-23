import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

section Formal
variable {r : ℕ}

abbrev PVec (r : ℕ) := Vec r × Vec r

def flat : (PVec r →₀ ℤ) →+ (Vec r →₀ ℤ) :=
  Finsupp.liftAddHom fun p => zmultiplesHom (Vec r →₀ ℤ) (lam p.1 p.2)

def rel1 (u u' v : Vec r) : PVec r →₀ ℤ :=
  Finsupp.single (u + u', v) 1 - Finsupp.single (u, v) 1 - Finsupp.single (u', v) 1

def rel2 (u v : Vec r) : PVec r →₀ ℤ :=
  Finsupp.single (u, v) 1 - Finsupp.single (v, u) 1

def sigP (W A A' : Matrix (Fin r) (Fin r) ℤ) : PVec r →₀ ℤ :=
  ∑ a : Fin 6, ∑ i, ∑ j, (rosatiε a * W i j) • Finsupp.single (rosVec A A' a i, rosVec A A' a j) 1

def rels (r : ℕ) : Set (PVec r →₀ ℤ) :=
  Set.range (fun p : Vec r × Vec r × Vec r => rel1 p.1 p.2.1 p.2.2) ∪ Set.range (fun p : Vec r × Vec r => rel2 p.1 p.2)

theorem flat_single (u v : Vec r) : flat (Finsupp.single (u, v) 1) = lam u v := by
  simp [flat]

theorem flat_sigP (W A A' : Matrix (Fin r) (Fin r) ℤ) : flat (sigP W A A') = sig W A A' := by
  simp only [sigP, sig, map_sum, map_zsmul, flat_single]

end Formal

section Maps
variable {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B] {r : ℕ}

def vecHom (pr : Fin r → (A ⟶ B)) (v : Vec r) : A ⊗ A ⟶ B :=
  (∏ k, (fst A A ≫ pr k) ^ v (Sum.inl k)) * ∏ k, (snd A A ≫ pr k) ^ v (Sum.inr k)

end Maps

def vecLat {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (xe : X' ≃+ (Fin r → X)) (v : Vec r)
    (y y' : X') : X :=
  ∑ k, v (Sum.inl k) • xe y k + ∑ k, v (Sum.inr k) • xe y' k

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ}

def Triv (Q : Data R) (D' : DegPre R) (pr : Fin r → (D'.P.A ⟶ Q.B)) (c : Vec r →₀ ℤ)
    (V : (z : (TK R).left) → (((TK R).left ⟶ Q.B.left) → Q.M.L.ι) → D'.X → D'.X →
      ((TK R).left.presheaf.stalk z)ˣ) : Prop :=
  ∃ Ξ : LB.Gen (LB.LinComb Q.M.L (fun v : c.support => (vecHom pr v.1).left) (fun v => c v.1)), Ξ.IsGen ∧
    (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J, Good Q.M.L z J → val Ξ (zero2 D'.P.A) z J = 1) ∧
    ∀ (z : (TK R).left) J, Good Q.M.L z J → ∀ y y' : D'.X, val Ξ (D'.pt2 y y') z J = V z J y y'

def tv (Q : Data R) {X' : Type} [AddCommGroup X'] (xe : X' ≃+ (Fin r → Q.X)) (n : PVec r →₀ ℤ) (z : (TK R).left)
    (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (y y' : X') : ((TK R).left.presheaf.stalk z)ˣ :=
  n.prod fun p k => val (Q.tau (vecLat xe p.1 y y') (vecLat xe p.2 y y')) (𝟙 _) z J ^ (-k)

end GlobalTheory.Mum.PolTens

noncomputable section
namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ}

section Maps
variable {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B]

theorem vecHom_add (pr : Fin r → (A ⟶ B)) (u v : Vec r) : vecHom pr (u + v) = vecHom pr u * vecHom pr v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (pr : Fin r → (A ⟶ B)) : vecHom pr 0 = 1 := by
  simp only [vecHom, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]

theorem comp_vecHom (pr : Fin r → (A ⟶ B)) {Z : Over S} (p q : Z ⟶ A) (v : Vec r) :
    lift p q ≫ vecHom pr v = (∏ k, (p ≫ pr k) ^ v (Sum.inl k)) * ∏ k, (q ≫ pr k) ^ v (Sum.inr k) := by
  rw [vecHom, MonObj.comp_mul, GlobalTheory.Mum.TensAct.comp_prod_zpow, GlobalTheory.Mum.TensAct.comp_prod_zpow]
  simp only [lift_fst_assoc, lift_snd_assoc]

end Maps

theorem vecLat_add {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ (Fin r → X)) (u v : Vec r) (y y' : X') :
    vecLat xe (u + v) y y' = vecLat xe u y y' + vecLat xe v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ}

theorem prod_support_eq {U : Type} [CommGroup U] (g : Vec r → ℤ → U) (d : Vec r →₀ ℤ) :
    ∏ v : d.support, g v.1 (d v.1) = d.prod g :=
  Finset.prod_coe_sort d.support (fun v => g v (d v))

variable (Q : Data R) (D' : DegPre R) (pr : Fin r → (D'.P.A ⟶ Q.B))

theorem triv_zero : Triv Q D' pr 0 (fun _ _ _ _ => 1) := by
  obtain ⟨t, ht, hv⟩ := exists_gen Q.M.isLB
    (φ' := fun v : (0 : Vec r →₀ ℤ).support => (vecHom pr v.1).left) (ε' := fun v => (0 : Vec r →₀ ℤ) v.1)
    (fun U _ h => by simp) (LB.oneGen Q.M.L (Y := (D'.P.A ⊗ D'.P.A).left)) (LB.isGen_oneGen _)
  refine ⟨t, ht, fun z J hJ => (hv _ _ z J hJ).trans (val_one _), fun z J hJ y y' => ?_⟩
  rw [hv _ _ z J hJ, val_one]

variable {Q D' pr}

theorem triv_add {c c' : Vec r →₀ ℤ} {V V'} (h : Triv Q D' pr c V) (h' : Triv Q D' pr c' V') :
    Triv Q D' pr (c + c') (fun z J y y' => V z J y y' * V' z J y y') := by
  obtain ⟨Ξ, hΞ, h1, h2⟩ := h
  obtain ⟨Ξ', hΞ', h1', h2'⟩ := h'
  have hform : FormEq (Sum.elim (fun v : c.support => (vecHom pr v.1).left) (fun v : c'.support => (vecHom pr v.1).left))
      (Sum.elim (fun v : c.support => c v.1) (fun v : c'.support => c' v.1))
      (fun v : (c + c').support => (vecHom pr v.1).left) (fun v => (c + c') v.1) := by
    intro U _ h
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_support_eq (fun v n => h (vecHom pr v).left ^ n) c,
      prod_support_eq (fun v n => h (vecHom pr v).left ^ n) c',
      prod_support_eq (fun v n => h (vecHom pr v).left ^ n) (c + c'),
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  obtain ⟨Ξ'', hΞ'', hv⟩ := exists_gen Q.M.isLB hform _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hΞ hΞ')
  refine ⟨Ξ'', hΞ'', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_mul hJ, h1 z J hJ, h1' z J hJ, _root_.mul_one]
  · rw [hv _ _ z J hJ, val_mul hJ, h2 z J hJ y y', h2' z J hJ y y']

theorem triv_neg {c : Vec r →₀ ℤ} {V} (h : Triv Q D' pr c V) :
    Triv Q D' pr (-c) (fun z J y y' => (V z J y y')⁻¹) := by
  obtain ⟨Ξ, hΞ, h1, h2⟩ := h
  have hF : FormEq (fun v : c.support => (vecHom pr v.1).left) (fun v => -(c v.1))
      (fun v : (-c).support => (vecHom pr v.1).left) (fun v => (-c) v.1) := by
    intro U _ h
    rw [Finset.prod_coe_sort c.support (fun v => h (vecHom pr v).left ^ (-(c v))),
      Finset.prod_coe_sort (-c).support (fun v => h (vecHom pr v).left ^ ((-c) v)),
      Finsupp.support_neg]
    simp only [Finsupp.neg_apply]
  obtain ⟨Ξ', hΞ', hv⟩ := exists_gen Q.M.isLB hF (LB.invGen Q.M.L _ _ Ξ) (LB.isGen_invGen Q.M.L _ _ Ξ hΞ)
  refine ⟨Ξ', hΞ', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_inv, h1 z J hJ, inv_one]
  · rw [hv _ _ z J hJ, val_inv, h2 z J hJ y y']

theorem zero_vecHom (hpr : ∀ i, IsMonHom (pr i)) (v : Vec r) : lift η[D'.P.A] η[D'.P.A] ≫ vecHom pr v = 1 := by
  have h : ∀ k, η[D'.P.A] ≫ pr k = 1 := fun k => by
    haveI := hpr k
    rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simp only [comp_vecHom, h, one_zpow, Finset.prod_const_one, _root_.mul_one]

theorem pt_vecHom (xe : D'.X ≃+ (Fin r → Q.X)) (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) (y y' : D'.X) (v : Vec r) :
    lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y') ≫ vecHom pr v = toUnit (TK R) ≫ Q.c (vecLat xe v y y') := by
  have hp : ∀ x k, DVR.cP D' (TK R) x ≫ pr k = toUnit (TK R) ≫ Q.c (xe x k) := fun x k => by
    simp only [DVR.cP, Category.assoc, hc]
  rw [comp_vecHom, vecLat, Q.c_add, PowLim.c_sum_zsmul Q, PowLim.c_sum_zsmul Q, MonObj.comp_mul,
    GlobalTheory.Mum.TensAct.comp_prod_zpow, GlobalTheory.Mum.TensAct.comp_prod_zpow]
  simp only [hp]

theorem triv_theta (xe : D'.X ≃+ (Fin r → Q.X)) (hpr : ∀ i, IsMonHom (pr i))
    (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) (a b c : Vec r) :
    Triv Q D' pr (theta a b c) (fun z J y y' => cubV Q.cub (T := TK R) z J (toUnit (TK R) ≫ Q.c (vecLat xe a y y'))
      (toUnit (TK R) ≫ Q.c (vecLat xe b y y')) (toUnit (TK R) ≫ Q.c (vecLat xe c y y'))) := by
  have hF : FormEq (fun I => (lift (vecHom pr a) (lift (vecHom pr b) (vecHom pr c))).left ≫ thφ Q.B (x3 Q.B) I) thε
      (fun v : (theta a b c).support => (vecHom pr v.1).left) (fun v => theta a b c v.1) := fun U _ h => by
    refine (prod_cub (vecHom pr a) (vecHom pr b) (vecHom pr c) h).trans ?_
    rw [Finset.prod_coe_sort (theta a b c).support (fun v => h (vecHom pr v).left ^ theta a b c v), prod_theta,
      vecHom_add, vecHom_add, vecHom_add, vecHom_add, vecHom_zero]
  obtain ⟨Ξ, hΞ, hv⟩ := exists_gen Q.M.isLB hF
    (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t (lift (vecHom pr a) (lift (vecHom pr b) (vecHom pr c))).left)
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ Q.cub.isGen _)
  refine ⟨Ξ, hΞ, fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · refine (hv _ _ z J hJ).trans ((val_cub Q.cub (lift η[D'.P.A] η[D'.P.A]) hJ _ _ _).trans ?_)
    rw [zero_vecHom hpr, zero_vecHom hpr, zero_vecHom hpr]
    exact (isCub_cubV Q.cub hJ).face _ _
  · refine (hv _ _ z J hJ).trans ((val_cub Q.cub (lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y')) hJ _ _ _).trans ?_)
    rw [pt_vecHom xe hc, pt_vecHom xe hc, pt_vecHom xe hc]

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ} {Q : Data R} {D' : DegPre R} {pr : Fin r → (D'.P.A ⟶ Q.B)}

theorem triv_congr {c : Vec r →₀ ℤ} {V V'} (h : Triv Q D' pr c V)
    (e : ∀ z J, Good Q.M.L z J → ∀ y y', V z J y y' = V' z J y y') : Triv Q D' pr c V' := by
  obtain ⟨Ξ, hΞ, h1, h2⟩ := h
  exact ⟨Ξ, hΞ, h1, fun z J hJ y y' => (h2 z J hJ y y').trans (e z J hJ y y')⟩

section TV
variable (Q) {X' : Type} [AddCommGroup X'] (xe : X' ≃+ (Fin r → Q.X))

theorem tv_add (n n' : PVec r →₀ ℤ) (z J) (y y' : X') : tv Q xe (n + n') z J y y' = tv Q xe n z J y y' * tv Q xe n' z J y y' :=
  Finsupp.prod_add_index' (fun _ => by simp only [neg_zero, zpow_zero]) (fun _ _ _ => by simp only [neg_add, zpow_add])

theorem tv_neg (n : PVec r →₀ ℤ) (z J) (y y' : X') : tv Q xe (-n) z J y y' = (tv Q xe n z J y y')⁻¹ := by
  rw [tv, tv, Finsupp.prod_neg_index (fun _ => by simp only [neg_zero, zpow_zero]), ← Finsupp.prod_inv]
  refine Finsupp.prod_congr fun p _ => ?_
  rw [neg_neg, zpow_neg, inv_inv]

theorem tv_zero (z J) (y y' : X') : tv Q xe 0 z J y y' = 1 := Finsupp.prod_zero_index

theorem tv_single (p : PVec r) (k : ℤ) (z J) (y y' : X') : tv Q xe (Finsupp.single p k) z J y y' =
    val (Q.tau (vecLat xe p.1 y y') (vecLat xe p.2 y y')) (𝟙 _) z J ^ (-k) :=
  Finsupp.prod_single_index (by simp only [neg_zero, zpow_zero])

end TV

theorem flattenMumfordBundleFormalSum_additivityRelation (u u' v : Vec r) : flat (rel1 u u' v) = theta u u' v := by
  simp only [rel1, map_sub, flat_single, lam, theta]
  abel

theorem flattenMumfordBundleFormalSum_symmetryRelation (u v : Vec r) : flat (rel2 u v) = 0 := by
  simp only [rel2, map_sub, flat_single, lam, add_comm v u]
  abel

variable (xe : D'.X ≃+ (Fin r → Q.X)) (hpr : ∀ i, IsMonHom (pr i)) (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i))
include hpr hc

theorem isTrivialMumfordFormalSumLattice_additivityRelation (u u' v : Vec r) : Triv Q D' pr (flat (rel1 u u' v)) (tv Q xe (rel1 u u' v)) := by
  rw [flattenMumfordBundleFormalSum_additivityRelation]
  refine triv_congr (triv_theta xe hpr hc u u' v) fun z J hJ y y' => ?_
  have e := Q.tau_add (vecLat xe u y y') (vecLat xe u' y y') (vecLat xe v y y') z J hJ
  rw [rel1, sub_eq_add_neg, sub_eq_add_neg, ← Finsupp.single_neg, ← Finsupp.single_neg, tv_add, tv_add,
    tv_single, tv_single, tv_single, vecLat_add]
  simp only [neg_neg, zpow_one, zpow_neg]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem isTrivialMumfordFormalSumLattice_symmetryRelation (u v : Vec r) : Triv Q D' pr (flat (rel2 u v)) (tv Q xe (rel2 u v)) := by
  rw [flattenMumfordBundleFormalSum_symmetryRelation]
  refine triv_congr (triv_zero Q D' pr) fun z J hJ y y' => ?_
  rw [rel2, sub_eq_add_neg, ← Finsupp.single_neg, tv_add, tv_single, tv_single]
  simp only [neg_neg, zpow_one, zpow_neg]
  rw [Q.tau_symm _ _ z J hJ, inv_mul_cancel]

theorem triv_span {n : PVec r →₀ ℤ} (hn : n ∈ Submodule.span ℤ (rels r)) : Triv Q D' pr (flat n) (tv Q xe n) := by
  induction hn using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact isTrivialMumfordFormalSumLattice_additivityRelation xe hpr hc _ _ _
    · exact isTrivialMumfordFormalSumLattice_symmetryRelation xe hpr hc _ _
  | zero =>
    rw [map_zero]
    exact triv_congr (triv_zero Q D' pr) fun z J _ y y' => (tv_zero Q xe z J y y').symm
  | add x y _ _ hx hy =>
    rw [map_add]
    exact triv_congr (triv_add hx hy) fun z J _ a b => (tv_add Q xe x y z J a b).symm
  | smul k x _ hx =>
    have hneg : ∀ m, Triv Q D' pr (flat m) (tv Q xe m) → Triv Q D' pr (flat (-m)) (tv Q xe (-m)) := fun m hm => by
      rw [map_neg]
      exact triv_congr (triv_neg hm) fun z J _ a b => (tv_neg Q xe m z J a b).symm
    have hadd : ∀ m m', Triv Q D' pr (flat m) (tv Q xe m) → Triv Q D' pr (flat m') (tv Q xe m') →
        Triv Q D' pr (flat (m + m')) (tv Q xe (m + m')) := fun m m' hm hm' => by
      rw [map_add]
      exact triv_congr (triv_add hm hm') fun z J _ a b => (tv_add Q xe m m' z J a b).symm
    have h0 : Triv Q D' pr (flat 0) (tv Q xe 0) := by
      rw [map_zero]
      exact triv_congr (triv_zero Q D' pr) fun z J _ y y' => (tv_zero Q xe z J y y').symm
    induction k using Int.induction_on with
    | zero => rw [zero_smul]; exact h0
    | succ j ih => rw [add_smul, one_smul]; exact hadd _ _ ih hx
    | pred j ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg]
      exact hadd _ _ ih (hneg _ hx)

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ} {Q : Data R} {D' : DegPre R} {pr : Fin r → (D'.P.A ⟶ Q.B)}
  (hl : IsLimit (Fan.mk D'.P.A pr))

theorem prod_single' {G : Type} [CommGroup G] (f : Fin r → G) (i : Fin r) :
    ∏ k, f k ^ (Pi.single i (1 : ℤ) : Fin r → ℤ) k = f i := by
  rw [Fintype.prod_eq_single i (fun k hk => by rw [Pi.single_eq_of_ne hk, zpow_zero])]
  rw [Pi.single_eq_same, zpow_one]

theorem vecHom_xv (i : Fin r) : vecHom pr (xv i) = fst D'.P.A D'.P.A ≫ pr i := by
  simp only [vecHom, xv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  exact prod_single' _ i

theorem vecHom_zv (i : Fin r) : vecHom pr (zv i) = snd D'.P.A D'.P.A ≫ pr i := by
  simp only [vecHom, zv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  exact prod_single' _ i

theorem vecHom_axv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom pr (axv A i) = fst D'.P.A D'.P.A ≫ PowLim.act pr hl A ≫ pr i := by
  simp only [vecHom, axv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  rw [PowLim.comp_act_pr]

theorem vecHom_azv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom pr (azv A i) = snd D'.P.A D'.P.A ≫ PowLim.act pr hl A ≫ pr i := by
  simp only [vecHom, azv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  rw [PowLim.comp_act_pr]

theorem ros_pr (hpr : ∀ i, IsMonHom (pr i)) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) :
    ∃ q : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') a = q.left ∧
      ∀ k, q ≫ pr k = vecHom pr (rosVec A A' a k) := by
  fin_cases a
  · refine ⟨(fst D'.P.A D'.P.A ≫ PowLim.act pr hl A) * snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom pr (axv A k + zv k)
    haveI := hpr k
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_axv hl, vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A ≫ PowLim.act pr hl A, rfl, fun k => ?_⟩
    show _ = vecHom pr (axv A k)
    rw [vecHom_axv hl, Category.assoc]
  · refine ⟨snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom pr (zv k)
    rw [vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A * (snd D'.P.A D'.P.A ≫ PowLim.act pr hl A'), rfl, fun k => ?_⟩
    show _ = vecHom pr (xv k + azv A' k)
    haveI := hpr k
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_xv, vecHom_azv hl]
  · refine ⟨fst D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom pr (xv k)
    rw [vecHom_xv]
  · refine ⟨snd D'.P.A D'.P.A ≫ PowLim.act pr hl A', rfl, fun k => ?_⟩
    show _ = vecHom pr (azv A' k)
    rw [vecHom_azv hl, Category.assoc]

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ} {Q : Data R} {D' : DegPre R} {pr : Fin r → (D'.P.A ⟶ Q.B)}
  (hl : IsLimit (Fan.mk D'.P.A pr))

def lamV (u v : Vec r) : Fin 4 → Vec r := ![u + v, u, v, 0]

theorem ros_lam (hpr : ∀ i, IsMonHom (pr i)) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i j : Fin r) (s : Fin 4) :
    rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') a ≫ GlobalTheory.PolDeg.lamPts (pr i) (pr j) s =
      (vecHom pr (lamV (rosVec A A' a i) (rosVec A A' a j) s)).left := by
  obtain ⟨q, hq, hk⟩ := ros_pr hl hpr A A' a
  rw [hq]
  fin_cases s
  · show q.left ≫ (pr i * pr j).left = _
    rw [← Over.comp_left, MonObj.comp_mul, hk, hk]
    show _ = (vecHom pr (rosVec A A' a i + rosVec A A' a j)).left
    rw [vecHom_add]
  · show q.left ≫ (pr i).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (pr j).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (1 : D'.P.A ⟶ Q.B).left = _
    rw [← Over.comp_left, MonObj.comp_one]
    show _ = (vecHom pr 0).left
    rw [vecHom_zero]

theorem formEq_sig (hpr : ∀ i, IsMonHom (pr i)) (W A A' : Matrix (Fin r) (Fin r) ℤ) :
    FormEq (fun p : Fin 6 × ((Fin r × Fin r) × Fin 4) =>
        rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') p.1 ≫ tensφ pr p.2)
      (fun p => rosatiε p.1 * tensε W p.2)
      (fun v : (sig W A A').support => (vecHom pr v.1).left) (fun v => sig W A A' v.1) := by
  intro U _ h
  let H : Vec r → Additive U := fun v => Additive.ofMul (h (vecHom pr v).left)
  let F : (Vec r →₀ ℤ) →+ Additive U := Finsupp.liftAddHom fun v => zmultiplesHom (Additive U) (H v)
  have hF1 : ∀ x, F (Finsupp.single x 1) = H x := fun x => by
    simp only [F, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]
  have hlam : ∀ u v, F (lam u v) = ∑ s : Fin 4, Oε s • H (lamV u v s) := fun u v => by
    simp only [lam, map_add, map_sub, hF1, Fin.sum_univ_four]
    simp [Oε, lamV]
    abel
  have hR : Additive.ofMul (∏ v : (sig W A A').support, h (vecHom pr v.1).left ^ sig W A A' v.1) =
      F (sig W A A') := by
    rw [ofMul_prod]
    simp only [ofMul_zpow]
    rw [Finset.sum_coe_sort (sig W A A').support (fun v => sig W A A' v • H v)]
    simp only [F, Finsupp.liftAddHom_apply]
    rfl
  apply Additive.ofMul.injective
  rw [hR]
  simp only [ofMul_prod, ofMul_zpow, sig, map_sum, map_zsmul, hlam]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (rosatiε a * (W i j * Oε s)) • Additive.ofMul (h (rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') a ≫
    GlobalTheory.PolDeg.lamPts (pr i) (pr j) s)) = _
  rw [ros_lam hl hpr, ← _root_.mul_assoc, mul_smul]

theorem ros_sig (hpr : ∀ i, IsMonHom (pr i)) {W : Matrix (Fin r) (Fin r) ℤ}
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))) (hw : w.IsGen) (A A' : Matrix (Fin r) (Fin r) ℤ)
    (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A')) rosatiε)) (hu' : u'.IsGen)
    (hn' : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L))
    (Ξ : LB.Gen (LB.LinComb Q.M.L (fun v : (sig W A A').support => (vecHom pr v.1).left) (fun v => sig W A A' v.1)))
    (hΞ : Ξ.IsGen) (hΞ0 : ∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J, Good Q.M.L z J → val Ξ (zero2 D'.P.A) z J = 1)
    (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι)
    (hJ : Good Q.M.L z J) (hJ' : Good D'.P.L z J') (y y' : D'.X) :
    (∏ a, isoV w z J J' (D'.pt2 y y' ≫ rosatiφ D'.P.A (PowLim.act pr hl A) (PowLim.act pr hl A') a) ^ rosatiε a) *
      val u' (D'.pt2 y y') z J' = val Ξ (D'.pt2 y y') z J := by
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  haveI := PowLim.act_isMonHom pr hl hpr A
  haveI := PowLim.act_isMonHom pr hl hpr A'
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : zero2 D'.P.A ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D'.P.A] η[D'.P.A])
  refine GlobalTheory.TensBalUniq.iso_unique Q.M.isLB D'.P.isLB w hw (formEq_sig hl hpr W A A') hu' hΞ _ (zero2 D'.P.A) he sj
    (fun s I I' hI hI' => ?_) _ (D'.pt2 y y') z J J' hJ hJ'
  have o : (η[D'.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = 1 := by simp [Hom.one_def]
  have p := prod_ros (PowLim.act pr hl A) (PowLim.act pr hl A') η[D'.P.A] η[D'.P.A] (fun q => isoV w s I I' q)
  rw [IsMonHom.one_hom, IsMonHom.one_hom, show η[D'.P.A] * η[D'.P.A] = η[D'.P.A] by rw [o, _root_.mul_one]] at p
  have v' := val_corr hI' hn' (𝟙 _)
  rw [val_pull hI', Category.id_comp, val_one] at v'
  rw [hΞ0 s I hI]
  refine (congrArg₂ (· * ·) p v').trans (by simp)

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ}

section Lat
variable {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ (Fin r → X)) (y y' : X')

theorem vecLat_xv (i : Fin r) : vecLat xe (xv i) y y' = xe y i := by
  simp [vecLat, xv, Pi.single_apply]

theorem vecLat_zv (i : Fin r) : vecLat xe (zv i) y y' = xe y' i := by
  simp [vecLat, zv, Pi.single_apply]

theorem vecLat_axv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : vecLat xe (axv A i) y y' = ∑ k, A i k • xe y k := by
  simp [vecLat, axv]

theorem vecLat_azv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : vecLat xe (azv A i) y y' = ∑ k, A i k • xe y' k := by
  simp [vecLat, azv]

end Lat

theorem tv_sigP (Q : Data R) {X' : Type} [AddCommGroup X'] (xe : X' ≃+ (Fin r → Q.X)) (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (fA fA' : X' → X') (hA : ∀ y i, xe (fA y) i = ∑ j, A i j • xe y j) (hA' : ∀ y i, xe (fA' y) i = ∑ j, A' i j • xe y j)
    (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (y y' : X') :
    tv Q xe (sigP W A A') z J y y' = ∏ a : Fin 6, (∏ i, ∏ j, val (Q.tau (xe (![fA y + y', fA y, y', y + fA' y', y, fA' y'] a) i)
      (xe (![fA y + y', fA y, y', y + fA' y', y, fA' y'] a) j)) (𝟙 _) z J ^ W i j) ^ (-(rosatiε a)) := by
  let T : (PVec r →₀ ℤ) →+ Additive ((TK R).left.presheaf.stalk z)ˣ :=
    { toFun := fun n => Additive.ofMul (tv Q xe n z J y y')
      map_zero' := by simp only [tv_zero]; rfl
      map_add' := fun n n' => by simp only [tv_add]; rfl }
  have hl : ∀ a i, vecLat xe (rosVec A A' a i) y y' = xe (![fA y + y', fA y, y', y + fA' y', y, fA' y'] a) i := by
    intro a i
    fin_cases a <;> simp [rosVec, vecLat_add, vecLat_xv, vecLat_zv, vecLat_axv, vecLat_azv, hA, hA']
  apply Additive.ofMul.injective
  change T (sigP W A A') = _
  simp only [sigP, map_sum, map_zsmul, ofMul_prod, ofMul_zpow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (rosatiε a * W i j) • Additive.ofMul (tv Q xe (Finsupp.single _ 1) z J y y') = _
  rw [tv_single, hl, hl, ofMul_zpow, smul_smul, smul_smul]
  congr 1
  ring

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

theorem axv_eq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : axv A i = ∑ l, A i l • xv l := by
  funext k
  rcases k with k | k
  · simp [axv, xv, Finset.sum_apply, Pi.single_apply]
  · simp [axv, xv, Finset.sum_apply]

theorem azv_eq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : azv A i = ∑ l, A i l • zv l := by
  funext k
  rcases k with k | k
  · simp [azv, zv, Finset.sum_apply]
  · simp [azv, zv, Finset.sum_apply, Pi.single_apply]

theorem span_sigP {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (hA : A.transpose * (W + W.transpose) = (W + W.transpose) * A') : sigP W A A' ∈ Submodule.span ℤ (rels r) := by
  set N := Submodule.span ℤ (rels r)
  let F : Vec r → Vec r → (PVec r →₀ ℤ) ⧸ N := fun u v => N.mkQ (Finsupp.single (u, v) 1)
  have hF1 : ∀ u u' v, F (u + u') v = F u v + F u' v := fun u u' v => by
    have hm : rel1 u u' v ∈ N := Submodule.subset_span (Or.inl ⟨(u, u', v), rfl⟩)
    have h0 := (Submodule.Quotient.mk_eq_zero N).2 hm
    simp only [rel1] at h0
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h0
    exact h0
  have hF2 : ∀ u v, F u v = F v u := fun u v => by
    have hm : rel2 u v ∈ N := Submodule.subset_span (Or.inr ⟨(u, v), rfl⟩)
    have h0 := (Submodule.Quotient.mk_eq_zero N).2 hm
    simp only [rel2] at h0
    rw [Submodule.Quotient.mk_sub, sub_eq_zero] at h0
    exact h0
  have hF1' : ∀ u v v', F u (v + v') = F u v + F u v' := fun u v v' => by
    rw [hF2, hF1, hF2 v, hF2 v']
  let Fl : Vec r → Vec r →+ (PVec r →₀ ℤ) ⧸ N := fun v => AddMonoidHom.mk' (fun u => F u v) (fun u u' => hF1 u u' v)
  let Fr : Vec r → Vec r →+ (PVec r →₀ ℤ) ⧸ N := fun u => AddMonoidHom.mk' (fun v => F u v) (fun v v' => hF1' u v v')
  have hsumL : ∀ (c : Fin r → ℤ) (s : Fin r → Vec r) v, F (∑ l, c l • s l) v = ∑ l, c l • F (s l) v := fun c s v => by
    have := map_sum (Fl v) (fun l => c l • s l) Finset.univ
    simp only [map_zsmul] at this
    exact this
  have hsumR : ∀ (c : Fin r → ℤ) (s : Fin r → Vec r) u, F u (∑ l, c l • s l) = ∑ l, c l • F u (s l) := fun c s u => by
    have := map_sum (Fr u) (fun l => c l • s l) Finset.univ
    simp only [map_zsmul] at this
    exact this
  let X : (Fin r → Vec r) → (Fin r → Vec r) → (PVec r →₀ ℤ) ⧸ N := fun s t => ∑ i, ∑ j, W i j • F (s i) (t j)
  let Bf : (Fin r → Vec r) → (Fin r → Vec r) → (PVec r →₀ ℤ) ⧸ N :=
    fun s t => ∑ i, ∑ j, (W + W.transpose) i j • F (s i) (t j)
  have expand : ∀ s t : Fin r → Vec r, X (fun i => s i + t i) (fun i => s i + t i) = X s s + X t t + Bf s t := by
    intro s t
    have hc : ∑ i, ∑ j, W i j • F (t i) (s j) = ∑ i, ∑ j, W.transpose i j • F (s i) (t j) := by
      rw [Finset.sum_comm]
      simp only [Matrix.transpose_apply, hF2 (t _)]
    simp only [X, Bf, hF1, hF1', smul_add, Finset.sum_add_distrib, Matrix.add_apply, add_smul]
    rw [hc]
    abel
  have hπ : N.mkQ (sigP W A A') = ∑ a : Fin 6, rosatiε a • X (rosVec A A' a) (rosVec A A' a) := by
    simp only [sigP, map_sum, map_zsmul, X, Finset.smul_sum, mul_smul]
    rfl
  have e0 : rosVec A A' 0 = fun i => axv A i + zv i := rfl
  have e1 : rosVec A A' 1 = fun i => axv A i := rfl
  have e2 : rosVec A A' 2 = fun i => zv i := rfl
  have e3 : rosVec A A' 3 = fun i => xv i + azv A' i := rfl
  have e4 : rosVec A A' 4 = fun i => xv i := rfl
  have e5 : rosVec A A' 5 = fun i => azv A' i := rfl
  have ε0 : rosatiε 0 = 1 := rfl
  have ε1 : rosatiε 1 = -1 := rfl
  have ε2 : rosatiε 2 = -1 := rfl
  have ε3 : rosatiε 3 = -1 := rfl
  have ε4 : rosatiε 4 = 1 := rfl
  have ε5 : rosatiε 5 = 1 := rfl
  have L : Bf (fun i => axv A i) (fun i => zv i) =
      ∑ l, ∑ j, (A.transpose * (W + W.transpose)) l j • F (xv l) (zv j) := by
    simp only [Bf, axv_eq, hsumL, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have Rr : Bf (fun i => xv i) (fun i => azv A' i) =
      ∑ i, ∑ m, ((W + W.transpose) * A') i m • F (xv i) (zv m) := by
    simp only [Bf, azv_eq, hsumR, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hB : Bf (fun i => axv A i) (fun i => zv i) = Bf (fun i => xv i) (fun i => azv A' i) := by
    rw [L, Rr, hA]
  rw [← Submodule.Quotient.mk_eq_zero N]
  change N.mkQ (sigP W A A') = 0
  rw [hπ, Fin.sum_univ_six, ε0, ε1, ε2, ε3, ε4, ε5, e0, e1, e2, e3, e4, e5, expand, expand, hB]
  simp only [one_smul, neg_smul]
  abel

end GlobalTheory.Mum.PolTens

namespace GlobalTheory.Mum.PolTens
open GlobalTheory.TensBal

theorem transpose_mul_eq {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det)
    (a : TensO (symUnitOf W h)) :
    (TensO.mat _ a).transpose * (W + W.transpose) = (W + W.transpose) * TensO.mat _ (star a) := by
  have hb : ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show _ = (W + W.transpose) * (((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ)))
  rw [hb.symm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

variable {R : Type} [CommRing R] [IsDomain R] {r : ℕ} {Q : Data R} {D' : DegPre R} {pr : Fin r → (D'.P.A ⟶ Q.B)}

theorem tau_pol {W : Matrix (Fin r) (Fin r) ℤ} (xe : D'.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hpsi : ∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' →
      val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j)
    {z : (TK R).left} {J J'} (hJ : Good Q.M.L z J) (hJ' : Good D'.P.L z J') (p q : D'.X) :
    val (D'.tau p q) (𝟙 _) z J' =
      isoV w z J J' (DVR.cP D' (TK R) (p + q)).left * (∏ i, ∏ j, val (Q.tau (xe (p + q) i) (xe (p + q) j)) (𝟙 _) z J ^ W i j) *
      (isoV w z J J' (DVR.cP D' (TK R) p).left * ∏ i, ∏ j, val (Q.tau (xe p i) (xe p j)) (𝟙 _) z J ^ W i j)⁻¹ *
      (isoV w z J J' (DVR.cP D' (TK R) q).left * ∏ i, ∏ j, val (Q.tau (xe q i) (xe q j)) (𝟙 _) z J ^ W i j)⁻¹ *
      (val D'.rigK (𝟙 _) z J')⁻¹ := by
  rw [GlobalTheory.TauBalBox.tau_val D' hJ', hpsi _ z J J' hJ hJ', hpsi _ z J J' hJ hJ', hpsi _ z J J' hJ hJ']
  rfl

end GlobalTheory.Mum.PolTens
