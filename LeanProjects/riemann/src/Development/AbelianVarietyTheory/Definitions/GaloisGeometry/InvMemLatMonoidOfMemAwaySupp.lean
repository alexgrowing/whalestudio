import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.EqOneOfHeckeEigNeBot
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMonHomIdPow
import Development.AbelianVarietyTheory.Definitions.Divisors.NontrivialOfArtinQE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemOfMemHeckeLevel
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W2

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.HodgeCoh
open GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.HeckeCorr
open scoped TensorProduct

section Side

variable {Γ : Type} [Group Γ]

theorem mem_heckeLevel_inv {K : Subgroup Γ} {h u : Γ} : u ∈ heckeLevel K h⁻¹ ↔ u ∈ K ∧ h * u * h⁻¹ ∈ K := by
  refine ⟨fun hu => ⟨heckeLevel_le K h⁻¹ hu, by simpa using conj_mem_of_mem_heckeLevel hu⟩, fun hu => ⟨hu.1, ?_⟩⟩
  exact ⟨h * u * h⁻¹, hu.2, by simp [MulAut.conj_apply, _root_.mul_assoc]⟩

theorem heckeLevel_inv_of_comm (K : Subgroup Γ) {h : Γ} (hc : ∀ u, h * u = u * h) : heckeLevel K h⁻¹ = K := by
  ext u
  rw [mem_heckeLevel_inv, hc u, mul_inv_cancel_right, and_self]

open Classical in

theorem cosetTrace_cosetTr_eq_hAct {K' K : Subgroup Γ} {g : Γ} (hle : K' ≤ heckeLevel K g)
    (hfin : K'.relIndex K ≠ 0) {W : Type} [AddCommGroup W] [Module ℂ W] (φ : Γ ⧸ K → W) (x : Γ) :
    cosetTrace (hle.trans (heckeLevel_le K g))
        (φ ∘ cosetTr K' K g fun _ hu => conj_mem_of_mem_heckeLevel (hle hu)) (x : Γ ⧸ K) =
      K'.relIndex (heckeLevel K g) • Formalism.UG.hAct K (Formalism.UG.dosetInd ℂ K g) (fun y => φ y) x := by
  haveI : Finite (K ⧸ K'.subgroupOf K) := Nat.finite_of_card_ne_zero hfin
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let f : K ⧸ K'.subgroupOf K → Γ ⧸ K := fun u => (((u.out : K) : Γ) * g : Γ)
  have hout : ∀ (a : K) (u : K ⧸ K'.subgroupOf K), (a : K ⧸ K'.subgroupOf K) = u → (a : Γ)⁻¹ * u.out ∈ K' := by
    intro a u h
    rw [← u.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    exact h

  have h1 : cosetTrace (hle.trans (heckeLevel_le K g))
      (φ ∘ cosetTr K' K g fun _ hu => conj_mem_of_mem_heckeLevel (hle hu)) (x : Γ ⧸ K) = ∑ u, φ (x • f u) := by
    unfold cosetTrace
    have hsum : ∑ u, φ (x • f u) = ∑ᶠ u ∈ (Set.univ : Set (K ⧸ K'.subgroupOf K)), φ (x • f u) := by
      rw [finsum_mem_univ, finsum_eq_sum_of_fintype]
    rw [hsum]
    symm
    refine finsum_mem_eq_of_bijOn (fun u : K ⧸ K'.subgroupOf K => ((x * (u.out : K) : Γ) : Γ ⧸ K')) ⟨?_, ?_, ?_⟩ ?_
    · intro u _
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq]
      simpa using u.out.2
    · intro u _ v _ huv
      simp only at huv
      rw [QuotientGroup.eq] at huv
      rw [← u.out_eq', ← v.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [_root_.mul_assoc] using huv
    · intro y hy
      induction y using QuotientGroup.induction_on with
      | H y =>
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq] at hy
      have hu : x⁻¹ * y ∈ K := by simpa using K.inv_mem hy
      refine ⟨((⟨_, hu⟩ : K) : K ⧸ K'.subgroupOf K), Set.mem_univ _, ?_⟩
      have := K'.inv_mem (hout ⟨_, hu⟩ _ rfl)
      simp only
      rw [QuotientGroup.eq]
      simpa [_root_.mul_assoc] using this
    · intro u _
      simp only [Function.comp_apply, cosetTr_mk, f, MulAction.Quotient.smul_mk, smul_eq_mul, _root_.mul_assoc]

  have h2 : ∀ u₀, (Finset.univ.filter fun u => f u = f u₀).card = K'.relIndex (heckeLevel K g) := by
    intro u₀
    let e : heckeLevel K g ⧸ K'.subgroupOf (heckeLevel K g) → {u // f u = f u₀} := fun a =>
      ⟨((u₀.out * ⟨a.out, heckeLevel_le K g a.out.2⟩ : K) : K ⧸ K'.subgroupOf K), by
        have h := hle (hout (u₀.out * ⟨a.out, heckeLevel_le K g a.out.2⟩) _ rfl)
        have h' := conj_mem_of_mem_heckeLevel ((heckeLevel K g).mul_mem a.out.2 h)
        symm
        simp only [f]
        rw [QuotientGroup.eq]
        simpa [_root_.mul_assoc] using h'⟩
    have he : Function.Bijective e := by
      constructor
      · intro a b hab
        have h := congrArg Subtype.val hab
        simp only [e] at h
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
        rw [← a.out_eq', ← b.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [_root_.mul_assoc] using h
      · rintro ⟨u, hu⟩
        have hu' := hu.symm
        simp only [f] at hu'
        rw [QuotientGroup.eq] at hu'
        have hm : ((u₀.out : K) : Γ)⁻¹ * u.out ∈ heckeLevel K g :=
          ⟨K.mul_mem (K.inv_mem u₀.out.2) u.out.2, _, hu', by simp [MulAut.conj_apply, _root_.mul_assoc]⟩
        refine ⟨((⟨_, hm⟩ : heckeLevel K g) : _ ⧸ K'.subgroupOf (heckeLevel K g)), Subtype.ext ?_⟩
        have h := (QuotientGroup.out_eq' ((⟨_, hm⟩ : heckeLevel K g) : _ ⧸ K'.subgroupOf (heckeLevel K g)))
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
        simp only [e]
        refine Eq.trans ?_ u.out_eq'
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [_root_.mul_assoc] using h
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← Nat.card_congr (Equiv.ofBijective e he)]
    rfl

  have h3 : ∀ z : Γ ⧸ K, z.out ∈ DoubleCoset.doubleCoset g (K : Set Γ) K ↔ z ∈ Finset.univ.image f := by
    intro z
    rw [DoubleCoset.mem_doubleCoset, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, b, hb, hz⟩
      refine ⟨((⟨a, ha⟩ : K) : K ⧸ K'.subgroupOf K), Finset.mem_univ _, ?_⟩
      have h := conj_mem_of_mem_heckeLevel (hle (K'.inv_mem (hout ⟨a, ha⟩ _ rfl)))
      rw [← z.out_eq', hz]
      simp only [f]
      rw [QuotientGroup.eq]
      simpa [_root_.mul_assoc] using K.mul_mem h hb
    · rintro ⟨u, -, hu⟩
      rw [← z.out_eq'] at hu
      simp only [f] at hu
      rw [QuotientGroup.eq] at hu
      exact ⟨_, u.out.2, _, hu, by simp [_root_.mul_assoc]⟩
  rw [h1, Finset.sum_comp (fun z => φ (x • z)) f, Formalism.UG.hAct,
    finsum_eq_sum_of_support_subset (s := Finset.univ.image f), Finset.smul_sum]
  · refine Finset.sum_congr rfl fun z hz => ?_
    obtain ⟨u₀, -, rfl⟩ := Finset.mem_image.1 hz
    rw [h2, Formalism.UG.dosetInd, Set.indicator_of_mem ((h3 _).2 hz), Pi.one_apply, one_smul]
    congr 2
    conv_lhs => rw [← (f u₀).out_eq']
    rfl
  · intro z hz
    by_contra hn
    apply hz
    simp only [Formalism.UG.dosetInd]
    rw [Set.indicator_of_notMem (fun h => hn (Finset.mem_coe.2 ((h3 z).1 h))), zero_smul]

end Side

section Corr

variable {G₀ : GDatum} {gb : GBase G₀ ℂ}

structure Corr {N N' : ℕ} (X : GenModel gb N) (X' : GenModel gb N') where

  q1 : X'.X ⟶ X.X

  q2 : X'.X ⟶ X.X
  firstProjection_structure : q1 ≫ X.s = X'.s
  secondProjection_structure : q2 ≫ X.s = X'.s

  φ1 : X'.univ.A.left ⟶ X.univ.A.left

  φ2 : X'.univ.A.left ⟶ X.univ.A.left
  φ1_w : φ1 ≫ X.univ.A.hom = X'.univ.A.hom ≫ q1
  φ2_w : φ2 ≫ X.univ.A.hom = X'.univ.A.hom ≫ q2

theorem matEnd_zs {N : ℕ} (X : GenModel gb N) {k : ℕ} (α : Matrix (Fin k) (Fin k) G₀.O) :
    (GlobalTheory.KS.matEnd X.univ.act α).left ≫ zs X k = zs X k := by
  rw [zs, ← Category.assoc, Over.w]

def twistPull {N : ℕ} (X : GenModel gb N) {k : ℕ} (α : Matrix (Fin k) (Fin k) G₀.O) (a b : ℕ) :
    hodgeH (zs X k) a b →ₗ[ℂ] hodgeH (zs X k) a b :=
  hodgePull (matEnd_zs X α) a b

namespace Corr

variable {N N' : ℕ} {X : GenModel gb N} {X' : GenModel gb N'} (C : Corr X X') (k : ℕ)

def c1 : Z X' k ⟶ Z X k := GlobalTheory.KS.powMap C.q1 C.φ1 C.φ1_w k

def c2 : Z X' k ⟶ Z X k := GlobalTheory.KS.powMap C.q2 C.φ2 C.φ2_w k

variable {k} in

def c2Tw (α : Matrix (Fin k) (Fin k) G₀.O) : Z X' k ⟶ Z X k := C.c2 k ≫ (GlobalTheory.KS.matEnd X.univ.act α).left

theorem firstLeg_overComplex : C.c1 k ≫ zs X k = zs X' k := by
  rw [zs, zs, c1, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, Category.assoc, C.firstProjection_structure]

theorem secondLeg_overComplex : C.c2 k ≫ zs X k = zs X' k := by
  rw [zs, zs, c2, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, Category.assoc, C.secondProjection_structure]

variable {k} in

theorem twistedSecondLeg_overComplex (α : Matrix (Fin k) (Fin k) G₀.O) : C.c2Tw α ≫ zs X k = zs X' k := by
  rw [c2Tw, Category.assoc, matEnd_zs, secondLeg_overComplex]

theorem twistedSecondLeg_one : C.c2Tw (1 : Matrix (Fin k) (Fin k) G₀.O) = C.c2 k := by
  rw [c2Tw, GlobalTheory.KS.Model.matEnd_one, Over.id_left, Category.comp_id]

def op [IsFinite (C.c1 k)] [Etale (C.c1 k)] (a b : ℕ) : hodgeH (zs X k) a b →ₗ[ℂ] hodgeH (zs X k) a b :=
  corrOp (C.c1 k) (C.c2 k) (C.firstLeg_overComplex k) (C.secondLeg_overComplex k) a b

variable {k} in

def opTw [IsFinite (C.c1 k)] [Etale (C.c1 k)] (α : Matrix (Fin k) (Fin k) G₀.O) (a b : ℕ) :
    hodgeH (zs X k) a b →ₗ[ℂ] hodgeH (zs X k) a b :=
  corrOp (C.c1 k) (C.c2Tw α) (C.firstLeg_overComplex k) (C.twistedSecondLeg_overComplex α) a b

variable {k} in

theorem opTw_eq [IsFinite (C.c1 k)] [Etale (C.c1 k)] (α : Matrix (Fin k) (Fin k) G₀.O) (a b : ℕ) :
    C.opTw α a b = C.op k a b ∘ₗ twistPull X α a b := by
  refine LinearMap.ext fun x => ?_
  exact congrArg (hodgeTrace (C.firstLeg_overComplex k) a b)
    (hodgePull_comp (matEnd_zs X α) (C.secondLeg_overComplex k) (C.twistedSecondLeg_overComplex α) a b x).symm

def mulBy (X : GenModel gb N) (c : ℕ) : Corr X X where
  q1 := 𝟙 _
  q2 := 𝟙 _
  firstProjection_structure := Category.id_comp _
  secondProjection_structure := Category.id_comp _
  φ1 := 𝟙 _
  φ2 := (𝟙 X.univ.A ^ c).left
  φ1_w := by simp
  φ2_w := by simp

theorem mulBy_secondLeg_projection (X : GenModel gb N) (c : ℕ) (i : Fin k) :
    (mulBy X c).c2 k ≫ (GlobalTheory.KS.pr X.univ.A i).left = (GlobalTheory.KS.pr X.univ.A i ^ c).left := by
  rw [c2, GlobalTheory.KS.PowPB.powMap_pr]
  show _ ≫ (𝟙 X.univ.A ^ c).left = _
  rw [← Over.comp_left, GlobalTheory.DrinLev.HT.MulModel.comp_pow', Category.comp_id]

def IsForget {k' : ℕ} {X' : GenModel gb (N * k')} (C : Corr X X') : Prop :=
  ∃ (hN : 0 < N) (hk : 0 < k') (m : GObjMap (X'.univ.forgetMul hN hk) X.univ C.q1), C.φ1 = m.φ

theorem IsForget.isHeckeLift {k' : ℕ} {X' : GenModel gb (N * k')} {C : Corr X X'} (h : C.IsForget) :
    IsHeckeLift X X' (k' • LinearMap.id) (k' ^ 2) C.q1 C.φ1 := by
  obtain ⟨hN, hk, m, e⟩ := h
  exact ⟨C.firstProjection_structure, _, 𝟙 _, m, isGHecke_forgetMul hN hk X'.univ, e.trans (Category.id_comp _).symm⟩

end Corr

theorem powMap_id_eq {S : Scheme.{0}} (A : Over S) (h : 𝟙 A.left ≫ A.hom = A.hom ≫ 𝟙 S) (k : ℕ) :
    GlobalTheory.KS.powMap (𝟙 S) (𝟙 A.left) h k = 𝟙 _ := by
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [GlobalTheory.KS.PowPB.powMap_w]; simp
  · intro i; rw [GlobalTheory.KS.PowPB.powMap_pr]; simp

theorem corrOp_of_eq_id {Y : Scheme.{0}} {s : Y ⟶ Sp ℂ} {c1 c2 : Y ⟶ Y} [IsFinite c1] [Etale c1] (e : c1 = 𝟙 Y)
    (h1 : c1 ≫ s = s) (h2 : c2 ≫ s = s) (a b : ℕ) : corrOp c1 c2 h1 h2 a b = hodgePull h2 a b := by
  subst e
  exact LinearMap.ext fun x => hodgeTrace_id s a b _

end Corr

section Relevel

variable {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G₀ R} {N M : ℕ}

def relevelObj (e : N = M) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj gb N s) : GObj gb M s :=
  { o with eta_ker := e ▸ o.eta_ker, geom := e ▸ o.geom }

def relevelModel (e : N = M) (X : GenModel gb N) : GenModel gb M where
  X := X.X
  s := X.s
  univ := relevelObj e X.univ
  rep S s' o := by subst e; exact X.rep S s' o

end Relevel

section Wit

variable {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

abbrev GTIsoAt {gb : GBase G₀ R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k]
    (t : Sp k ⟶ S) : Type :=
  GTateIso G₀ k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def GInducesAt {gb : GBase G₀ R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k]
    (t : Sp k ⟶ S) (I : GTIsoAt o t) : Prop :=
  ∀ y, toUnit _ ≫ o.eta y = I.ev N y

theorem gTateIso_ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : G₀.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G₀ k Q act e) (n c : ℕ) (x : G₀.La) : I.ev n (c • x) = I.ev n x ^ c := by
  induction c with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ c ih => rw [succ_nsmul, I.add, ih, pow_succ]

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG R}

def GActsAt {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} {o' : GObj gb N' s} {o'' : GObj gb N s} {k : Type} [Field k]
    {t : Sp k ⟶ S} (I' : GTIsoAt o' t) (I'' : GTIsoAt o'' t) (ψ : o'.A ⟶ o''.A) (m : ℤ) (h : G.GAf) : Prop :=
  ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
    I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, m • L.actG h (inAf D x) = inAf D y + n • v

def IsGIsogWit (h : G.GAf) {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} (o' : GObj gb N' s) (o'' : GObj gb N s)
    (ψ : o'.A ⟶ o''.A) (ψ' : o''.A ⟶ o'.A) (m d : ℕ) : Prop :=
  IsMonHom ψ ∧ IsMonHom ψ' ∧ (∀ c : D.O, o'.act.act c ≫ ψ = ψ ≫ o''.act.act c) ∧
    (∀ c : D.O, o''.act.act c ≫ ψ' = ψ' ≫ o'.act.act c) ∧
    ψ ≫ ψ' = (𝟙 o'.A) ^ d ∧ ψ' ≫ ψ = (𝟙 o''.A) ^ d ∧ m.Coprime p ∧ d.Coprime p ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (β : R →+* k), t ≫ s = spMap β →
      ∃ (I' : GTIsoAt o' t) (I'' : GTIsoAt o'' t), GInducesAt o' t I' ∧ GInducesAt o'' t I'' ∧
        GActsAt L I' I'' ψ m h

def IsGHeckeWit (h : G.GAf) {N N' : ℕ} (X' : GenModel gb N') (X : GenModel gb N) (q : X'.X ⟶ X.X)
    (o'' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o''.A) (ψ' : o''.A ⟶ X'.univ.A) (m d : ℕ)
    (_φ : GObjMap o'' X.univ q) : Prop :=
  q ≫ X.s = X'.s ∧ IsGIsogWit L h X'.univ o'' ψ ψ' m d

def latMonoid : Submonoid G.GAf where
  carrier := {h | ∀ v ∈ LaHat D, L.actG h v ∈ LaHat D}
  one_mem' := fun v hv => by rw [map_one]; exact hv
  mul_mem' := fun {a b} ha hb v hv => by rw [map_mul, Module.End.mul_apply]; exact ha _ (hb v hv)

theorem mem_latMonoid_of_mem_KN {N : ℕ} {h : G.GAf} (hh : h ∈ L.KN N) : h ∈ latMonoid L := fun v hv => by
  obtain ⟨w, hw, e⟩ := hh.1 v hv
  rw [e]
  exact add_mem hv (nsmul_mem hw N)

theorem smul_mem_laHat {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a', x, ha', rfl⟩ := hu
    refine AddSubgroup.subset_closure ⟨a * a', x, fun w => ?_, by rw [TensorProduct.smul_tmul', smul_eq_mul]⟩
    rw [map_mul]
    exact mul_mem (ha w) (ha' w)
  | zero => rw [smul_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => rw [smul_add]; exact add_mem hu hu'
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem GActsAt.mem_latMonoid {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} {o' : GObj gb N' s} {o'' : GObj gb N s}
    {k : Type} [Field k] {t : Sp k ⟶ S} {I' : GTIsoAt o' t} {I'' : GTIsoAt o'' t} {ψ : o'.A ⟶ o''.A} [IsMonHom ψ]
    {h : G.GAf} (H : GActsAt L I' I'' ψ 1 h) : h ∈ latMonoid L := by
  intro v hv
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    have e1 : I'.ev 1 x = 1 := (I'.ker 1 one_pos x).2 ⟨x, (one_nsmul _).symm⟩
    have e2 : I''.ev 1 (0 : D.La) = 1 := (I''.ker 1 one_pos _).2 ⟨(0 : D.La), (one_nsmul _).symm⟩
    obtain ⟨w, hw, e⟩ := (H 1 one_pos (Nat.coprime_one_left p) x 0).1 (by rw [e1, e2, MonObj.one_comp])
    have e0 : inAf D 0 = 0 := map_zero (ForgetHecke.inAfHom D)
    rw [one_smul, e0, zero_add, one_nsmul] at e
    have e3 : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = a • inAf D x := by rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e3, map_smul, e]
    exact smul_mem_laHat ha hw
  | zero => rw [map_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => rw [map_add]; exact add_mem hu hu'
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

theorem GActsAt.comp {S : Scheme.{0}} {s : S ⟶ Sp R} {N₁ N₂ N₃ : ℕ} {o₁ : GObj gb N₁ s} {o₂ : GObj gb N₂ s}
    {o₃ : GObj gb N₃ s} {k : Type} [Field k] {t : Sp k ⟶ S} {I₁ : GTIsoAt o₁ t} {I₂ : GTIsoAt o₂ t}
    {I₃ : GTIsoAt o₃ t} {ψ₁ : o₁.A ⟶ o₂.A} {ψ₂ : o₂.A ⟶ o₃.A} [IsMonHom ψ₁] [IsMonHom ψ₂] {h₁ h₂ : G.GAf}
    (H₁ : GActsAt L I₁ I₂ ψ₁ 1 h₁) (H₂ : GActsAt L I₂ I₃ ψ₂ 1 h₂) :
    GActsAt L I₁ I₃ (ψ₁ ≫ ψ₂) 1 (h₂ * h₁) := by
  have hΔ := H₂.mem_latMonoid
  intro n hn hnp x z
  have ht : (I₁.ev n x ≫ ψ₁) ^ n = 1 := by
    rw [← GlobalTheory.DrinLev.HT.MulModel.pow_comp', (I₁.onto n hn _).2 ⟨x, rfl⟩, MonObj.one_comp]
  obtain ⟨y, hy⟩ := (I₂.onto n hn _).1 ht
  obtain ⟨w, hw, e⟩ := (H₁ n hn hnp x y).1 hy.symm
  rw [← Category.assoc, ← hy, H₂ n hn hnp y z]
  simp only [one_smul] at e ⊢
  rw [map_mul, Module.End.mul_apply, e, map_add, map_nsmul]
  constructor
  · rintro ⟨v, hv, e'⟩
    exact ⟨v + L.actG h₂ w, add_mem hv (hΔ w hw), by rw [e', smul_add, add_assoc]⟩
  · rintro ⟨v, hv, e'⟩
    exact ⟨v - L.actG h₂ w, sub_mem hv (hΔ w hw), by rw [smul_sub, ← add_sub_assoc, ← e', add_sub_cancel_right]⟩

def scalarAf (G : HTGroup p) (a : (AfP p)ˣ) : G.GAf :=
  ⟨(Units.map (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)).toMonoidHom a, a * a), by
    show algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a * (starT G.star (AfP p) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a)).unop =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((a : AfP p) * a)
    have e : algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a = (a : AfP p) ⊗ₜ[ℚ] (1 : G.C) := rfl
    rw [map_mul, e, starT_tmul, map_one, MulOpposite.unop_one]⟩

theorem actG_scalarAf (a : (AfP p)ˣ) (v : AfP p ⊗[ℚ] VQ D) : L.actG (scalarAf G a) v = (a : AfP p) • v := by
  show actOn L.rep (AfP p) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a) v = _
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

theorem scalarAf_mem_latMonoid {a : (AfP p)ˣ} (ha : IsIntAf (a : AfP p)) : scalarAf G a ∈ latMonoid L := fun v hv => by
  rw [actG_scalarAf]; exact smul_mem_laHat ha hv

theorem scalarAf_comm (a : (AfP p)ˣ) (u : G.GAf) : scalarAf G a * u = u * scalarAf G a :=
  Subtype.ext (Prod.ext (Units.ext (Algebra.commutes (a : AfP p) _)) (mul_comm _ _))

def natUnit (p : ℕ) (c : ℕ) (hc : c ≠ 0) : (AfP p)ˣ :=
  Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 (c : ℚ) (Nat.cast_ne_zero.2 hc))

theorem actG_natScalar (c : ℕ) (hc : c ≠ 0) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG (scalarAf G (natUnit p c hc)) v = c • v := by
  rw [actG_scalarAf]
  show algebraMap ℚ (AfP p) (c : ℚ) • v = _
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

theorem isGIsogWit_mul {S : Scheme.{0}} {s : S ⟶ Sp R} {N M : ℕ} (e : N = M) (o : GObj gb N s) {h : G.GAf} {m c : ℕ}
    (hm : m.Coprime p) (hc : c.Coprime p) (hh : ∀ v, (m : ℤ) • L.actG h v = c • v) :
    IsGIsogWit L h (relevelObj e o) o (𝟙 o.A ^ c) (𝟙 o.A ^ c) m (c * c) := by
  subst e
  show IsGIsogWit L h o o (𝟙 o.A ^ c) (𝟙 o.A ^ c) m (c * c)
  haveI := GlobalTheory.DrinLev.HT.MulModel.isMonHom_id_pow o.A c
  refine ⟨inferInstance, inferInstance, fun a => ?_, fun a => ?_, ?_, ?_, hm, Nat.Coprime.mul hc hc,
    fun k _ _ t β ht => ?_⟩
  · haveI := o.act.hom a
    rw [MonObj.comp_pow, GlobalTheory.DrinLev.HT.MulModel.pow_comp', Category.comp_id, Category.id_comp]
  · haveI := o.act.hom a
    rw [MonObj.comp_pow, GlobalTheory.DrinLev.HT.MulModel.pow_comp', Category.comp_id, Category.id_comp]
  · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  obtain ⟨I, hI⟩ := o.geom k t β ht
  refine ⟨I, I, hI, hI, fun n hn hnp x y => ?_⟩
  have e1 : (m : ℤ) • L.actG h (inAf D x) = ((1 : ℕ) : ℤ) • L.actG 1 (inAf D (c • x)) := by
    rw [hh]
    simp only [map_one, Module.End.one_apply, Nat.cast_one, one_smul]
    exact (map_nsmul (ForgetHecke.inAfHom D) c x).symm
  show I.ev n x ≫ 𝟙 o.A ^ c = I.ev n y ↔ _
  rw [e1, ForgetHecke.acts_one_iff L n hn hnp (c • x) y, MonObj.comp_pow, Category.comp_id]
  refine Iff.trans ?_ (I.ker n hn (c • x - y))
  have hx : I.ev n x ^ c = I.ev n (c • x - y) * I.ev n y :=
    (gTateIso_ev_nsmul I n c x).symm.trans
      ((congrArg (I.ev n) (sub_add_cancel (c • x) y).symm).trans (I.add n (c • x - y) y))
  rw [hx]
  exact mul_eq_right

theorem isGIsogWit_refl {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) :
    IsGIsogWit L 1 o o (𝟙 o.A) (𝟙 o.A) 1 1 := by
  have h := isGIsogWit_mul L rfl o (h := 1) (m := 1) (c := 1) (Nat.coprime_one_left p) (Nat.coprime_one_left p)
    (fun v => by simp)
  rw [pow_one] at h
  exact h

theorem isGIsogWit_forgetMul {S : Scheme.{0}} {s : S ⟶ Sp R} {N k' : ℕ} (hN : 0 < N) (hk : 0 < k')
    (o : GObj gb (N * k') s) : IsGIsogWit L 1 o (o.forgetMul hN hk) (𝟙 o.A) (𝟙 o.A) 1 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := isGIsogWit_refl L o
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun k _ _ t β ht => ?_⟩
  obtain ⟨I, hI⟩ := o.geom k t β ht
  refine ⟨I, I, hI, fun y => ?_, fun n hn hnp x y => ?_⟩
  · show toUnit _ ≫ o.eta (k' • y) = I.ev N y
    rw [o.eta_nsmul, MonObj.comp_pow, hI, I.tower N k' hN hk]
  · show I.ev n x ≫ 𝟙 o.A = I.ev n y ↔ _
    rw [ForgetHecke.acts_one_iff L n hn hnp x y, Category.comp_id]
    refine Iff.trans ?_ (I.ker n hn (x - y))
    have hx : I.ev n x = I.ev n (x - y) * I.ev n y :=
      (congrArg (I.ev n) (sub_add_cancel x y).symm).trans (I.add n (x - y) y)
    rw [hx]
    exact mul_eq_right

end Wit

section Op

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG ℂ} {N : ℕ}

def hkIndex (N N' : ℕ) (h : G.GAf) : ℕ := (L.KN N').relIndex (heckeLevel (L.KN N) h⁻¹)

theorem relIndex_KN_ne_zero {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N') : (L.KN N').relIndex (L.KN N) ≠ 0 := by
  obtain ⟨K, hK⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N hN
  obtain ⟨K', hK'⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N' hN'
  haveI : CompactSpace (L.KN N) := isCompact_iff_compactSpace.1 (hK ▸ K.compact)
  have ho : IsOpen ((L.KN N').subgroupOf (L.KN N) : Set (L.KN N)) :=
    (show IsOpen (L.KN N' : Set G.GAf) from hK' ▸ K'.K.isOpen).preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

theorem hkIndex_ne_zero {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N') (h : G.GAf) : hkIndex L N N' h ≠ 0 := fun h0 =>
  relIndex_KN_ne_zero L hN hN' (Subgroup.relIndex_eq_zero_of_le_right (heckeLevel_le _ _) h0)

def IsAdelicHecke (h : G.GAf) {k' : ℕ} {X : GenModel gb N} {X' : GenModel gb (N * k')} (C : Corr X X') : Prop :=
  (N * k').Coprime p ∧ L.KN (N * k') ≤ heckeLevel (L.KN N) h⁻¹ ∧ C.IsForget ∧
    ∃ (o'' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o''.A) (ψ' : o''.A ⟶ X'.univ.A) (d : ℕ) (φ : GObjMap o'' X.univ C.q2),
      IsGHeckeWit L h X' X C.q2 o'' ψ ψ' 1 d φ ∧ C.φ2 = ψ.left ≫ φ.φ

theorem IsAdelicHecke.hkIndex_ne_zero {h : G.GAf} {k' : ℕ} {X : GenModel gb N} {X' : GenModel gb (N * k')}
    {C : Corr X X'} (H : IsAdelicHecke L h C) : hkIndex L N (N * k') h ≠ 0 := by
  obtain ⟨hN, hk, -⟩ := H.2.2.1
  exact GlobalTheory.W2.hkIndex_ne_zero L hN (Nat.mul_pos hN hk) h

theorem IsAdelicHecke.conj_mem {h : G.GAf} {k' : ℕ} {X : GenModel gb N} {X' : GenModel gb (N * k')}
    {C : Corr X X'} (H : IsAdelicHecke L h C) {u : G.GAf} (hu : u ∈ L.KN (N * k')) : h * u * h⁻¹ ∈ L.KN N :=
  (mem_heckeLevel_inv.1 (H.2.1 hu)).2

theorem KN_mul_le (N k' : ℕ) : L.KN (N * k') ≤ L.KN N := by
  have key : ∀ g, L.CongOne (N * k') g → L.CongOne N g := fun g hg v hv => by
    obtain ⟨w, hw, e⟩ := hg v hv
    exact ⟨k' • w, nsmul_mem hw k', by rw [e, mul_smul]⟩
  exact fun g hg => ⟨key _ hg.1, key _ hg.2⟩

theorem exists_isAdelicHecke_one {k' : ℕ} (hp : (N * k').Coprime p) (X : GenModel gb N) (X' : GenModel gb (N * k')) :
    ∃ C : Corr X X', IsAdelicHecke L 1 C ∧ C.q1 = C.q2 := by
  have h0 : N * k' ≠ 0 := fun h0 => (Fact.out : p.Prime).ne_one (by simpa [h0] using hp)
  have hN : 0 < N := Nat.pos_of_ne_zero (left_ne_zero_of_mul h0)
  have hk : 0 < k' := Nat.pos_of_ne_zero (right_ne_zero_of_mul h0)
  obtain ⟨q, ⟨hq, ⟨m⟩⟩, -⟩ := X.rep X'.X X'.s (X'.univ.forgetMul hN hk)
  refine ⟨⟨q, q, hq, hq, m.φ, m.φ, m.cart.1.w, m.cart.1.w⟩, ⟨hp, ?_, ⟨hN, hk, m, rfl⟩, _, 𝟙 X'.univ.A, 𝟙 X'.univ.A, 1, m,
    ⟨hq, isGIsogWit_forgetMul L hN hk X'.univ⟩, (Category.id_comp _).symm⟩, rfl⟩
  rw [heckeLevel_inv_of_comm _ fun u => by simp]
  exact KN_mul_le L N k'

def IsHeckeOpZ (X : GenModel gb N) (k : ℕ) (h : G.GAf) (a b : ℕ) (T : Module.End ℂ (hodgeH (zs X k) a b)) : Prop :=
  ∃ (k' : ℕ) (X' : GenModel gb (N * k')) (C : Corr X X') (_ : IsFinite (C.c1 k)) (_ : Etale (C.c1 k)),
    IsAdelicHecke L h C ∧ T = ((hkIndex L N (N * k') h : ℂ))⁻¹ • C.op k a b

theorem normalised_model_eq_hAct {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N') {h : G.GAf}
    (hle : L.KN N' ≤ heckeLevel (L.KN N) h⁻¹) {W : Type} [AddCommGroup W] [Module ℂ W] (φ : G.GAf ⧸ L.KN N → W)
    (x : G.GAf) :
    ((hkIndex L N N' h : ℂ))⁻¹ • cosetTrace (hle.trans (heckeLevel_le _ _))
        (φ ∘ cosetTr (L.KN N') (L.KN N) h⁻¹ fun _ hu => conj_mem_of_mem_heckeLevel (hle hu)) (x : G.GAf ⧸ L.KN N) =
      Formalism.UG.hAct (L.KN N) (Formalism.UG.dosetInd ℂ (L.KN N) h⁻¹) (fun y => φ y) x := by
  rw [cosetTrace_cosetTr_eq_hAct hle (relIndex_KN_ne_zero L hN hN'), ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  exact (congrArg (· • _) (inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hkIndex_ne_zero L hN hN' h)))).trans (one_smul _ _)

def mulPull {G₀ : GDatum} {gb : GBase G₀ ℂ} (X : GenModel gb N) (k c a b : ℕ) : Module.End ℂ (hodgeH (zs X k) a b) :=
  hodgePull ((Corr.mulBy X c).secondLeg_overComplex k) a b

theorem mulPull_one {G₀ : GDatum} {gb : GBase G₀ ℂ} (X : GenModel gb N) (k a b : ℕ) : mulPull X k 1 a b = 1 := by
  have e : (Corr.mulBy X 1).c2 k = 𝟙 _ := by
    apply GlobalTheory.KS.PowPB.pow_left_hom_ext
    · rw [Corr.c2, GlobalTheory.KS.PowPB.powMap_w]; exact (Category.comp_id _).trans (Category.id_comp _).symm
    · intro i; rw [Corr.mulBy_secondLeg_projection, pow_one, Category.id_comp]
  have key : ∀ (f : Z X k ⟶ Z X k) (hf : f ≫ zs X k = zs X k), f = 𝟙 _ → hodgePull hf a b = 1 := by
    rintro _ hf rfl
    exact LinearMap.ext fun x => hodgePull_id _ a b x
  exact key _ _ e

theorem isHeckeOpZ_of_mul (hN : N.Coprime p) (X : GenModel gb N) (k : ℕ) {h : G.GAf} {c : ℕ} (hc : c.Coprime p)
    (hcomm : ∀ u, h * u = u * h) (hh : ∀ v, L.actG h v = c • v) (a b : ℕ) :
    IsHeckeOpZ L X k h a b (mulPull X k c a b) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h0 => (Fact.out : p.Prime).ne_one (by simpa [h0] using hN)
  let X' : GenModel gb (N * 1) := relevelModel (Nat.mul_one N).symm X
  let C₀ := Corr.mulBy X c
  let C : Corr X X' := ⟨C₀.q1, C₀.q2, C₀.firstProjection_structure, C₀.secondProjection_structure, C₀.φ1, C₀.φ2, C₀.φ1_w, C₀.φ2_w⟩
  have e1 : C.c1 k = 𝟙 (Z X k) := powMap_id_eq X.univ.A _ k
  have hf : IsFinite (C.c1 k) := by rw [e1]; exact inferInstanceAs (IsFinite (𝟙 (Z X k)))
  have he : Etale (C.c1 k) := by rw [e1]; exact inferInstanceAs (Etale (𝟙 (Z X k)))
  let m₀ : GObjMap X.univ X.univ (𝟙 X.X) :=
    { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id X.univ.A, sq := ⟨by simp, by simp⟩,
      act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id X.univ.isLB, eta := fun y => by simp }
  have hlev : heckeLevel (L.KN N) h⁻¹ = L.KN (N * 1) := by rw [heckeLevel_inv_of_comm _ hcomm, Nat.mul_one]
  refine ⟨1, X', C, hf, he, ⟨by rwa [Nat.mul_one], hlev.ge, ⟨hN0, one_pos,
    ⟨m₀.φ, m₀.φ₂, m₀.cart, m₀.sq, m₀.act, m₀.pol, fun y => ?_⟩, rfl⟩, X.univ, 𝟙 X.univ.A ^ c, 𝟙 X.univ.A ^ c, c * c, m₀,
    ⟨Category.id_comp _, isGIsogWit_mul L (Nat.mul_one N).symm X.univ (Nat.coprime_one_left p) hc fun v => ?_⟩,
    (Category.comp_id _).symm⟩, ?_⟩
  · show (X.univ.eta (1 • y)).left ≫ _ = _
    rw [one_nsmul]
    exact m₀.eta y
  · rw [Nat.cast_one, one_smul, hh]
  · rw [hkIndex, hlev, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    exact (@corrOp_of_eq_id _ (zs X k) (C.c1 k) (C.c2 k) hf he e1 (C.firstLeg_overComplex k) (C.secondLeg_overComplex k) a b).symm

theorem isHeckeOpZ_one (hN : N.Coprime p) (X : GenModel gb N) (k a b : ℕ) : IsHeckeOpZ L X k 1 a b 1 := by
  rw [← mulPull_one X k a b]
  exact isHeckeOpZ_of_mul L hN X k (Nat.coprime_one_left p) (fun u => by simp) (fun v => by simp) a b

theorem isHeckeOpZ_natScalar (hN : N.Coprime p) (X : GenModel gb N) (k : ℕ) {c : ℕ} (hc0 : c ≠ 0) (hc : c.Coprime p)
    (a b : ℕ) : IsHeckeOpZ L X k (scalarAf G (natUnit p c hc0)) a b (mulPull X k c a b) :=
  isHeckeOpZ_of_mul L hN X k hc (scalarAf_comm _) (actG_natScalar L c hc0) a b

def IsHeckeOpFun (X : GenModel gb N) (k : ℕ) (f : G.GAf → ℂ) (a b : ℕ) (T : Module.End ℂ (hodgeH (zs X k) a b)) :
    Prop :=
  ∃ (J : Type) (s : Finset J) (h : J → G.GAf) (c : J → ℂ) (Th : J → Module.End ℂ (hodgeH (zs X k) a b)),
    (∀ i ∈ s, IsHeckeOpZ L X k (h i) a b (Th i)) ∧ f = ∑ i ∈ s, c i • Formalism.UG.dosetInd ℂ (L.KN N) (h i)⁻¹ ∧
      T = ∑ i ∈ s, c i • Th i

variable {L}

theorem IsHeckeOpZ.isHeckeOpFun {X : GenModel gb N} {k : ℕ} {h : G.GAf} {a b : ℕ}
    {T : Module.End ℂ (hodgeH (zs X k) a b)} (H : IsHeckeOpZ L X k h a b T) :
    IsHeckeOpFun L X k (Formalism.UG.dosetInd ℂ (L.KN N) h⁻¹) a b T :=
  ⟨Unit, {()}, fun _ => h, fun _ => 1, fun _ => T, fun _ _ => H, by simp, by simp⟩

theorem isHeckeOpFun_zero (X : GenModel gb N) (k a b : ℕ) : IsHeckeOpFun L X k 0 a b 0 :=
  ⟨Unit, ∅, fun _ => 1, fun _ => 0, fun _ => 0, by simp, by simp, by simp⟩

theorem IsHeckeOpFun.smul {X : GenModel gb N} {k : ℕ} {f : G.GAf → ℂ} {a b : ℕ}
    {T : Module.End ℂ (hodgeH (zs X k) a b)} (H : IsHeckeOpFun L X k f a b T) (z : ℂ) :
    IsHeckeOpFun L X k (z • f) a b (z • T) := by
  obtain ⟨J, s, h, c, Th, h1, rfl, rfl⟩ := H
  exact ⟨J, s, h, fun i => z * c i, Th, h1, by simp [Finset.smul_sum, mul_smul], by simp [Finset.smul_sum, mul_smul]⟩

theorem IsHeckeOpFun.add {X : GenModel gb N} {k : ℕ} {f f' : G.GAf → ℂ} {a b : ℕ}
    {T T' : Module.End ℂ (hodgeH (zs X k) a b)} (H : IsHeckeOpFun L X k f a b T) (H' : IsHeckeOpFun L X k f' a b T') :
    IsHeckeOpFun L X k (f + f') a b (T + T') := by
  obtain ⟨J, s, h, c, Th, h1, rfl, rfl⟩ := H
  obtain ⟨J', s', h', c', Th', h1', rfl, rfl⟩ := H'
  refine ⟨J ⊕ J', s.disjSum s', Sum.elim h h', Sum.elim c c', Sum.elim Th Th', ?_, by simp [Finset.sum_disjSum],
    by simp [Finset.sum_disjSum]⟩
  rintro (i | i) hi
  · exact h1 i (Finset.inl_mem_disjSum.1 hi)
  · exact h1' i (Finset.inr_mem_disjSum.1 hi)

theorem IsHeckeOpFun.mem_hecke {X : GenModel gb N} {k : ℕ} {f : G.GAf → ℂ} {a b : ℕ}
    {T : Module.End ℂ (hodgeH (zs X k) a b)} (H : IsHeckeOpFun L X k f a b T) : f ∈ Formalism.UG.Hecke ℂ (L.KN N) := by
  obtain ⟨J, s, h, c, -, -, rfl, -⟩ := H
  exact Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (Formalism.UG.Final.DosetIndMem _ _ _ _)

end Op

section Away

def IsGoodPrime (G₀ : GDatum) (q : ℕ) [Fact q.Prime] : Prop :=
  Nonempty ((G₀.O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 G₀.F] Matrix (Fin G₀.m) (Fin G₀.m) (𝓞 G₀.F ⊗[ℤ] ℤ_[q])) ∧
    (∃ e : ℕ, e.Coprime q ∧ ∀ f : G₀.La →ₗ[ℤ] ℤ, ∃ x, G₀.EF x = e • f) ∧ ¬ (q : ℤ) ∣ NumberField.discr G₀.F

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

def CoversBad (D : Datum p) (N : ℕ) (S : Finset ℕ) : Prop :=
  p ∈ S ∧ ∀ (q : ℕ) [Fact q.Prime], q ∉ S → ¬ q ∣ N ∧ IsGoodPrime D.toG q

def awayGrp (G : HTGroup p) (S : Finset ℕ) : Subgroup G.GAf :=
  ⨅ (v : AwayP p) (_ : ∃ q ∈ S, q.Prime ∧ (q : ℤ) ∈ v.1.asIdeal), (ubcMap (AfP.eval v)).ker

theorem mem_awayGrp {S : Finset ℕ} {g : G.GAf} :
    g ∈ awayGrp G S ↔ ∀ v : AwayP p, (∃ q ∈ S, q.Prime ∧ (q : ℤ) ∈ v.1.asIdeal) → ubcMap (AfP.eval v) g = 1 := by
  simp only [awayGrp, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem scalarAf_mem_awayGrp {S : Finset ℕ} {a : (AfP p)ˣ}
    (ha : ∀ v : AwayP p, (∃ q ∈ S, q.Prime ∧ (q : ℤ) ∈ v.1.asIdeal) → AfP.eval v (a : AfP p) = 1) :
    scalarAf G a ∈ awayGrp G S := by
  refine mem_awayGrp.2 fun v hv => Subtype.ext (Prod.ext (Units.ext ?_) (Units.ext ?_))
  · show Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) ((a : AfP p) ⊗ₜ[ℚ] (1 : G.C)) = 1
    rw [Algebra.TensorProduct.map_tmul, ha v hv, map_one]
    rfl
  · show AfP.eval v ((a : AfP p) * a) = 1
    rw [map_mul, ha v hv, _root_.mul_one]

def locUnit (v : AwayP p) (x : (v.1.adicCompletion ℚ)ˣ) : (AfP p)ˣ :=
  letI := Classical.decEq (AwayP p)
  { val := RestrictedProduct.mulSingle (fun w : AwayP p => w.1.adicCompletionIntegers ℚ) v (x : v.1.adicCompletion ℚ)
    inv := RestrictedProduct.mulSingle (fun w : AwayP p => w.1.adicCompletionIntegers ℚ) v
      ((x⁻¹ : (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ)
    val_inv := (RestrictedProduct.mulSingle_mul _ _ _ _).symm.trans
      (by rw [Units.mul_inv]; exact RestrictedProduct.mulSingle_one _ _)
    inv_val := (RestrictedProduct.mulSingle_mul _ _ _ _).symm.trans
      (by rw [Units.inv_mul]; exact RestrictedProduct.mulSingle_one _ _) }

theorem eval_locUnit_same (v : AwayP p) (x : (v.1.adicCompletion ℚ)ˣ) :
    AfP.eval v (locUnit v x : AfP p) = x := by
  letI := Classical.decEq (AwayP p)
  exact RestrictedProduct.mulSingle_eq_same (fun w : AwayP p => w.1.adicCompletionIntegers ℚ) v _

theorem eval_locUnit_of_ne {v w : AwayP p} (hw : w ≠ v) (x : (v.1.adicCompletion ℚ)ˣ) :
    AfP.eval w (locUnit v x : AfP p) = 1 := by
  letI := Classical.decEq (AwayP p)
  exact RestrictedProduct.mulSingle_eq_of_ne (fun w : AwayP p => w.1.adicCompletionIntegers ℚ) _ hw

variable (L : Link D G)

theorem isIntAf_of_scalarAf_mem {a : (AfP p)ˣ} (ha : scalarAf G a ∈ latMonoid L) : IsIntAf (a : AfP p) := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.finBasis ℤ D.La
  have hr : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos
  have h := GlobalTheory.LKGeo.KNLevel.repr_isIntAf b _ (ha _ (GlobalTheory.LKGeo.KNLevel.bA_mem b ⟨0, hr⟩)) ⟨0, hr⟩
  rwa [actG_scalarAf, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    _root_.mul_one] at h

theorem scalarAf_locUnit_spec {S : Finset ℕ} {v : AwayP p} (hv : ∀ q ∈ S, q.Prime → (q : ℤ) ∉ v.1.asIdeal)
    {x : (v.1.adicCompletion ℚ)ˣ} (hx : (x : v.1.adicCompletion ℚ) ∈ v.1.adicCompletionIntegers ℚ)
    (hx' : ((x⁻¹ : (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) ∉ v.1.adicCompletionIntegers ℚ) (N : ℕ) :
    scalarAf G (locUnit v x) ∈ awayGrp G S ∧ scalarAf G (locUnit v x) ∈ latMonoid L ∧
      scalarAf G (locUnit v x) ∉ L.KN N := by
  refine ⟨scalarAf_mem_awayGrp fun w ⟨q, hq, hqp, hw⟩ => eval_locUnit_of_ne (fun (e : w = v) => hv q hq hqp (by rw [← e]; exact hw)) x,
    scalarAf_mem_latMonoid L fun w => ?_, fun hK => hx' ?_⟩
  · by_cases e : w = v
    · subst e; rwa [eval_locUnit_same]
    · rw [eval_locUnit_of_ne e]; exact one_mem _
  · have e : (scalarAf G (locUnit v x))⁻¹ = scalarAf G (locUnit v x⁻¹) :=
      Subtype.ext (Prod.ext (Units.ext rfl) (Units.ext rfl))
    have h := isIntAf_of_scalarAf_mem L (e ▸ mem_latMonoid_of_mem_KN L ((L.KN N).inv_mem hK)) v
    rwa [eval_locUnit_same] at h

def awaySupp (N : ℕ) (S : Finset ℕ) : Set G.GAf :=
  {g | ∃ h ∈ awayGrp G S, h ∈ latMonoid L ∧ g ∈ DoubleCoset.doubleCoset h⁻¹ (L.KN N : Set G.GAf) (L.KN N)}

def heckeAway (N : ℕ) (S : Finset ℕ) : Submodule ℂ (G.GAf → ℂ) :=
  Formalism.UG.Hecke ℂ (L.KN N) ⊓
    { carrier := {f | ∀ g, f g ≠ 0 → g ∈ awaySupp L N S}
      zero_mem' := fun _ h => (h rfl).elim
      add_mem' := fun {f f'} hf hf' g hg => by
        by_cases h : f g = 0
        · exact hf' g fun h' => hg (by simp [h, h'])
        · exact hf g h
      smul_mem' := fun c f hf g hg => hf g fun h => hg (by simp [h]) }

theorem mem_heckeAway {N : ℕ} {S : Finset ℕ} {f : G.GAf → ℂ} :
    f ∈ heckeAway L N S ↔ f ∈ Formalism.UG.Hecke ℂ (L.KN N) ∧ ∀ g, f g ≠ 0 → g ∈ awaySupp L N S := Iff.rfl

theorem dosetInd_mem_heckeAway {N : ℕ} {S : Finset ℕ} {h : G.GAf} (hS : h ∈ awayGrp G S) (hΔ : h ∈ latMonoid L) :
    Formalism.UG.dosetInd ℂ (L.KN N) h⁻¹ ∈ heckeAway L N S :=
  ⟨Formalism.UG.Final.DosetIndMem _ _ _ _, fun _ hg => ⟨h, hS, hΔ, Set.mem_of_indicator_ne_zero hg⟩⟩

theorem inv_mem_latMonoid_of_mem_awaySupp {N : ℕ} {S : Finset ℕ} {g : G.GAf} (hg : g ∈ awaySupp L N S) :
    g⁻¹ ∈ latMonoid L := by
  obtain ⟨h, -, hΔ, hg⟩ := hg
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [mul_inv_rev, mul_inv_rev, inv_inv]
  exact mul_mem (mem_latMonoid_of_mem_KN L ((L.KN N).inv_mem hb))
    (mul_mem hΔ (mem_latMonoid_of_mem_KN L ((L.KN N).inv_mem ha)))

end Away

section Basic₂

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG ℂ} {N : ℕ}

example (hN : N.Coprime p) (S : Finset ℕ) (X : GenModel gb N) (k a b : ℕ) :
    Formalism.UG.dosetInd ℂ (L.KN N) 1 ∈ heckeAway L N S ∧ IsHeckeOpFun L X k (Formalism.UG.dosetInd ℂ (L.KN N) 1) a b 1 := by
  have h1 := dosetInd_mem_heckeAway L (N := N) (S := S) (one_mem _) (one_mem _)
  have h2 := (isHeckeOpZ_one L hN X k a b).isHeckeOpFun
  rw [inv_one] at h1 h2
  exact ⟨h1, h2⟩

example (c : ℕ) (hc : c ≠ 0) : scalarAf G (natUnit p c hc) ∈ latMonoid L := fun v hv => by
  rw [actG_natScalar]; exact nsmul_mem hv c

example (a : (AfP p)ˣ) (N' : ℕ) : hkIndex L N N' (scalarAf G a) = (L.KN N').relIndex (L.KN N) := by
  rw [hkIndex, heckeLevel_inv_of_comm _ (scalarAf_comm a)]

example (hN : p ∣ N) (X : GenModel gb N) (k : ℕ) (h : G.GAf) (a b : ℕ) (T : Module.End ℂ (hodgeH (zs X k) a b)) :
    ¬ IsHeckeOpZ L X k h a b T := by
  rintro ⟨k', X', C, _, _, H, -⟩
  exact (Fact.out : p.Prime).ne_one (Nat.Coprime.eq_one_of_dvd H.1.symm (hN.mul_right k'))

example (h : ¬ (p : ℤ) ∣ NumberField.discr D.F) : IsGoodPrime D.toG p := ⟨D.splitP, D.perfP, h⟩

end Basic₂

end GlobalTheory.W2
