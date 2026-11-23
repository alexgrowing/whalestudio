import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.HasEnoughRootsOfUnityGlobalSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteAbelianWeightDecomposition

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulSplit

open FiniteAbelianWeights in

theorem nonempty_equiv_pi_of_weights {R M N G : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [CommGroup G] [Finite G] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity R n]
    (hn : IsUnit (n : R)) (hG : ∀ g : G, g ^ n = 1) (ρ : Representation R G M) (W : Submodule R M)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W)
    (h : ∀ χ : G →* Rˣ, ∃ f : N →ₗ[R] M, Function.Injective f ∧
      ∀ v, (∃ x, f x = v) ↔ v ∈ W ∧ ∀ g, ρ g v = (χ g : R) • v) :
    Nonempty (W ≃ₗ[R] (G → N)) := by
  classical
  haveI : HasEnoughRootsOfUnity R (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd R (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R
  haveI : Finite (G →* Rˣ) := Finite.of_equiv G e.toEquiv.symm
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite (G →* Rˣ)
  obtain ⟨u, hu⟩ : ∃ u : R, u * (Fintype.card G : R) = 1 := by
    have h1 := card_dvd_exponent_pow_rank' G hG
    rw [Nat.card_eq_fintype_card] at h1
    have h2 : (Fintype.card G : R) ∣ (n : R) ^ Group.rank G := by
      exact_mod_cast Nat.cast_dvd_cast (α := R) h1
    exact (isUnit_of_dvd_unit h2 (hn.pow _)).exists_left_inv
  choose f hf hr using h
  let F : ((G →* Rˣ) → N) →ₗ[R] M := ∑ χ, (f χ).comp (LinearMap.proj χ)
  have hF : ∀ x, F x = ∑ χ, f χ (x χ) := fun x => by simp [F, LinearMap.sum_apply]
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext c
    apply hf c
    have := congrArg (avg ρ u c) hx
    rw [hF, map_sum, map_zero, Finset.sum_eq_single c, avg_of_weight ρ u hu c _ ((hr c _).1 ⟨_, rfl⟩).2] at this
    · simpa using this
    · exact fun d _ hd => avg_of_weight_ne ρ u c d hd _ ((hr d _).1 ⟨_, rfl⟩).2
    · simp
  have hrange : LinearMap.range F = W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hF]
      exact W.sum_mem fun c _ => ((hr c _).1 ⟨_, rfl⟩).1
    · intro w hw
      have : ∀ c, ∃ x, f c x = avg ρ u c w := fun c => (hr c _).2 ⟨by
        rw [avg_apply]
        exact W.smul_mem _ (W.sum_mem fun t _ => W.smul_mem _ (hW t w hw)), fun g => apply_avg ρ u c g w⟩
      choose x hx using this
      refine ⟨x, ?_⟩
      rw [hF, Finset.sum_congr rfl fun c _ => hx c, sum_avg ρ u hu]
  exact ⟨(LinearEquiv.ofEq _ _ hrange).symm.trans ((LinearEquiv.ofInjective F hinj).symm.trans
    (LinearEquiv.funCongrLeft R N e.toEquiv.symm))⟩

section Values

variable {X Y B : Scheme.{0}} (L : LB X) (p : Y ⟶ B)

def Idx : Type :=
  {t : Y × ((Y ⟶ X) → L.ι) × (Y ⟶ Y) // Good L t.1 t.2.1 ∧ t.2.2 ≫ p = p}

def Vals : Type := ∀ i : Idx L p, Y.presheaf.stalk i.1.1

instance : CommRing (Vals L p) := inferInstanceAs (CommRing (∀ i : Idx L p, Y.presheaf.stalk i.1.1))

def cstHom : Γ(B, ⊤) →+* Vals L p :=
  Pi.ringHom fun i => (Y.presheaf.germ (p ⁻¹ᵁ ⊤) i.1.1 trivial).hom.comp (p.app ⊤).hom

instance : Algebra Γ(B, ⊤) (Vals L p) := (cstHom L p).toAlgebra

variable {L p}

theorem algebraMap_vals (c : Γ(B, ⊤)) (i : Idx L p) :
    algebraMap Γ(B, ⊤) (Vals L p) c i = gs p i.1.1 ⊤ c := (gs_eq p i.1.1 ⊤ trivial c).symm

theorem mul_vals (v w : Vals L p) (i : Idx L p) : (v * w) i = v i * w i := rfl

variable {K K' : Type} [Fintype K] [Fintype K']

variable (p) in

def ev {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) : Vals L p :=
  fun i => sval s i.1.2.2 i.1.1 i.1.2.1

def dv (φ : K → (Y ⟶ X)) (ε : K → ℤ) : (Y ⟶ X) →₀ ℤ := ∑ k, Finsupp.single (φ k) (ε k)

theorem formEq_of_dv {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : dv φ ε = dv φ' ε') : FormEq φ ε φ' ε' := by
  intro U _ f
  have := congrArg (Finsupp.linearCombination ℤ (fun ψ => Additive.ofMul (f ψ))) h
  simp only [dv, map_sum, Finsupp.linearCombination_single] at this
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow] using this

theorem dv_support (D : (Y ⟶ X) →₀ ℤ) : dv (fun k : D.support => k.1) (fun k => D k.1) = D :=
  (Finset.sum_coe_sort D.support (fun ψ => Finsupp.single ψ (D ψ))).trans D.sum_single

theorem dv_comp {Y' : Scheme.{0}} (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    dv (fun k => h ≫ φ k) ε = (dv φ ε).mapDomain (h ≫ ·) := by
  simp only [dv, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]

theorem ev_add {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s t u : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ j, u.f j = s.f j + t.f j) : ev p u = ev p s + ev p t :=
  funext fun i => (congrArg (gs _ _ _) (h _)).trans (gs_add _ _ _ (i.2.1.mem φ _) _ _)

theorem ev_smul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s u : LB.Sec (LB.LinComb L φ ε)} (c : Γ(B, ⊤))
    (h : ∀ j, u.f j = (Y.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom c) * s.f j) :
    ev p u = c • ev p s := by
  funext i
  have hm := i.2.1.mem φ i.1.2.2
  refine (congrArg (gs _ _ _) (h _)).trans ((gs_mul _ _ _ hm _ _).trans ?_)
  rw [Algebra.smul_def, mul_vals, algebraMap_vals]
  refine congrArg₂ (· * ·) ((gs_res _ _ _ hm _).trans ((gs_pull _ p _ ⊤ trivial c).trans ?_)) rfl
  rw [i.2.2]

theorem ev_zero {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) :
    ev p s = 0 :=
  funext fun i => (congrArg (gs _ _ _) (h _)).trans ((gs_eq _ _ _ (i.2.1.mem φ _) _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem ev_inj (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s t : LB.Sec (LB.LinComb L φ ε)}
    (h : ev p s = ev p t) (j : K → L.ι) : s.f j = t.f j :=
  sec_ext_val hL (fun y J hJ => congrFun h ⟨(y, J, 𝟙 Y), hJ, Category.id_comp _⟩) j

variable (L p) in

def Sg (D : (Y ⟶ X) →₀ ℤ) : Submodule Γ(B, ⊤) (Vals L p) where
  carrier := {v | ∃ s : LB.Sec (LB.LinComb L (fun k : D.support => k.1) (fun k => D k.1)), ev p s = v}
  add_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨secAdd s t, ev_add fun _ => rfl⟩
  zero_mem' := ⟨secZero _, ev_zero fun _ => rfl⟩
  smul_mem' := by
    rintro c _ ⟨s, rfl⟩
    exact ⟨secCMul (fun _ => le_top) (p.appTop.hom c) s, ev_smul c fun _ => rfl⟩

theorem mem_Sg (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {D : (Y ⟶ X) →₀ ℤ} (h : dv φ ε = D)
    (v : Vals L p) : v ∈ Sg L p D ↔ ∃ s : LB.Sec (LB.LinComb L φ ε), ev p s = v := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', hs⟩ := exists_sec hL (formEq_of_dv ((dv_support D).trans h.symm)) s
    exact ⟨s', funext fun i => hs _ _ _ _ i.2.1⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨s', hs⟩ := exists_sec hL (formEq_of_dv (h.trans (dv_support D).symm)) s
    exact ⟨s', funext fun i => hs _ _ _ _ i.2.1⟩

theorem mul_mem_Sg (hL : L.IsLB) {D E F : (Y ⟶ X) →₀ ℤ} {v w : Vals L p} (hv : v ∈ Sg L p D)
    (hw : w ∈ Sg L p E) (h : D + E = F) : v * w ∈ Sg L p F := by
  obtain ⟨s, rfl⟩ := hv
  obtain ⟨t, rfl⟩ := hw
  refine (mem_Sg hL ?_ _).2 ⟨mulSec s t, funext fun i => sval_mulSec s t _ _ i.2.1⟩
  rw [← h]
  exact (Fintype.sum_sum_type _).trans (congrArg₂ (· + ·) (dv_support D) (dv_support E))

variable (L) in

def pl (h : Y ⟶ Y) (hh : h ≫ p = p) : Vals L p →ₐ[Γ(B, ⊤)] Vals L p where
  toFun v := fun i => v ⟨(i.1.1, i.1.2.1, i.1.2.2 ≫ h), i.2.1, by rw [Category.assoc, hh, i.2.2]⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem pl_pl {h h' h'' : Y ⟶ Y} (hh : h ≫ p = p) (hh' : h' ≫ p = p) (hh'' : h'' ≫ p = p) (e : h ≫ h' = h'')
    (v : Vals L p) : pl L h hh (pl L h' hh' v) = pl L h'' hh'' v := by
  subst e
  funext i
  have : ∀ (a b : Y ⟶ Y) (ha hb), a = b → v ⟨(i.1.1, i.1.2.1, a), ha⟩ = v ⟨(i.1.1, i.1.2.1, b), hb⟩ := by
    rintro a b ha hb rfl; rfl
  exact this _ _ _ _ (Category.assoc _ _ _)

theorem pl_id {h : Y ⟶ Y} (hh : h ≫ p = p) (e : h = 𝟙 Y) (v : Vals L p) : pl L h hh v = v := by
  subst e
  funext i
  have : ∀ (a b : Y ⟶ Y) (ha hb), a = b → v ⟨(i.1.1, i.1.2.1, a), ha⟩ = v ⟨(i.1.1, i.1.2.1, b), hb⟩ := by
    rintro a b ha hb rfl; rfl
  exact this _ _ _ i.2 (Category.comp_id _)

theorem pl_mem_Sg (hL : L.IsLB) {h : Y ⟶ Y} (hh : h ≫ p = p) {D E : (Y ⟶ X) →₀ ℤ} {v : Vals L p}
    (hv : v ∈ Sg L p D) (e : D.mapDomain (h ≫ ·) = E) : pl L h hh v ∈ Sg L p E := by
  obtain ⟨s, rfl⟩ := hv
  refine (mem_Sg hL ?_ _).2 ⟨pullSec s h, funext fun i => sval_pullSec s h _ _ i.2.1⟩
  rw [dv_comp, dv_support, e]

def IsG (D : (Y ⟶ X) →₀ ℤ) (u : (Vals L p)ˣ) : Prop := u.val ∈ Sg L p D ∧ (u⁻¹).val ∈ Sg L p (-D)

theorem exists_isG (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : (Vals L p)ˣ, IsG (dv φ ε) u ∧ ∀ i : Idx L p, u.val i = (val t i.1.2.2 i.1.1 i.1.2.1).val := by
  refine ⟨⟨fun i => (val t i.1.2.2 i.1.1 i.1.2.1).val, fun i => ((val t i.1.2.2 i.1.1 i.1.2.1)⁻¹).val,
    funext fun i => Units.mul_inv _, funext fun i => Units.inv_mul _⟩, ⟨?_, ?_⟩, fun _ => rfl⟩
  · exact (mem_Sg hL rfl _).2 ⟨genSec t ht, funext fun i => sval_genSec t ht _ _ i.2.1⟩
  · refine (mem_Sg hL ?_ _).2 ⟨genSec (LB.invGen L φ ε t) (DVR.invGen_isGen _ _ _ _ ht), funext fun i =>
      (sval_genSec _ _ _ _ i.2.1).trans (congrArg Units.val (val_inv t _))⟩
    simp only [dv, Finsupp.single_neg, Finset.sum_neg_distrib]

theorem IsG.inv {D : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (h : IsG D u) : IsG (-D) u⁻¹ :=
  ⟨h.2, by rw [inv_inv, neg_neg]; exact h.1⟩

theorem IsG.mul (hL : L.IsLB) {D E : (Y ⟶ X) →₀ ℤ} {u w : (Vals L p)ˣ} (h : IsG D u) (h' : IsG E w) :
    IsG (D + E) (u * w) :=
  ⟨mul_mem_Sg hL h.1 h'.1 rfl, by rw [mul_inv]; exact mul_mem_Sg hL h.2 h'.2 (neg_add _ _).symm⟩

theorem IsG.pow (hL : L.IsLB) {D : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (h : IsG D u) (j : ℕ) :
    IsG ((j + 1) • D) (u ^ (j + 1)) := by
  induction j with
  | zero => simpa using h
  | succ j ih => rw [succ_nsmul, pow_succ]; exact ih.mul hL h

theorem IsG.pull (hL : L.IsLB) {h : Y ⟶ Y} (hh : h ≫ p = p) {D : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ}
    (hu : IsG D u) : IsG (D.mapDomain (h ≫ ·)) (Units.map (pl L h hh : Vals L p →* Vals L p) u) :=
  ⟨pl_mem_Sg hL hh hu.1 rfl, pl_mem_Sg hL hh hu.2 (map_neg (Finsupp.mapDomain.addMonoidHom (h ≫ ·)) D)⟩

theorem IsG.equiv (hL : L.IsLB) {D E F : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (hu : IsG D u) (h : E + D = F) :
    Nonempty (Sg L p E ≃ₗ[Γ(B, ⊤)] Sg L p F) :=
  ⟨{ toFun := fun v => ⟨v.1 * u.val, mul_mem_Sg hL v.2 hu.1 h⟩
     invFun := fun v => ⟨v.1 * (u⁻¹).val, mul_mem_Sg hL v.2 hu.2 (by rw [← h]; abel)⟩
     map_add' := fun _ _ => Subtype.ext (add_mul _ _ _)
     map_smul' := fun _ _ => Subtype.ext (smul_mul_assoc _ _ _)
     left_inv := fun _ => Subtype.ext (Units.mul_inv_cancel_right _ _)
     right_inv := fun _ => Subtype.ext (Units.inv_mul_cancel_right _ _) }⟩

theorem pl_equiv (hL : L.IsLB) {h h' : Y ⟶ Y} (hh : h ≫ p = p) (hh' : h' ≫ p = p) (e : h ≫ h' = 𝟙 Y)
    (e' : h' ≫ h = 𝟙 Y) {D E : (Y ⟶ X) →₀ ℤ} (hE : D.mapDomain (h ≫ ·) = E) :
    Nonempty (Sg L p D ≃ₗ[Γ(B, ⊤)] Sg L p E) :=
  ⟨{ toFun := fun v => ⟨pl L h hh v.1, pl_mem_Sg hL hh v.2 hE⟩
     invFun := fun v => ⟨pl L h' hh' v.1, pl_mem_Sg hL hh' v.2 (by
       rw [← hE, ← Finsupp.mapDomain_comp]
       refine (congrArg (Finsupp.mapDomain · D) (funext fun ψ => ?_)).trans Finsupp.mapDomain_id
       show h' ≫ h ≫ ψ = ψ
       rw [← Category.assoc, e', Category.id_comp])⟩
     map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
     map_smul' := fun _ _ => Subtype.ext (map_smul (pl L h hh) _ _)
     left_inv := fun _ => Subtype.ext ((pl_pl _ _ (Category.id_comp _) e' _).trans (pl_id _ rfl _))
     right_inv := fun _ => Subtype.ext ((pl_pl _ _ (Category.id_comp _) e _).trans (pl_id _ rfl _)) }⟩

end Values

section Descent

variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B} {G : Type}

def Descends (q : Y ⟶ Y) (τ : G → (Y ⟶ Y)) : Prop :=
  (∀ U : Y.Opens, Function.Injective (q.app U).hom) ∧
  ∀ (U : Y.Opens) (f : Γ(Y, q ⁻¹ᵁ U)),
    (∀ g, ∀ y ∈ q ⁻¹ᵁ U, gs (τ g) y (q ⁻¹ᵁ U) f = gs (𝟙 Y) y (q ⁻¹ᵁ U) f) → ∃ a, (q.app U).hom a = f

theorem gs_comp {Z W : Scheme.{0}} (r : Z ⟶ W) (t : W ⟶ Y) (z : Z) (U : Y.Opens) (h : t (r z) ∈ U)
    (f : Γ(Y, U)) : gs (r ≫ t) z U f = (r.stalkMap z).hom (gs t (r z) U f) := by
  rw [← gs_pull r t z U h, gs_stalkMap r z (t ⁻¹ᵁ U) h, gs_pull (𝟙 W) t (r z) U h, Category.id_comp]

theorem Descends.of_iso {A : Scheme.{0}} {q : A ⟶ A} {τ : G → (A ⟶ A)} (H : Descends q τ)
    (hτq : ∀ g, τ g ≫ q = q) (e : Y ≅ A)
    {q' : Y ⟶ Y} {τ' : G → (Y ⟶ Y)} (hq : e.inv ≫ q' = q ≫ e.inv) (hτ : ∀ g, e.inv ≫ τ' g = τ g ≫ e.inv) :
    Descends q' τ' := by
  obtain rfl : q' = e.hom ≫ q ≫ e.inv := by rw [← hq, Iso.hom_inv_id_assoc]
  refine ⟨fun U => ?_, fun U f hf => ?_⟩
  · exact (ConcreteCategory.bijective_of_isIso (e.hom.app (q ⁻¹ᵁ (e.inv ⁻¹ᵁ U)))).1.comp
      ((H.1 (e.inv ⁻¹ᵁ U)).comp (ConcreteCategory.bijective_of_isIso (e.inv.app U)).1)
  · have m : q ⁻¹ᵁ (e.inv ⁻¹ᵁ U) ≤ e.inv ⁻¹ᵁ ((e.hom ≫ q ≫ e.inv) ⁻¹ᵁ U) := fun z hz =>
      (congrArg (fun t => t z ∈ U) hq).mpr hz
    obtain ⟨a, ha⟩ := H.2 (e.inv ⁻¹ᵁ U) ((e.inv.appLE _ _ m).hom f) (fun g z hz => by
      have hz' : τ g z ∈ q ⁻¹ᵁ (e.inv ⁻¹ᵁ U) := (congrArg (fun t => e.inv (t z) ∈ U) (hτq g)).mpr hz
      have hz'' : τ' g (e.inv z) ∈ (e.hom ≫ q ≫ e.inv) ⁻¹ᵁ U :=
        (congrArg (fun t => t z ∈ (e.hom ≫ q ≫ e.inv) ⁻¹ᵁ U) (hτ g)).mpr (m hz')
      rw [gs_appLE _ _ _ m (τ g) z hz', gs_appLE _ _ _ m (𝟙 A) z hz, ← hτ, gs_comp _ _ _ _ hz'', hf g _ (m hz),
        ← gs_comp e.inv (𝟙 Y) z _ (m hz), Category.comp_id, Category.id_comp])
    have m' : U ≤ e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ U) := fun y hy => (congrArg (fun t => t y ∈ U) e.hom_inv_id).mpr hy
    refine ⟨(e.hom.appLE _ _ m').hom a, fn_ext fun y hy => ?_⟩
    have hy' : e.hom y ∈ q ⁻¹ᵁ (e.inv ⁻¹ᵁ U) := hy
    rw [gs_pull (𝟙 Y) _ y U hy, Category.id_comp, gs_appLE _ _ _ m' _ y hy, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, ← gs_pull e.hom q y _ hy', ha, gs_appLE _ _ _ m _ y hy', Iso.hom_inv_id]

theorem Descends.injective (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ) (hq : q ≫ p = p)
    {D : (Y ⟶ X) →₀ ℤ} {v : Vals L p} (hv : v ∈ Sg L p D) (h : pl L q hq v = 0) : v = 0 := by
  obtain ⟨s, rfl⟩ := hv
  refine ev_zero fun j => H.1 _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
  have h0 : sval s (𝟙 Y ≫ q) y I = 0 := congrFun h ⟨(y, I, 𝟙 Y), hI, Category.id_comp _⟩
  refine (gs_pull (𝟙 Y) q y _ hy _).trans ((sec_trans s (𝟙 Y ≫ q) y hy (Good.mem hI _ _)).trans ?_)
  refine ((congrArg _ h0).trans (mul_zero _)).trans (Eq.symm ?_)
  exact (gs_pull (𝟙 Y) q y _ hy _).trans ((gs_eq _ _ _ hy _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem Descends.exists_mem (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ) (hq : q ≫ p = p)
    (hτ : ∀ g, τ g ≫ p = p) (hτq : ∀ g, τ g ≫ q = q) {D : (Y ⟶ X) →₀ ℤ} {v : Vals L p}
    (hv : v ∈ Sg L p (D.mapDomain (q ≫ ·))) (h : ∀ g, pl L (τ g) (hτ g) v = v) :
    ∃ w ∈ Sg L p D, pl L q hq w = v := by
  let φ : D.support → (Y ⟶ X) := fun k => k.1
  let ε : D.support → ℤ := fun k => D k.1
  obtain ⟨s, rfl⟩ := (mem_Sg hL (φ := fun k => q ≫ φ k) (ε := ε) (by rw [dv_comp, dv_support]) v).1 hv
  have le : ∀ j, q ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => q ≫ φ k) j :=
    fun j _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have ge : ∀ j, LB.wchart L (fun k => q ≫ φ k) j ≤ q ⁻¹ᵁ LB.wchart L φ j :=
    fun j _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have ex : ∀ j, ∃ a, (q.app (LB.wchart L φ j)).hom a = (Y.presheaf.map (homOfLE (le j)).op).hom (s.f j) :=
    fun j => H.2 _ _ fun g y hy => by
      have hy' : τ g y ∈ q ⁻¹ᵁ LB.wchart L φ j := (congrArg (fun t => t y ∈ LB.wchart L φ j) (hτq g)).mpr hy
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have h0 : sval s (𝟙 Y ≫ τ g) y I = sval s (𝟙 Y) y I :=
        congrFun (h g) ⟨(y, I, 𝟙 Y), hI, Category.id_comp _⟩
      rw [Category.id_comp] at h0
      refine (gs_res _ y (le j) hy' _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y (le j) hy _).symm)
      refine (sec_trans s (τ g) y (le j hy') (Good.mem hI _ _)).trans
        (Eq.trans ?_ (sec_trans s (𝟙 Y) y (le j hy) (Good.mem hI _ _)).symm)
      refine congrArg₂ (· * ·) ?_ h0
      have e : ∀ k, τ g ≫ q ≫ φ k = 𝟙 Y ≫ q ≫ φ k := fun k => by
        rw [← Category.assoc, hτq, Category.id_comp]
      refine congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)
      show gm (τ g ≫ q ≫ φ k) y (L.U (j k) ⊓ L.U (I (τ g ≫ q ≫ φ k))) (L.g (j k) (I (τ g ≫ q ≫ φ k))) ^ _ =
        gm (𝟙 Y ≫ q ≫ φ k) y (L.U (j k) ⊓ L.U (I (𝟙 Y ≫ q ≫ φ k))) (L.g (j k) (I (𝟙 Y ≫ q ≫ φ k))) ^ _
      rw [e]
  choose a ha using ex
  have key : ∀ (r : Y ⟶ Y) (y : Y) (j), r y ∈ LB.wchart L (fun k => q ≫ φ k) j →
      gs (r ≫ q) y (LB.wchart L φ j) (a j) = gs r y (LB.wchart L (fun k => q ≫ φ k) j) (s.f j) :=
    fun r y j hy => (gs_pull r q y (LB.wchart L φ j) (show r y ∈ q ⁻¹ᵁ LB.wchart L φ j from ge j hy) _).symm.trans ((congrArg (gs r y _) (ha j)).trans
      (gs_res r y (le j) (ge j hy) _))
  let s' : LB.Sec (LB.LinComb L φ ε) := ⟨a, fun j j' => H.1 _ (fn_ext fun y hy => by
    have hm : (𝟙 Y ≫ q) y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
    refine (gs_pull (𝟙 Y) q y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y) q y _ hy _).symm)
    refine ((gs_res _ y _ hm _).trans (key _ y j (le j hy.1))).trans (Eq.trans ?_ ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans
        (congrArg Units.val (gm_linComb L φ ε (𝟙 Y ≫ q) y j j' hm.1 hm.2)))
        ((gs_res _ y _ hm _).trans (key _ y j' (le j' hy.2))))).symm)
    rw [sec_trans s (𝟙 Y) y (le j hy.1) (le j' hy.2)]
    simp only [trF, Category.assoc])⟩
  refine ⟨ev p s', ⟨s', rfl⟩, funext fun i => ?_⟩
  exact (sval_of s' (i.1.2.2 ≫ q) i.1.1 i.1.2.1 (fun k => i.1.2.1 (i.1.2.2 ≫ q ≫ φ k))
    (fun k => by rw [Category.assoc])).trans (key _ _ _ (i.2.1.mem _ _))

theorem Descends.weight (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ) (hq : q ≫ p = p)
    (hτ : ∀ g, τ g ≫ p = p) (hτq : ∀ g, τ g ≫ q = q) {D E F : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (hu : IsG E u)
    (χ : G → Γ(B, ⊤)ˣ) (hχ : ∀ g, pl L (τ g) (hτ g) u.val = (χ g).val • u.val)
    (hF : D.mapDomain (q ≫ ·) + E = F) :
    ∃ f : Sg L p D →ₗ[Γ(B, ⊤)] Vals L p, Function.Injective f ∧
      ∀ v, (∃ x, f x = v) ↔ v ∈ Sg L p F ∧ ∀ g, pl L (τ g) (hτ g) v = (χ g).val • v := by
  refine ⟨⟨⟨fun x => pl L q hq x.1 * u.val, fun x y => ?_⟩, fun c x => ?_⟩, ?_, fun v => ⟨?_, ?_⟩⟩
  · rw [Submodule.coe_add, map_add, add_mul]
  · show pl L q hq (c • x.1) * u.val = c • (pl L q hq x.1 * u.val)
    rw [map_smul, smul_mul_assoc]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (H.injective hL hq x.2 (u.mul_left_eq_zero.1 hx))
  · rintro ⟨x, rfl⟩
    refine ⟨mul_mem_Sg hL (pl_mem_Sg hL hq x.2 rfl) hu.1 hF, fun g => ?_⟩
    show pl L (τ g) (hτ g) (pl L q hq x.1 * u.val) = (χ g).val • (pl L q hq x.1 * u.val)
    rw [map_mul, hχ, pl_pl _ _ hq (hτq g), mul_smul_comm]
  · rintro ⟨hv, hv'⟩
    obtain ⟨w, hw, e⟩ := H.exists_mem hL hq hτ hτq (D := D) (v := v * (u⁻¹).val)
      (mul_mem_Sg hL hv hu.2 (by rw [← hF]; abel)) (fun g => by
        have h1 : pl L (τ g) (hτ g) (v * (u⁻¹).val) * pl L (τ g) (hτ g) u.val = pl L (τ g) (hτ g) v := by
          rw [← map_mul, Units.inv_mul_cancel_right]
        rw [hχ, hv', mul_smul_comm] at h1
        have h2 := congrArg (fun t => ((χ g)⁻¹).val • t) h1
        simp only [smul_smul, Units.inv_mul, one_smul] at h2
        exact (Units.eq_mul_inv_iff_mul_eq u).2 h2)
    refine ⟨⟨w, hw⟩, ?_⟩
    show pl L q hq w * u.val = v
    rw [e, Units.inv_mul_cancel_right]

end Descent

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

theorem secM_equiv {L : LB A.left} (hL : L.IsLB) (a : ℤ) :
    Nonempty (SecM A L a T ≃ₗ[Γ(T.left, ⊤)] Sg L (fst T A).left (Finsupp.single (snd T A).left a)) := by
  let f : SecM A L a T →ₗ[Γ(T.left, ⊤)] Vals L (fst T A).left :=
    { toFun := fun s => ev (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) _ (SecM.toSec A s)
      map_add' := fun s t => ev_add fun _ => rfl
      map_smul' := fun c s => ev_smul c fun _ => rfl }
  have hf : Function.Injective f := fun s t h => Subtype.ext (funext (ev_inj hL h))
  have hr : LinearMap.range f = Sg L (fst T A).left (Finsupp.single (snd T A).left a) := by
    ext v
    rw [mem_Sg hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (Fin.sum_univ_one _)]
    exact ⟨fun ⟨s, hs⟩ => ⟨SecM.toSec A s, hs⟩, fun ⟨s, hs⟩ => ⟨SecM.ofSec A s, hs⟩⟩
  exact ⟨(LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)⟩

theorem translPt_eq (x : T ⟶ A) : translPt A x = (fst T A ≫ x) * snd T A := rfl

theorem translT_fst' (x : T ⟶ A) : translT A x ≫ fst T A = fst T A := lift_fst _ _

theorem translT_snd' (x : T ⟶ A) : translT A x ≫ snd T A = translPt A x := lift_snd _ _

theorem mulT_fst (n : ℕ) : mulT A T n ≫ fst T A = fst T A := lift_fst _ _

theorem mulT_snd (n : ℕ) : mulT A T n ≫ snd T A = snd T A ^ n := lift_snd _ _

theorem translT_translPt (x y : T ⟶ A) : translT A x ≫ translPt A y = translPt A (y * x) := by
  rw [translPt_eq y, MonObj.comp_mul, ← Category.assoc, translT_fst', translT_snd', translPt_eq, translPt_eq,
    MonObj.comp_mul, _root_.mul_assoc]

theorem translT_translT (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, translT_fst', translT_fst', translT_fst']
  · rw [Category.assoc, translT_snd', translT_snd', translT_translPt]

theorem translPt_one : translPt A (1 : T ⟶ A) = snd T A := by
  rw [translPt_eq, MonObj.comp_one, _root_.one_mul]

theorem translT_one : translT A (1 : T ⟶ A) = 𝟙 _ := by
  rw [translT, translPt_one, lift_fst_snd]

theorem translT_mulT [IsCommMonObj A] (x : T ⟶ A) (n : ℕ) :
    translT A x ≫ mulT A T n = mulT A T n ≫ translT A (x ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, translT_fst', mulT_fst, translT_fst']
  · rw [Category.assoc, Category.assoc, translT_snd', mulT_snd, MonObj.comp_pow, translT_snd', translPt_eq,
      translPt_eq, MonObj.comp_mul, ← Category.assoc, mulT_fst, mulT_snd, MonObj.comp_pow, mul_pow]

theorem descends_mulT [IsCommMonObj A] (n : ℕ)
    (H : ∀ (U : A.left.Opens) (f : Γ(A.left, (mulA A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over S) ⟶ A, y ^ n = 1 →
      ∀ (e : (mulA A n).left ⁻¹ᵁ U ≤ ((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ ((mulA A n).left ⁻¹ᵁ U)),
        (((toUnit A ≫ y) * 𝟙 A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(A.left, U), ((mulA A n).left.app U).hom g = f) :
    Descends (mulT A (baseOver S) n).left
      (fun y : {y : baseOver S ⟶ A // y ^ n = 1} => (translT A y.1).left) := by
  let t : A ⟶ baseOver S := Over.homMk A.hom (Category.comp_id _)
  have inv : ∀ {T' : Over S} (t' : A ⟶ T') (y : T' ⟶ A), y ^ n = 1 →
      ((t' ≫ y) * 𝟙 A).left ≫ (mulA A n).left = (mulA A n).left := fun t' y hy => by
    rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy, MonObj.comp_one,
      _root_.one_mul]
  have H' : Descends (mulA A n).left
      (fun y : {y : baseOver S ⟶ A // y ^ n = 1} => ((t ≫ y.1) * 𝟙 A).left) := by
    refine ⟨fun U a b hab => ?_, fun U f hf => ?_⟩
    · refine (H U _ fun y hy e => fn_ext fun z hz => ?_).unique hab rfl
      refine (gs_appLE _ _ _ e (𝟙 _) z hz _).trans ((gs_pull (𝟙 _ ≫ ((toUnit A ≫ y) * 𝟙 A).left) _ z U (e hz) b).trans
        (Eq.trans ?_ (gs_pull (𝟙 _) _ z U hz b).symm))
      rw [Category.assoc, inv _ y hy]
    · refine (H U f fun y hy e => fn_ext fun z hz => ?_).exists
      refine (gs_appLE _ _ _ e (𝟙 _) z hz _).trans (Eq.trans ?_ (hf ⟨toUnit _ ≫ y, by
        rw [← MonObj.comp_pow, hy, MonObj.comp_one]⟩ z hz))
      show _ = gs ((t ≫ toUnit _ ≫ y) * 𝟙 A).left z _ f
      rw [Category.id_comp, ← Category.assoc, comp_toUnit]
  let e : baseOver S ⊗ A ≅ A := ⟨snd _ _, lift t (𝟙 A), by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · simp, lift_snd _ _⟩
  refine H'.of_iso (fun y => inv t y.1 y.2) ((Over.forget S).mapIso e) ?_ fun y => ?_
  · refine congrArg (fun r => r.left)
      (show lift t (𝟙 A) ≫ mulT A (baseOver S) n = mulA A n ≫ lift t (𝟙 A) from ?_)
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · rw [Category.assoc, Category.assoc, mulT_snd, MonObj.comp_pow, lift_snd, Category.comp_id]
  · refine congrArg (fun r => r.left)
      (show lift t (𝟙 A) ≫ translT A y.1 = ((t ≫ y.1) * 𝟙 A) ≫ lift t (𝟙 A) from ?_)
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · rw [Category.assoc, Category.assoc, translT_snd', translPt_eq, MonObj.comp_mul, lift_snd, Category.comp_id,
        lift_fst_assoc]

end Group

section Weights

variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B}

theorem pl_inv {h : Y ⟶ Y} (hh : h ≫ p = p) {u : (Vals L p)ˣ} {c : Γ(B, ⊤)ˣ}
    (e : pl L h hh u.val = c.val • u.val) : pl L h hh (u⁻¹).val = (c⁻¹).val • (u⁻¹).val := by
  have h1 : pl L h hh (u⁻¹).val * pl L h hh u.val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  rw [e, mul_smul_comm] at h1
  have h2 := congrArg (fun t => (c⁻¹).val • (t * (u⁻¹).val)) h1
  simpa only [smul_mul_assoc, smul_smul, Units.inv_mul, one_smul, Units.mul_inv_cancel_right,
    _root_.one_mul] using h2

end Weights

end GlobalTheory.MulSplit

namespace GlobalTheory

open MulSplit in

theorem sections_mulPull_split :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 → ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤ ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)), (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε)))) → CharPairSt → WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left, (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) := by
  intro hmul hfin hgal hchi hchar _ _ htw K _ _ P n j hn hj
  haveI := P.isAb.comm
  haveI : NeZero (n : K) := ⟨hn⟩
  haveI : NeZero n := .of_neZero_natCast K
  haveI := (hfin _ P n NeZero.one_le).1
  haveI hF := finite_torsion_of_isFinite_mul K P n
  haveI := hasEnoughRootsOfUnity_globalSections K n hn
  let eK : K ≃+* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  haveI : IsDomain Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) := eK.symm.toMulEquiv.isDomain K
  have hnu : IsUnit (n : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)) := by
    simpa using (Ne.isUnit hn).map eK
  have hL := P.isLB
  have hD := descends_mulT n (hgal K P n hn)
  have htw' := htw _ P K (𝟙 _)
  specialize hchi K P n
  specialize hchar K P n hn
  obtain ⟨α, hα⟩ := hmul _ P n
  change ∀ q : ℕ, 1 ≤ q → ∀ c : baseOver (Spec (CommRingCat.of K)) ⟶ P.A,
    ∃ d : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3)
      ![(snd (baseOver (Spec (CommRingCat.of K))) P.A).left, (translPt P.A c).left, (translPt P.A d).left]
      ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen at htw'
  clear hmul hfin hgal htw
  set T := baseOver (Spec (CommRingCat.of K))
  let G : Subgroup (T ⟶ P.A) := (powMonoidHom n).ker
  haveI : Finite G := hF
  have hτ : ∀ x : T ⟶ P.A, (translT P.A x).left ≫ (fst T P.A).left = (fst T P.A).left :=
    CommPairing.translT_fst
  have hττ : ∀ x y : T ⟶ P.A, (translT P.A x).left ≫ (translT P.A y).left = (translT P.A (y * x)).left :=
    fun x y => by rw [← Over.comp_left, translT_translT]
  have hτ1 : (translT P.A (1 : T ⟶ P.A)).left = 𝟙 _ := by rw [translT_one]; rfl
  have hq : (mulT P.A T n).left ≫ (fst T P.A).left = (fst T P.A).left := by
    rw [← Over.comp_left, mulT_fst]
  have hqs : (mulT P.A T n).left ≫ (snd T P.A).left = (snd T P.A ^ n).left := by
    rw [← Over.comp_left, mulT_snd]
  have hτq : ∀ y : {y : T ⟶ P.A // y ^ n = 1},
      (translT P.A y.1).left ≫ (mulT P.A T n).left = (mulT P.A T n).left := fun y => by
    rw [← Over.comp_left, translT_mulT, y.2, translT_one, Category.comp_id]
  let ρ : Representation Γ(T.left, ⊤) G (Vals P.L (fst T P.A).left) :=
    { toFun := fun y => (pl P.L (translT P.A y.1).left (hτ _)).toLinearMap
      map_one' := LinearMap.ext fun v => pl_id (hτ _) hτ1 v
      map_mul' := fun x y => LinearMap.ext fun v =>
        (pl_pl (hτ _) (hτ _) (hτ _) ((hττ x.1 y.1).trans (by rw [_root_.mul_comm]; rfl)) v).symm }

  have hgen : ∀ χ : G →* Γ(T.left, ⊤)ˣ, ∃ (c : T ⟶ P.A) (u : (Vals P.L (fst T P.A).left)ˣ),
      IsG (Finsupp.single (snd T P.A ^ n).left 1 +
        Finsupp.single ((mulT P.A T n).left ≫ (translPt P.A c).left) (-1)) u ∧
      ∀ y : G, pl P.L (translT P.A y.1).left (hτ _) u.val = (χ y).val • u.val := by
    intro χ
    obtain ⟨b, ⟨hb, hbχ⟩, -⟩ := hchar (fun x => χ ⟨x.1, x.2⟩) (fun x y => χ.map_mul ⟨x.1, x.2⟩ ⟨y.1, y.2⟩)
    obtain ⟨t, ε, ht, hε, hc⟩ := hchi b hb
    obtain ⟨u, hu, hv⟩ := exists_isG (p := (fst T P.A).left) hL t ht
    have hu' : IsG (Finsupp.single ((mulT P.A T n).left ≫ (translPt P.A b).left) 1 +
        Finsupp.single (snd T P.A ^ n).left (-1)) u := by
      rw [dv, Fin.sum_univ_two] at hu; exact hu
    have hw : ∀ y : G, pl P.L (translT P.A y.1).left (hτ _) u.val = ((χ y)⁻¹ ^ ε).val • u.val := by
      intro y
      funext i
      have h1 := val_corr i.2.1 (hc y.1 _ y.2 (CommPairing.weilIs_symm hL (hbχ ⟨y.1, y.2⟩))) i.1.2.2
      rw [val_pull i.2.1, val_mul i.2.1, H1.val_constGen, i.2.2] at h1
      rw [Algebra.smul_def, mul_vals, algebraMap_vals, hv, _root_.mul_comm, gs_unit _ _ ⊤ trivial]
      exact (hv _).trans (congrArg Units.val h1)
    rcases hε with rfl | rfl
    · refine ⟨b, u⁻¹, ?_, fun y => ?_⟩
      · convert hu'.inv using 1
        rw [neg_add, ← Finsupp.single_neg, ← Finsupp.single_neg, neg_neg, add_comm]
      · simpa using pl_inv _ (hw y)
    · obtain ⟨x, hx, -⟩ := htw' n NeZero.one_le b⁻¹
      refine ⟨b⁻¹, Units.map (pl P.L (translT P.A x).left (hτ _) : Vals _ _ →* Vals _ _) u, ?_, fun y => ?_⟩
      · convert hu'.pull hL (hτ x) using 1
        rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← hqs]
        simp only [← Over.comp_left]
        rw [← Category.assoc, ← Category.assoc, translT_mulT, Category.assoc, Category.assoc, translT_translPt,
          translT_snd', hx, mul_inv_cancel, translPt_one]
      · show pl P.L _ (hτ _) (pl P.L _ (hτ x) u.val) = (χ y).val • pl P.L _ (hτ x) u.val
        rw [pl_pl _ _ (hτ _) (hττ _ _), _root_.mul_comm x, ← pl_pl (hτ _) (hτ _) (hτ _) (hττ _ _), hw, map_smul]
        simp

  obtain ⟨e₁⟩ := nonempty_equiv_pi_of_weights (N := Sg P.L (fst T P.A).left (Finsupp.single (snd T P.A).left (j : ℤ)))
    n hnu (fun g : G => Subtype.ext g.2) ρ (Sg P.L (fst T P.A).left (Finsupp.single (snd T P.A ^ n).left (j : ℤ)))
    (fun g v hv => pl_mem_Sg hL (hτ _) hv (by
      rw [Finsupp.mapDomain_single, ← hqs, ← Category.assoc, hτq ⟨g.1, g.2⟩])) (fun χ => by
      obtain ⟨c, u, hu, hw⟩ := hgen χ
      obtain ⟨d, -, w, hw'⟩ := htw' j hj c
      obtain ⟨w', hw'', -⟩ := exists_isG (p := (fst T P.A).left) hL w hw'
      obtain ⟨f, hf, hf'⟩ := hD.weight hL hq (fun y => hτ _) hτq
        (D := Finsupp.single (snd T P.A).left ((j : ℤ) - 1) + Finsupp.single (translPt P.A c).left 1)
        (F := Finsupp.single (snd T P.A ^ n).left (j : ℤ)) hu (fun y => χ ⟨y.1, y.2⟩) (fun y => hw ⟨y.1, y.2⟩) (by
          rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hqs,
            Finsupp.single_sub, Finsupp.single_neg]
          abel)
      obtain ⟨a₁⟩ := pl_equiv hL (hτ d) (hτ d⁻¹) ((hττ _ _).trans (by rw [inv_mul_cancel, hτ1]))
        ((hττ _ _).trans (by rw [mul_inv_cancel, hτ1])) (D := Finsupp.single (snd T P.A).left (j : ℤ))
        (E := Finsupp.single (translPt P.A d).left (j : ℤ)) (by
          rw [Finsupp.mapDomain_single, ← Over.comp_left, translT_snd'])
      obtain ⟨a₂⟩ := hw''.equiv hL (E := Finsupp.single (translPt P.A d).left (j : ℤ))
        (F := Finsupp.single (snd T P.A).left ((j : ℤ) - 1) + Finsupp.single (translPt P.A c).left 1) (by
          rw [dv, Fin.sum_univ_three]
          show _ + (Finsupp.single (snd T P.A).left ((j : ℤ) - 1) + Finsupp.single (translPt P.A c).left 1 +
            Finsupp.single (translPt P.A d).left (-(j : ℤ))) = _
          rw [Finsupp.single_neg]
          abel)
      refine ⟨f.comp (a₁.trans a₂).toLinearMap, hf.comp (a₁.trans a₂).injective, fun v => Iff.trans ?_ (hf' v)⟩
      exact ⟨fun ⟨x, hx⟩ => ⟨_, hx⟩, fun ⟨x, hx⟩ => ⟨(a₁.trans a₂).symm x, by
        rw [← hx]; exact congrArg f ((a₁.trans a₂).apply_symm_apply x)⟩⟩)

  obtain ⟨u, hu, -⟩ := exists_isG (p := (fst T P.A).left) hL _ (DVR.pullGen_isGen _ _ _ _ hα (snd T P.A).left)
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨e₂⟩ := (hu.pow hL j).equiv hL (E := Finsupp.single (snd T P.A ^ n).left ((j + 1 : ℕ) : ℤ))
    (F := Finsupp.single (snd T P.A).left ((n ^ 2 * (j + 1) : ℕ) : ℤ)) (by
      rw [dv, Fin.sum_univ_two]
      show _ + (j + 1) • (Finsupp.single ((snd T P.A).left ≫ 𝟙 _) ((n : ℤ) ^ 2) +
        Finsupp.single (snd T P.A ≫ mulA P.A n).left (-1)) = _
      rw [mulA, MonObj.comp_pow, Category.comp_id, Category.comp_id, smul_add, Finsupp.smul_single,
        Finsupp.smul_single, add_left_comm, ← Finsupp.single_add]
      have e₁ : ((j + 1 : ℕ) : ℤ) + (j + 1) • (-1 : ℤ) = 0 := by simp
      have e₂ : (j + 1) • (n : ℤ) ^ 2 = ((n ^ 2 * (j + 1) : ℕ) : ℤ) := by simp; ring
      rw [e₁, e₂, Finsupp.single_zero, add_zero])
  obtain ⟨e₃⟩ := secM_equiv (T := T) hL ((n ^ 2 * (j + 1) : ℕ) : ℤ)
  obtain ⟨e₄⟩ := secM_equiv (T := T) hL ((j + 1 : ℕ) : ℤ)
  exact ⟨e₃.trans (e₂.symm.trans (e₁.trans (LinearEquiv.piCongrRight fun _ => e₄.symm)))⟩

end GlobalTheory
