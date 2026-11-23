import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionLimit

section Alg

variable {R : Type} [CommRing R] (I : Ideal R)

theorem exists_lim [IsPrecomplete I R] (c : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1)) = c e) :
    ∃ a : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) a = c e := by
  choose x hx using fun e => Ideal.Quotient.mk_surjective (c e)
  have h1 : ∀ e, x e - x (e + 1) ∈ I ^ (e + 1) := fun e => by
    rw [← Ideal.Quotient.eq, hx, ← hc e, ← hx, Ideal.Quotient.factor_mk]
  have h2 : ∀ m n, m ≤ n → x m - x n ∈ I ^ m := fun m n h => by
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := (I ^ m).add_mem ih (Ideal.pow_le_pow_right (hmn.trans (Nat.le_succ n)) (h1 n))
      simpa using this
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := x) (fun {m n} h => by
    rw [SModEq.sub_mem]; simpa using h2 m n h)
  refine ⟨a, fun e => ?_⟩
  have h3 : x (e + 1) - a ∈ I ^ (e + 1) := by
    have := ha (e + 1)
    rw [SModEq.sub_mem] at this
    simpa using this
  rw [← hx, eq_comm, Ideal.Quotient.eq]
  simpa using (I ^ (e + 1)).add_mem (h1 e) h3

theorem eq_of_mk_eq [IsHausdorff I R] {a b : R}
    (h : ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) a = Ideal.Quotient.mk (I ^ (e + 1)) b) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) (M := R) inferInstance _ fun n => ?_
  rw [SModEq.zero]
  simpa using Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))

end Alg

section Calc

variable {X Y Y' : Scheme.{0}} {L : LB X}

theorem exists_pull {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      (∀ j (le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j),
        s'.f j = (Y'.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨pullSec L φ ε s h, fun _ _ => rfl, fun Z r z J hJ => SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

def linSec {M : LB Y} {N : ℕ} (c : Fin N → Γ(Y, ⊤)) (t : Fin N → LB.Sec M) : LB.Sec M where
  f j := ∑ i, resTop _ (c i) * (t i).f j
  compat i j := by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (SecOps.secScale (c k) (t k)).compat i j

variable {C : Type} [CommRing C] {n N : ℕ}

def Rep (π : Y ⟶ X) (f : Y ⟶ Sp C) (β : Fin N → H0 L n)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (n : ℤ)))) (c : Fin N → C) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
    sval s r z J = ∑ i, cst (r ≫ f) z (c i) * sval (β i) (r ≫ π) z J

theorem rep_transport {π : Y ⟶ X} {f : Y ⟶ Sp C} {β : Fin N → H0 L n} (e : Y' ≅ Y)
    {π' : Y' ⟶ X} {f' : Y' ⟶ Sp C} (hπ : e.hom ≫ π = π') (hf : e.hom ≫ f = f')
    (H : ∀ s, ∃! c, Rep π f β s c) : ∀ s, ∃! c, Rep π' f' β s c := by
  subst hπ hf
  intro s'
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (fun _ : Fin 1 => π) (fun _ => e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ π) (e.hom ≫ f) β s' c ↔ Rep π f β s c := fun c => by
    constructor
    · intro h Z r z J hJ
      rw [hs Z r z J hJ, h Z _ z J hJ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · intro h Z r z J hJ
      have := h Z (r ≫ e.hom) z J hJ
      rw [hs Z _ z J hJ] at this
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  simp only [key]
  exact H s

theorem sval_linSec {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (f : Y ⟶ Sp C) (c : Fin N → C)
    (t : Fin N → LB.Sec (LB.LinComb L φ ε)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    sval (linSec (fun i => scal f (c i)) t) r z J = ∑ i, cst (r ≫ f) z (c i) * sval (t i) r z J := by
  rw [SectionScalarValuation.sval_lin (s := linSec (fun i => scal f (c i)) t) (fun i => scal f (c i)) t (fun _ => rfl) r z hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r f z ⊤ trivial _)

end Calc

theorem exists_basis (hS : SecBaseChangeSt) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (N : ℕ) (β : Fin N → H0 P.L n), ∀ (C : Type) [CommRing C] (q : Sp C ⟶ Sp R) (Y : Scheme.{0})
      (π : Y ⟶ P.A.left) (f : Y ⟶ Sp C), IsPullback f π q P.A.hom → ∀ s, ∃! c, Rep π f β s c := by
  have hL := P.isLB
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) P n hn (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let V := overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤
  let t₀ : Spec (CommRingCat.of R) ⟶ V.left := (Spec (CommRingCat.of R)).topIso.inv
  have ht : t₀ ≫ V.hom = 𝟙 _ := by
    show (Spec (CommRingCat.of R)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.inv_hom_id
  have ht' : V.hom ≫ t₀ = 𝟙 _ := by
    show (Scheme.Opens.ι ⊤ ≫ 𝟙 _) ≫ (Spec (CommRingCat.of R)).topIso.inv = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.hom_inv_id
  let u : P.A ⟶ V := Over.homMk (P.A.hom ≫ t₀) (by rw [Category.assoc, ht, Category.comp_id])
  have hu : snd V P.A ≫ u = fst V P.A := Over.OverMorphism.ext (by
    show (snd V P.A).left ≫ P.A.hom ≫ t₀ = (fst V P.A).left
    rw [← Category.assoc, Over.w (snd V P.A), ← Over.w (fst V P.A), Category.assoc, ht', Category.comp_id])
  have e₁ : lift u (𝟙 P.A) ≫ snd V P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd V P.A ≫ lift u (𝟙 P.A) = 𝟙 _ := by
    rw [comp_lift, hu, Category.comp_id, lift_fst_snd]
  choose β hβ0 hβ using fun i => exists_pull (K := Fin 1) (b i) (lift u (𝟙 P.A)).left (fun _ => 𝟙 P.A.left)
    (fun _ => congrArg CommaMorphism.left e₁)
  refine ⟨_, β, fun C _ q Y π f hp => ?_⟩
  let t : Spec (CommRingCat.of C) ⟶ V.left := q ≫ t₀
  have hq : (baseAt t).hom = q := by
    show (q ≫ t₀) ≫ V.hom = q
    rw [Category.assoc, ht, Category.comp_id]
  choose b' hb0 hb' using fun i => exists_pull (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
  obtain ⟨hli, hsp⟩ := hb C t b' (fun i j => hb0 i j _)
  have e₃ : snd (baseAt t) P.A ≫ lift u (𝟙 P.A) = homAt t ▷ P.A := by
    rw [← whiskerRight_snd (homAt t) P.A, Category.assoc, e₂, Category.comp_id]
  have e₄ : (snd (baseAt t) P.A).left ≫ (lift u (𝟙 P.A)).left = (homAt t ▷ P.A).left :=
    congrArg CommaMorphism.left e₃
  have hp' : IsPullback f π (baseAt t).hom P.A.hom := hq ▸ hp
  refine rep_transport (Y := (baseAt t ⊗ P.A).left) (π := (snd (baseAt t) P.A).left)
    (f := (fst (baseAt t) P.A).left) hp'.isoPullback hp'.isoPullback_hom_snd hp'.isoPullback_hom_fst fun s => ?_
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  have hv : ∀ (c : Fin (n ^ P.g) → C) (Z : Scheme.{0}) (r : Z ⟶ (baseAt t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      sval (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b') r z J =
        ∑ i, cst (r ≫ (fst (baseAt t) P.A).left) z (c i) * sval (β i) (r ≫ (snd (baseAt t) P.A).left) z J :=
    fun c Z r z J hJ => by
      rw [sval_linSec _ _ _ _ _ hJ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb' i Z r z J hJ, hβ i Z _ z J hJ, Category.assoc, e₄]
  have key : ∀ c : Fin (n ^ P.g) → C, Rep (snd (baseAt t) P.A).left (fst (baseAt t) P.A).left β s c ↔
      ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) •
        (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
    have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) •
        (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
        (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b').f j := fun j => by
      rw [Submodule.coe_sum, Finset.sum_apply]
      rfl
    constructor
    · intro h
      refine Subtype.ext (funext fun j => (ev j).trans ?_)
      exact sec_ext_val hL (fun y J hJ => (hv c _ _ y J hJ).trans (h _ _ y J hJ).symm) j
    · intro h Z r z J hJ
      have : s = linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b' :=
        SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)
      rw [this]
      exact hv c Z r z J hJ
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
  choose a ha using fun i => bij.2 (r i)
  obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (a i)) = r := funext ha
  refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i

theorem existsUnique_sec_of_compatible : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Geo.Tor.Good P.L z J → Geo.Tor.sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = Geo.Tor.sval (s e) r z J) → ∃! σ : H0 P.L n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Geo.Tor.Good P.L z J → Geo.Tor.sval σ (r ≫ (fstG I e P.A).left) z J = Geo.Tor.sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hL := P.isLB
  obtain ⟨N, β, hβ⟩ := exists_basis hS R P n hn
  have hpe : ∀ e, IsPullback (thickObj R I e P.A).hom (fstG I e P.A).left (thick R I e) P.A.hom :=
    fun e => (IsPullback.of_hasPullback P.A.hom (thick R I e)).flip
  choose c hc hcu using fun e => hβ _ _ _ _ _ (hpe e) (s e)
  have hcomp : ∀ e i, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1) i) = c e i :=
    fun e => congrFun (hcu e (fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (c (e + 1) i)) fun Z r z J hJ => by
        have h₁ : thickMap R I e P.A ≫ (thickObj R I (e + 1) P.A).hom =
            (thickObj R I e P.A).hom ≫ thickTrans R I e := pullback.lift_snd _ _ _
        have h₂ : thickMap R I e P.A ≫ (fstG I (e + 1) P.A).left = (fstG I e P.A).left :=
          (pullback.lift_fst _ _ _).trans (Category.comp_id _)
        rw [← hs e Z r z J hJ, hc (e + 1) Z _ z J hJ, Category.assoc, Category.assoc, h₁, h₂, ← Category.assoc]
        exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _))
  choose a ha using fun i => exists_lim I (fun e => c e i) (fun e => hcomp e i)
  have down : ∀ (σ : H0 P.L n) (a : Fin N → R), Rep (𝟙 _) P.A.hom β σ a → ∀ (e : ℕ) (Z : Scheme.{0})
      (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      sval σ (r ≫ (fstG I e P.A).left) z J = ∑ i, cst (r ≫ (thickObj R I e P.A).hom) z
        (Ideal.Quotient.mk (I ^ (e + 1)) (a i)) * sval (β i) (r ≫ (fstG I e P.A).left) z J :=
    fun σ a h e Z r z J hJ => by
      rw [h Z _ z J hJ, Category.comp_id, Category.assoc, ← (hpe e).w, ← Category.assoc]
      exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _)
  have hlin : Rep (𝟙 _) P.A.hom β (linSec (fun i => scal P.A.hom (a i)) β) a := fun Z r z J hJ => by
    rw [sval_linSec _ _ _ _ _ hJ, Category.comp_id]
  refine ⟨linSec (fun i => scal P.A.hom (a i)) β, fun e Z r z J hJ => ?_, fun σ hσ => ?_⟩
  · rw [down _ a hlin e Z r z J hJ, hc e Z r z J hJ]
    simp only [ha]
  · obtain ⟨a', ha', -⟩ := hβ R (𝟙 _) _ (𝟙 _) P.A.hom (IsPullback.of_vert_isIso ⟨by simp⟩) σ
    have : a' = a := funext fun i => eq_of_mk_eq I fun e => by
      rw [ha]
      exact congrFun (hcu e (fun i => Ideal.Quotient.mk (I ^ (e + 1)) (a' i)) fun Z r z J hJ =>
        (hσ e Z r z J hJ).symm.trans (down σ a' ha' e Z r z J hJ)) i
    subst this
    exact SecOps.sec_ext (sec_ext_val hL fun y J hJ => (ha' _ _ y J hJ).trans (hlin _ _ y J hJ).symm)

end GlobalTheory.SectionLimit
