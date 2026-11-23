import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtNatural

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftUnits

theorem le_pre_inf {X Y : Scheme.{0}} {y : Y ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ y ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := fun _ hp => ⟨hU hp, hV hp⟩

theorem le_pre_of_eq {X Y Z : Scheme.{0}} {f : Z ⟶ Y} {y : Y ⟶ X} {z : Z ⟶ X} (e : f ≫ y = z) {U : X.Opens}
    (hU : ⊤ ≤ y ⁻¹ᵁ U) : ⊤ ≤ z ⁻¹ᵁ U := by
  subst e
  intro p _
  exact hU (Set.mem_univ (f p))

theorem map_evalAt {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') {x : Sp C ⟶ X}
    {y : Sp C' ⟶ X} (e : spMap φ ≫ x = y) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) :
    φ (evalAt x U h f) = evalAt y U h' f := by
  subst e
  obtain ⟨_, hn, -⟩ := GlobalTheory.EvalNat.evalAt_natural φ x U h
  exact (hn f).symm

theorem evalAt_g_mul {X : Scheme.{0}} {C : Type} [CommRing C] {M : LB X} (hM : M.IsLB) (y : Sp C ⟶ X) {a b c : M.ι}
    (ha : ⊤ ≤ y ⁻¹ᵁ M.U a) (hb : ⊤ ≤ y ⁻¹ᵁ M.U b) (hc : ⊤ ≤ y ⁻¹ᵁ M.U c) :
    evalAt y _ (le_pre_inf ha hb) (M.g a b).val * evalAt y _ (le_pre_inf hb hc) (M.g b c).val =
      evalAt y _ (le_pre_inf ha hc) (M.g a c).val := by
  have hres : ∀ {U V : X.Opens} (h : V ≤ U) (u : (Γ(X, U))ˣ),
      ((res h u : (Γ(X, V))ˣ) : Γ(X, V)) = (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := fun _ _ => rfl
  have q2 := congrArg (fun u => evalAt y (M.U a ⊓ M.U b ⊓ M.U c) (le_pre_inf (le_pre_inf ha hb) hc) (Units.val u))
    (hM.cocycle a b c)
  simp only [Units.val_mul, map_mul, hres] at q2
  obtain ⟨_, -, hr⟩ := GlobalTheory.EvalNat.evalAt_natural (RingHom.id C) y (M.U a ⊓ M.U b ⊓ M.U c) (le_pre_inf (le_pre_inf ha hb) hc)
  rw [hr (M.U a ⊓ M.U b) (le_trans inf_le_left le_rfl) (le_pre_inf ha hb),
    hr (M.U b ⊓ M.U c) (le_inf (le_trans inf_le_left inf_le_right) inf_le_right) (le_pre_inf hb hc),
    hr (M.U a ⊓ M.U c) (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) (le_pre_inf ha hc)]
  exact q2

theorem isUnit_evalAt {X : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ y ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) : IsUnit (evalAt y U h u.val) := u.isUnit.map (evalAt y U h)

theorem mul_eq_one_of_covolume_identity {R : Type} [CommRing R] {g₁ g₂ g₃ g₄ g₅ u v w A S f : R} (c₁ : g₁ * g₂ = g₅) (c₂ : g₃ * g₄ = g₅)
    (hu : u = g₁) (hv : v = g₂ * S) (hw : w = g₃ * f) (hf : f = g₄ * A * S) : u * v * A = w := by
  subst hu hv hw hf
  linear_combination (S * A) * c₁ - (S * A) * c₂

theorem exists_units : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) := by
  intro I _ g Λ _ F B _ X s σ K r M hM j hj fr a hfr hcoc i hi uu huu
  have hjT : ∀ T : K.Obj, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (j T.k) := fun T =>
    le_pre_of_eq (f := spMap ((Ideal.Quotient.mk T.J).comp T.ρ)) (y := r.x T.k) rfl (hj T.k)
  have hlift : ∀ T : K.Obj, ∃ c : T.C, IsUnit c ∧ Ideal.Quotient.mk T.J c =
      @id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T.J (T.ρ (fr T.k)) := by
    intro T
    have hu : IsUnit (@id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T.J (T.ρ (fr T.k))) :=
      (isUnit_evalAt (r.obj T).x (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k))).mul
        (((hfr T.k).map T.ρ).map (Ideal.Quotient.mk T.J))
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (@id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T))
      (M.g (i T) (j T.k)).val) * Ideal.Quotient.mk T.J (T.ρ (fr T.k)))
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (((hu.unit⁻¹ : (T.C ⧸ T.J)ˣ)) : T.C ⧸ T.J)
    refine ⟨c, ?_, hc⟩
    have hmem : c * d - 1 ∈ T.J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, hd, map_one, IsUnit.mul_val_inv, sub_self]
    have hnil : IsNilpotent (c * d - 1) := by
      obtain ⟨n, hn⟩ := T.nil
      refine ⟨n, ?_⟩
      have hp := Ideal.pow_mem_pow hmem n
      rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
    have hcd : IsUnit (c * d) := by
      have h1 := hnil.isUnit_one_add
      rwa [add_sub_cancel] at h1
    exact isUnit_of_mul_isUnit_left hcd
  choose c hcu hcε using hlift
  refine ⟨fun T => (hcu T).unit, ?_⟩
  intro T T' φ
  have hle : K.le φ.deg T'.k T.k := Charts.Hom.le φ
  have hiT : ⊤ ≤ (r.obj T').x ⁻¹ᵁ M.U (i T) :=
    le_pre_of_eq (f := spMap (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem)) (y := (r.obj T).x) (r.analyticChartsRealization_comp_point_eq φ) (hi T)
  have hjk : ⊤ ≤ (r.obj T').x ⁻¹ᵁ M.U (j T.k) :=
    le_pre_of_eq (f := spMap (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem)) (y := (r.obj T).x) (r.analyticChartsRealization_comp_point_eq φ) (hjT T)
  have hxk : ⊤ ≤ r.x T'.k ⁻¹ᵁ (M.U (j T'.k) ⊓ M.U (j T.k)) :=
    le_pre_inf (hj T'.k) (le_pre_of_eq (r.compat hle) (hj T.k))
  have c₁ := evalAt_g_mul hM (r.obj T').x (hi T') hiT hjk
  have c₂ := evalAt_g_mul hM (r.obj T').x (hi T') (hjT T') hjk
  have hu := huu T T' φ (le_pre_inf (hi T') hiT)
  have hS : Ideal.Quotient.mk T'.J (φ.φ (T.ρ (fr T.k))) =
      Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) :=
    Ideal.Quotient.eq.mpr (Close.sub_mem φ.close (fr T.k))
  have hv : Ideal.Quotient.mk T'.J (φ.φ (c T)) =
      @id (T'.C ⧸ T'.J) (evalAt (r.obj T').x _ (le_pre_inf hiT hjk) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) := by
    have h1 : Ideal.Quotient.mk T'.J (φ.φ (c T)) =
        Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem (Ideal.Quotient.mk T.J (c T)) := by
      rfl
    have h2 : Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem (Ideal.Quotient.mk T.J (T.ρ (fr T.k))) =
        Ideal.Quotient.mk T'.J (φ.φ (T.ρ (fr T.k))) := by
      rfl
    rw [h1, hcε T, map_mul, h2, hS]
    congr 1
    exact map_evalAt (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem) (x := (r.obj T).x) (y := (r.obj T').x)
      (r.analyticChartsRealization_comp_point_eq φ) _ (le_pre_inf hiT hjk) _
  have hf : Ideal.Quotient.mk T'.J (T'.ρ (fr T'.k)) =
      @id (T'.C ⧸ T'.J) (evalAt (r.obj T').x _ (le_pre_inf (hjT T') hjk) (M.g (j T'.k) (j T.k)).val) *
        Ideal.Quotient.mk T'.J (T'.ρ (a φ.deg T'.k)) * Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) := by
    rw [hcoc φ.deg T'.k T.k hle hxk, map_mul, map_mul, map_mul, map_mul]
    congr 2
    exact map_evalAt ((Ideal.Quotient.mk T'.J).comp T'.ρ) (x := r.x T'.k) (y := (r.obj T').x) rfl _ _ _
  refine Ideal.Quotient.eq.mp ?_
  rw [map_mul, map_mul]
  exact mul_eq_one_of_covolume_identity (R := T'.C ⧸ T'.J) c₁ c₂ hu hv (hcε T') hf

end GlobalTheory.LiftUnits
