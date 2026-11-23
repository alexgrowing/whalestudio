import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FlatGenDescent

variable {X X' : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

theorem exists_mul {M : LB X} (hM : M.IsLB) (u : LB.Sec M) (v : LB.Sec (AbLaw.pw M (-1))) :
    ∃ a : Γ(X, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : M.ι), r z ∈ M.U k →
      gs r z ⊤ a = gs r z (M.U k) (u.f k) * gs r z (M.U k) (v.f k) := by
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' M.U ⊤ (fun k => homOfLE le_top) hM.cover.ge
    (fun k => (show Γ(X, M.U k) from u.f k) * (show Γ(X, M.U k) from v.f k))
    (fun k l => fn_ext (V := M.U k ⊓ M.U l) fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      refine (gs_mul (𝟙 X) y _ hy.1 _ _).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy.2 _ _).symm)
      have h₁ := FlatSec.gs_sec_trans u (𝟙 X) y hy.1 hy.2
      have h₂ : gs (𝟙 X) y (M.U k) (v.f k) = (gm (𝟙 X) y (M.U k ⊓ M.U l) (M.g k l ^ (-1 : ℤ))).val *
          gs (𝟙 X) y (M.U l) (v.f l) := FlatSec.gs_sec_trans v (𝟙 X) y (k := k) (l := l) hy.1 hy.2
      rw [h₁, h₂, map_zpow, zpow_neg_one, _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])
  refine ⟨a, fun Z r z k hk => ?_⟩
  exact (gs_res r z le_top hk a).symm.trans ((congrArg (gs r z (M.U k)) (ha k)).trans (gs_mul r z _ hk _ _))

def invSec (M : LB X) (π : X' ⟶ X) (t : LB.Gen (M.pull π)) (ht : t.IsGen) : LB.Sec ((AbLaw.pw M (-1)).pull π) :=
  genSec (M := (AbLaw.pw M (-1)).pull π) ⟨fun j => (t.s j)⁻¹⟩ fun i j => by
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    refine h.trans (congrArg₂ (· * ·) ?_ rfl)
    show (∏ _k : PUnit, (res _ (pullU π _ (M.g _ _))) ^ (1 : ℤ))⁻¹ =
      ∏ _k : PUnit, (res _ (pullU π _ (M.g _ _ ^ (-1 : ℤ)))) ^ (1 : ℤ)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, map_zpow, map_zpow, zpow_neg_one]

theorem exists_sec_of_flat {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Sp R) (π : X' ⟶ X) (f' : X' ⟶ Sp R') (H : IsPullback π f' f (spMap g))
    (M : LB X) (hM : M.IsLB) (t : LB.Gen (M.pull π)) (ht : t.IsGen) (m : Ideal Γ(X, ⊤)) (hm : m.IsMaximal) :
    ∃ u : LB.Sec M, ∀ z : X', (∀ a ∈ m, π z ∉ X.basicOpen a) → π z ∈ nonzeroLocus u := by
  classical
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H M hM (genSec t ht)
  obtain ⟨n', c', v, hv⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ (AbLaw.isLB_pw hM (-1))
    (invSec M π t ht)
  choose a ha using fun i j => exists_mul hM (u i) (v j)
  by_cases hne : ∃ i j, a i j ∉ m
  · obtain ⟨i, j, hij⟩ := hne
    refine ⟨u i, fun z hz => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    obtain ⟨y, x, hx, e⟩ := hm.exists_inv hij
    have e' := congrArg (gs π z ⊤) e
    rw [gs_add π z ⊤ trivial, gs_mul π z ⊤ trivial, gs_eq π z ⊤ trivial 1, map_one, map_one] at e'
    have hxu : ¬ IsUnit (gs π z ⊤ x) := fun h => hz x hx ((isUnit_gs_iff π z ⊤ trivial x).1 h)
    have hu1 : IsUnit (gs π z ⊤ y * gs π z ⊤ (a i j)) :=
      (IsLocalRing.isUnit_or_isUnit_of_add_one e').resolve_right hxu
    have hu2 := isUnit_of_mul_isUnit_right hu1
    rw [ha i j X' π z k hk] at hu2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff π z _ hk _).1 (isUnit_of_mul_isUnit_left hu2)⟩
  · push_neg at hne
    refine ⟨⟨fun _ => 0, fun _ _ => by simp⟩, fun z hz => False.elim ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    have hz' : z ∈ (M.pull π).U (fun _ => k) := mem_pull.2 hk
    have h₁ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hu z k hk)
    have h₂ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)⁻¹).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hv z k hk)
    have h₃ := congrArg₂ (· * ·) h₁ h₂
    rw [map_inv, Units.mul_inv, Finset.sum_mul_sum] at h₃
    apply (IsLocalRing.maximalIdeal.isMaximal (X'.presheaf.stalk z)).ne_top
    rw [Ideal.eq_top_iff_one, h₃]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    rw [_root_.mul_mul_mul_comm]
    refine Ideal.mul_mem_left _ _ ?_
    have h₄ : ¬ IsUnit (gs π z ⊤ (a i j)) := fun h => hz _ (hne i j) ((isUnit_gs_iff π z ⊤ trivial _).1 h)
    rw [ha i j X' π z k hk] at h₄
    exact h₄

theorem flat_of_basis {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R')
    (h : ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) : g.Flat := by
  let _ : Algebra R R' := g.toAlgebra
  have hb : Function.Bijective (Fintype.linearCombination R b) := by
    rw [Function.bijective_iff_existsUnique]
    intro r'
    refine (existsUnique_congr fun c => ?_).1 (h r')
    rw [Fintype.linearCombination_apply, eq_comm]
    rfl
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective _ hb).symm

theorem exists_sec_of_free : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R'), (∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) → ∀ (Z Z' : Scheme.{0}) (k' : Z' ⟶ Z) (f : Z ⟶ Sp R) (f' : Z' ⟶ Sp R'), IsPullback k' f' f (spMap g) → ∀ (O : Z.Opens), IsCompact (O : Set Z) → IsQuasiSeparated (O : Set Z) → ∀ (L : LB Z), L.IsLB → ∀ σ : LB.Gen ((L.pull k').pull (k' ⁻¹ᵁ O).ι), σ.IsGen → ∀ m : Ideal Γ(Z, O), m.IsMaximal → ∃ u : LB.Sec (L.pull O.ι), ∀ z : (k' ⁻¹ᵁ O).toScheme, (∀ a ∈ m, k' ((k' ⁻¹ᵁ O).ι z) ∉ Z.basicOpen a) → ∀ z₀ : O.toScheme, O.ι z₀ = k' ((k' ⁻¹ᵁ O).ι z) → z₀ ∈ nonzeroLocus u := by
  intro R R' _ _ g d b hb Z Z' k' f f' H O hO hO' L hL σ hσ m hm
  haveI : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hO
  haveI : QuasiSeparatedSpace O.toScheme := (isQuasiSeparated_iff_quasiSeparatedSpace _ O.isOpen).mp hO'
  have H' : IsPullback (k' ∣_ O) ((k' ⁻¹ᵁ O).ι ≫ f') (O.ι ≫ f) (spMap g) :=
    (isPullback_morphismRestrict k' O).paste_vert H
  obtain ⟨t₁, h₁⟩ := gen_chartPull (chartPullIn L (fun _ : PUnit => k') (fun _ => 1) (k' ⁻¹ᵁ O).ι) σ hσ
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullOut L (fun _ : PUnit => O.ι) (fun _ => 1) (k' ∣_ O) _
    fun _ => (morphismRestrict_ι k' O).symm) t₁ h₁
  let e : Γ(O.toScheme, ⊤) ≃+* Γ(Z, O) := O.topIso.commRingCatIsoToRingEquiv
  haveI := hm
  obtain ⟨u, hu⟩ := exists_sec_of_flat g (flat_of_basis g d b hb) (O.ι ≫ f) (k' ∣_ O) _ H' (L.pull O.ι)
    (LB.isLB_pull hL _) t ht (m.comap e) (Ideal.comap_isMaximal_of_surjective e e.surjective)
  refine ⟨u, fun z hz z₀ hz₀ => ?_⟩
  have hc : O.ι ((k' ∣_ O) z) = k' ((k' ⁻¹ᵁ O).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  obtain rfl : z₀ = (k' ∣_ O) z := O.ι.injective (hz₀.trans hc.symm)
  refine hu z fun a ha h => hz (e a) ha ?_
  rw [← hc]
  have := O.ι_image_basicOpen_topIso_inv (e a)
  rw [← this]
  exact ⟨_, (show _ ∈ O.toScheme.basicOpen (O.topIso.inv.hom (e a)) from (e.symm_apply_apply a).symm ▸ h), rfl⟩

end GlobalTheory.FlatGenDescent
