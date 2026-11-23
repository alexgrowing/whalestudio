import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount.LieZFil

theorem omega_sq {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) :
    D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
  rw [← D.tr_eq, ← D.nm_eq]; ring

theorem end_sq {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (h : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) (act (algebraMap (𝓞 D.F) D.O D.ω) h) =
      (D.tr : C) • act (algebraMap (𝓞 D.F) D.O D.ω) h - (D.nm : C) • h := by
  have e := congrArg (fun x => act (algebraMap (𝓞 D.F) D.O x) h) (omega_sq D)
  simp only [map_mul, map_sub, map_intCast, Module.End.mul_apply, LinearMap.sub_apply] at e
  rw [e]
  simp [Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

theorem rho_part_eig {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (ρ : C) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0) (y : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) -
      ρ • ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, end_sq]
  have hn : (D.nm : C) = ρ * (D.tr - ρ) := by linear_combination hρ
  rw [hn]
  module

theorem sum_mem_fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {C : Type} [CommRing C] [IsLocalRing C] (β : R →+* C)
    {s : Sp C ⟶ Sp R} (hs : s = spMap β) (o : GlobalTheory.UPel.HT.Obj b N s) {r : ℕ} (lam : Fin r → C)
    (c : Fin r → 𝓞 D.F) (hlam : ∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) (y : HdR o.A) :
    ∑ l, lam l • GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O (c l))
      ((GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O D.ω) -
        ((D.tr : C) - β b.ρ) • 1) y) ∈ Fil o.A := by
  set act := GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act with hact
  set u := (act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - β b.ρ) • 1) y with hu
  have hfil : ∀ (x : D.O) {h : HdR o.A}, h ∈ Fil o.A → act x h ∈ Fil o.A := fun x h hh => by
    haveI := o.act.hom x
    exact push_mem_Fil (o.act.act x) hh
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hω : act (algebraMap (𝓞 D.F) D.O D.ω) u - β b.ρ • u ∈ Fil o.A := by
    rw [hu, rho_part_eig act (β b.ρ) hρ y]; exact zero_mem _
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N C β s hs o u hω
  set c' := fun l => algebraMap (𝓞 D.F) D.O (c l)
  have h1 : ∀ l, act (c' l) u - ∑ i, act (c' l) (w i) ∈ Fil o.A := fun l => by
    rw [← map_sum, ← map_sub]; exact hfil _ hsum
  have h2 : ∀ i, ∑ l, lam l • act (c' l) (w i) ∈ Fil o.A := fun i => by
    have e : ∑ l, lam l • act (c' l) (w i) = ∑ l, lam l • (act (c' l) (w i) - β (b.t i (c l)) • w i) +
        (∑ l, lam l * β (b.t i (c l))) • w i := by
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_sub, mul_smul]; abel
    rw [e, hlam i, zero_smul, add_zero]
    exact sum_mem fun l _ => Submodule.smul_mem _ _ (hw i (c l))
  have e : ∑ l, lam l • act (c' l) u = ∑ l, lam l • (act (c' l) u - ∑ i, act (c' l) (w i)) +
      ∑ i, ∑ l, lam l • act (c' l) (w i) := by
    rw [Finset.sum_comm (f := fun i l => lam l • act (c' l) (w i)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.smul_sum, ← smul_add, sub_add_cancel]
  show ∑ l, lam l • act (c' l) u ∈ Fil o.A
  rw [e]
  exact add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (h1 l)) (sum_mem fun i _ => h2 i)

theorem dualNumber_local (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

end GlobalTheory.HTCount.LieZFil

namespace GlobalTheory.HTCount

open LieZFil in
set_option maxHeartbeats 800000 in

theorem lieZ_mem_fil_and_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  intro p _ D R _ b N k _ t o₀ β ht o' m' z hz
  constructor
  · induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      exact sum_mem_fil β ht o₀ lam c hlam y'
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · have hbc := GlobalTheory.HTRealise.isBC_constMor o₀.ab
    suffices H : ∀ z ∈ lieZ o₀ β, hbc.bcMap z ∈ liftFil (epsDP k) m'.cart by
      refine ⟨hbc.bcMap z, H z hz, fun c => ?_⟩
      rw [(hbc.corr_iff.2 rfl) c]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hE : ∀ (x : D.O) (h : HdR o₀.A), crysToDR (epsDP k) m'.cart (hbc.bcMap (crysAct o₀ x h)) =
        GlobalTheory.HTSummand.crysAct (dp0 (DualNumber k)) (𝟙 _) o'.act x (crysToDR (epsDP k) m'.cart (hbc.bcMap h)) := by
      intro x h
      haveI := o₀.act.hom x
      haveI := o'.act.hom x
      have e1 : hbc.bcMap (crysAct o₀ x h) =
          push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act x) (hbc.bcMap h) := by
        rw [← hbc.corr_iff]
        exact GrpMor.Corr.push (m := constMor o₀.A) (constMor o₀.A) (o₀.act.act x) (o₀.act.act x) (by rfl)
          (hbc.corr_iff.2 rfl)
      have e2 := crysToDR_push (epsDP k) m'.cart m'.cart (o₀.act.act x) (o'.act.act x) (m'.act x).symm (hbc.bcMap h)
      exact (congrArg (crysToDR (epsDP k) m'.cart) e1).trans e2
    have hs : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
      rw [ht]; unfold spMap; rw [← Spec.map_comp]; rfl
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      have hlam' : ∀ i, ∑ l, algebraMap k (DualNumber k) (lam l) *
          ((algebraMap k (DualNumber k)).comp β) (b.t i (c l)) = 0 := fun i => by
        simp only [RingHom.comp_apply, ← map_mul, ← map_sum, hlam i, map_zero]
      haveI : IsLocalRing (DualNumber k) := dualNumber_local k
      have key := sum_mem_fil ((algebraMap k (DualNumber k)).comp β) hs o' (fun l => algebraMap k _ (lam l)) c hlam'
        (crysToDR (epsDP k) m'.cart (hbc.bcMap y'))
      rw [liftFil, Submodule.mem_comap]
      convert key using 2
      simp only [map_sum, map_smulₛₗ, hE, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, RingHom.comp_apply, map_intCast, RingHom.id_apply, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.HTCount
