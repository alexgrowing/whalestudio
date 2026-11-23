import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
open ReciprocityTheory.ChartRestriction.G.DVR (tu_def wu linCombIso_res linCombIso_isGen)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC ReciprocityTheory.ChartRestriction.G.Semi.Transport

namespace GlobalTheory.CompanionTheory.PerfIso

variable {X Y : Scheme.{0}}

theorem rs_app (π : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (h' : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U) (x : Γ(Y, U)) :
    rs X h' ((π.app U).hom x) = (π.app V).hom (rs Y h x) := by
  have e := congrArg (fun φ => φ.hom x) (π.naturality (homOfLE h).op)
  exact e.symm

theorem swap_rel {U V : Y.Opens} (u : Γ(Y, V ⊓ U)ˣ) (x : Γ(Y, U)) (y : Γ(Y, V))
    (h : rs Y (inf_le_left : U ⊓ V ≤ U) x =
      ((res (le_inf inf_le_right inf_le_left : U ⊓ V ≤ V ⊓ U) u)⁻¹).val *
        rs Y (inf_le_right : U ⊓ V ≤ V) y) :
    rs Y (inf_le_left : V ⊓ U ≤ V) y = u.val * rs Y (inf_le_right : V ⊓ U ≤ U) x := by
  have hr : res (le_inf inf_le_right inf_le_left : V ⊓ U ≤ U ⊓ V)
      (res (le_inf inf_le_right inf_le_left : U ⊓ V ≤ V ⊓ U) u) = u :=
    Units.ext ((GlobalTheory.AbLaw.rs_rs _ _ _).trans (rs_self _ _))
  have hu : rs Y (le_inf inf_le_right inf_le_left : V ⊓ U ≤ U ⊓ V)
      ((res (le_inf inf_le_right inf_le_left : U ⊓ V ≤ V ⊓ U) u)⁻¹).val = (u⁻¹).val := by
    change (res (le_inf inf_le_right inf_le_left : V ⊓ U ≤ U ⊓ V)
      ((res (le_inf inf_le_right inf_le_left : U ⊓ V ≤ V ⊓ U) u)⁻¹)).val = _
    rw [map_inv, hr]
  have e := congrArg (rs Y (le_inf inf_le_right inf_le_left : V ⊓ U ≤ U ⊓ V)) h
  simp only [map_mul, GlobalTheory.AbLaw.rs_rs, hu] at e
  rw [e, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]

theorem isoRel_of_inv {A B : LB Y} (w : LB.Iso A B) {s : LB.Sec A} {t : LB.Sec B}
    (h : IsoRel (invIso w) t s) : IsoRel w s t :=
  fun i k => swap_rel (w.s (i, k)) (s.f k) (t.f i) (h k i)

theorem exists_secEquiv {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen) :
    ∃ E : LB.Sec A ≃ LB.Sec B, ∀ s, IsoRel w s (E s) := by
  choose F hF using fun s => exists_isoRel hA hB hw s
  have hinj : Function.Injective F := fun s t h =>
    isoRel_inj_left hB (hF s) (by rw [h]; exact hF t)
  have hsurj : Function.Surjective F := fun t => by
    obtain ⟨s, hs⟩ := exists_isoRel hB hA (invIso_spec hA hB w hw).1 t
    exact ⟨s, isoRel_inj_right hA (hF s) (isoRel_of_inv w hs)⟩
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, hF⟩

abbrev pullIso {M M' : LB Y} (w : LB.Iso M M') (π : X ⟶ Y) : LB.Iso (M.pull π) (M'.pull π) :=
  LB.linCombIso w (K := PUnit) (fun _ => π) (fun _ => 1)

theorem rs_pullIso {M M' : LB Y} (w : LB.Iso M M') (π : X ⟶ Y) (a : M'.ι) (b : M.ι) {O : Y.Opens}
    (hO : O ≤ M'.U a ⊓ M.U b)
    (hp : π ⁻¹ᵁ O ≤ (M'.pull π).U (fun _ => a) ⊓ (M.pull π).U (fun _ => b)) :
    rs X hp ((pullIso w π).s (fun _ => a, fun _ => b)).val =
      (π.app O).hom (rs Y hO (w.s (a, b)).val) := by
  have e := linCombIso_res w (K := PUnit) (fun _ => π) (fun _ => 1) (fun _ => a, fun _ => b)
    (V := π ⁻¹ᵁ O) hp
  rw [Fintype.prod_unique, zpow_one] at e
  have hk : π ⁻¹ᵁ O ≤ π ⁻¹ᵁ (LB.div M' M).U (a, b) := fun _ hy => hO hy
  have e2 : wu w (π ⁻¹ᵁ O) π a b = res hk (pullU π _ (w.s (a, b))) :=
    tu_def (U := (LB.div M' M).U) (p := (a, b)) hk
  have e3 := congrArg Units.val (e.trans e2)
  refine e3.trans ?_
  exact rs_app π hO hk _

theorem rel_res {A B O : X.Opens} (hp : O ≤ A ⊓ B) (u : Γ(X, A ⊓ B)ˣ) (x : Γ(X, A)) (y : Γ(X, B))
    (h : rs X (inf_le_left : A ⊓ B ≤ A) x = u.val * rs X (inf_le_right : A ⊓ B ≤ B) y) :
    rs X (hp.trans inf_le_left) x = rs X hp u.val * rs X (hp.trans inf_le_right) y := by
  have e := congrArg (rs X hp) h
  simp only [map_mul, GlobalTheory.AbLaw.rs_rs] at e
  exact e

theorem rel_on {M M' : LB Y} (w : LB.Iso M M') (π : X ⟶ Y) {S : LB.Sec (M.pull π)}
    {S' : LB.Sec (M'.pull π)} (h : IsoRel (pullIso w π) S S') (a : M'.ι) (b : M.ι) {O : Y.Opens}
    (hO : O ≤ M'.U a ⊓ M.U b) :
    rs X (le_pull M' π (hO.trans inf_le_left)) (S'.f (fun _ => a)) =
      (π.app O).hom (rs Y hO (w.s (a, b)).val) *
        rs X (le_pull M π (hO.trans inf_le_right)) (S.f (fun _ => b)) := by
  have hp : π ⁻¹ᵁ O ≤ (M'.pull π).U (fun _ => a) ⊓ (M.pull π).U (fun _ => b) :=
    le_inf (le_pull M' π (hO.trans inf_le_left)) (le_pull M π (hO.trans inf_le_right))
  have e := rel_res hp ((pullIso w π).s (fun _ => a, fun _ => b)) (S'.f (fun _ => a))
    (S.f (fun _ => b)) (h (fun _ => a) (fun _ => b))
  exact e.trans (congrArg (· * _) (rs_pullIso w π a b hO hp))

theorem perf_of_iso : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R))
    {M M' : LB Y}, M.IsLB → M'.IsLB → ∀ (w : LB.Iso M M'), w.IsGen → Perf f M' →
    Nonempty (Perf f M) := by
  intro R _ Y f M M' hM hM' w hw P
  refine ⟨{ a := P.a, b := P.b, c := P.c, D₀ := P.D₀, D₁ := P.D₁, comp := P.comp, I := P.I × M.ι,
            W := fun p => P.W p.1 ⊓ M.U p.2, ch := fun p => p.2, le := fun _ => inf_le_right,
            cover := ?_,
            u := fun k p => rs Y (le_inf (inf_le_left.trans (P.le p.1)) inf_le_right :
                P.W p.1 ⊓ M.U p.2 ≤ M'.U (P.ch p.1) ⊓ M.U p.2) ((w.s (P.ch p.1, p.2))⁻¹).val *
              rs Y inf_le_left (P.u k p.1),
            sec := ?_, exact := ?_ }⟩
  · apply top_unique
    intro x _
    have hx : x ∈ ⨆ i, P.W i := by rw [P.cover]; trivial
    have hy : x ∈ ⨆ j, M.U j := by rw [hM.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  · intro R' _ g X' π f' hpb
    obtain ⟨E, hE⟩ := P.sec R' g X' π f' hpb
    obtain ⟨T, hT⟩ := exists_secEquiv (LB.isLB_pull hM π) (LB.isLB_pull hM' π) (pullIso w π)
      (linCombIso_isGen w hw _ _)
    refine ⟨E.trans T.symm, fun v p => ?_⟩
    obtain ⟨i, j⟩ := p
    have hrel : IsoRel (pullIso w π) (T.symm (E v)) (E v) := by
      have := hT (T.symm (E v))
      rwa [Equiv.apply_symm_apply] at this
    have hO : P.W i ⊓ M.U j ≤ M'.U (P.ch i) ⊓ M.U j :=
      le_inf (inf_le_left.trans (P.le i)) inf_le_right
    have r := rel_on w π hrel (P.ch i) j hO
    have hl : π ⁻¹ᵁ (P.W i ⊓ M.U j) ≤ π ⁻¹ᵁ P.W i := fun _ hy => hy.1
    have hv := congrArg (rs X' hl) (hE v i)
    simp only [GlobalTheory.AbLaw.rs_rs, map_sum, map_mul, rs_cst, rs_app π inf_le_left hl] at hv
    have haa : (π.app (P.W i ⊓ M.U j)).hom (rs Y hO ((w.s (P.ch i, j))⁻¹).val) *
        (π.app (P.W i ⊓ M.U j)).hom (rs Y hO (w.s (P.ch i, j)).val) = 1 := by
      rw [← map_mul]
      exact (congrArg _ (H1Iso.rs_inv_mul hO
        (show Γ(Y, M'.U (P.ch i) ⊓ M.U j)ˣ from w.s (P.ch i, j)))).trans (map_one _)
    simp only [map_mul, Equiv.trans_apply]
    rw [Finset.sum_congr rfl (fun k _ => mul_left_comm _ _ _), ← Finset.mul_sum, ← hv]
    rw [r, ← _root_.mul_assoc, haa, _root_.one_mul]
  · intro R' _ g X' π f' hpb h0 v hv
    have hA := LB.isLB_pull hM π
    have hB := LB.isLB_pull hM' π
    exact P.exact R' g X' π f' hpb
      (H1Iso.firstCohomologyVanishes_of_iso_of_isGen hA.cover hB (invIso (pullIso w π))
        (invIso_spec hA hB _ (linCombIso_isGen w hw _ _)).1 h0) v hv

end GlobalTheory.CompanionTheory.PerfIso
