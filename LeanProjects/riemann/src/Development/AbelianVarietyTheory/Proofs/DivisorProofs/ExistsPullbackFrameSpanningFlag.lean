import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)
open GlobalTheory.LB (exists_fun_of_cover)

theorem pullCol_res {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ}
    (e : Fin m → Γ(E, U)) {V V' : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) (h : V' ≤ V)
    (M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    resM _ h (pullCol π e hV M j) = pullCol π e (h.trans hV) (M.map (resG Y h)) j := by
  simp only [pullCol, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (resG Y h (M l j) • ·) (QCoh.res_pullbackSections π E hV h (e l))

theorem Spans.res {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V V' : X.Opens}
    {v : Fin m → Γ(F, V)} (hs : Spans fl V v) (h : V' ≤ V) :
    Spans fl V' fun j => resM F h (v j) := fun l => by
  obtain ⟨s, hfr, hv⟩ := hs l
  exact ⟨fun j => resM _ h (s j), hfr.res h, fun j => by rw [app_resM, hv]⟩

def IsCellCoord {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} {r : ι → ℕ} {E : ι → B.Modules}
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) {U : B.Opens}
    (eU : ∀ a, Fin (r a) → Γ(E a, U)) (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (n : (Σ a, Low (r a)) → Γ(Y, V)) : Prop :=
  ∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩))

theorem IsCellCoord.res {B Y : Scheme.{0}} {π : Y ⟶ B} {ι : Type} {r : ι → ℕ} {E : ι → B.Modules}
    {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} {U : B.Opens}
    {eU : ∀ a, Fin (r a) → Γ(E a, U)} {V V' : Y.Opens} {hV : V ≤ π ⁻¹ᵁ U}
    {n : (Σ a, Low (r a)) → Γ(Y, V)} (hn : IsCellCoord π fl eU V hV n) (h : V' ≤ V) :
    IsCellCoord π fl eU V' (h.trans hV) fun s => resG Y h (n s) := fun a => by
  have e : (fun j => resM _ h (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩) j)) =
      pullCol π (eU a) (h.trans hV) (uniR fun s => resG Y h (n ⟨a, s⟩)) :=
    funext fun j => by rw [pullCol_res, map_uniR]
  exact e ▸ (hn a).res h

theorem exists_cellLocus : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, W)), (∀ a, Spans (fl a) W (pullCol π (eU a) hW (uniR fun s => n ⟨a, s⟩))) ∧ ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(Y, V)), (∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n' ⟨a, s⟩))) → ∃ hVW : V ≤ W, ∀ s, Y.presheaf.map (homOfLE hVW).op (n s) = n' s := by
  intro B Y π ι r E fl hE U eU heU
  have uniq : ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n₁ n₂ : (Σ a, Low (r a)) → Γ(Y, V)),
      IsCellCoord π fl eU V hV n₁ → IsCellCoord π fl eU V hV n₂ → n₁ = n₂ := by
    intro V hV n₁ n₂ h₁ h₂
    funext ⟨a, s⟩
    exact congrFun (GlobalTheory.T.pullback_unipotent_frame_unique Y B π (E a) (r a) (hE a) U (eU a) (heU a) (fl a) V hV _ _
      (h₁ a) (h₂ a)) s
  let K := {V : Y.Opens // ∃ (hV : V ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, V)),
    IsCellCoord π fl eU V hV n}
  choose hK nK gK using fun k : K => k.2
  have hWk : ∀ k : K, k.1 ≤ ⨆ k : K, k.1 := fun k => le_iSup (fun k : K => k.1) k
  have hW : (⨆ k : K, k.1) ≤ π ⁻¹ᵁ U := iSup_le hK
  have compat : ∀ (k l : K) s, resG Y (inf_le_left : k.1 ⊓ l.1 ≤ k.1) (nK k s) =
      resG Y (inf_le_right : k.1 ⊓ l.1 ≤ l.1) (nK l s) := fun k l s =>
    congrFun (uniq _ (inf_le_left.trans (hK k)) _ _ ((gK k).res inf_le_left)
      ((gK l).res inf_le_right)) s
  choose N hN using fun s => exists_fun_of_cover (fun k : K => k.1) hWk le_rfl
    (fun k => nK k s) fun k l => compat k l s
  have resN : ∀ k : K, (fun s => resG Y (hWk k) (N s)) = nK k := fun k => funext fun s => hN s k
  have good : IsCellCoord π fl eU (⨆ k : K, k.1) hW N := by
    intro a l
    have hv : ∀ k : K, pullCol π (eU a) (hK k) (uniR fun s => nK k ⟨a, s⟩) =
        fun j => resM _ (hWk k) (pullCol π (eU a) hW (uniR fun s => N ⟨a, s⟩) j) := by
      intro k; funext j; rw [pullCol_res, map_uniR, ← resN k]
    choose sK hsK hιK using fun k : K => gK k a l
    have compS : ∀ (k k' : K) j, resM _ (inf_le_left : k.1 ⊓ k'.1 ≤ k.1) (sK k j) =
        resM _ (inf_le_right : k.1 ⊓ k'.1 ≤ k'.1) (sK k' j) := by
      intro k k' j
      apply QCoh.injective_app_of_mono ((fl a).ι l)
      rw [app_resM, app_resM, hιK, hιK]
      simp only [hv, resM_resM]
    choose t ht using fun j => exists_sec_of_cover (F := (fl a).F l) (fun k : K => k.1) hWk le_rfl
      (fun k => sK k j) fun k k' => compS k k' j
    refine ⟨t, ?_, fun j => ?_⟩
    · refine isFrame_of_forall_exists fun V' h y hy => ?_
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ k : K, k.1 from h hy)
      refine ⟨V' ⊓ k.1, inf_le_left, ⟨hy, hk⟩, ?_⟩
      have e : (fun j => resM _ ((inf_le_left : V' ⊓ k.1 ≤ V').trans h) (t j)) =
          fun j => resM _ (inf_le_right : V' ⊓ k.1 ≤ k.1) (sK k j) := by
        funext j; rw [← ht j k, resM_resM]
      rw [e]
      exact hsK k _ inf_le_right
    · refine sec_ext_of_cover (fun k : K => k.1) hWk le_rfl fun k => ?_
      rw [← app_resM, ht, hιK]
      simp only [hv]
  refine ⟨⨆ k : K, k.1, hW, N, good, fun V hV n' hn' => ⟨hWk ⟨V, hV, n', hn'⟩, fun s => ?_⟩⟩
  exact (hN s _).trans (congrFun (uniq V hV _ _ (gK ⟨V, hV, n', hn'⟩) hn') s)

end GlobalTheory.FlagCell
