import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Glue

open GlobalTheory.KS

variable {X Y : Scheme.{0}}

theorem map_eq_rsT {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    (Y.presheaf.map (homOfLE h).op).hom s = rsT s O := (rsT_of_le h s).symm

theorem rsT_pow' {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) (k : ℕ) : rsT (s ^ k) O = rsT s O ^ k := by
  rw [rsT_of_le h, rsT_of_le h, map_pow]

theorem le_wchart {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) {O : Y.Opens} (h : O ≤ m ⁻¹ᵁ L.U (c 0)) :
    O ≤ LB.wchart L (fun _ : Fin 1 => m) c := fun y hy =>
  Set.mem_iInter.2 fun x => by rw [Subsingleton.elim x 0]; exact h hy

theorem pullbackBundleChart_le_preimage {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => m) c ≤ m ⁻¹ᵁ L.U (c 0) := LB.wchart_le L _ c 0

theorem pbT_cocycle {L : LB X} (hL : L.IsLB) (m : Y ⟶ X) (a b c : L.ι) {O : Y.Opens}
    (h : O ≤ m ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)) :
    pbT m (L.g a b).val O * pbT m (L.g b c).val O = pbT m (L.g a c).val O := by
  have e := congrArg (fun u => pbT m u.val O) (hL.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, pbT_mul] at e
  rwa [pbT_rsT m inf_le_left h, pbT_rsT m (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    pbT_rsT m (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem linComb_g {L : LB X} (m : Y ⟶ X) (k : ℕ) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val O =
      pbT m (L.g (c 0) (c' 0)).val O ^ k := by
  have hle : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0)) :=
    fun y hy => ⟨pullbackBundleChart_le_preimage c hy.1, pullbackBundleChart_le_preimage c' hy.2⟩
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [rsT_pow' h]
  exact congrArg (· ^ k) ((congrArg (fun s => rsT s O) (GlobalTheory.KS.AdjDlog.val_res_pullU m hle (L.g (c 0) (c' 0)))).trans
    (rsT_pbT m hle h _))

theorem sec_rel {L : LB X} (m : Y ⟶ X) (k : ℕ) (τ : SecM m L k) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT (τ.f c) O = pbT m (L.g (c 0) (c' 0)).val O ^ k * rsT (τ.f c') O := by
  have e := congrArg (fun s => rsT s O) (τ.compat c c')
  simp only [map_eq_rsT] at e
  have h' : O ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := h
  rwa [rsT_rsT inf_le_left h', rsT_mul, linComb_g m k c c' h, rsT_rsT inf_le_right h'] at e

theorem exists_acts : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (dd : Fin n → Fld G.left), (∀ a, IsField ⊤ (dd a)) →
    ∀ (D : R → R) (h : Heat G m L dd D) (k : ℕ) (τ : SecM m L k), ∃ τ' : SecM m L k, h.Acts k τ τ' := by
  intro R _ G _ _ n X m L hL dd hdd D h k τ

  have loc : ∀ i O (hO : O ≤ h.W i) (f : Γ(G.left, h.W i)),
      rsT (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) O =
        op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (rsT f O) := by
    intro i O hO f
    have hd : ∀ g, resG G.left hO (h.d i (h.W i) g) = h.d i O (resG G.left hO g) :=
      fun g => ((h.lift i).1.2.2 (h.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG G.left hO (dd a (h.W i) g) = dd a O (resG G.left hO g) :=
      fun a g => ((hdd a).2.2 (h.W i) O hO le_top g).symm
    have hc : ∀ r, resG G.left hO (constFn G.hom (h.W i) r) = constFn G.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn G.hom hO r)
    have hp : ∀ q : Γ(G.left, h.W i), resG G.left hO (rsT q (h.W i)) = rsT q O := fun q => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]
    simp only [op, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]
  obtain ⟨F, hF⟩ : ∃ F : ∀ i, Γ(G.left, h.W i), ∀ i,
      F i = op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i)) :=
    ⟨_, fun _ => rfl⟩
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => le_wchart _ (h.le i)

  have Fc : ∀ i i', rsT (F i) (h.W i ⊓ h.W i') =
      pbT m (L.g (h.j i) (h.j i')).val (h.W i ⊓ h.W i') ^ k * rsT (F i') (h.W i ⊓ h.W i') := by
    intro i i'
    have hWc' : ∀ i, h.W i ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U (fun _ => h.j i) := hWc
    rw [hF, hF, loc i _ inf_le_left, loc i' _ inf_le_right, rsT_rsT (hWc' i) inf_le_left,
      rsT_rsT (hWc' i') inf_le_right,
      sec_rel m k τ (fun _ => h.j i) (fun _ => h.j i') (inf_le_inf (hWc i) (hWc i'))]
    exact h.glue k i i' _ le_rfl _
  have cov : ∀ V : G.left.Opens, V ≤ ⨆ i, V ⊓ h.W i := by
    intro V y hy
    have : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩

  have glue : ∀ c : Fin 1 → L.ι, ∃ t : Γ(G.left, LB.wchart L (fun _ : Fin 1 => m) c), ∀ i,
      rsT t (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) =
        pbT m (L.g (c 0) (h.j i)).val (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ^ k *
          rsT (F i) (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) := by
    intro c
    refine exists_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) (fun i => inf_le_left) (cov _) _
      fun i i' => ?_
    have hN1 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := inf_le_left
    have hN2 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i' := inf_le_right
    have hNW : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        h.W i ⊓ h.W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have hV : ∀ i, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun i y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i) ⊓ L.U (h.j i')) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, h.le i hy.1.2⟩, h.le i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_pow' hN1, rsT_pow' hN2, rsT_pbT m (hV i) hN1, rsT_pbT m (hV i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_pow' hNW, rsT_pbT m (show h.W i ⊓ h.W i' ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i')) from fun y hy => ⟨h.le i hy.1, h.le i' hy.2⟩) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  choose t ht using glue

  refine ⟨⟨t, fun c c' => ?_⟩, fun i => ?_⟩
  · have goal : rsT (t c) ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') =
        ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val *
          rsT (t c') ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
            (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') := ?_
    · exact (rsT_of_le inf_le_left (t c)).symm.trans (goal.trans (congrArg _ (rsT_of_le inf_le_right (t c'))))
    refine eq_of_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i)
      (fun i => inf_le_left) (cov _) _ _ fun i => ?_
    have a1 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have hV : ∀ c : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun c y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0) ⊓ L.U (h.j i)) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, pullbackBundleChart_le_preimage c' hy.1.2⟩, h.le i hy.2⟩
    have e' : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := inf_le_left
    have eL : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c := inf_le_left
    have eR : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c' := inf_le_right
    erw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', linComb_g m k c c' e',
      ← rsT_rsT inf_le_left a1 (t c), ← rsT_rsT inf_le_left a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_pow' a1, rsT_pow' a2, rsT_pbT m (hV c) a1, rsT_pbT m (hV c') a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  ·
    change rsT (t fun _ => h.j i) (h.W i) = _
    have a : h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i := le_inf (hWc i) le_rfl
    rw [← rsT_rsT inf_le_left a, ht, rsT_mul, rsT_pow' a,
      rsT_pbT m (show LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i))
        from fun y hy => ⟨pullbackBundleChart_le_preimage _ hy.1, h.le i hy.2⟩) a, rsT_rsT inf_le_right a, rsT_self,
      GlobalTheory.KS.AdjDlog.pbT_g_self hL m (h.j i) (h.le i), one_pow, _root_.one_mul, hF]

end GlobalTheory.Heat.Glue
