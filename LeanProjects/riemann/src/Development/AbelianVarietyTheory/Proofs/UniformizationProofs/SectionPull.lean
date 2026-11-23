import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecPullIso

theorem gs_sec_trans {X Z : Scheme.{0}} {L : LB X} (s : LB.Sec L) (r : Z ⟶ X) (z : Z) {j j' : L.ι}
    (hj : r z ∈ L.U j) (hj' : r z ∈ L.U j') :
    gs r z (L.U j) (s.f j) = (gm r z (L.U j ⊓ L.U j') (L.g j j')).val * gs r z (L.U j') (s.f j') := by
  have hm : r z ∈ L.U j ⊓ L.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  have e : r z ∈ X.basicOpen a ↔ z ∈ Z.basicOpen ((r.app U).hom a) := by
    rw [← Scheme.preimage_basicOpen]; rfl
  rw [e]
  exact (Scheme.mem_basicOpen Z _ z h).symm

theorem exists_pull {X X' : Scheme.{0}} (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ))
    (hH : H.IsLB) (hH' : H'.IsLB) (hw : w.IsGen) (s : LB.Sec H) :
    ∃ s' : LB.Sec H', ∀ z (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ (s.f k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
  have hp := (isGen_iff w).1 hw
  have ind : ∀ (z : X') (k j : H.ι) (k' j' : H'.ι), φ z ∈ H.U k → φ z ∈ H.U j → z ∈ H'.U k' → z ∈ H'.U j' →
      ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) =
        (gm (𝟙 X') z _ (H'.g k' j')).val * (((Geo.Tor.gw w (𝟙 _) z j j')⁻¹).val * gs φ z _ (s.f j)) := by
    intro z k j k' j' hk hj hk' hj'
    have a := hp _ (𝟙 X') z k j k' j' hk hj hk' hj'
    rw [Category.id_comp] at a
    rw [a, gs_sec_trans s φ z hk hj, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    generalize gm φ z _ (H.g k j) = A
    generalize gm (𝟙 X') z _ (H'.g k' j') = B
    generalize Geo.Tor.gw w (𝟙 _) z j j' = C
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ k' : H'.ι, ∃ a : Γ(X', H'.U k'), ∀ (z : X') (k : H.ι), φ z ∈ H.U k → z ∈ H'.U k' →
      gs (𝟙 X') z _ a = ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) := by
    intro k'
    let W : H.ι → X'.Opens := fun k => (H.pull φ).U (fun _ => k) ⊓ H'.U k'
    have l₁ : ∀ k, W k ≤ φ ⁻¹ᵁ H.U k := fun k x hx => mem_pull.1 hx.1
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', W k), ∀ (z : X') k, z ∈ W k →
        gs (𝟙 X') z (W k) (u k) = ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) :=
      ⟨fun k => ((show Γ(X', W k)ˣ from w.s (fun _ => k, k'))⁻¹).val *
          (X'.presheaf.map (homOfLE (l₁ k)).op).hom ((φ.app _).hom (s.f k)), fun z k hz =>
        (gs_mul (𝟙 X') z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit (𝟙 X') z _ hz _).trans (congrArg Units.val (map_inv _ _)))
          ((gs_res (𝟙 X') z _ hz _).trans ((gs_pull (𝟙 X') φ z _ (l₁ k hz) _).trans (by rw [Category.id_comp]))))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (H'.U k')
      (fun k => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hH (φ y)
        exact Opens.mem_iSup.2 ⟨k, mem_pull.2 hk, hy⟩) u
      (fun k j => fn_ext (V := W k ⊓ W j) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu y k hy.1, hu y j hy.2, ind y k j k' k' (l₁ k hy.1) (l₁ j hy.2) hy.1.2 hy.1.2,
          gm_self hH' (𝟙 X') y hy.1.2, Units.val_one, _root_.one_mul])
    refine ⟨a, fun z k h₁ h₂ => ?_⟩
    have hz : z ∈ W k := ⟨mem_pull.2 h₁, h₂⟩
    exact (gs_res (𝟙 X') z inf_le_right hz a).symm.trans ((congrArg (gs (𝟙 X') z (W k)) (ha k)).trans
      (hu z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun z k k' hk hk' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hH (φ y)
    refine (gs_res (𝟙 X') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X') y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 X') y _ hy _) (gs_res (𝟙 X') y _ hy _))).symm)
    rw [ha j y k hk hy.1, ha j' y k hk hy.2]
    exact ind y k k j j' hk hk hy.1 hy.2
  · show _ = _ * gs (𝟙 X') z _ (a k')
    rw [ha k' z k hk hk', Units.mul_inv_cancel_left]

theorem section_pull : ∀ (X X' : Scheme.{0}) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ)), H.IsLB → H'.IsLB → w.IsGen → ∀ s : LB.Sec H, (∃! s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k'))) ∧ ∀ s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) → nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by
  intro X X' φ H H' w hH hH' hw s
  constructor
  · obtain ⟨s', hs'⟩ := exists_pull φ H H' w hH hH' hw s
    refine ⟨s', hs', fun t ht => ?_⟩
    obtain ⟨f, hf⟩ := t
    obtain ⟨g, hg⟩ := s'
    obtain rfl : f = g := funext fun k' => fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hH (φ z)
      exact (Units.mul_right_inj _).1 ((ht z k k' hk hz).symm.trans (hs' z k k' hk hz))
    rfl
  · intro s' hs'
    have key : ∀ (z : X') (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
        (φ z ∈ X.basicOpen (s.f k) ↔ z ∈ X'.basicOpen (s'.f k')) := fun z k k' hk hk' => by
      rw [← isUnit_gs_iff φ z hk, hs' z k k' hk hk', Units.isUnit_units_mul]
      exact isUnit_gs_iff (𝟙 X') z hk' _
    ext z
    constructor
    · intro hz
      obtain ⟨k', hk'⟩ := Opens.mem_iSup.1 hz
      obtain ⟨k, hk⟩ := exists_chart hH (φ z)
      exact Opens.mem_iSup.2 ⟨k, (key z k k' hk (X'.basicOpen_le _ hk')).2 hk'⟩
    · intro hz
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show φ z ∈ nonzeroLocus s from hz)
      obtain ⟨k', hk'⟩ := exists_chart hH' z
      exact Opens.mem_iSup.2 ⟨k', (key z k k' (X.basicOpen_le _ hk) hk').1 hk⟩

end GlobalTheory.SecPullIso
