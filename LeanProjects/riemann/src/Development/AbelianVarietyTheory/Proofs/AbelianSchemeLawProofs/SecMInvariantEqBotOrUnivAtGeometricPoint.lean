import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GeomPointSections

section Transfer

variable {X X' Y Y' : Scheme.{0}}

theorem exists_sec_transfer {M : LB Y} {N : LB Y'} (hM : M.IsLB) (hN : N.IsLB) (k : Y ⟶ Y')
    (c : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), M.ι → N.ι → (Z.presheaf.stalk z)ˣ)
    (hc : ∀ p q, ∃ u : Γ(Y, M.U p ⊓ k ⁻¹ᵁ N.U q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ M.U p → k (r z) ∈ N.U q → gm r z _ u = c Z r z p q)
    (htr : ∀ (y : Y) p p' q q', y ∈ M.U p → y ∈ M.U p' → k y ∈ N.U q → k y ∈ N.U q' →
      c Y (𝟙 Y) y p q = gm (𝟙 Y) y (M.U p ⊓ M.U p') (M.g p p') *
        (gm (𝟙 Y ≫ k) y (N.U q ⊓ N.U q') (N.g q q'))⁻¹ * c Y (𝟙 Y) y p' q')
    (s : LB.Sec N) : ∃ s' : LB.Sec M, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q,
      r z ∈ M.U p → k (r z) ∈ N.U q →
      gs r z _ (s'.f p) = (c Z r z p q).val * gs (r ≫ k) z _ (s.f q) := by
  choose u hu using hc
  have glue : ∀ p, ∃ a : Γ(Y, M.U p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ M.U p → k (r z) ∈ N.U q → gs r z _ a = (c Z r z p q).val * gs (r ≫ k) z _ (s.f q) := by
    intro p
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, M.U p ⊓ k ⁻¹ᵁ N.U q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
        r z ∈ M.U p ⊓ k ⁻¹ᵁ N.U q → gs r z _ (v q) = (c Z r z p q).val * gs (r ≫ k) z _ (s.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE inf_le_right).op).hom ((k.app _).hom (s.f q)),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val (hu p q Z r z hz.1 hz.2)))
          ((gs_res r z _ hz _).trans (gs_pull r k z _ hz.2 _)))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (fun q => M.U p ⊓ k ⁻¹ᵁ N.U q) (M.U p)
      (fun j => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hN (k y)
        exact Opens.mem_iSup.2 ⟨j, hy, hj⟩) v
      (fun j j' => fn_ext (V := (M.U p ⊓ k ⁻¹ᵁ N.U j) ⊓ (M.U p ⊓ k ⁻¹ᵁ N.U j')) fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y j hy.1, hv _ _ y j' hy.2, gs_compat s (𝟙 Y ≫ k) y hy.1.2 hy.2.2,
          htr y p p j j' hy.1.1 hy.1.1 hy.1.2 hy.2.2, gm_self hM (𝟙 Y) y hy.1.1, _root_.one_mul,
          ← _root_.mul_assoc, ← Units.val_mul, mul_right_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨a, fun Z r z j h₁ h₂ => ?_⟩
    have hz : r z ∈ M.U p ⊓ k ⁻¹ᵁ N.U j := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha j)).trans (hv Z r z j hz))
  choose a ha using glue
  refine ⟨⟨a, fun p p' => fn_ext fun y hy => ?_⟩, fun Z r z p q h₁ h₂ => ha p Z r z q h₁ h₂⟩
  obtain ⟨j, hj⟩ := exists_chart hN (k y)
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, ha p _ _ y j hy.1 hj,
    ha p' _ _ y j hy.2 hj, htr y p p' j j hy.1 hy.2 hj hj, gm_self hN (𝟙 Y ≫ k) y hj, inv_one, _root_.mul_one,
    Units.val_mul, _root_.mul_assoc]

variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem pw_comp {Z : Scheme.{0}} (w : LB.Iso L' (L.pull F)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (k : Y ⟶ Y')
    (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι) :
    pw w (fun i => k ≫ φ' i) ε r z p q = pw w φ' ε (r ≫ k) z p q := by
  simp only [pw, Category.assoc]

theorem trF_comp {Z : Scheme.{0}} (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (k : Y ⟶ Y')
    (r : Z ⟶ Y) (z : Z) (q q' : K → L'.ι) :
    trF (fun i => k ≫ φ' i) ε r z q q' = trF φ' ε (r ≫ k) z q q' := by
  simp only [trF, Category.assoc]

theorem mem_wchart_comp (φ' : K → (Y' ⟶ X')) (k : Y ⟶ Y') (y : Y) (q : K → L'.ι) :
    y ∈ LB.wchart L' (fun i => k ≫ φ' i) q ↔ k y ∈ LB.wchart L' φ' q :=
  ⟨fun h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i, fun h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i⟩

theorem exists_sec_up {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (k : Y ⟶ Y') (hk : ∀ i, φ i = (k ≫ φ' i) ≫ F)
    (s' : LB.Sec (LB.LinComb L' φ' ε)) : ∃ s : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q, r z ∈ LB.wchart L φ p → k (r z) ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L φ p) (s.f p) =
          (pw w φ' ε (r ≫ k) z p q).val * gs (r ≫ k) z (LB.wchart L' φ' q) (s'.f q) := by
  obtain rfl : φ = fun i => (k ≫ φ' i) ≫ F := funext hk
  refine exists_sec_transfer (DVR.linComb_isLB L hL _ ε) (DVR.linComb_isLB L' hL' φ' ε) k
    (fun Z r z p q => pw w φ' ε (r ≫ k) z p q) (fun p q => ?_) (fun y (p p' : K → L.ι) (q q' : K → L'.ι) a b c d => ?_) s'
  · obtain ⟨u, hu⟩ := exists_pw w (fun i => k ≫ φ' i) ε p q
    have le : LB.wchart L (fun i => (k ≫ φ' i) ≫ F) p ⊓ k ⁻¹ᵁ LB.wchart L' φ' q ≤
        LB.wchart L (fun i => (k ≫ φ' i) ≫ F) p ⊓ LB.wchart L' (fun i => k ≫ φ' i) q :=
      fun y hy => ⟨hy.1, (mem_wchart_comp φ' k y q).2 hy.2⟩
    exact ⟨res le u, fun Z r z h₁ h₂ => (gm_res r z le ⟨h₁, h₂⟩ u).trans
      ((hu Z r z (le ⟨h₁, h₂⟩)).trans (pw_comp w φ' ε k r z p q))⟩
  · have e := pw_trans hw (fun i => k ≫ φ' i) ε (𝟙 Y) y a b ((mem_wchart_comp φ' k y q).2 c)
      ((mem_wchart_comp φ' k y q').2 d)
    rw [pw_comp, pw_comp, trF_comp φ'] at e
    exact e.trans (congrArg₂ (· * ·) (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L _ ε (𝟙 Y) y p p' a b).symm
      (gm_linComb L' φ' ε (𝟙 Y ≫ k) y q q' c d).symm) rfl)

theorem exists_sec_down {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hh : ∀ i, φ' i ≫ F = h ≫ φ i)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L' φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p q, h (r z) ∈ LB.wchart L φ p → r z ∈ LB.wchart L' φ' q →
        gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (s'.f q) := by
  have e : (fun i => φ' i ≫ F) = fun i => h ≫ φ i := funext hh
  have m : ∀ (y : Y') p, h y ∈ LB.wchart L φ p → y ∈ LB.wchart L (fun i => φ' i ≫ F) p := fun y p hy => by
    rw [e]; exact (mem_wchart_comp φ h y p).2 hy
  obtain ⟨s', hs'⟩ := exists_sec_transfer (DVR.linComb_isLB L' hL' φ' ε) (DVR.linComb_isLB L hL φ ε) h
    (fun Z r z q p => (pw w φ' ε r z p q)⁻¹) (fun q p => by
      obtain ⟨u, hu⟩ := exists_pw w φ' ε p q
      have le : LB.wchart L' φ' q ⊓ h ⁻¹ᵁ LB.wchart L φ p ≤
          LB.wchart L (fun i => φ' i ≫ F) p ⊓ LB.wchart L' φ' q := fun y hy => ⟨m y p hy.2, hy.1⟩
      exact ⟨(res le u)⁻¹, fun Z r z h₁ h₂ => (map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z le ⟨h₁, h₂⟩ u).trans (hu Z r z (le ⟨h₁, h₂⟩))))⟩)
    (fun y (q q' : K → L'.ι) (p p' : K → L.ι) a b c d => by
      have e₁ := pw_trans hw φ' ε (𝟙 Y') y (m y p c) (m y p' d) a b
      rw [e, trF_comp φ] at e₁
      refine (congrArg (·⁻¹) e₁).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (fun a b => a * b⁻¹)
        (gm_linComb L' φ' ε (𝟙 Y') y q q' a b).symm (gm_linComb L φ ε (𝟙 Y' ≫ h) y p p' c d).symm) rfl))
      show (_ * _⁻¹ * _)⁻¹ = trF φ' ε (𝟙 Y') y q q' * (trF φ ε (𝟙 Y' ≫ h) y p p')⁻¹ * _
      rw [mul_inv, mul_inv, inv_inv, mul_comm (trF φ ε (𝟙 Y' ≫ h) y p p')⁻¹]) s
  refine ⟨s', fun Z r z p q h₁ h₂ => ?_⟩
  exact (Units.mul_inv_cancel_left _ _).symm.trans (congrArg _ (hs' Z r z q p h₂ h₁).symm)

theorem exists_gen_up {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (k : Y ⟶ Y') (hk : ∀ i, φ i = k ≫ φ' i ≫ F)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q, r z ∈ LB.wchart L φ p → k (r z) ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L φ p) (t.s p) =
          pw w φ' ε (r ≫ k) z p q * gm (r ≫ k) z (LB.wchart L' φ' q) (a.s q) := by
  obtain rfl : φ = fun i => k ≫ φ' i ≫ F := funext hk
  obtain ⟨t, ht, hv⟩ := exists_up hw hL hL' a ha
  refine ⟨LB.pullGen L _ ε t k, DVR.pullGen_isGen _ _ _ t ht k, fun Z r z p q h₁ h₂ => ?_⟩
  exact (gm_pullGen L _ ε t k r z p h₁).trans
    (hv Z (r ≫ k) z p q ((mem_wchart_comp (fun i => φ' i ≫ F) k (r z) p).1 h₁) h₂)

end Transfer

section Relation

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

def PullRel (w : LB.Iso L' (L.pull F)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (f : ∀ p, Γ(Y, LB.wchart L φ p)) (f' : ∀ q, Γ(Y', LB.wchart L' φ' q)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p q, h (r z) ∈ LB.wchart L φ p → r z ∈ LB.wchart L' φ' q →
    gs (r ≫ h) z (LB.wchart L φ p) (f p) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (f' q)

variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}

theorem PullRel.unique_left (hL' : L'.IsLB) {k : Y ⟶ Y'} (hk : k ≫ h = 𝟙 Y) {f₁ f₂ f'}
    (h₁ : PullRel w φ' φ ε h f₁ f') (h₂ : PullRel w φ' φ ε h f₂ f') : f₁ = f₂ := by
  refine funext fun p => fn_ext fun y hy => ?_
  choose q hq using fun i => exists_chart hL' (φ' i (k y))
  have m : h (k y) ∈ LB.wchart L φ p := (congrArg (fun u : Y ⟶ Y => u y ∈ LB.wchart L φ p) hk).mpr hy
  have e := (h₁ Y k y p q m (Set.mem_iInter.2 hq)).trans (h₂ Y k y p q m (Set.mem_iInter.2 hq)).symm
  rwa [hk] at e

theorem PullRel.unique_right (hL : L.IsLB) {f f₁ f₂}
    (h₁ : PullRel w φ' φ ε h f f₁) (h₂ : PullRel w φ' φ ε h f f₂) : f₁ = f₂ := by
  refine funext fun q => fn_ext fun y hy => ?_
  choose p hp using fun i => exists_chart hL (φ i (h y))
  exact (Units.mul_right_inj _).1 ((h₁ Y' (𝟙 Y') y p q (Set.mem_iInter.2 hp) hy).symm.trans
    (h₂ Y' (𝟙 Y') y p q (Set.mem_iInter.2 hp) hy))

theorem PullRel.add {f₁ f₂ f₁' f₂'} (h₁ : PullRel w φ' φ ε h f₁ f₁') (h₂ : PullRel w φ' φ ε h f₂ f₂') :
    PullRel w φ' φ ε h (fun p => f₁ p + f₂ p) (fun q => f₁' q + f₂' q) := fun Z r z p q a b => by
  rw [gs_add (r ≫ h) z _ a, gs_add r z _ b, h₁ Z r z p q a b, h₂ Z r z p q a b, mul_add]

theorem PullRel.smul {f f'} (H : PullRel w φ' φ ε h f f') (c : Γ(Y, ⊤)) (c' : Γ(Y', ⊤))
    (hc : h.appTop.hom c = c') :
    PullRel w φ' φ ε h (fun p => (Y.presheaf.map (homOfLE le_top).op).hom c * f p)
      (fun q => (Y'.presheaf.map (homOfLE le_top).op).hom c' * f' q) := fun Z r z p q a b => by
  have e : gs (r ≫ h) z ⊤ c = gs r z ⊤ c' := hc ▸ (gs_pull r h z ⊤ trivial c).symm
  rw [gs_mul (r ≫ h) z _ a, gs_mul r z _ b, H Z r z p q a b, gs_res (r ≫ h) z _ a, gs_res r z _ b, e, mul_left_comm]

theorem exists_pullRel_up (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {k : Y ⟶ Y'} (hk : k ≫ h = 𝟙 Y)
    (hk' : h ≫ k = 𝟙 Y') (hh : ∀ i, φ' i ≫ F = h ≫ φ i) (s' : LB.Sec (LB.LinComb L' φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), PullRel w φ' φ ε h s.f s'.f := by
  obtain ⟨s, hs⟩ := exists_sec_up hw hL hL' (φ := φ) k
    (fun i => by rw [Category.assoc, hh, ← Category.assoc, hk, Category.id_comp]) s'
  refine ⟨s, fun Z r z p q a b => ?_⟩
  have e : (r ≫ h) ≫ k = r := by rw [Category.assoc, hk', Category.comp_id]
  have := hs Z (r ≫ h) z p q a ((congrArg (fun u : Z ⟶ Y' => u z ∈ LB.wchart L' φ' q) e).mpr b)
  rwa [e] at this

end Relation

section Action

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {n : ℤ} {T : Over S}

theorem isActOf_iff (θ : ThetaGrp A L n T) (s s' : LB.Sec (LPow A L n T)) :
    (IsActOf A L n θ s s' → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (j : Fin 2 → L.ι),
      r z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j) (θ.φ.s j)).val *
          gs (r ≫ (translT A θ.pt).left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1))) ∧
    ((∀ (z : (T ⊗ A).left) (j : Fin 2 → L.ι),
      z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j →
      gs (𝟙 _) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm (𝟙 _) z (LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j) (θ.φ.s j)).val *
          gs (𝟙 _ ≫ (translT A θ.pt).left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1))) → IsActOf A L n θ s s') := by
  have l₁ := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _)
  constructor
  · intro H Z r z j hz
    exact (gs_res r z (chart_le_zero A L _ j) hz _).symm.trans ((congrArg (gs r z _) (H j)).trans
      ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _)
        ((gs_res r z (l₁ j) hz _).trans (gs_pull r (translT A θ.pt).left z
          (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (l₁ j hz) _)))))
  · intro H j
    exact fn_ext fun z hz => (gs_res (𝟙 _) z (chart_le_zero A L _ j) hz _).trans ((H z j hz).trans
      ((gs_mul (𝟙 _) z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) z _ hz _)
        ((gs_res (𝟙 _) z (l₁ j) hz _).trans (gs_pull (𝟙 _) (translT A θ.pt).left z
          (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (l₁ j hz) _)))).symm)

end Action

section BaseChange

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left}
  {g : A'.left ⟶ A.left} {w : LB.Iso L' (L.pull g)} {T : Over S} {T' : Over S'}
  {h : (T' ⊗ A').left ⟶ (T ⊗ A).left} {k : (T ⊗ A).left ⟶ (T' ⊗ A').left}

theorem exists_secEquiv (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (hk : k ≫ h = 𝟙 _) (hk' : h ≫ k = 𝟙 _)
    (hs : (snd T' A').left ≫ g = h ≫ (snd T A).left) (σ : Γ(T'.left, ⊤) → Γ(T.left, ⊤))
    (hσ : ∀ c, h.appTop.hom ((fst T A).left.appTop.hom (σ c)) = (fst T' A').left.appTop.hom c) (n : ℤ) :
    ∃ E : SecM A' L' n T' ≃+ SecM A L n T, (∀ c x, E (c • x) = σ c • E x) ∧
      ∀ x, PullRel w (fun _ : Fin 1 => (snd T' A').left) (fun _ => (snd T A).left) (fun _ => n) h (E x).1 x.1 := by
  have up : ∀ x : SecM A' L' n T', ∃ y : SecM A L n T,
      PullRel w (fun _ : Fin 1 => (snd T' A').left) (fun _ => (snd T A).left) (fun _ => n) h y.1 x.1 := fun x => by
    obtain ⟨s, hs⟩ := exists_pullRel_up hw hL hL' (φ' := fun _ : Fin 1 => (snd T' A').left)
      (φ := fun _ => (snd T A).left) (ε := fun _ => n) hk hk' (fun _ => hs) (SecM.toSec A' x)
    exact ⟨SecM.ofSec A s, hs⟩
  choose E hE using up
  have hadd : ∀ x y, E (x + y) = E x + E y := fun x y =>
    Subtype.ext ((hE (x + y)).unique_left hL' hk ((hE x).add (hE y)))
  have hbij : Function.Bijective (AddMonoidHom.mk' E hadd) := by
    refine ⟨fun x y e => Subtype.ext ((hE x).unique_right hL ?_), fun y => ?_⟩
    · have e' : E x = E y := e
      rw [e']; exact hE y
    · obtain ⟨s, hs⟩ := exists_sec_down hw hL hL' (φ' := fun _ : Fin 1 => (snd T' A').left)
        (φ := fun _ => (snd T A).left) (ε := fun _ => n) h (fun _ => hs) (SecM.toSec A y)
      exact ⟨SecM.ofSec A' s, Subtype.ext ((hE _).unique_left hL' hk hs)⟩
  exact ⟨AddEquiv.ofBijective _ hbij, fun c x =>
    Subtype.ext ((hE (c • x)).unique_left hL' hk ((hE x).smul _ _ (hσ c))), hE⟩

theorem exists_theta_up (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (hk : k ≫ h = 𝟙 _)
    (hs : (snd T' A').left ≫ g = h ≫ (snd T A).left) {n : ℤ} (θ' : ThetaGrp A' L' n T') (x : T ⟶ A)
    (hx : (translPt A' θ'.pt).left ≫ g = h ≫ (translPt A x).left)
    (hx' : (translT A' θ'.pt).left ≫ h = h ≫ (translT A x).left) :
    ∃ θ : ThetaGrp A L n T, ∀ (s₁ s₂ : LB.Sec (LPow A L n T)) (s₁' s₂' : LB.Sec (LPow A' L' n T')),
      PullRel w (fun _ : Fin 1 => (snd T' A').left) (fun _ => (snd T A).left) (fun _ => n) h s₁.f s₁'.f →
      PullRel w (fun _ : Fin 1 => (snd T' A').left) (fun _ => (snd T A).left) (fun _ => n) h s₂.f s₂'.f →
      IsActOf A' L' n θ' s₁' s₂' → IsActOf A L n θ s₁ s₂ := by
  have a₀ : (snd T A).left = k ≫ (snd T' A').left ≫ g := by rw [hs, ← Category.assoc, hk, Category.id_comp]
  have a₁ : (translPt A x).left = k ≫ (translPt A' θ'.pt).left ≫ g := by
    rw [hx, ← Category.assoc, hk, Category.id_comp]
  obtain ⟨t, ht, hv⟩ := exists_gen_up hw hL hL' (K := Fin 2)
    (φ' := ![(snd T' A').left, (translPt A' θ'.pt).left]) (φ := ![(snd T A).left, (translPt A x).left])
    (ε := ![n, -n]) k (fun i => by fin_cases i; exacts [a₀, a₁]) θ'.φ θ'.isGen
  refine ⟨⟨x, t, ht⟩, fun s₁ s₂ s₁' s₂' R₁ R₂ H => (isActOf_iff _ s₁ s₂).2 fun y j hy => ?_⟩
  choose q hq using fun i : Fin 2 => exists_chart hL' (![(snd T' A').left, (translPt A' θ'.pt).left] i (k y))
  have mq : k y ∈ LB.wchart L' ![(snd T' A').left, (translPt A' θ'.pt).left] q := Set.mem_iInter.2 hq
  have b : (k ≫ (translT A' θ'.pt).left) ≫ h = (translT A x).left := by
    rw [Category.assoc, hx', ← Category.assoc, hk, Category.id_comp]
  have b' : (k ≫ (translT A' θ'.pt).left) ≫ (snd T' A').left = k ≫ (translPt A' θ'.pt).left := by
    rw [Category.assoc, ← Over.comp_left, translT, lift_snd]
  have e₀ := (isActOf_iff θ' s₁' s₂').1 H _ k y q mq
  have e₁ := R₁ _ (k ≫ (translT A' θ'.pt).left) y (fun _ => j 1) (fun _ => q 1)
    ((congrArg (fun u : (T ⊗ A).left ⟶ (T ⊗ A).left =>
      u y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) b).mpr
      (chart_le_pull A L (translT A x) (translPt A x) (lift_snd _ _) j hy))
    (chart_le_pull A' L' (translT A' θ'.pt) (translPt A' θ'.pt) (lift_snd _ _) q mq)
  have e₂ := R₂ _ k y (fun _ => j 0) (fun _ => q 0)
    ((congrArg (fun u : (T ⊗ A).left ⟶ (T ⊗ A).left =>
      u y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) hk).mpr
      (chart_le_zero A L _ j hy)) (chart_le_zero A' L' _ q mq)
  have e₃ := hv _ (𝟙 _) y j q hy mq
  rw [b] at e₁
  rw [hk] at e₂
  rw [Category.id_comp] at e₃
  have p₁ : pw w (fun _ : Fin 1 => (snd T' A').left) (fun _ => n) (k ≫ (translT A' θ'.pt).left) y (fun _ => j 1)
      (fun _ => q 1) = gw w (k ≫ (translPt A' θ'.pt).left) y (j 1) (q 1) ^ n := by
    rw [pw, Fin.prod_univ_one, b']
  have p₂ : pw w (fun _ : Fin 1 => (snd T' A').left) (fun _ => n) k y (fun _ => j 0)
      (fun _ => q 0) = gw w (k ≫ (snd T' A').left) y (j 0) (q 0) ^ n := by
    rw [pw, Fin.prod_univ_one]
  have p₃ : pw w ![(snd T' A').left, (translPt A' θ'.pt).left] ![n, -n] k y j q =
      gw w (k ≫ (snd T' A').left) y (j 0) (q 0) ^ n * (gw w (k ≫ (translPt A' θ'.pt).left) y (j 1) (q 1) ^ n)⁻¹ := by
    rw [pw, Fin.prod_univ_two, ← zpow_neg]; rfl
  rw [p₁] at e₁
  rw [p₂] at e₂
  rw [p₃] at e₃
  refine e₂.trans (Eq.trans (congrArg _ e₀) (Eq.symm ((congrArg₂ (· * ·) (congrArg Units.val e₃)
    ((congrArg (fun u => gs u y _ _) (Category.id_comp _)).trans e₁)).trans ?_)))
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_right_comm _ _ (_ ^ n),
    inv_mul_cancel_right]

end BaseChange

section Geometry

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {g : A'.left ⟶ A.left}

theorem exists_totalIso (hg : IsPullback g A'.hom A.hom f)
    (hmul : ∀ (T : Over S') (x y : T ⟶ A'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) :
    ∃ (h : (baseOver S' ⊗ A').left ⟶ (Over.mk f ⊗ A).left) (k : (Over.mk f ⊗ A).left ⟶ (baseOver S' ⊗ A').left),
      k ≫ h = 𝟙 _ ∧ h ≫ k = 𝟙 _ ∧ (snd (baseOver S') A').left ≫ g = h ≫ (snd (Over.mk f) A).left ∧
      h ≫ (fst (Over.mk f) A).left = (fst (baseOver S') A').left ∧
      ∀ x' : baseOver S' ⟶ A', ∃ x : Over.mk f ⟶ A,
        (translPt A' x').left ≫ g = h ≫ (translPt A x).left ∧
        (translT A' x').left ≫ h = h ≫ (translT A x).left := by
  have c' : (fst (baseOver S') A').left = (baseOver S' ⊗ A').hom :=
    (Category.comp_id _).symm.trans (Over.w (fst (baseOver S') A'))
  have c'' : (snd (baseOver S') A').left ≫ A'.hom = (fst (baseOver S') A').left :=
    (Over.w (snd (baseOver S') A')).trans c'.symm
  let u : Over.mk ((baseOver S' ⊗ A').hom ≫ f) ⟶ Over.mk f :=
    Over.homMk (fst (baseOver S') A').left (congrArg (· ≫ f) c')
  let H : Over.mk ((baseOver S' ⊗ A').hom ≫ f) ⟶ Over.mk f ⊗ A := lift u (toBase hg.w (snd (baseOver S') A'))
  have h₁ : H.left ≫ (fst (Over.mk f) A).left = (fst (baseOver S') A').left :=
    congrArg (fun q => q.left) (lift_fst u (toBase hg.w (snd (baseOver S') A')))
  have h₂ : H.left ≫ (snd (Over.mk f) A).left = (snd (baseOver S') A').left ≫ g :=
    congrArg (fun q => q.left) (lift_snd u (toBase hg.w (snd (baseOver S') A')))
  have sq : (snd (Over.mk f) A).left ≫ A.hom = (fst (Over.mk f) A).left ≫ f :=
    (Over.w (snd (Over.mk f) A)).trans (Over.w (fst (Over.mk f) A)).symm
  let T₂ : Over S' := Over.mk (Y := (Over.mk f ⊗ A).left) (fst (Over.mk f) A).left
  let a : T₂ ⟶ baseOver S' := Over.homMk (fst (Over.mk f) A).left (Category.comp_id _)
  let b : T₂ ⟶ A' := Over.homMk (hg.lift _ _ sq) (hg.lift_snd _ _ _)
  have k₁ : (lift a b).left ≫ (fst (baseOver S') A').left = (fst (Over.mk f) A).left :=
    congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd (baseOver S') A').left = hg.lift _ _ sq :=
    congrArg (fun q => q.left) (lift_snd a b)
  have ext₁ : ∀ {Z : Scheme.{0}} {r r' : Z ⟶ (Over.mk f ⊗ A).left},
      r ≫ (fst (Over.mk f) A).left = r' ≫ (fst (Over.mk f) A).left →
      r ≫ (snd (Over.mk f) A).left = r' ≫ (snd (Over.mk f) A).left → r = r' := fun e e' => pullback.hom_ext e e'
  have ext₂ : ∀ {Z : Scheme.{0}} {r r' : Z ⟶ (baseOver S' ⊗ A').left},
      r ≫ (fst (baseOver S') A').left = r' ≫ (fst (baseOver S') A').left →
      r ≫ (snd (baseOver S') A').left ≫ g = r' ≫ (snd (baseOver S') A').left ≫ g → r = r' := fun e e' =>
    pullback.hom_ext e (hg.hom_ext ((Category.assoc _ _ _).trans (e'.trans (Category.assoc _ _ _).symm))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) c'').trans (e.trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) c'')).symm))))
  have k₃ : (lift a b).left ≫ (snd (baseOver S') A').left ≫ g = (snd (Over.mk f) A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) k₂).trans (hg.lift_fst _ _ _))
  refine ⟨H.left, (lift a b).left, ext₁ ?_ ?_, ext₂ ?_ ?_, h₂.symm, h₁, fun x' => ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans (k₁.trans (Category.id_comp _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (k₃.trans (Category.id_comp _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k₁).trans (h₁.trans (Category.id_comp _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k₃).trans (h₂.trans (Category.id_comp _).symm))
  · let x : Over.mk f ⟶ A := Over.homMk (x'.left ≫ g) ((Over.w (toBase hg.w x')).trans (Category.id_comp f))
    have e₀ : H ≫ fst (Over.mk f) A ≫ x = toBase hg.w (fst (baseOver S') A' ≫ x') :=
      (lift_fst_assoc _ _ _).trans (Over.OverMorphism.ext (Category.assoc _ _ _).symm)
    have e₁ : H ≫ translPt A x = toBase hg.w (translPt A' x') := by
      refine (MonObj.comp_mul H (fst (Over.mk f) A ≫ x) (snd (Over.mk f) A)).trans
        (Eq.trans ?_ (hmul _ (fst (baseOver S') A' ≫ x') (snd (baseOver S') A')).symm)
      rw [e₀, lift_snd]
    have e₂ : (translPt A' x').left ≫ g = H.left ≫ (translPt A x).left := (congrArg (fun q => q.left) e₁).symm
    have t₁ : (translT A x).left ≫ (fst (Over.mk f) A).left = (fst (Over.mk f) A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (Over.mk f) A) (translPt A x))
    have t₂ : (translT A x).left ≫ (snd (Over.mk f) A).left = (translPt A x).left :=
      congrArg (fun q => q.left) (lift_snd (fst (Over.mk f) A) (translPt A x))
    have t₁' : (translT A' x').left ≫ (fst (baseOver S') A').left = (fst (baseOver S') A').left :=
      congrArg (fun q => q.left) (lift_fst (fst (baseOver S') A') (translPt A' x'))
    have t₂' : (translT A' x').left ≫ (snd (baseOver S') A').left = (translPt A' x').left :=
      congrArg (fun q => q.left) (lift_snd (fst (baseOver S') A') (translPt A' x'))
    refine ⟨x, e₂, ext₁ ?_ ?_⟩
    · exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans t₁')).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) t₁).trans h₁)).symm
    · exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ g) t₂').trans e₂)))).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) t₂)).symm

end Geometry

theorem exists_baseChange_secEquiv (hBC : PolBaseChangeSt) {S S' : Scheme.{0}} (P : PolAV S) (f : S' ⟶ S) :
    ∃ P' : PolAV S', P'.g = P.g ∧ ∀ n : ℤ,
      ∃ (E : SecM P'.A P'.L n (baseOver S') ≃+ SecM P.A P.L n (Over.mk f))
        (σ : Γ((baseOver S').left, ⊤) → Γ((Over.mk f).left, ⊤)), Function.Bijective σ ∧
        (∀ c x, E (c • x) = σ c • E x) ∧
        ∀ θ' : ThetaGrp P'.A P'.L n (baseOver S'), ∃ θ : ThetaGrp P.A P.L n (Over.mk f),
          ∀ s₁' s₂' : LB.Sec (LPow P'.A P'.L n (baseOver S')), IsActOf P'.A P'.L n θ' s₁' s₂' →
            IsActOf P.A P.L n θ (SecM.toSec P.A (E (SecM.ofSec P'.A s₁'))) (SecM.toSec P.A (E (SecM.ofSec P'.A s₂'))) := by
  obtain ⟨P', g, hg, hdim, hmul, hiso⟩ := hBC S S' f P
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨h, k, hk, hk', hs, hf, hx⟩ := exists_totalIso hg hmul
  refine ⟨P', hdim, fun n => ?_⟩
  obtain ⟨E, hE, hR⟩ := exists_secEquiv hw' P.isLB P'.isLB hk hk' hs (fun c => c)
    (fun c => congrArg (fun q => q.appTop.hom c) hf) n
  refine ⟨E, fun c => c, Function.bijective_id, hE, fun θ' => ?_⟩
  obtain ⟨x, e₁, e₂⟩ := hx θ'.pt
  obtain ⟨θ, hθ⟩ := exists_theta_up hw' P.isLB P'.isLB hk hs θ' x e₁ e₂
  exact ⟨θ, fun s₁' s₂' => hθ _ _ s₁' s₂' (hR (SecM.ofSec P'.A s₁')) (hR (SecM.ofSec P'.A s₂'))⟩

end GeomPointSections

theorem secM_invariant_eq_bot_or_univ_at_geometric_point :
    PolBaseChangeSt → (GlobalSectionsRankAlgClosed → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g)) ∧ (IrredSt → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (k : ℕ), (k = 1 ∨ 4 ≤ k) → (k : K) ≠ 0 → ∀ W : Submodule Γ((Over.mk t).left, ⊤) (SecM P.A P.L k (Over.mk t)), (∀ (θ : ThetaGrp P.A P.L k (Over.mk t)) (s s' : LB.Sec (LPow P.A P.L k (Over.mk t))), IsActOf P.A P.L k θ s s' → SecM.ofSec P.A s ∈ W → SecM.ofSec P.A s' ∈ W) → W = ⊥ ∨ W = ⊤)) := by
  intro hBC
  refine ⟨fun hH S P K _ _ t n hn => ?_, fun hI S P K _ _ t k hk hk0 W hW => ?_⟩
  · obtain ⟨P', hdim, H⟩ := GeomPointSections.exists_baseChange_secEquiv hBC P t
    obtain ⟨E, σ, hσ, hE, -⟩ := H n
    rw [← hdim, ← hH K P' n hn]
    exact (congrArg Cardinal.toNat (rank_eq_of_equiv_equiv σ E hσ hE)).symm
  · obtain ⟨P', -, H⟩ := GeomPointSections.exists_baseChange_secEquiv hBC P t
    obtain ⟨E, σ, -, hE, hθ⟩ := H k
    let W' : Submodule Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P'.A P'.L k (baseOver (Spec (CommRingCat.of K)))) :=
      { carrier := {x | E x ∈ W}
        add_mem' := fun {x y} hx hy => by
          show E (x + y) ∈ W
          rw [E.map_add]; exact W.add_mem hx hy
        zero_mem' := by
          show E 0 ∈ W
          rw [E.map_zero]; exact W.zero_mem
        smul_mem' := fun c x hx => by
          show E (c • x) ∈ W
          rw [hE]; exact W.smul_mem _ hx }
    have key := hI K P' k hk hk0 W' fun θ' s s' hact hs => by
      obtain ⟨θ, h⟩ := hθ θ'
      exact hW θ _ _ (h s s' hact) hs
    refine key.imp (fun e => (Submodule.eq_bot_iff _).2 fun y hy => ?_) (fun e => Submodule.eq_top_iff'.2 fun y => ?_)
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [(Submodule.eq_bot_iff _).1 e x hy, E.map_zero]
    · obtain ⟨x, rfl⟩ := E.surjective y
      exact Submodule.eq_top_iff'.1 e x

end GlobalTheory
