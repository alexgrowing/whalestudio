import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section Bundles

variable {X : Scheme.{0}}

def idIso (L : LB X) : LB.Iso L L := ⟨fun p => L.g p.1 p.2⟩

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem cocycle_identity_iso {L : LB X} (hL : L.IsLB) (p₁ p₂ q₁ q₂ : L.ι) :
    res (inf_le_left : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂) (L.g p₁ p₂) =
      res (inf_le_inf inf_le_left inf_le_left : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁) (L.g p₁ q₁) *
        (res (inf_le_inf inf_le_right inf_le_right : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₂ ⊓ L.U q₂) (L.g p₂ q₂))⁻¹ *
      res (inf_le_right : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U q₁ ⊓ L.U q₂) (L.g q₁ q₂) := by
  have h1 := congrArg (res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
      L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂ ⊓ L.U q₂)) (hL.cocycle p₁ p₂ q₂)
  have h2 := congrArg (res (le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right) :
      L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁ ⊓ L.U q₂)) (hL.cocycle p₁ q₁ q₂)
  simp only [map_mul, res_res_lemma] at h1 h2
  rw [eq_mul_inv_of_mul_eq h1, ← h2]
  exact mul_right_comm _ _ _

theorem idIso_isGen {L : LB X} (hL : L.IsLB) : (idIso L).IsGen := by
  intro i j
  exact cocycle_identity_iso hL i.1 i.2 j.1 j.2

theorem idIso_maps {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    LB.Gen.Maps (LB.linCombIso (idIso L.L) (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L.rig L.rig := fun p => L.rigGen p.1 p.2

theorem exists_iso_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G} (h : L₁ = L₂) :
    ∃ w : LB.Iso L₁.L L₂.L, w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  subst h
  exact ⟨idIso L₁.L, idIso_isGen L₁.isLB, idIso_maps L₁⟩

def gv {L' L : LB X} (w : LB.Iso L' L) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y _ (w.s (j, k))

theorem gm_isGen {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j j' : L.ι)
    (k k' : L'.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gv w f y j k = gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gv w f y j' k' := by
  have hV : f y ∈ (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
  have hw' : res (inf_le_left : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L'.U k) (w.s (j, k)) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L.U j') (L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
      res (inf_le_right : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j' ⊓ L'.U k') (w.s (j', k')) :=
    hw (j, k) (j', k')
  have key := congrArg (gm f y ((L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k'))) hw'
  simp only [map_mul, map_inv, gm_res f y _ hV] at key
  rw [gm_res f y (U := L.U j ⊓ L'.U k) _ hV (w.s (j, k)),
    gm_res f y (U := L.U j' ⊓ L'.U k') _ hV (w.s (j', k'))] at key
  exact key

def isoPullId {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) : LB.Iso L' (L.pull F) :=
  ⟨fun p => res (fun y hy => ⟨by have := mem_pull.1 hy.1; rw [hF] at this; exact this, hy.2⟩ :
    (LB.pull L F).U p.1 ⊓ L'.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L'.U p.2) (w.s (p.1 PUnit.unit, p.2))⟩

theorem gw_isoPullId {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y)
    (j : L.ι) (k : L'.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L'.U k) :
    gw (isoPullId w hF) f y j k = gv w f y j k := by
  have hmem : f y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 (by rw [hF]; exact hj), hk⟩
  exact gm_res f y _ hmem (w.s (j, k))

theorem isoPullId_pgen {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {F : X ⟶ X} (hF : F = 𝟙 X) :
    PGen (isoPullId w hF) := by
  intro Y f y j j' k k' hj hj' hk hk'
  subst hF
  rw [gw_isoPullId w rfl f y j k hj hk, gw_isoPullId w rfl f y j' k' hj' hk', Category.comp_id]
  exact gm_isGen hw f y j j' k k' hj hj' hk hk'

private theorem gm_pullU_eq_gm_comp {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {U : X.Opens}
    (h : φ (r z) ∈ U) (x : Γ(X, U)ˣ) :
    gm r z (φ ⁻¹ᵁ U) (pullU φ U x) = gm (r ≫ φ) z U x := by
  have h₁ : r z ∈ φ ⁻¹ᵁ U := h
  have h₂ : (r ≫ φ) z ∈ U := h
  simp only [gm, dif_pos h₁, dif_pos h₂, MonoidHom.comp_apply]
  ext
  simp only [Units.coe_map, pullU, MonoidHom.coe_coe]
  first
    | rfl
    | (rw [Scheme.comp_app]; rfl)

theorem gm_maps_pt {L' L : LB X} {w : LB.Iso L' L} {Y : Scheme.{0}} {φ : Y ⟶ X} {a : LB.Gen (L'.pull φ)}
    {b : LB.Gen (L.pull φ)} (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => φ) (fun _ => 1)) a b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : L.ι) (q : L'.ι) (hp : φ (r z) ∈ L.U p) (hq : φ (r z) ∈ L'.U q) :
    gm r z _ (b.s (fun _ => p)) = gv w (r ≫ φ) z p q * gm r z _ (a.s (fun _ => q)) := by
  have hV : r z ∈ LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q) :=
    ⟨mem_pull.2 hp, mem_pull.2 hq⟩
  have h' : res (U := LB.wchart L (fun _ => φ) (fun _ => p))
        (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q)) inf_le_left
        (b.s (fun _ => p)) =
      (∏ _k : PUnit, (res (U := φ ⁻¹ᵁ (L.U p ⊓ L'.U q))
          (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q))
          (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => φ) (fun _ => p) PUnit.unit))
            (inf_le_right.trans (LB.wchart_le L' (fun _ => φ) (fun _ => q) PUnit.unit)))
          (pullU φ (L.U p ⊓ L'.U q) (w.s (p, q)))) ^ (1 : ℤ)) *
      res (U := LB.wchart L' (fun _ => φ) (fun _ => q))
        (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q)) inf_le_right
        (a.s (fun _ => q)) :=
    h (fun _ => p, fun _ => q)
  rw [Fintype.prod_unique, zpow_one] at h'
  have key := congrArg (gm r z (LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q))) h'
  rw [map_mul, gm_res r z (U := LB.wchart L (fun _ => φ) (fun _ => p)) _ hV (b.s (fun _ => p))] at key
  refine key.trans (congrArg₂ (· * ·) ((gm_res r z _ hV _).trans
    (gm_pullU_eq_gm_comp φ r z (U := L.U p ⊓ L'.U q) ⟨hp, hq⟩ (w.s (p, q)))) (gm_res r z _ hV _))

private theorem res_eq_mul_res_of_gm_id_eq_mul {Y : Scheme.{0}} {V U₁ U₃ : Y.Opens} {h₁ : V ≤ U₁} {h₃ : V ≤ U₃}
    {a : Γ(Y, U₁)ˣ} {m : Γ(Y, V)ˣ} {c : Γ(Y, U₃)ˣ}
    (H : ∀ y ∈ V, gm (𝟙 Y) y U₁ a = gm (𝟙 Y) y V m * gm (𝟙 Y) y U₃ c) :
    res h₁ a = m * res h₃ c := by
  apply Units.ext
  refine TopCat.Presheaf.section_ext Y.sheaf V _ _ (fun y hy => ?_)
  have key := H y hy
  rw [← gm_res (𝟙 Y) y h₁ hy a, ← gm_res (𝟙 Y) y h₃ hy c, ← map_mul] at key
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', MonoidHom.comp_apply] at key
  have key2 := congrArg Units.val key
  exact key2

theorem isoPullId_maps {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L' L : RigLB G} {w : LB.Iso L'.L L.L}
    (hm : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L'.rig L.rig)
    {F : G.left ⟶ G.left} (hF : F = 𝟙 _) {e : (𝟙_ (Over S)).left ⟶ (𝟙_ (Over S)).left} (he₀ : e = 𝟙 _)
    (he : eSec G ≫ F = e ≫ eSec G) :
    LB.Gen.Maps (LB.linCombIso (isoPullId w hF) (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L'.rig
      (rigPullOf F e he L.L L.rig) := by
  subst hF he₀
  rintro ⟨j, i⟩
  have hmid : (LB.linCombIso (isoPullId w (rfl : 𝟙 G.left = 𝟙 G.left)) (K := PUnit) (fun _ => eSec G)
      (fun _ => 1)).s (j, i) =
      res (U := eSec G ⁻¹ᵁ ((L.L.pull (𝟙 G.left)).U (j PUnit.unit) ⊓ L'.L.U (i PUnit.unit)))
        (V := LB.wchart (L.L.pull (𝟙 G.left)) (fun _ => eSec G) j ⊓ LB.wchart L'.L (fun _ => eSec G) i)
        (le_inf (inf_le_left.trans (LB.wchart_le (L.L.pull (𝟙 G.left)) (fun _ => eSec G) j PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L'.L (fun _ => eSec G) i PUnit.unit)))
        (pullU (eSec G) ((L.L.pull (𝟙 G.left)).U (j PUnit.unit) ⊓ L'.L.U (i PUnit.unit))
          ((isoPullId w (rfl : 𝟙 G.left = 𝟙 G.left)).s (j PUnit.unit, i PUnit.unit))) :=
    by
      simp only [LB.linCombIso, zpow_one]
      first
        | exact Fintype.prod_unique _
        | exact Fintype.prod_unique
        | simp
  refine res_eq_mul_res_of_gm_id_eq_mul (fun z hz => ?_)
  have hz1' := mem_pull.1 (mem_pull.1 hz.1)
  have hz2' := mem_pull.1 hz.2
  have hz1 : eSec G z ∈ L.L.U (j PUnit.unit PUnit.unit) := hz1'
  have hz2 : eSec G z ∈ L'.L.U (i PUnit.unit) := hz2'
  have eL := (gm_res (𝟙 _) z (rigPull_le (𝟙 G.left) (𝟙 _) he L.L j) hz.1
      (pullU (𝟙 _) _ (L.rig.s (fun _ => j PUnit.unit PUnit.unit)))).trans
    (gm_pullU_eq_gm_comp (𝟙 _) (𝟙 _) z (U := (L.L.pull (eSec G)).U (fun _ => j PUnit.unit PUnit.unit))
      (mem_pull.2 hz1) (L.rig.s (fun _ => j PUnit.unit PUnit.unit)))
  rw [Category.comp_id] at eL
  have eM := (congrArg (gm (𝟙 _) z _) hmid).trans ((gm_res (𝟙 _) z _ hz _).trans
    ((gm_pullU_eq_gm_comp (eSec G) (𝟙 _) z (U := (L.L.pull (𝟙 G.left)).U (j PUnit.unit) ⊓ L'.L.U (i PUnit.unit))
      ⟨mem_pull.2 hz1, hz2⟩ ((isoPullId w (rfl : 𝟙 G.left = 𝟙 G.left)).s (j PUnit.unit, i PUnit.unit))).trans
      (gw_isoPullId w rfl (𝟙 _ ≫ eSec G) z (j PUnit.unit PUnit.unit) (i PUnit.unit) hz1 hz2)))
  have eR := gm_maps_pt hm (𝟙 _) z (j PUnit.unit PUnit.unit) (i PUnit.unit) hz1 hz2
  exact eL.trans (eR.trans (congrArg (· * _) eM.symm))

end Bundles

section Unif

open ReciprocityTheory.ChartRestriction.G.Out

theorem gm_of_res_eq {Y : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂} {h₃ : V ≤ U₃}
    {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : res h₁ a * res h₂ b = res h₃ c * res h₄ d) {y : Y} (hy : y ∈ V) :
    gm (𝟙 Y) y U₁ a * gm (𝟙 Y) y U₂ b = gm (𝟙 Y) y U₃ c * gm (𝟙 Y) y U₄ d := by
  have key := congrArg (gm (𝟙 Y) y V) H
  simp only [map_mul, gm_res (𝟙 Y) y _ hy] at key
  exact key

theorem res_eq_of_gm {Y : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂} {h₃ : V ≤ U₃}
    {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : ∀ y ∈ V, gm (𝟙 Y) y U₁ a * gm (𝟙 Y) y U₂ b = gm (𝟙 Y) y U₃ c * gm (𝟙 Y) y U₄ d) :
    res h₁ a * res h₂ b = res h₃ c * res h₄ d := by
  apply Units.ext
  refine TopCat.Presheaf.section_ext Y.sheaf V _ _ (fun y hy => ?_)
  have key := H y hy
  rw [← gm_res (𝟙 Y) y h₁ hy a, ← gm_res (𝟙 Y) y h₂ hy b, ← gm_res (𝟙 Y) y h₃ hy c, ← gm_res (𝟙 Y) y h₄ hy d,
    ← map_mul, ← map_mul] at key
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', MonoidHom.comp_apply] at key
  have key2 := congrArg Units.val key
  exact key2

private theorem isoPullId_isGen_of_isGen {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen)
    {F : X ⟶ X} (hF : F = 𝟙 X) : (isoPullId w hF).IsGen := by
  subst hF
  rintro ⟨J, k⟩ ⟨J', k'⟩
  have hpg : (L.pull (𝟙 X)).g J J' =
      res (U := (𝟙 X) ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)))
        (V := LB.wchart L (fun _ => 𝟙 X) J ⊓ LB.wchart L (fun _ => 𝟙 X) J')
        (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => 𝟙 X) J PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ => 𝟙 X) J' PUnit.unit)))
        (pullU (𝟙 X) (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit))) := by
    change (∏ _k : PUnit, _) = _
    first
      | (rw [Fintype.prod_unique]; exact zpow_one _)
      | exact (Fintype.prod_unique _).trans (zpow_one _)
      | simp
  refine res_eq_mul_res_of_gm_id_eq_mul (fun z hz => ?_)
  have hz' : (𝟙 X) z ∈ ((L.pull (𝟙 X)).U J ⊓ L'.U k) ⊓ ((L.pull (𝟙 X)).U J' ⊓ L'.U k') := hz
  have hJa' := mem_pull.1 hz'.1.1
  have hJb' := mem_pull.1 hz'.2.1
  have hJa : (𝟙 X) z ∈ L.U (J PUnit.unit) := hJa'
  have hJb : (𝟙 X) z ∈ L.U (J' PUnit.unit) := hJb'
  have hk : (𝟙 X) z ∈ L'.U k := hz'.1.2
  have hk' : (𝟙 X) z ∈ L'.U k' := hz'.2.2
  have hzJJ : (𝟙 X) z ∈ LB.wchart L (fun _ => 𝟙 X) J ⊓ LB.wchart L (fun _ => 𝟙 X) J' := ⟨hz'.1.1, hz'.2.1⟩
  have eA : gm (𝟙 X) z ((L.pull (𝟙 X)).U J ⊓ (L.pull (𝟙 X)).U J') ((L.pull (𝟙 X)).g J J') =
      gm (𝟙 X) z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit)) :=
    (congrArg (gm (𝟙 X) z _) hpg).trans ((gm_res (𝟙 X) z _ hzJJ _).trans
      ((gm_pullU_eq_gm_comp (𝟙 X) (𝟙 X) z (U := L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) ⟨hJa, hJb⟩
        (L.g (J PUnit.unit) (J' PUnit.unit))).trans (by rw [Category.comp_id])))
  have hdiv : (LB.div (L.pull (𝟙 X)) L').g (J, k) (J', k') =
      res (V := ((L.pull (𝟙 X)).U J ⊓ L'.U k) ⊓ ((L.pull (𝟙 X)).U J' ⊓ L'.U k'))
        (U := (L.pull (𝟙 X)).U J ⊓ (L.pull (𝟙 X)).U J')
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) ((L.pull (𝟙 X)).g J J') *
      (res (V := ((L.pull (𝟙 X)).U J ⊓ L'.U k) ⊓ ((L.pull (𝟙 X)).U J' ⊓ L'.U k')) (U := L'.U k ⊓ L'.U k')
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L'.g k k'))⁻¹ := rfl
  have eB : gm (𝟙 X) z (((L.pull (𝟙 X)).U J ⊓ L'.U k) ⊓ ((L.pull (𝟙 X)).U J' ⊓ L'.U k'))
        ((LB.div (L.pull (𝟙 X)) L').g (J, k) (J', k')) =
      gm (𝟙 X) z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit)) *
        (gm (𝟙 X) z (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ := by
    rw [hdiv, map_mul, map_inv, gm_res (𝟙 X) z _ hz', gm_res (𝟙 X) z _ hz', eA]
  have eL := gw_isoPullId w rfl (𝟙 X) z (J PUnit.unit) k hJa hk
  have eR := gw_isoPullId w rfl (𝟙 X) z (J' PUnit.unit) k' hJb hk'
  exact eL.trans ((gm_isGen hw (𝟙 X) z (J PUnit.unit) (J' PUnit.unit) k k' hJa hJb hk hk').trans
    (congrArg₂ (· * ·) eB.symm eR.symm))

theorem isPullUnif_of_uniq {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) (U' : Unif I D' A' G) (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre)
    (wL : LB.Iso U'.LG.L U.LG.L) (hwg : wL.IsGen)
    (hwm : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig U.LG.rig)
    (hlev : ∀ n : ℕ,
      (U'.gt n).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
        (U.gt n).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt n).pG) x k ≫ hD.e.hom.left ≫
              pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
            𝟙 _ ≫ D.toPre.Oφ ((U.gt n).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt n).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫
                            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) (𝟙 _) _
            Oinvε _ hψ ((U.gt n).t (hD.xe x)))) ∧
      ∀ (jM : PUnit → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jL : U.LG.L.ι),
        res (X := (thickObj R I n G).left) (inf_le_left.trans (inf_le_left.trans inf_le_left) :
            (U'.gt n).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
                pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) D'.toPre.P.L).U (jM, jM') ⊓
              (LB.div (D'.toPre.P.L.pull (U'.gt n).pG.left) (U'.LG.L.pull (fstG I n G).left)).U
                (fun _ => jM', fun _ => jL') ⊓
              (LB.div (D.toPre.P.L.pull (U.gt n).pG.left) (U.LG.L.pull (fstG I n G).left)).U
                (jM, fun _ => jL) ⊓
              (fstG I n G).left ⁻¹ᵁ (LB.div U.LG.L U'.LG.L).U (jL, jL') ≤
            (U'.gt n).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
                pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) D'.toPre.P.L).U (jM, jM'))
          (pullU (U'.gt n).pG.left _ (hD.w.s (jM, jM'))) *
        res (X := (thickObj R I n G).left) (inf_le_left.trans (inf_le_left.trans inf_le_right))
          ((U'.w n).s (fun _ => jM', fun _ => jL')) =
        res (X := (thickObj R I n G).left) (inf_le_left.trans inf_le_right)
          ((U.w n).s (jM, fun _ => jL)) *
        res (X := (thickObj R I n G).left) inf_le_right
          (pullU (fstG I n G).left _ (wL.s (jL, jL'))))
    (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G)
    (hbc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 _) :
    IsPullUnif (RingHom.id R) hD bc U U' := by
  have he₀ : specOf (RingHom.id R) = 𝟙 _ := by
    first
      | simp [specOf]
      | exact Spec.map_id _
      | rfl
  have he : eSec G ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec G := by
    rw [hbc, Category.comp_id, he₀]
    exact (Category.id_comp _).symm
  refine ⟨⟨isoPullId wL hbc, isoPullId_isGen_of_isGen hwg hbc, he, isoPullId_maps hwm hbc he₀ he,
    fun n => ⟨𝟙 _, ?_, ?_, (hlev n).2.1, ?_⟩⟩⟩
  · rw [hbc, Category.comp_id, Category.id_comp]
  · rw [Category.id_comp]
    exact (hlev n).1
  · intro jM jM' jL' jL
    refine res_eq_of_gm (fun y hy => ?_)
    have h4' : (fstG I n G).left y ∈
        (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)))).U jL ⊓ U'.LG.L.U jL' := hy.2
    have h4a' := mem_pull.1 h4'.1
    have h4a : (fstG I n G).left y ∈ U.LG.L.U (jL PUnit.unit) := by
      rw [hbc] at h4a'
      exact h4a'
    have h4y : (fstG I n G).left y ∈ U'.LG.L.U jL' := h4'.2
    have hyh4 : (fstG I n G).left y ∈ U.LG.L.U (jL PUnit.unit) ⊓ U'.LG.L.U jL' := ⟨h4a, h4y⟩
    have key := gm_of_res_eq ((hlev n).2.2 jM jM' jL' (jL PUnit.unit)) (y := y)
      ⟨⟨⟨hy.1.1.1, hy.1.1.2⟩, hy.1.2⟩, hyh4⟩
    refine key.trans (congrArg₂ (· * ·) ?_ ?_)
    · exact ((gm_pullU_eq_gm_comp (𝟙 _) (𝟙 _) y
        (U := (LB.div (D.toPre.P.L.pull (U.gt n).pG.left) (U.LG.L.pull (fstG I n G).left)).U (jM, jL))
        hy.1.2 ((U.w n).s (jM, jL))).trans (by rw [Category.comp_id] <;> rfl)).symm
    · exact (gm_pullU_eq_gm_comp (fstG I n G).left (𝟙 _) y (U := (LB.div U.LG.L U'.LG.L).U (jL PUnit.unit, jL'))
        hyh4 (wL.s (jL PUnit.unit, jL'))).trans
        ((gw_isoPullId wL hbc (𝟙 _ ≫ (fstG I n G).left) y (jL PUnit.unit) jL' h4a h4y).symm.trans
          (gm_pullU_eq_gm_comp (fstG I n G).left (𝟙 _) y
            (U := (LB.div (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)))) U'.LG.L).U
              (jL, jL'))
            h4' ((isoPullId wL hbc).s (jL, jL'))).symm)

end Unif

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
