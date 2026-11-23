import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompletedPointOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePointsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BundleExt

open TopologicalSpace

variable {X₀ X Y : Scheme.{0}}

theorem gm_comp {Z : Scheme.{0}} (κ : Z ⟶ Y) (w : Z) (r : Y ⟶ X) (U : X.Opens) (h : r (κ w) ∈ U)
    (a : Γ(X, U)ˣ) : gm (κ ≫ r) w U a = Units.map (κ.stalkMap w).hom.toMonoidHom (gm r (κ w) U a) := by
  apply Units.ext
  rw [gm_val (κ ≫ r) w U h]
  show _ = (κ.stalkMap w).hom (gm r (κ w) U a).val
  rw [gm_val r (κ w) U h]
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) w h _).symm

theorem gs_eq_of_germ [IsIntegral X] {U V : X.Opens} {a : Γ(X, U)} {b : Γ(X, V)} {y : X} (hU : y ∈ U)
    (hV : y ∈ V) (h : gs (𝟙 X) y U a = gs (𝟙 X) y V b) {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (h₁ : f z ∈ U)
    (h₂ : f z ∈ V) : gs f z U a = gs f z V b := by
  have hm : y ∈ U ⊓ V := ⟨hU, hV⟩
  have hz : f z ∈ U ⊓ V := ⟨h₁, h₂⟩
  rw [← gs_res _ y inf_le_left hm a, ← gs_res _ y inf_le_right hm b, gs_eq _ y _ hm, gs_eq _ y _ hm] at h
  have e := germ_injective_of_isIntegral X y hm h
  rw [← gs_res f z inf_le_left hz a, ← gs_res f z inf_le_right hz b]
  exact congrArg _ e

theorem fn_ext_dense (q₀ : X₀ ⟶ X) [QuasiCompact q₀] [IsSchemeTheoreticallyDominant q₀] (g : Y ⟶ X) [Flat g]
    {T : Y.Opens} {s t : Γ(Y, T)}
    (h : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (r : Z ⟶ X₀) (z : Z), r ≫ q₀ = ρ ≫ g → ρ z ∈ T →
      gs ρ z T s = gs ρ z T t) : s = t := by
  refine (pullback.fst g q₀).app_injective T (fn_ext fun y hy => ?_)
  refine (gs_pull (𝟙 _) _ y T hy s).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ y T hy t).symm)
  rw [Category.id_comp]
  exact h _ _ (pullback.snd g q₀) y pullback.condition.symm hy

theorem unit_ext_dense (q₀ : X₀ ⟶ X) [QuasiCompact q₀] [IsSchemeTheoreticallyDominant q₀] {U : X.Opens}
    {a b : Γ(X, U)ˣ} (h : ∀ x, q₀ x ∈ U → gm q₀ x U a = gm q₀ x U b) : a = b := by
  have e : pullU q₀ U a = pullU q₀ U b := unit_ext fun x hx => by
    rw [gm_pull (𝟙 X₀) q₀ x U hx, gm_pull (𝟙 X₀) q₀ x U hx, Category.id_comp]; exact h x hx
  exact Units.ext (q₀.app_injective U (congrArg Units.val e))

theorem exists_push (q₀ : X₀ ⟶ X) [IsOpenImmersion q₀] (W : X₀.Opens) (a : Γ(X₀, W)ˣ) :
    ∃ a' : Γ(X, q₀ ''ᵁ W)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X₀) (z : Z), r z ∈ W →
      gm (r ≫ q₀) z _ a' = gm r z W a := by
  refine ⟨Units.map (q₀.appIso W).inv.hom.toMonoidHom a, fun Z r z hz => ?_⟩
  have hm : q₀ (r z) ∈ q₀ ''ᵁ W := ⟨_, hz, rfl⟩
  rw [← gm_pull r q₀ z _ hm, ← gm_res r z (q₀.preimage_image_eq W).le hm a]
  congr 1
  exact Units.ext (congrArg (fun q => q.hom a.val) (q₀.appIso_inv_app W))

theorem exists_local_unit [IsIntegral X] [IsLocallyNoetherian X] (q₀ : X₀ ⟶ X) [IsOpenImmersion q₀]
    (W : X₀.Opens) (hW : (W : Set X₀).Nonempty) (a : Γ(X₀, W)ˣ) (g : Y ⟶ X) [Flat g] (v : Γ(Y, ⊤)ˣ)
    (H : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (r : Z ⟶ X₀), r ≫ q₀ = ρ ≫ g → ∀ z : Z, gm r z W a = gm ρ z ⊤ v)
    (p : Y) : ∃ (V : X.Opens) (c : Γ(X, V)ˣ), g p ∈ V ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₀) (z : Z),
      q₀ (r z) ∈ V → r z ∈ W → gm (r ≫ q₀) z V c = gm r z W a := by
  obtain ⟨a', ha'⟩ := exists_push q₀ W a
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g p)) isOpen_univ
  replace hV : IsAffineOpen V := hV
  obtain ⟨w, hw⟩ := hW
  obtain ⟨y, hyV, hyW⟩ := nonempty_preirreducible_inter V.isOpen (q₀ ''ᵁ W).isOpen ⟨_, hpV⟩ ⟨_, w, hw, rfl⟩
  obtain ⟨d, hdW, hyd⟩ := hV.exists_basicOpen_le (⟨y, hyW⟩ : q₀ ''ᵁ W) hyV
  have hloc := hV.isLocalization_basicOpen d
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj d ((X.presheaf.map (homOfLE hdW).op).hom a'.val)
  have hpow : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z), f z ∈ V → gs f z V (d ^ n) = gs f z V d ^ n :=
    fun f z h => by simp only [gs_eq f z V h, map_pow]
  have hb' : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z), f z ∈ X.basicOpen d →
      gs f z _ a'.val * gs f z V (d ^ n) = gs f z V b := fun f z h => by
    rw [← map_pow] at hb
    have := congrArg (gs f z (X.basicOpen d)) hb
    rw [gs_mul f z _ h, gs_res f z hdW h] at this
    exact (congrArg _ (gs_res f z (X.basicOpen_le d) h _).symm).trans
      (this.trans (gs_res f z (X.basicOpen_le d) h _))
  have hdense : Dense (X.basicOpen d : Set X) := (X.basicOpen d).isOpen.dense ⟨y, hyd⟩
  have := Opens.isDominant_ι (X := X) hdense
  have : IsSchemeTheoreticallyDominant (X.basicOpen d).ι := .of_isDominant _
  have hr : Set.range (X.basicOpen d).ι ⊆ Set.range q₀ := by
    rw [Scheme.Opens.range_ι]
    intro x hx
    obtain ⟨u, -, hu⟩ := hdW hx
    exact ⟨u, hu⟩
  have e : (Y.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ V ≤ ⊤)).op).hom v.val * (g.app V).hom (d ^ n) =
      (g.app V).hom b := by
    refine fn_ext_dense (X.basicOpen d).ι g fun Z ρ r z hρ hz => ?_
    have hl : (r ≫ IsOpenImmersion.lift q₀ _ hr) ≫ q₀ = ρ ≫ g := by
      rw [Category.assoc, IsOpenImmersion.lift_fac, hρ]
    have hzd : (ρ ≫ g) z ∈ X.basicOpen d := by rw [← hρ]; exact (r z).2
    have hzW : (r ≫ IsOpenImmersion.lift q₀ _ hr) z ∈ W := by
      rw [← q₀.preimage_image_eq W]
      show ((r ≫ IsOpenImmersion.lift q₀ _ hr) ≫ q₀) z ∈ q₀ ''ᵁ W
      rw [hl]; exact hdW hzd
    rw [gs_mul ρ z _ hz, gs_res ρ z _ hz, gs_pull ρ g z V hz, gs_pull ρ g z V hz, ← hb' _ z hzd,
      gs_unit ρ z ⊤ trivial, ← H Z ρ _ hl z, ← ha' Z _ z hzW, hl, gs_unit _ z _ (hdW hzd)]
  have e' : (gm (𝟙 Y) p ⊤ v).val * (g.stalkMap p).hom (gs (𝟙 X) (g p) V (d ^ n)) =
      (g.stalkMap p).hom (gs (𝟙 X) (g p) V b) := by
    have := congrArg (gs (𝟙 Y) p (g ⁻¹ᵁ V)) e
    have hp : (𝟙 Y : Y ⟶ Y) p ∈ g ⁻¹ᵁ V := hpV
    rwa [gs_mul _ p _ hp, gs_res _ p _ hp, gs_pull (𝟙 Y) g p V hpV, gs_pull (𝟙 Y) g p V hpV, Category.id_comp,
      gs_unit _ p ⊤ trivial, gs_stalkMap g p V hpV, gs_stalkMap g p V hpV] at this
  obtain ⟨c₀, hc₀⟩ := dvd_descend g p (Dvd.intro_left _ e')
  obtain ⟨c₁, hc₁⟩ := dvd_descend g p (a := gs (𝟙 X) (g p) V b) (b := gs (𝟙 X) (g p) V (d ^ n))
    (by rw [← e']; exact Units.mul_left_dvd.2 dvd_rfl)
  have hd0 : ∀ x ∈ V, gs (𝟙 X) x V (d ^ n) ≠ 0 := fun x hx h0 => by
    have h1 : gs (𝟙 X) x V (d ^ n) = gs (𝟙 X) x V 0 := by rw [h0, gs_eq _ x V hx, map_zero, map_zero]
    have h2 := gs_eq_of_germ hx hx h1 (𝟙 X) y hyV hyV
    have h3 : IsUnit (gs (𝟙 X) y V d) := by
      rw [gs_eq _ y V hyV]; exact (X.mem_basicOpen d y hyV).1 hyd
    rw [hpow _ y hyV, gs_eq _ y V hyV 0, map_zero, map_zero] at h2
    exact (h3.pow n).ne_zero h2
  have hu : IsUnit c₀ := by
    refine IsUnit.of_mul_eq_one c₁ (mul_left_cancel₀ (hd0 _ hpV) ?_)
    rw [← _root_.mul_assoc, ← hc₀, ← hc₁, _root_.mul_one]
  obtain ⟨U, hU, c, rfl⟩ := X.presheaf.germ_exist c₀
  have hpc : g p ∈ X.basicOpen c := (X.mem_basicOpen c _ hU).2 hu
  refine ⟨X.basicOpen c, (X.toRingedSpace.isUnit_res_basicOpen c).unit, hpc, fun Z r z h₁ h₂ => ?_⟩
  have hm : g p ∈ U ⊓ V := ⟨hU, hpV⟩
  have k : gs (𝟙 X) (g p) V b = gs (𝟙 X) (g p) (U ⊓ V) ((X.presheaf.map (homOfLE inf_le_right).op).hom (d ^ n) *
      (X.presheaf.map (homOfLE inf_le_left).op).hom c) := by
    rw [gs_mul (𝟙 X) (g p) _ hm, gs_res (𝟙 X) (g p) _ hm, gs_res (𝟙 X) (g p) _ hm, hc₀,
      gs_eq (𝟙 X) (g p) U hU]
    rfl
  obtain ⟨x, hxU, hxd⟩ := nonempty_preirreducible_inter U.isOpen (X.basicOpen d).isOpen ⟨_, hU⟩ ⟨_, hyd⟩
  have hxV := X.basicOpen_le d hxd
  have hxm : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  have k' := gs_eq_of_germ hpV hm k (𝟙 X) x hxV hxm
  rw [gs_mul (𝟙 X) x _ hxm, gs_res (𝟙 X) x _ hxm, gs_res (𝟙 X) x _ hxm, ← hb' _ x hxd, _root_.mul_comm] at k'
  have k'' := gs_eq_of_germ (hdW hxd) hxU (mul_left_cancel₀ (hd0 x hxV) k') (r ≫ q₀) z ⟨_, h₂, rfl⟩
    (X.basicOpen_le c h₁)
  apply Units.ext
  rw [← ha' Z r z h₂, ← gs_unit (r ≫ q₀) z (q₀ ''ᵁ W) ⟨_, h₂, rfl⟩, k'']
  exact (gs_unit (r ≫ q₀) z (X.basicOpen c) h₁ _).symm.trans (gs_res (r ≫ q₀) z (X.basicOpen_le c) h₁ c)

theorem exists_iso_of_local (q₀ : X₀ ⟶ X) [QuasiCompact q₀] [IsSchemeTheoreticallyDominant q₀] {L : LB Y} {L' : LB X}
    (ψ : X ⟶ Y) (w : LB.Iso (L'.pull q₀) (L.pull (q₀ ≫ ψ))) (hw : PGen w)
    (H : ∀ x : X, ∃ (j : L.ι) (k : L'.ι) (V : X.Opens) (c : Γ(X, V)ˣ), x ∈ V ∧ ψ x ∈ L.U j ∧ x ∈ L'.U k ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X₀) (z : Z), q₀ (r z) ∈ V → ψ (q₀ (r z)) ∈ L.U j → q₀ (r z) ∈ L'.U k →
        gm (r ≫ q₀) z V c = Geo.Tor.gw w r z j (fun _ => k)) :
    ∃ w' : LB.Iso L' (L.pull ψ), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₀) (z : Z) (j : L.ι) (k : L'.ι),
      ψ (q₀ (r z)) ∈ L.U j → q₀ (r z) ∈ L'.U k →
        Geo.Tor.gw w' (r ≫ q₀) z j k = Geo.Tor.gw w r z j (fun _ => k) := by
  have tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ X₀) (z : Z) (j j' : L.ι) (k k' : L'.ι), ψ (q₀ (r z)) ∈ L.U j →
      ψ (q₀ (r z)) ∈ L.U j' → q₀ (r z) ∈ L'.U k → q₀ (r z) ∈ L'.U k' → Geo.Tor.gw w r z j (fun _ => k) =
        gm ((r ≫ q₀) ≫ ψ) z _ (L.g j j') * (gm (r ≫ q₀) z _ (L'.g k k'))⁻¹ * Geo.Tor.gw w r z j' (fun _ => k') :=
    fun Z r z j j' k k' hj hj' hk hk' => by
      have := hw Z r z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk) (mem_pull.2 hk')
      rw [gm_pull_g L' q₀ r z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at this
      rw [Category.assoc]
      exact this
  choose J K V c hV hJ hK hc using H
  have glue : ∀ (j : L.ι) (k : L'.ι), ∃ s : Γ(X, (L.pull ψ).U (fun _ => j) ⊓ L'.U k)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X₀) (z : Z), ψ (q₀ (r z)) ∈ L.U j → q₀ (r z) ∈ L'.U k →
        gm (r ≫ q₀) z _ s = Geo.Tor.gw w r z j (fun _ => k) := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : X → X.Opens, ∀ i x, x ∈ W i ↔
        (ψ x ∈ L.U j ∧ ψ x ∈ L.U (J i)) ∧ (x ∈ L'.U k ∧ x ∈ L'.U (K i)) ∧ x ∈ V i :=
      ⟨fun i => ψ ⁻¹ᵁ (L.U j ⊓ L.U (J i)) ⊓ ((L'.U k ⊓ L'.U (K i)) ⊓ V i), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull ψ).U (fun _ => j) ⊓ L'.U k := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).1.1, ((hW i x).1 hx).2.1.1⟩
    have l₁ : ∀ i, W i ≤ ψ ⁻¹ᵁ (L.U j ⊓ L.U (J i)) := fun i x hx => ((hW i x).1 hx).1
    have l₂ : ∀ i, W i ≤ L'.U k ⊓ L'.U (K i) := fun i x hx => ((hW i x).1 hx).2.1
    have l₃ : ∀ i, W i ≤ V i := fun i x hx => ((hW i x).1 hx).2.2
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X, W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X₀) (z : Z) (i : X), q₀ (r z) ∈ W i →
        gm (r ≫ q₀) z (W i) (u i) = Geo.Tor.gw w r z j (fun _ => k) := by
      refine ⟨fun i => res (l₁ i) (pullU ψ _ (L.g j (J i))) * (res (l₂ i) (L'.g k (K i)))⁻¹ * res (l₃ i) (c i),
        fun Z r z i hz => ?_⟩
      have h := (hW i _).1 hz
      rw [map_mul, map_mul, map_inv, gm_res (r ≫ q₀) z _ hz, gm_res (r ≫ q₀) z _ hz, gm_res (r ≫ q₀) z _ hz,
        gm_pull (r ≫ q₀) ψ z _ (l₁ i hz), hc i Z r z h.2.2 h.1.2 h.2.1.2]
      exact (tr Z r z j (J i) k (K i) h.1.1 h.1.2 h.2.1.1 h.2.1.2).symm
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx =>
        Opens.mem_iSup.2 ⟨x, (hW x x).2 ⟨⟨mem_pull.1 hx.1, hJ x⟩, ⟨hx.2, hK x⟩, hV x⟩⟩) u (fun i i' x hx => by
      have e : res (inf_le_left : W i ⊓ W i' ≤ W i) (u i) = res inf_le_right (u i') :=
        unit_ext_dense q₀ fun z hz => by
          have := (hu _ (𝟙 X₀) z i hz.1).trans (hu _ (𝟙 X₀) z i' hz.2).symm
          rw [Category.id_comp] at this
          rw [gm_res q₀ z _ hz, gm_res q₀ z _ hz, this]
      exact (gm_res _ x inf_le_left hx _).symm.trans ((congrArg _ e).trans (gm_res _ x inf_le_right hx _)))
    refine ⟨s, fun Z r z hj hk => ?_⟩
    have hy := (hW (q₀ (r z)) _).2 ⟨⟨hj, hJ _⟩, ⟨hk, hK _⟩, hV _⟩
    exact (gm_res (r ≫ q₀) z (l₀ _) hy s).symm.trans ((congrArg (gm (r ≫ q₀) z (W _)) (hs _)).trans (hu Z r z _ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, ?_, fun Z r z j k hj hk => hs j k Z r z hj hk⟩
  rintro ⟨j, k⟩ ⟨j', k'⟩
  refine unit_ext_dense q₀ fun x hx => ?_
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have := tr _ (𝟙 X₀) x _ _ k k' hj hj' hx.1.2 hx.2.2
  rw [← hs _ _ _ (𝟙 X₀) x hj hx.1.2, ← hs _ _ _ (𝟙 X₀) x hj' hx.2.2, Category.id_comp,
    ← gm_div_g q₀ x _ _ k k' hj hj' hx.1.2 hx.2.2] at this
  exact (gm_res _ x _ hx _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

theorem gm_eq_of_dense (q₀ : X₀ ⟶ X) [QuasiCompact q₀] [IsSchemeTheoreticallyDominant q₀] (g : Y ⟶ X) [Flat g]
    {W : X.Opens} (s : Γ(X, W)ˣ) (v : Γ(Y, ⊤)ˣ)
    (h : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (r : Z ⟶ X₀) (z : Z), r ≫ q₀ = ρ ≫ g → g (ρ z) ∈ W →
      gm (ρ ≫ g) z W s = gm ρ z ⊤ v) {Z : Scheme.{0}} (ρ : Z ⟶ Y) (z : Z) (hz : g (ρ z) ∈ W) :
    gm (ρ ≫ g) z W s = gm ρ z ⊤ v := by
  have e : pullU g W s = res le_top v := Units.ext (fn_ext_dense q₀ g fun Z ρ r z hr hz => by
    rw [gs_unit ρ z _ hz, gs_unit ρ z _ hz, gm_pull ρ g z W hz, gm_res ρ z _ hz, h Z ρ r z hr hz])
  rw [← gm_pull ρ g z W hz, e, gm_res ρ z _ hz]

theorem exists_iso_of_flat [IsIntegral X] [IsLocallyNoetherian X] (q₀ : X₀ ⟶ X) [IsOpenImmersion q₀] [IsDominant q₀]
    {L : LB Y} {L' : LB X} (hL : L.IsLB) (hL' : L'.IsLB) (ψ : X ⟶ Y) (F : X₀ ⟶ Y) (hF : F = q₀ ≫ ψ)
    (w : LB.Iso (L'.pull q₀) (L.pull F)) (hw : w.IsGen)
    (H : ∀ x : X, x ∉ Set.range q₀ → ∃ (T : Scheme.{0}) (g : T ⟶ X) (j : L.ι) (k : L'.ι) (v : Γ(T, ⊤)ˣ), Flat g ∧
      x ∈ Set.range g ∧ ψ x ∈ L.U j ∧ x ∈ L'.U k ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ X₀), r ≫ q₀ = ρ ≫ g →
        ∀ z : Z, Geo.Tor.gw w r z j (fun _ => k) = gm ρ z ⊤ v) :
    ∃ w' : LB.Iso L' (L.pull ψ), w'.IsGen ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X) (j : L.ι) (k : L'.ι) (v : Γ(T, ⊤)ˣ),
      Flat g → (∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ X₀), r ≫ q₀ = ρ ≫ g →
        ∀ z : Z, Geo.Tor.gw w r z j (fun _ => k) = gm ρ z ⊤ v) →
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (z : Z), ψ (g (ρ z)) ∈ L.U j → g (ρ z) ∈ L'.U k →
        Geo.Tor.gw w' (ρ ≫ g) z j k = gm ρ z ⊤ v := by
  subst hF
  have : IsSchemeTheoreticallyDominant q₀ := .of_isDominant _
  obtain ⟨w', hw', e⟩ := exists_iso_of_local q₀ ψ w ((isGen_iff w).1 hw) fun x => by
    by_cases hx : x ∈ Set.range q₀
    · obtain ⟨y, rfl⟩ := hx
      obtain ⟨j, hj⟩ := exists_chart hL (ψ (q₀ y))
      obtain ⟨k, hk⟩ := exists_chart hL' (q₀ y)
      obtain ⟨c, hc⟩ := exists_push q₀ ((L.pull (q₀ ≫ ψ)).U (fun _ => j) ⊓ (L'.pull q₀).U (fun _ => k))
        (w.s (fun _ => j, fun _ => k))
      exact ⟨j, k, _, c, ⟨y, ⟨mem_pull₂.2 hj, mem_pull.2 hk⟩, rfl⟩, hj, hk, fun Z r z _ h₁ h₂ =>
        hc Z r z ⟨mem_pull₂.2 h₁, mem_pull.2 h₂⟩⟩
    · obtain ⟨T, g, j, k, v, hg, ⟨p, rfl⟩, hj, hk, hv⟩ := H x hx
      obtain ⟨y, hy⟩ := q₀.denseRange.exists_mem_open (ψ ⁻¹ᵁ L.U j ⊓ L'.U k).isOpen ⟨g p, hj, hk⟩
      obtain ⟨V, c, hV, hc⟩ := exists_local_unit q₀ ((L.pull (q₀ ≫ ψ)).U (fun _ => j) ⊓ (L'.pull q₀).U (fun _ => k))
        ⟨y, mem_pull₂.2 hy.1, mem_pull.2 hy.2⟩ (w.s (fun _ => j, fun _ => k)) g v hv p
      exact ⟨j, k, V, c, hV, hj, hk, fun Z r z h h₁ h₂ => hc Z r z h ⟨mem_pull₂.2 h₁, mem_pull.2 h₂⟩⟩
  refine ⟨w', hw', fun T g j k v hg hv Z ρ z hj hk => ?_⟩
  refine gm_eq_of_dense q₀ g _ v (fun Z ρ r z hr hz => ?_) ρ z ⟨mem_pull.2 hj, hk⟩
  have hp : q₀ (r z) = g (ρ z) := congrArg (fun f => f z) hr
  rw [← hv Z ρ r hr z, ← e Z r z j k (by rw [hp]; exact mem_pull.1 hz.1) (by rw [hp]; exact hz.2), hr]
  rfl

theorem gw_comp {Z Z' : Scheme.{0}} {L : LB Y} {L' : LB X} {F : X ⟶ Y} (w : LB.Iso L' (L.pull F)) (κ : Z' ⟶ Z)
    (z : Z') (r : Z ⟶ X) (j : L.ι) (k : L'.ι) (hj : F (r (κ z)) ∈ L.U j) (hk : r (κ z) ∈ L'.U k) :
    Units.map (κ.stalkMap z).hom.toMonoidHom (Geo.Tor.gw w r (κ z) j k) = Geo.Tor.gw w (κ ≫ r) z j k :=
  (gm_comp κ z r ((L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _).symm

theorem gw_chart {Z : Scheme.{0}} {M : LB Y} (hM : M.IsLB) {L : LB X} {F : X₀ ⟶ Y} {a : X₀ ⟶ X}
    {w : LB.Iso (L.pull a) (M.pull F)} (hw : w.IsGen) (r : Z ⟶ X₀) (z : Z) (m : M.ι) (k k' : L.ι)
    (hm : F (r z) ∈ M.U m) (hk : a (r z) ∈ L.U k) (hk' : a (r z) ∈ L.U k') :
    Geo.Tor.gw w r z m (fun _ => k) =
      (gm (r ≫ a) z _ (L.g k k'))⁻¹ * Geo.Tor.gw w r z m (fun _ => k') := by
  have := (isGen_iff w).1 hw Z r z m m (fun _ => k) (fun _ => k') hm hm (mem_pull.2 hk) (mem_pull.2 hk')
  rw [gm_pull_g L a r z _ _ (mem_pull.2 hk) (mem_pull.2 hk'), gm_self hM (r ≫ F) z hm, _root_.one_mul] at this
  exact this

theorem square_of_flat {S S' B B' T : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB Y} {L' : LB X} (hM : M.IsLB)
    (hM' : M'.IsLB) {β : B' ⟶ B} {p : S ⟶ B} {p' : S' ⟶ B'} {a : S ⟶ Y} {a' : S' ⟶ X} {ψ : X ⟶ Y} {t : S' ⟶ S}
    (hψ : a' ≫ ψ = t ≫ a) (u : LB.Iso M' (M.pull β)) {w : LB.Iso (L.pull a) (M.pull p)} (hw : w.IsGen)
    {w' : LB.Iso (L'.pull a') (M'.pull p')} (hw' : w'.IsGen) {wL : LB.Iso L' (L.pull ψ)} (hwL : wL.IsGen)
    (hp : p' ≫ β = t ≫ p) (g' : T ⟶ X) [Flat g'] (g : T ⟶ Y) (j₀ : L.ι) (k₀ : L'.ι) (v : Γ(T, ⊤)ˣ)
    (hk₀ : ⊤ ≤ g' ⁻¹ᵁ L'.U k₀) (hj₀ : ⊤ ≤ g ⁻¹ᵁ L.U j₀)
    (hg : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ S'), r ≫ a' = ρ ≫ g' → r ≫ t ≫ a = ρ ≫ g)
    (hv : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (z : Z), ψ (g' (ρ z)) ∈ L.U j₀ → g' (ρ z) ∈ L'.U k₀ →
      Geo.Tor.gw wL (ρ ≫ g') z j₀ k₀ = gm ρ z ⊤ v)
    (H : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ S') (z : Z) (m : M.ι) (m' : M'.ι), r ≫ a' = ρ ≫ g' →
      β (p' (r z)) ∈ M.U m → p' (r z) ∈ M'.U m' → a (t (r z)) ∈ L.U j₀ → a' (r z) ∈ L'.U k₀ →
      Geo.Tor.gw u (r ≫ p') z m m' * Geo.Tor.gw w' r z m' (fun _ => k₀) =
        Geo.Tor.gw w (r ≫ t) z m (fun _ => j₀) * gm ρ z ⊤ v)
    {Z : Scheme.{0}} (r : Z ⟶ S') (z : Z) (hz : a' (r z) ∈ Set.range g') (m : M.ι) (m' : M'.ι) (j : L.ι)
    (k : L'.ι) (hm : β (p' (r z)) ∈ M.U m) (hm' : p' (r z) ∈ M'.U m') (hj : a (t (r z)) ∈ L.U j)
    (hk : a' (r z) ∈ L'.U k) :
    Geo.Tor.gw u (r ≫ p') z m m' * Geo.Tor.gw w' r z m' (fun _ => k) =
      Geo.Tor.gw w (r ≫ t) z m (fun _ => j) * Geo.Tor.gw wL (r ≫ a') z j k := by
  have e₁ : ∀ x, ψ (a' x) = a (t x) := fun x => congrArg (fun f => f x) hψ
  have e₂ : ∀ x, β (p' x) = p (t x) := fun x => congrArg (fun f => f x) hp
  obtain ⟨y, hy⟩ := hz
  obtain ⟨z, rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := r ≫ a') (g := g') z y hy.symm
  have hc : (pullback.fst (r ≫ a') g' ≫ r) ≫ a' = pullback.snd (r ≫ a') g' ≫ g' := by
    rw [Category.assoc, pullback.condition]
  refine Units.map_injective (f := ((pullback.fst (r ≫ a') g').stalkMap z).hom.toMonoidHom)
    (faithfullyFlat_stalkMap_of_flat _ z).injective ?_
  rw [map_mul, map_mul, gw_comp u _ z (r ≫ p') m m' hm hm', gw_comp w' _ z r m' _ hm' (mem_pull.2 hk),
    gw_comp w _ z (r ≫ t) m _ ((e₂ _).symm ▸ hm :) (mem_pull.2 hj),
    gw_comp wL _ z (r ≫ a') j k ((e₁ _).symm ▸ hj :) hk, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  change β (p' ((pullback.fst (r ≫ a') g' ≫ r) z)) ∈ _ at hm
  change p' ((pullback.fst (r ≫ a') g' ≫ r) z) ∈ _ at hm'
  change a (t ((pullback.fst (r ≫ a') g' ≫ r) z)) ∈ _ at hj
  change a' ((pullback.fst (r ≫ a') g' ≫ r) z) ∈ _ at hk
  generalize pullback.fst (r ≫ a') g' ≫ r = s at hc hm hm' hj hk ⊢
  generalize pullback.snd (r ≫ a') g' = ρ at hc
  have e₃ : a' (s z) = g' (ρ z) := congrArg (fun f => f z) hc
  have e₄ : a (t (s z)) = g (ρ z) := congrArg (fun f => f z) (hg _ ρ s hc)
  have hk' : a' (s z) ∈ L'.U k₀ := by rw [e₃]; exact hk₀ trivial
  have hj' : a (t (s z)) ∈ L.U j₀ := by rw [e₄]; exact hj₀ trivial
  have hm₂ : p (t (s z)) ∈ M.U m := by rw [← e₂]; exact hm
  have h₁ := H _ ρ s z m m' hc hm hm' hj' hk'
  have h₂ := hv _ ρ z (by rw [← e₃, e₁]; exact hj') (by rw [← e₃]; exact hk')
  have h₃ := (isGen_iff wL).1 hwL _ (s ≫ a') z j j₀ k k₀ (by show ψ (a' (s z)) ∈ _; rw [e₁]; exact hj)
    (by show ψ (a' (s z)) ∈ _; rw [e₁]; exact hj') hk hk'
  rw [← hc] at h₂
  rw [h₃, h₂, gw_chart hM' hw' s z m' k k₀ hm' hk hk', gw_chart hM hw (s ≫ t) z m j j₀ hm₂ hj hj',
    mul_left_comm, h₁, Category.assoc s a' ψ, hψ, Category.assoc s t a]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem range_thick (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    Set.range (thick R I e) = PrimeSpectrum.zeroLocus (I : Set R) := by
  have : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) = _ :=
    range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_pow _ (Nat.succ_ne_zero e)] at this
  exact this

end GlobalTheory.BundleExt

open GlobalTheory.BundleExt in

theorem GlobalTheory.exists_bundleIso_extending_generic : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) → ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull ψ.hom.left), wL.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G').left) z jL jL' := by
  intro h₁ h₂ R _ _ _ I hI hIm D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj ΦK wK hw ψ ⟨_, hψ, hψe⟩
  have := hG'.smooth
  have : IsIntegral G'.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G'
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have := GlobalTheory.GenericExt.isOpenImmersion_jK R
  have : IsDominant (jK R) := DVR.isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsDominant (pullback.fst G'.hom (jK R)) := inferInstance
  have hF : ΦK.hom.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ ψ.hom.left := by
    rw [← hψ]
    exact pullback.lift_fst _ _ _
  have hsp : ∀ y : G'.left, G'.hom y ∈ PrimeSpectrum.zeroLocus (I : Set R) → ∃ x, (fstG I 0 G').left x = y :=
    fun y hy => by
      rw [← range_thick R I 0] at hy
      exact (Scheme.Pullback.range_fst G'.hom (thick R I 0)).ge hy
  have pts := GlobalTheory.exists_completed_point_of_thickenings R I hI hIm D D' A A' G G' hG hG' U U' hD j hj
  have fml := GlobalTheory.T.generic_iso_agrees_on_complete_points_alt h₁ h₂ R I hI hIm D D' A A' G G' hG hG' U U' hD j hj ΦK wK hw
  obtain ⟨wL, hwL, hv⟩ := exists_iso_of_flat (pullback.fst G'.hom (jK R)) U.LG.isLB U'.LG.isLB ψ.hom.left _ hF wK
    hw.1 fun y hy => by
      obtain ⟨x, rfl⟩ := hsp y (by
        have h₀ := GlobalTheory.GenericExt.eq_closedPoint_of_not_mem_range R (G'.hom y) fun h => hy (by
          rw [Scheme.Pullback.range_fst]; exact h)
        exact (hIm.trans (congrArg PrimeSpectrum.asIdeal h₀).symm).le)
      obtain ⟨B, _, _, g', g, jL, jL', hB, -, hg', ⟨p, hp⟩, H⟩ := pts x
      obtain ⟨v, hv, -⟩ := fml B g' g jL jL' hB H
      refine ⟨_, g', jL, jL', v, hg', ⟨p, hp⟩, ?_, ?_, fun Z ρ r h => (hv Z ρ r h).2⟩
      · obtain ⟨z, rfl, rfl⟩ :=
          Scheme.Pullback.exists_preimage_pullback (f := (fstG I 0 G').left) (g := g') x p hp.symm
        have e := H.2.2.2.2 0 _ _ _ (pullback.condition (f := (fstG I 0 G').left) (g := g'))
        have e' := congrArg (fun f => f z) ((congrArg (_ ≫ ·) (hψe 0)).trans e)
        exact (congrArg (· ∈ U.LG.L.U jL) e').mpr (H.2.2.2.1 trivial)
      · rw [← hp]; exact H.2.2.1 trivial
  refine ⟨wL, hwL, fun e Z r z jM jM' jL jL' m₁ m₂ m₃ m₄ => ?_⟩
  obtain ⟨x, hx⟩ := hsp ((fstG I e G').left (r z)) (by
    rw [← range_thick R I e]
    exact (Scheme.Pullback.range_fst G'.hom (thick R I e)).le ⟨r z, rfl⟩)
  obtain ⟨B, _, _, g', g, j₀, k₀, hB, -, hg', hp, H⟩ := pts x
  obtain ⟨v, hv₁, hv₂⟩ := fml B g' g j₀ k₀ hB H
  exact square_of_flat D.toPre.P.isLB D'.toPre.P.isLB (hψe e) hD.w (U.w_gen e) (U'.w_gen e) hwL (hj e).2.2.1
    g' g j₀ k₀ v H.2.2.1 H.2.2.2.1 (H.2.2.2.2 e) (hv _ g' j₀ k₀ v hg' fun Z ρ r h => (hv₁ Z ρ r h).2) (hv₂ e)
    r z (hx ▸ hp) jM jM' jL jL' m₁ m₂ m₃ m₄
