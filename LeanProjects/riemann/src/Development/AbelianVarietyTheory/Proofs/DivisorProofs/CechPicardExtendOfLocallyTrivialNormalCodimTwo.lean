import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundles
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExtendClass

open GlobalTheory.GlueLineBundle TopologicalSpace

variable {X : Scheme.{0}}

theorem gm_eq_map {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (hy : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U hy, Units.coe_map, gm_val (𝟙 X) (f y) U hy]
  show _ = (f.stalkMap y).hom ((X.presheaf.germ U (f y) hy).hom a.val)
  rw [Scheme.Hom.germ_stalkMap_apply]

theorem map_stalk_inj {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    Function.Injective (Units.map (j.stalkMap y).hom.toMonoidHom) :=
  Units.map_injective (f := (j.stalkMap y).hom.toMonoidHom)
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective

theorem exists_res_eq {U V : X.Opens} (h : V ≤ U) (hb : Function.Bijective (resG X h)) (u : Γ(X, V)ˣ) :
    ∃ a : Γ(X, U)ˣ, res h a = u := by
  obtain ⟨a, ha⟩ := hb.2 u.val
  obtain ⟨b, hb'⟩ := hb.2 u.inv
  have e1 : a * b = 1 := hb.1 (by rw [map_mul, map_one, ha, hb']; exact u.val_inv)
  exact ⟨⟨a, b, e1, (mul_comm _ _).trans e1⟩, Units.ext ha⟩

theorem eq_of_gm_ι (W : X.Opens) (hW : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)))
    {V : X.Opens} {a b : Γ(X, V)ˣ} (h : ∀ w : W.toScheme, W.ι w ∈ V → gm W.ι w V a = gm W.ι w V b) : a = b := by
  have e : res (inf_le_left : V ⊓ W ≤ V) a = res inf_le_left b := by
    apply unit_ext_imm
    intro x hx
    have hxW : x ∈ W := hx.2
    have hxV : x ∈ V := hx.1
    have hx' : W.ι ⟨x, hxW⟩ ∈ V ⊓ W := hx
    refine ⟨_, W.ι, inferInstance, ⟨x, hxW⟩, rfl, ?_⟩
    exact (gm_res W.ι _ inf_le_left hx' a).trans ((h _ hxV).trans (gm_res W.ι _ inf_le_left hx' b).symm)
  exact Units.ext ((hW V).1 (congrArg Units.val e))

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace
variable {X : Scheme.{0}}

theorem exists_sigma (W : X.Opens) {M : LB W.toScheme} (N : X.Opens)
    (t : LB.Gen (M.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)))) (ht : t.IsGen) :
    ∃ σ : ∀ k, Γ(W.toScheme, W.ι ⁻¹ᵁ N ⊓ M.U k)ˣ, ∀ (z : W.toScheme) (k k' : M.ι), W.ι z ∈ N → z ∈ M.U k →
      z ∈ M.U k' → gm (𝟙 _) z _ (σ k) = gm (𝟙 _) z (M.U k ⊓ M.U k') (M.g k k') * gm (𝟙 _) z _ (σ k') := by
  revert t
  set ι₁ := X.homOfLE (inf_le_right : N ⊓ W ≤ W) with hι₁
  intro t ht
  have pre : ∀ z : W.toScheme, W.ι z ∈ N → ∃ a : (N ⊓ W : X.Opens).toScheme, ι₁ a = z := fun z hz =>
    ⟨⟨z.1, hz, z.2⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have hle : ∀ k, W.ι ⁻¹ᵁ N ⊓ M.U k ≤ ι₁ ''ᵁ (M.pull ι₁).U (fun _ => k) := fun k z hz => by
    obtain ⟨a, rfl⟩ := pre z hz.1
    exact ι₁.apply_mem_image_iff.2 (mem_pull.2 hz.2)
  refine ⟨fun k => res (hle k) (imU ι₁ _ (t.s fun _ => k)), fun z k k' hz hk hk' => ?_⟩
  obtain ⟨a, rfl⟩ := pre z hz
  have ev : ∀ k, ι₁ a ∈ M.U k → gm ι₁ a (W.ι ⁻¹ᵁ N ⊓ M.U k) (res (hle k) (imU ι₁ _ (t.s fun _ => k))) =
      gm (𝟙 _) a _ (t.s fun _ => k) := fun k hk => by
    have hm : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k := ⟨hz, hk⟩
    rw [gm_res ι₁ a (hle k) hm]
    have := gm_imU ι₁ (𝟙 _) a ((M.pull ι₁).U fun _ => k) (mem_pull.2 hk) (t.s fun _ => k)
    rwa [Category.id_comp] at this
  have eg : gm ι₁ a (M.U k ⊓ M.U k') (M.g k k') = gm (𝟙 _) a _ ((M.pull ι₁).g (fun _ => k) (fun _ => k')) := by
    have := gm_pull_g M ι₁ (𝟙 _) a (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
    rw [Category.id_comp] at this
    exact this.symm
  have m1 : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k := ⟨hz, hk⟩
  have m2 : ι₁ a ∈ M.U k ⊓ M.U k' := ⟨hk, hk'⟩
  have m3 : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k' := ⟨hz, hk'⟩
  apply map_stalk_inj ι₁ a
  beta_reduce
  rw [map_mul, ← gm_eq_map ι₁ a _ m1, ← gm_eq_map ι₁ a _ m2, ← gm_eq_map ι₁ a _ m3,
    ev k hk, ev k' hk', eg]
  exact (isGen_iff_germ t).1 ht a (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace
variable {X : Scheme.{0}}

theorem mul_ringHom_units_ratio {G : Type} [CommGroup G] (g a b : G) : g * a * (g * b)⁻¹ = a * b⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (W : X.Opens) {M : LB W.toScheme} (hM : M.IsLB) {I : Type} (N : I → X.Opens)
    (σ : ∀ x k, Γ(W.toScheme, W.ι ⁻¹ᵁ N x ⊓ M.U k)ˣ)
    (hσ : ∀ x (z : W.toScheme) (k k' : M.ι), W.ι z ∈ N x → z ∈ M.U k → z ∈ M.U k' →
      gm (𝟙 _) z _ (σ x k) = gm (𝟙 _) z (M.U k ⊓ M.U k') (M.g k k') * gm (𝟙 _) z _ (σ x k')) (x y : I) :
    ∃ r : Γ(W.toScheme, W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y)ˣ, ∀ (z : W.toScheme) (k : M.ι), W.ι z ∈ N x → W.ι z ∈ N y →
      z ∈ M.U k → gm (𝟙 _) z _ r = gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ := by
  let O : M.ι → W.toScheme.Opens := fun k => W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y ⊓ M.U k
  have l0 : ∀ k, O k ≤ W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y := fun k => inf_le_left
  have lx : ∀ k, O k ≤ W.ι ⁻¹ᵁ N x ⊓ M.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have ly : ∀ k, O k ≤ W.ι ⁻¹ᵁ N y ⊓ M.U k := fun k z hz => ⟨hz.1.2, hz.2⟩
  have ev : ∀ k (z : W.toScheme) (hz : z ∈ O k),
      gm (𝟙 _) z (O k) (res (ly k) (σ y k) * (res (lx k) (σ x k))⁻¹) =
        gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ := fun k z hz => by
    rw [map_mul, map_inv, gm_res _ z (ly k) hz, gm_res _ z (lx k) hz]
  obtain ⟨r, hr⟩ := glue_unit _ O l0 (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hM z
      exact Opens.mem_iSup.2 ⟨k, show z ∈ O k from ⟨hz, hk⟩⟩) (fun k => res (ly k) (σ y k) * (res (lx k) (σ x k))⁻¹)
    (fun k k' z hz => by
      have h1 : z ∈ O k := hz.1
      have h2 : z ∈ O k' := hz.2
      have hx : W.ι z ∈ N x := h1.1.1
      have hy : W.ι z ∈ N y := h1.1.2
      have hk : z ∈ M.U k := h1.2
      have hk' : z ∈ M.U k' := h2.2
      rw [ev k z h1, ev k' z h2, hσ x z k k' hx hk hk', hσ y z k k' hy hk hk', mul_ringHom_units_ratio])
  refine ⟨r, fun z k hx hy hk => ?_⟩
  have hz : z ∈ O k := ⟨⟨hx, hy⟩, hk⟩
  rw [← gm_res _ z (l0 k) hz, hr k, ev k z hz]

theorem exists_ext (W : X.Opens) (hW : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)))
    (P Q : X.Opens) (r : Γ(W.toScheme, W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q)ˣ) :
    ∃ g : Γ(X, P ⊓ Q)ˣ, ∀ z : W.toScheme, W.ι z ∈ P → W.ι z ∈ Q → gm W.ι z (P ⊓ Q) g = gm (𝟙 _) z _ r := by
  have hle : P ⊓ Q ⊓ W ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q) := fun p hp => by
    have hpW : p ∈ W := hp.2
    have hpP : p ∈ P := hp.1.1
    have hpQ : p ∈ Q := hp.1.2
    have hm : (⟨p, hpW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q := ⟨hpP, hpQ⟩
    exact W.ι.apply_mem_image_iff.2 hm
  obtain ⟨g, hg⟩ := exists_res_eq (inf_le_left : P ⊓ Q ⊓ W ≤ P ⊓ Q) (hW _) (res hle (imU W.ι _ r))
  refine ⟨g, fun z hP hQ => ?_⟩
  have hz : W.ι z ∈ P ⊓ Q ⊓ W := ⟨⟨hP, hQ⟩, z.2⟩
  rw [← gm_res W.ι z inf_le_left hz, hg, gm_res W.ι z hle hz]
  have := gm_imU W.ι (𝟙 _) z _ (show z ∈ W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q from ⟨hP, hQ⟩) r
  rwa [Category.id_comp] at this

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace

theorem commGroup_cocycle_mul_inv_mul_mul_inv {G : Type} [CommGroup G] (a b c : G) : b * a⁻¹ * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commGroup_inv_eq_conj_twist_identity {G : Type} [CommGroup G] (a b g : G) : a⁻¹ = g * b * a⁻¹ * g⁻¹ * b⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.ExtendClass

open GlobalTheory.GlueLineBundle TopologicalSpace GlobalTheory.ExtendClass in

theorem GlobalTheory.extend_class_of_locally_trivial : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ W : X.Opens, (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic W.toScheme, (∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0) → ∃ c' : Pic X, GlobalTheory.CechPic.pull W.ι c' = c := by
  intro X _ hX W hW c hc
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have hbij : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)) :=
    ((extension_over_codim_two X hX).1 W hW).1
  choose N hN ht using hc
  have ht' : ∀ x, ∃ t : LB.Gen (M.pull (X.homOfLE (inf_le_right : N x ⊓ W ≤ W))), t.IsGen := fun x =>
    (cls_eq_zero_iff (pull_isLB hM _)).1 (ht x)
  choose t htg using ht'
  choose σ hσ using fun x => exists_sigma W (N x) (t x) (htg x)
  choose r hr using exists_ratio W hM N σ hσ
  choose g hg using fun x y => exists_ext W hbij (N x) (N y) (r x y)
  let L : LB X := ⟨↥X, N, g⟩
  have hgr : ∀ x y (z : W.toScheme) k, W.ι z ∈ N x → W.ι z ∈ N y → z ∈ M.U k →
      gm W.ι z (N x ⊓ N y) (g x y) = gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ :=
    fun x y z k hx hy hk => (hg x y z hx hy).trans (hr x y z k hx hy hk)
  have hL : L.IsLB :=
    { cover := top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hN x⟩
      g_self := fun x => eq_of_gm_ι W hbij fun z hz => by
        obtain ⟨k, hk⟩ := exists_chart hM z
        dsimp only [L]
        rw [gm_res W.ι z _ hz, map_one]
        exact (hgr x x z k hz hz hk).trans (mul_inv_cancel _)
      cocycle := fun x y w => eq_of_gm_ι W hbij fun z hz => by
        obtain ⟨k, hk⟩ := exists_chart hM z
        have hx : W.ι z ∈ N x := hz.1.1
        have hy : W.ι z ∈ N y := hz.1.2
        have hw : W.ι z ∈ N w := hz.2
        have h1 : W.ι z ∈ N x ⊓ N y := ⟨hx, hy⟩
        have h2 : W.ι z ∈ N y ⊓ N w := ⟨hy, hw⟩
        have h3 : W.ι z ∈ N x ⊓ N w := ⟨hx, hw⟩
        dsimp only [L] at hz ⊢
        rw [map_mul, gm_res W.ι z _ hz, gm_res W.ι z _ hz, gm_res W.ι z _ hz]
        rw [hgr x y z k hx hy hk, hgr y w z k hy hw hk, hgr x w z k hx hw hk, commGroup_cocycle_mul_inv_mul_mul_inv] }
  have hle : ∀ p : (PUnit → L.ι) × M.ι, (L.pull W.ι).U p.1 ⊓ M.U p.2 ≤ W.ι ⁻¹ᵁ N (p.1 PUnit.unit) ⊓ M.U p.2 :=
    fun p z hz => ⟨mem_pull.1 hz.1, hz.2⟩
  let w : LB.Iso M (L.pull W.ι) := ⟨fun p => res (hle p) (σ (p.1 PUnit.unit) p.2)⁻¹⟩
  have ew : ∀ (p : (PUnit → L.ι) × M.ι) (z : W.toScheme) (hz : z ∈ (L.pull W.ι).U p.1 ⊓ M.U p.2),
      gm (𝟙 _) z _ (w.s p) = (gm (𝟙 _) z _ (σ (p.1 PUnit.unit) p.2))⁻¹ := fun p z hz =>
    (gm_res _ z (hle p) hz _).trans (map_inv _ _)
  have hw : w.IsGen := by
    rintro ⟨J, k⟩ ⟨J', k'⟩
    apply unit_ext
    intro z hz
    have hj : W.ι z ∈ L.U (J PUnit.unit) := mem_pull.1 hz.1.1
    have hj' : W.ι z ∈ L.U (J' PUnit.unit) := mem_pull.1 hz.2.1
    have hk : z ∈ M.U k := hz.1.2
    have hk' : z ∈ M.U k' := hz.2.2
    have e := gm_div_g (L := L) (L' := M) (F := W.ι) (𝟙 _) z (J PUnit.unit) (J' PUnit.unit) k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    have e' : gm (𝟙 _) z _ ((LB.div (L.pull W.ι) M).g (J, k) (J', k')) = _ := e
    refine (gm_res _ z inf_le_left hz _).trans ?_
    rw [map_mul, gm_res _ z inf_le_right hz, e', ew _ z hz.1, ew _ z hz.2]
    show _ = gm W.ι z (N (J PUnit.unit) ⊓ N (J' PUnit.unit)) (g (J PUnit.unit) (J' PUnit.unit)) * _ * _
    rw [hgr _ _ z k hj hj' hk, hσ (J' PUnit.unit) z k k' hj' hk hk']
    exact commGroup_inv_eq_conj_twist_identity _ _ _
  refine ⟨cls L hL, ?_⟩
  rw [← cls_pull hL W.ι (pull_isLB hL _)]
  exact (cls_eq_iff _ _).2 (LBIso.symm ⟨w, hw⟩)
