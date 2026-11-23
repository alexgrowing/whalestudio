import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVDefect
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVCat

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem specMap_appTop_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  intro a b hab
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have ha := congrArg (fun g => g.hom a) n
  have hb := congrArg (fun g => g.hom b) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at ha hb
  rw [hab, hb] at ha
  have h2 := hf ha
  have i := (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
  have ia := congrArg (fun g => g.hom a) i
  have ib := congrArg (fun g => g.hom b) i
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at ia ib
  rw [← ia, ← ib, h2]

theorem pullCubDescent (hExt : extendGenSt.{0}) (hGF : GlobalFnsDvrSt) : PullCubDescentSt := by
  intro E _ _ _ H V _ _ _ hc t t' tK hK m m' ψ hψm hψ
  obtain ⟨w₁, p₁, r₁, θ₁⟩ := (isPullCubical_iff m.cm t.cub tK.cub).1 m.lin
  obtain ⟨w₂, p₂, r₂, θ₂⟩ := (isPullCubical_iff m'.cm t'.cub tK.cub).1 m'.lin
  obtain ⟨io, hiom, hio⟩ := extV_genIso t tK m
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  haveI := t.semi.geomConnected
  let ja : (genFibre V t.G).left ⟶ t.G.left := pullback.fst t.G.hom (specMap V (FractionRing V))
  have h₁ : io.hom.left ≫ m.φ = ja := hio
  have h₂ : io.hom.left ≫ m'.φ = ja ≫ ψ.left := by rw [← hψ, ← Category.assoc, h₁]
  let N : RigLB t.G := ⟨LB.div (t'.PP.L.pull ψ.left) t.PP.L,
    divPullGen (eSec t.G) t.PP.rig ((CubeMap.ofHom ψ).rigPull t'.PP.L t'.PP.rig),
    LB.isLB_div (pull_isLB t'.PP.isLB ψ.left) t.PP.isLB,
    divPullGen_isGen _ _ _ t.PP.rigGen (rigPullOf_isGen _ _ _ _ _ t'.PP.rigGen)⟩
  obtain ⟨r, hr⟩ := exists_gen_ratio ψ.left m.φ m'.φ io.hom.left ja h₁ h₂ tK.PP.isLB t.PP.isLB t'.PP.isLB w₁ w₂ p₁ p₂
  have hrg := gen_ratio_isGen ψ.left m.φ m'.φ io.hom.left ja h₁ h₂ tK.PP.isLB w₁ w₂ p₁ p₂ r hr
  let eA : Spec (CommRingCat.of (FractionRing V)) ⟶ genA V (FractionRing V) t.G := eSec tK.G ≫ io.inv.left
  have e2 : eA ≫ io.hom.left = eSec tK.G := by
    show (eSec tK.G ≫ io.inv.left) ≫ io.hom.left = _
    rw [Category.assoc, ← Over.comp_left, io.inv_hom_id, Over.id_left, Category.comp_id]
  have e3 : eA ≫ ja = eSec tK.G ≫ m.φ := by rw [← h₁, ← Category.assoc, e2]
  have heA : eA ≫ jA V (FractionRing V) t.G = eK V (FractionRing V) t.G := by
    show eA ≫ ja = etaK V (FractionRing V) ≫ eSec t.G
    rw [e3]
    exact m.cm.e_comm.trans (by rw [m.base])
  have eJ : (𝟙 _ ≫ etaK V (FractionRing V)) ≫ eSec t.G = (𝟙 _ ≫ eA) ≫ ja := by
    rw [Category.id_comp, Category.id_comp]; exact heA.symm
  have hNrig : ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left) → N.L.ι),
      Good N.L y J → val N.rig (𝟙 _ ≫ etaK V (FractionRing V)) y J =
        gm ((𝟙 _ ≫ etaK V (FractionRing V)) ≫ 𝟙 _) y _ (t'.PP.rig.s (fun _ => (J ((𝟙 _ ≫ eA) ≫ ja)).1 ⟨⟩)) *
          (gm (𝟙 _ ≫ etaK V (FractionRing V)) y _ (t.PP.rig.s (fun _ => (J ((𝟙 _ ≫ eA) ≫ ja)).2)))⁻¹ := by
    intro y J hJ
    have hQ : J ((𝟙 _ ≫ etaK V (FractionRing V)) ≫ eSec t.G) = J ((𝟙 _ ≫ eA) ≫ ja) := by rw [eJ]
    rw [val_of N.rig (𝟙 _ ≫ etaK V (FractionRing V)) y J (fun _ => J ((𝟙 _ ≫ eA) ≫ ja)) (fun _ => hQ)]
    have hz : (𝟙 _ ≫ etaK V (FractionRing V)) y ∈
        ((LB.div (t'.PP.L.pull ψ.left) t.PP.L).pull (eSec t.G)).U (fun _ => J ((𝟙 _ ≫ eA) ≫ ja)) := by
      have := hJ.mem (fun _ : PUnit => eSec t.G) (𝟙 _ ≫ etaK V (FractionRing V))
      rw [hQ] at this
      exact this
    exact (gm_divPullGen (eSec t.G) t.PP.rig ((CubeMap.ofHom ψ).rigPull t'.PP.L t'.PP.rig)
      (𝟙 _ ≫ etaK V (FractionRing V)) y (fun _ => J ((𝟙 _ ≫ eA) ≫ ja)) hz).trans
      (congrArg₂ (fun a b => a * b⁻¹) (gm_rigPullOf ψ.left (𝟙 _) _ t'.PP.L t'.PP.rig
        (𝟙 _ ≫ etaK V (FractionRing V)) y _ (le_div_left (eSec t.G) _ hz)) rfl)
  have hcorr : LB.Gen.Corr N.L _ _ _ _ (LB.pullGen N.L _ _ r eA) (LB.pullGen N.L _ _ N.rig (etaK V (FractionRing V))) := by
    refine corr_of_val N.isLB fun y J hJ => ?_
    rw [val_pull hJ, val_pull hJ]
    have hm := hJ ((𝟙 _ ≫ eA) ≫ ja)
    obtain ⟨k₂, hk₂⟩ := exists_chart tK.PP.isLB (eSec tK.G y)
    have pe : io.hom.left ((𝟙 _ ≫ eA) y) = eSec tK.G y :=
      congrArg (fun g : Spec (CommRingCat.of (FractionRing V)) ⟶ tK.G.left => g y)
        (show (𝟙 _ ≫ eA) ≫ io.hom.left = eSec tK.G by rw [Category.id_comp]; exact e2)
    have pm : ((𝟙 _ ≫ eA) ≫ ja) y = m.φ (eSec tK.G y) :=
      congrArg (fun g : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => g y)
        (show (𝟙 _ ≫ eA) ≫ ja = eSec tK.G ≫ m.φ by rw [Category.id_comp]; exact e3)
    have mem3 : io.hom.left ((𝟙 _ ≫ eA) y) ∈ tK.PP.L.U k₂ := by rw [pe]; exact hk₂
    have hL := hr _ (𝟙 _ ≫ eA) y ((J ((𝟙 _ ≫ eA) ≫ ja)).1 ⟨⟩) (J ((𝟙 _ ≫ eA) ≫ ja)).2 k₂
      ((mem_pull_iff ψ.left _ _).1 hm.1) hm.2 mem3
    have hval : val r (𝟙 _ ≫ eA) y J =
        gw w₂ ((𝟙 _ ≫ eA) ≫ io.hom.left) y ((J ((𝟙 _ ≫ eA) ≫ ja)).1 ⟨⟩) k₂ *
          (gw w₁ ((𝟙 _ ≫ eA) ≫ io.hom.left) y (J ((𝟙 _ ≫ eA) ≫ ja)).2 k₂)⁻¹ := hL
    rw [hval]
    have e4 : (𝟙 _ ≫ eA) ≫ io.hom.left = 𝟙 _ ≫ eSec tK.G := by rw [Category.id_comp, Category.id_comp, e2]
    rw [e4]
    rw [hNrig y J hJ]
    have mφ : m.φ (eSec tK.G y) ∈ t.PP.L.U (J ((𝟙 _ ≫ eA) ≫ ja)).2 := pm ▸ hm.2
    have mφ' : m'.φ (eSec tK.G y) ∈ t'.PP.L.U ((J ((𝟙 _ ≫ eA) ≫ ja)).1 ⟨⟩) := by
      have h' : m'.φ (eSec tK.G y) = ψ.left (((𝟙 _ ≫ eA) ≫ ja) y) := by
        rw [pm]; exact congrArg (fun g : tK.G.left ⟶ t'.G.left => g (eSec tK.G y)) hψ.symm
      rw [h']; exact (mem_pull_iff ψ.left _ _).1 hm.1
    have q₁ := r₁ _ (𝟙 _) y (fun _ => (J ((𝟙 _ ≫ eA) ≫ ja)).2) (fun _ => k₂) (fun _ => mφ) (fun _ => hk₂)
    have q₂ := r₂ _ (𝟙 _) y (fun _ => (J ((𝟙 _ ≫ eA) ≫ ja)).1 ⟨⟩) (fun _ => k₂) (fun _ => mφ') (fun _ => hk₂)
    simp only [Fintype.prod_unique, zpow_one] at q₁ q₂
    have b₁ : 𝟙 _ ≫ m.cm.e = 𝟙 _ ≫ etaK V (FractionRing V) := by rw [m.base]; rfl
    have b₂ : 𝟙 _ ≫ m'.cm.e = (𝟙 _ ≫ etaK V (FractionRing V)) ≫ 𝟙 _ := by rw [m'.base, Category.comp_id]; rfl
    rw [b₁] at q₁
    rw [b₂] at q₂
    refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹) q₂ q₁).symm
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨w, ⟨hwg, hwpull⟩, -⟩ := hExt V (FractionRing V) t.G eA heA N r hrg hcorr
  rw [isPullCubical_iff]
  refine ⟨w, (isGen_iff w).1 hwg, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := exists_defect t'.PP.isLB t.PP.isLB w ((isGen_iff w).1 hwg) t.PP.rig t.PP.rigGen t'.PP.rig
      t'.PP.rigGen (CubeMap.ofHom ψ).e (fun _ => (CubeMap.ofHom ψ).e_comm)
    have key : ∀ y₀ : Spec (CommRingCat.of (FractionRing V)), gm (𝟙 _ ≫ etaK V (FractionRing V)) y₀ ⊤ u = 1 := by
      intro y₀
      choose J hJ using fun χ : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => exists_chart N.isLB (χ y₀)
      have hG : Good N.L y₀ J := hJ
      have hv := val_corr hG hcorr (𝟙 _)
      rw [val_pull hG, val_pull hG, hNrig y₀ J hG, ← hwpull] at hv
      have hP := hG ((𝟙 _ ≫ eA) ≫ ja)
      have pJ : ∀ x, ((𝟙 _ ≫ etaK V (FractionRing V)) ≫ eSec t.G) x = ((𝟙 _ ≫ eA) ≫ ja) x :=
        fun x => congrArg (fun g : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => g x) eJ
      have hw' : gw w ((𝟙 _ ≫ etaK V (FractionRing V)) ≫ eSec t.G) y₀ ((J ((𝟙 _ ≫ eA) ≫ ja)).1 ⟨⟩)
          (J ((𝟙 _ ≫ eA) ≫ ja)).2 = val (LB.genPull N.L w (jA V (FractionRing V) t.G)) (𝟙 _ ≫ eA) y₀ J := by
        show _ = gm (𝟙 _ ≫ eA) y₀ _ (res _ (pullU _ _ (w.s _)))
        rw [eJ]
        exact ((gm_res _ y₀ _ (hG.mem _ _) _).trans (gm_pull _ _ y₀ _ hP _)).symm
      have m1 : ψ.left (eSec t.G ((𝟙 _ ≫ etaK V (FractionRing V)) y₀)) ∈ t'.PP.L.U ((J ((𝟙 _ ≫ eA) ≫ ja)).1 ⟨⟩) := by
        have := (mem_pull_iff ψ.left _ _).1 hP.1
        rw [← pJ] at this
        exact this
      have m2 : eSec t.G ((𝟙 _ ≫ etaK V (FractionRing V)) y₀) ∈ t.PP.L.U (J ((𝟙 _ ≫ eA) ≫ ja)).2 := by
        have := hP.2
        rw [← pJ] at this
        exact this
      have hu' := hu _ (𝟙 _ ≫ etaK V (FractionRing V)) y₀ (fun _ => (J ((𝟙 _ ≫ eA) ≫ ja)).1 ⟨⟩)
        (fun _ => (J ((𝟙 _ ≫ eA) ≫ ja)).2) (fun _ => m1) (fun _ => m2)
      simp only [Fintype.prod_unique, zpow_one] at hu'
      rw [hw', hv] at hu'
      exact mul_eq_right.mp ((congrArg (fun x => gm (𝟙 _ ≫ etaK V (FractionRing V)) y₀ ⊤ u * x)
        (inv_mul_cancel_right _ _)).symm.trans hu'.symm)
    have h1 : pullU (etaK V (FractionRing V)) ⊤ u = 1 := unit_ext fun y _ => by
      rw [gm_pull (𝟙 _) (etaK V (FractionRing V)) y ⊤ trivial, map_one]
      exact key y
    have hu1 : u = 1 := by
      apply Units.ext
      have := congrArg Units.val h1
      exact specMap_appTop_injective _ (IsFractionRing.injective V (FractionRing V)) (this.trans (by simp; rfl))
    intro Z r z p q hp hq
    rw [hu Z r z p q hp hq, hu1, map_one, _root_.one_mul]
    rfl
  · obtain ⟨u, hu⟩ := exists_defect t'.PP.isLB t.PP.isLB w ((isGen_iff w).1 hwg) t.cub.t t.cub.isGen t'.cub.t
      t'.cub.isGen (CubeMap.ofHom ψ).F3 (fun I => (CubeMap.ofHom ψ).psum_comm I.down)
    have hF3 : eSec (G3 t.G) ≫ (CubeMap.ofHom ψ).F3 = eSec (G3 t'.G) := by
      show (η[G3 t.G]).left ≫ (ψ ⊗ₘ ψ ⊗ₘ ψ).left = (η[G3 t'.G]).left
      rw [← Over.comp_left, eta_eq_one, eta_eq_one]
      congr 1
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, tensorHom_fst, tensorHom_fst_assoc, tensorHom_snd_assoc]
        simp only [← Category.assoc, MonObj.one_comp]
      · apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, tensorHom_fst, tensorHom_snd, tensorHom_fst_assoc, tensorHom_snd_assoc]
          simp only [← Category.assoc, MonObj.one_comp]
        · simp only [Category.assoc, tensorHom_fst, tensorHom_snd, tensorHom_fst_assoc, tensorHom_snd_assoc]
          simp only [← Category.assoc, MonObj.one_comp]
    have hsum : (∑ I : thK.{0}, thε I) = 0 := by decide
    have key : ∀ z : (𝟙_ (Over (Sp V))).left, gm (eSec (G3 t.G)) z ⊤ u = 1 := by
      intro z
      obtain ⟨p₀, hp₀⟩ := exists_chart t'.PP.isLB (eSec t'.G z)
      obtain ⟨q₀, hq₀⟩ := exists_chart t.PP.isLB (eSec t.G z)
      have pt' : ∀ I, (eSec (G3 t.G) ≫ thφ t.G (x3 t.G) I ≫ ψ.left) z = eSec t'.G z := fun I =>
        congrArg (fun g : (𝟙_ (Over (Sp V))).left ⟶ t'.G.left => g z)
          (by rw [← Category.assoc, eSec_thφ]; exact (CubeMap.ofHom ψ).e_comm.trans (Category.id_comp _))
      have pt₁ : ∀ I, (eSec (G3 t.G) ≫ thφ t.G (x3 t.G) I) z = eSec t.G z := fun I =>
        congrArg (fun g : (𝟙_ (Over (Sp V))).left ⟶ t.G.left => g z) (eSec_thφ t.G I)
      have hu' := hu _ (eSec (G3 t.G)) z (fun _ => p₀) (fun _ => q₀)
        (fun I => (congrArg (· ∈ t'.PP.L.U p₀) (pt' I)).mpr hp₀)
        (fun I => (congrArg (· ∈ t.PP.L.U q₀) (pt₁ I)).mpr hq₀)
      have c₁ := cub_at_one t.G t.cub z q₀ hq₀
      have c₂ := cub_at_one t'.G t'.cub z p₀ hp₀
      rw [hF3] at hu'
      have hprod : ∏ I : thK, gw w (eSec (G3 t.G) ≫ thφ t.G (x3 t.G) I) z p₀ q₀ ^ thε I = 1 := by
        simp only [eSec_thφ]
        apply Additive.ofMul.injective
        simp only [ofMul_prod, ofMul_zpow, ofMul_one, ← Finset.sum_smul]
        rw [hsum, zero_smul]
      have h2 : gm (eSec (G3 t.G)) z ⊤ u *
          ((∏ I : thK, gw w (eSec (G3 t.G) ≫ thφ t.G (x3 t.G) I) z p₀ q₀ ^ thε I) * 1) = 1 :=
        (congrArg (fun y => gm (eSec (G3 t.G)) z ⊤ u *
          ((∏ I : thK, gw w (eSec (G3 t.G) ≫ thφ t.G (x3 t.G) I) z p₀ q₀ ^ thε I) * y)) c₁).symm.trans
            (hu'.symm.trans c₂)
      rw [hprod, _root_.mul_one, _root_.mul_one] at h2
      exact h2
    have hprop : IsProper ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj t.G).hom := by
      haveI : IsIso io.hom.left := ⟨⟨io.inv.left, by rw [← Over.comp_left, io.hom_inv_id, Over.id_left],
        by rw [← Over.comp_left, io.inv_hom_id, Over.id_left]⟩⟩
      rw [← Over.w io.hom]
      infer_instance
    have hbij := hGF E H V hc t hprop 3
    let E : G3 t.G ≅ powObj t.G 3 := whiskerLeftIso t.G (whiskerLeftIso t.G (ρ_ t.G).symm)
    let e : G3 t.G ⟶ powObj t.G 3 := E.hom
    let e' : powObj t.G 3 ⟶ G3 t.G := E.inv
    have ee' : e ≫ e' = 𝟙 _ := E.hom_inv_id
    have he : e.left ≫ (powObj t.G 3).hom = (G3 t.G).hom := Over.w e
    obtain ⟨a, ha⟩ := hbij.2 ((e'.left).appTop.hom u.val)
    have hu_a : (G3 t.G).hom.appTop.hom a = u.val := by
      rw [← he, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ha, ← RingHom.comp_apply,
        ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← Over.comp_left, ee', Over.id_left]
      simp
    have hs : eSec (G3 t.G) ≫ (G3 t.G).hom = 𝟙 _ := Over.w η[G3 t.G]
    have hpu : pullU (eSec (G3 t.G)) ⊤ u = 1 := unit_ext fun y _ => by
      rw [gm_pull (𝟙 _) _ y ⊤ trivial, Category.id_comp, map_one]
      exact key y
    have ha1 : a = 1 := by
      have h1 := congrArg Units.val hpu
      have h2 : (eSec (G3 t.G) ≫ (G3 t.G).hom).appTop.hom a = (eSec (G3 t.G)).appTop.hom u.val := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hu_a]
      rw [hs] at h2
      have h3 : a = (eSec (G3 t.G)).appTop.hom u.val := h2
      rw [h3]
      exact h1.trans (by simp; rfl)
    have hu1 : u = 1 := Units.ext (by rw [← hu_a, ha1, map_one]; rfl)
    intro Z r z p q hp hq
    exact (hu Z r z p q hp hq).trans (by rw [hu1, map_one, _root_.one_mul]; rfl)

theorem extV_holds (hHom : HomExtDvrSt) (hExt : extendGenSt.{0}) (hGF : GlobalFnsDvrSt) : ExtVStatement :=
  extV_of hHom (pullCubDescent hExt hGF)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
