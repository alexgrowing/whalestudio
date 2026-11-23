import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSection
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

section Transport

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {P B : LB Y}

def isoSec (w : LB.Iso P B) (hw : w.IsGen) : (LB.div B P).Sec := ⟨fun i => (w.s i : _), fun i j => by
  have := congrArg Units.val (hw i j)
  rw [Units.val_mul] at this
  exact this⟩

theorem val_congr_pt {O : Y.Opens} {R : Type} [CommRing R] {x x' : Sp R ⟶ Y} (h : x = x') (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hO' : ⊤ ≤ x' ⁻¹ᵁ O) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst h; rfl

theorem val_restr_eq {O O' : Y.Opens} (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ Y) (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

end Transport

set_option maxHeartbeats 1000000 in

theorem exists_rule_of_cls_pull : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  intro D T j Y e o hG hE Z TF la L hL hc
  have hP : (L.pull (π₀ TF.X Z)).IsLB := LB.isLB_pull hL _
  have hB := isLB_L₀ TF.X Z la
  obtain ⟨w, hw⟩ := (cls_eq_iff hP hB).1 ((cls_pull hL _ hP).trans hc)
  let C := divChart hB hP
  let G : H0 (str₀ TF.X Z) (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))) ⊤ := H0.ofSec _ ⊤ (isoSec w hw)
  let sOf : H0 (s₀ TF.Y Z) L ⊤ → H0 (str₀ TF.X Z) (L₀ TF.X Z la) ⊤ := fun t =>
    C.mul (H0.pull (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) G
  choose f hf hf' using fun t => exists_suppOn_sec₀_eq _ _ _ _ _ _ _ _ _ (AllWt.exOf _ la 0) (H0.restr le_top (sOf t))
  refine ⟨fun t => (f t).1, fun t ht => ?_, fun yy v hv k hk => ?_⟩
  · have hs : sOf t ∈ vanBd TF.X Z la := (mem_vanBd _ _).2 fun y hy hn => by
      obtain ⟨τ, ha, hb, hcc⟩ := C.cover y
      have u1 : IsUnit (H0.germ (C.c τ) y (memTop y) hcc (sOf t)) := by
        rw [← ger_toSec]; exact (isUnit_ger_iff _ hcc).2 hn
      have e3 := C.germ_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G τ y (memTop y) ha hb hcc
      have u1' : IsUnit (H0.germ (C.a τ) y (memTop y) ha
          (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) *
          H0.germ (C.b τ) y (memTop y) hb G) := (congrArg IsUnit e3).mp u1
      have u2 := (congrArg IsUnit (H0.germ_pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top (C.a τ) y (memTop y) ha t)).mp
        (isUnit_of_mul_isUnit_left u1')
      have u3 := (isUnit_map_iff (Scheme.Hom.stalkMap (π₀ TF.X Z) y).hom _).1 u2
      rw [← ger_toSec] at u3
      obtain ⟨v', hv'⟩ := ht ((isUnit_ger_iff _ _).1 u3)
      refine hy (show TF.X.π (inc₀ TF.X Z y) ∈ LogKS.interior TF.Y from ⟨i₀ TF.Y Z v', ?_⟩)
      rw [← Scheme.Hom.comp_apply, ← j₀_ι, Scheme.Hom.comp_apply, hv', ← Scheme.Hom.comp_apply, morphismRestrict_ι,
        Scheme.Hom.comp_apply]
    obtain ⟨g, hg⟩ := vanBd_le_space D T j Y e o hG hE Z TF la hs
    have e0 : f t = Submodule.inclusion (cusp_le_secZ Z Y.U la) g := by
      refine sub_eq_zero.1 (eq_zero_of_sec₀ TF.X Z (Submodule.sub_mem _ (hf t) g.2.2) ?_)
      rw [map_sub, hf' t, ← hg]
      exact sub_self _
    show (f t).1 ∈ _
    rw [e0]
    exact g.2
  · have e1 : TF.X.ptY yy ≫ TF.X.π = v ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
      rw [(TF.X.lies_ptY yy).1, j₀_ι, ← Category.assoc, hv]
      rfl
    have hr : Set.range (TF.X.ptY yy) ⊆ Set.range (inc₀ TF.X Z) := by
      rintro _ ⟨s, rfl⟩
      refine ⟨⟨_, show TF.X.π (TF.X.ptY yy s) ∈ barComp TF.Y Z from ?_⟩, rfl⟩
      rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
      exact ((v ≫ j₀ TF.Y Z) s).2
    let zz := IsOpenImmersion.lift (inc₀ TF.X Z) (TF.X.ptY yy) hr
    have hzz : zz ≫ inc₀ TF.X Z = TF.X.ptY yy := IsOpenImmersion.lift_fac _ _ _
    have e2 : zz ≫ π₀ TF.X Z = v ≫ j₀ TF.Y Z := by
      have h1 : (zz ≫ π₀ TF.X Z) ≫ (barComp TF.Y Z).ι = (v ≫ j₀ TF.Y Z) ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, Category.assoc, ← e1, ← hzz, Category.assoc]
        exact congrArg (zz ≫ ·) (morphismRestrict_ι TF.X.π (barComp TF.Y Z))
      exact (cancel_mono _).1 h1
    obtain ⟨k', hk'⟩ := exists_chart_of_field (TF.X.F.isLB_LL (AllWt.exOf (T.Q.Dw j) la 0)) (TF.X.pt yy ≫ TF.X.inc)
    obtain ⟨Q, tt, hQ, htt⟩ := FlagCover.exists_chartFr_frBor TF.X yy k' hk'
    have hO : ⊤ ≤ (TF.X.pt yy ≫ TF.X.inc) ⁻¹ᵁ flagOpen TF.X :=
      FlagMod.le_preimage_map TF.X.inc (top_le_inc TF.X) le_top
    have hzO : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by rw [hzz, ← FlagCover.pt_inc]; exact hO
    have hzk : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ (TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0)).U k' := by
      rw [hzz, ← FlagCover.pt_inc]; exact hk'
    have hTop : ⊤ ≤ zz ⁻¹ᵁ (⊤ : (Y₀ TF.X Z).Opens) := fun _ _ => trivial
    have hz1 : ⊤ ≤ zz ⁻¹ᵁ U₀ TF.X Z := hzO
    have hz2 : ⊤ ≤ zz ⁻¹ᵁ (L₀ TF.X Z la).U (pIdx _ (inc₀ TF.X Z) k') := fun s hs => mem_pIdx.2 (hzk hs)
    have hπ1 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ (⊤ : (X₀ TF.Y Z).Opens) := fun _ _ => trivial
    have hπ2 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ L.U k := by rw [e2]; exact hk
    have hz3 : ⊤ ≤ zz ⁻¹ᵁ (L.pull (π₀ TF.X Z)).U (pIdx L (π₀ TF.X Z) k) := fun s hs => mem_pIdx.2 (hπ2 hs)
    have hz4 : ⊤ ≤ zz ⁻¹ᵁ (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))).U
        (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) := fun s hs => ⟨hz2 hs, hz3 hs⟩
    have hu : IsUnit (H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G) := by
      rw [H0.val_ofSec]
      exact (w.s (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)).isUnit.map (GlobalTheory.TangentOrigin.evalPt zz _ hz4)
    obtain ⟨c0, hc0⟩ : ∃ c0 : ℂˣ, ∀ g : AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0),
        evR _ _ g.1 yy = c0.val * H0.val (TF.X.pt yy ≫ TF.X.inc) k' hO hk' (secOf TF.X _ g) :=
      ⟨_, fun g => evR_eq_val_secOf g hO hQ htt⟩
    refine ⟨c0 * hu.unit, fun t => ?_⟩
    show evR _ _ (f t).1 yy = _
    rw [hc0 (f t)]
    rw [val_congr_pt (p := flagStr TF.X) (B := TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0))
      ((FlagCover.pt_inc TF.X yy).trans hzz.symm) k' hO hk' hzO hzk]
    rw [show H0.val (zz ≫ inc₀ TF.X Z) k' hzO hzk (secOf TF.X _ (f t)) =
        H0.val zz (pIdx _ (inc₀ TF.X Z) k') hz1 hz2 (sec₀ TF.X Z _ (f t)) from
      (H0.val_pull (inc₀ TF.X Z) le_rfl zz (pIdx _ _ k') hz1 hz2 hzO hzk _).symm]
    rw [hf' t, val_restr_eq le_top zz _ hTop hz1 hz2]
    have e4 : H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) =
        H0.val (v ≫ j₀ TF.Y Z) k le_top hk t :=
      (H0.val_pull (π₀ TF.X Z) le_top zz (pIdx _ _ k) hTop hz3 hπ1 hπ2 t).trans (val_congr_pt e2 k hπ1 hπ2 le_top hk t)
    have e5 : H0.val zz (pIdx _ (inc₀ TF.X Z) k') hTop hz2 (sOf t) =
        H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) *
          H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G :=
      C.val_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) zz
        hTop hz3 hz4 hz2
    rw [e5, e4, Units.val_mul, IsUnit.unit_spec]
    ring

end GlobalTheory.OrbitSep
