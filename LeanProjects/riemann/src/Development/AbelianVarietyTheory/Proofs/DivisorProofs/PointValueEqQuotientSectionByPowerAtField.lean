import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecQuot

open TopologicalSpace

variable {X : Scheme.{0}} {L : LB X}

abbrev ch1 (L : LB X) (j : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) j

theorem mem_finOnePowerChartOpen_iff {j : Fin 1 → L.ι} {x : X} : x ∈ ch1 L j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

theorem gm_secM_g {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z (ch1 L j ⊓ ch1 L j') ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) r z j j' hj hj').trans ?_
  rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast]

abbrev M1 (L : LB X) (k : ℕ) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))

theorem germ_finOnePowerLineBundle_transition_eq_pow {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z ((M1 L k).U j ⊓ (M1 L k).U j') ((M1 L k).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := gm_secM_g k r z j j' hj hj'

theorem lineBundlePowChartOpen_le_finOnePowerChartOpen (J : PUnit → L.ι) : powChart L J ≤ ch1 L (fun _ => J PUnit.unit) :=
  fun _ h => mem_finOnePowerChartOpen_iff.2 (mem_powChart.1 h)

def toPow {k : ℕ} (s : SecM (𝟙 X) L k) : (lbPow L k).Sec :=
  powSecOfGerm k (fun J => resG X (lineBundlePowChartOpen_le_finOnePowerChartOpen J) (s.f fun _ => J PUnit.unit)) fun y J J' hJ hJ' => by
    have e := gs_compat s (𝟙 X) y (j := fun _ => J PUnit.unit) (j' := fun _ => J' PUnit.unit)
      (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    have e2 := germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    refine (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _).trans (e.trans ?_)
    refine (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J') hJ' _).symm).trans ?_
    rw [Units.val_pow_eq_pow_val]

theorem gs_toPow {k : ℕ} (s : SecM (𝟙 X) L k) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (J : PUnit → L.ι)
    (hJ : r z ∈ powChart L J) : gs r z _ (powFn (toPow s) J) = gs r z _ (s.f fun _ => J PUnit.unit) :=
  gs_res r z (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _

theorem exists_secM_of_pow {n N : ℕ} (hn : n = N) (u : (lbPow L n).Sec) :
    ∃ c : SecM (𝟙 X) L N, ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ ch1 L j →
      gs r z _ (c.f j) = gs r z _ (powFn u (fun _ => j 0)) := by
  subst hn
  have le : ∀ j : Fin 1 → L.ι, ch1 L j ≤ powChart L (fun _ => j 0) := fun j _ h => mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 h)
  refine ⟨GlobalTheory.LBGerm.secOfGerm (M := M1 L n) (fun j => resG X (le j) (powFn u (fun _ => j 0)))
    fun y (j j' : Fin 1 → L.ι) hj hj' => ?_, fun r z j hj => gs_res r z (le j) hj _⟩
  have e := gs_powFn_compat u (𝟙 X) y _ _ (le j hj) (le j' hj')
  have e2 := germ_finOnePowerLineBundle_transition_eq_pow n (𝟙 X) y j j' hj hj'
  refine (gs_res (𝟙 X) y (le j) hj _).trans (e.trans ?_)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res (𝟙 X) y (le j') hj' _)).symm
  rw [Units.val_pow_eq_pow_val]

theorem gs_appLE₁ {Y Z : Scheme.{0}} (F : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ F ⁻¹ᵁ U) (r : Z ⟶ Y)
    (z : Z) (hz : r z ∈ V) (a : Γ(X, U)) : gs r z V ((F.appLE U V h).hom a) = gs (r ≫ F) z U a :=
  (gs_res r z h hz _).trans (gs_pull r F z U (h hz) a)

theorem valR_congr₁ {A : Type} [CommRing A] (x : Sp A ⟶ X) {U U' : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hU' : ⊤ ≤ x ⁻¹ᵁ U') (a : Γ(X, U)) (a' : Γ(X, U')) (h : ∀ z, gs x z U a = gs x z U' a') :
    valR x U a = valR x U' a' := by
  rw [valR, valR, dif_pos hU, dif_pos hU']
  refine congrArg _ (fn_ext fun z hz => ?_)
  rw [gs_appLE₁ _ _ _ _ _ _ hz, gs_appLE₁ _ _ _ _ _ _ hz]
  simp only [Category.id_comp]
  exact h z

theorem mem_of_top_le {A : Type} [CommRing A] {x : Sp A ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp A) :
    x z ∈ U := h (show z ∈ (⊤ : (Sp A).Opens) from trivial)

theorem valR_mul_pow_of_gs {A : Type} [CommRing A] (x : Sp A ⟶ X) {U V W : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (hW : ⊤ ≤ x ⁻¹ᵁ W) (c : Γ(X, U)) (f : Γ(X, V)) (s : Γ(X, W)) (m : ℕ)
    (h : ∀ z, gs x z U c = gs x z V f * gs x z W s ^ m) : valR x U c = valR x V f * valR x W s ^ m := by
  have hO : ⊤ ≤ x ⁻¹ᵁ (V ⊓ W) := fun z hz => ⟨hV hz, hW hz⟩
  have e1 : valR x V f = valR x (V ⊓ W) (resG X inf_le_left f) :=
    valR_congr₁ x hV hO _ _ fun z => (gs_res x z inf_le_left (mem_of_top_le hO z) f).symm
  have e2 : valR x W s = valR x (V ⊓ W) (resG X inf_le_right s) :=
    valR_congr₁ x hW hO _ _ fun z => (gs_res x z inf_le_right (mem_of_top_le hO z) s).symm
  have e3 : valR x U c = valR x (V ⊓ W) (resG X inf_le_left f * resG X inf_le_right s ^ m) :=
    valR_congr₁ x hU hO _ _ fun z => by
      rw [h z, gs_mul _ z _ (mem_of_top_le hO z), GlobalTheory.LBGerm.gs_pow _ z _ (mem_of_top_le hO z),
        gs_res x z inf_le_left (mem_of_top_le hO z), gs_res x z inf_le_right (mem_of_top_le hO z)]
  rw [e1, e2, e3, valR, valR, valR, dif_pos hO, dif_pos hO, dif_pos hO, map_mul, map_mul, map_pow, map_pow]

theorem nonzeroLocus_toPow {k : ℕ} (s : SecM (𝟙 X) L k) : nonzeroLocus (toPow s) = nonzeroLocus s := by
  refine nonzeroLocus_eq_of (toPow s) _ (fun y hy => ?_) fun y J hJ => ?_
  · have ⟨j, hj⟩ : ∃ j : Fin 1 → L.ι, y ∈ ch1 L j := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j 0, mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 hj)⟩
  · have e : gs (𝟙 X) y _ ((toPow s).f J) = gs (𝟙 X) y _ (s.f fun _ => J PUnit.unit) := gs_toPow s (𝟙 X) y J hJ
    rw [e]
    exact (mem_nonzeroLocus_iff_isUnit s (k := fun _ => J PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ)).symm

theorem extend_part [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) {k : ℕ} (s : SecM (𝟙 X) L k)
    (f : Γ(X, nonzeroLocus s)) : ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N,
      ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i → r z ∈ nonzeroLocus s →
        gs r z _ (c.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  have hs' := nonzeroLocus_toPow s
  have le : ∀ J : PUnit → L.ι, nonzeroLocus (toPow s) ⊓ powChart L J ≤ nonzeroLocus s :=
    fun J => inf_le_left.trans hs'.le
  obtain ⟨N₀, hN₀⟩ := exists_sec_eq_pow_mul (m := 0) hL (toPow s) (fun J => resG X (le J) f)
    (GlobalTheory.LBGerm.mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' hy hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
      exact (gs_res (𝟙 X) y (le J) ⟨hy, hJ⟩ f).trans (gs_res (𝟙 X) y (le J') ⟨hy, hJ'⟩ f).symm)
  refine ⟨N₀, fun m N hm hN => ?_⟩
  obtain ⟨u, hu⟩ := hN₀ m hm
  obtain ⟨c, hc⟩ := exists_secM_of_pow (show 0 + k * m = N by omega) u
  refine ⟨c, fun r z i hi hz => ?_⟩
  have hJ : r z ∈ powChart L (fun _ => i) := mem_powChart.2 hi
  have hy : r z ∈ nonzeroLocus (toPow s) ⊓ powChart L (fun _ => i) := ⟨by rw [hs']; exact hz, hJ⟩
  have e := congrArg (gs r z _) (hu (fun _ => i))
  rw [gs_res r z _ hy, gs_mul r z _ hy, GlobalTheory.LBGerm.gs_pow r z _ hy, gs_res r z _ hy, gs_res r z _ hy] at e
  rw [hc r z (fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi), e, gs_toPow s r z _ hJ, _root_.mul_comm]

theorem quot_part {k : ℕ} (s : SecM (𝟙 X) L k) (m N : ℕ) (hN : N = k * m) (ρ : SecM (𝟙 X) L N) :
    ∃ f : Γ(X, nonzeroLocus s), ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i →
      r z ∈ nonzeroLocus s →
      gs r z _ (ρ.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  subst hN
  have loc : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X, X.basicOpen (s.f j)),
      resG X (X.basicOpen_le _) (ρ.f j) = a * resG X (X.basicOpen_le _) (s.f j) ^ m := fun j => by
    obtain ⟨b, hb⟩ := (show IsUnit (resG X (X.basicOpen_le (s.f j)) (s.f j)) from
      X.toRingedSpace.isUnit_res_basicOpen (s.f j)).exists_left_inv
    refine ⟨resG X (X.basicOpen_le _) (ρ.f j) * b ^ m, ?_⟩
    have key : ∀ {R : Type} [CommRing R] (x y c : R), c * y = 1 → x = x * c ^ m * y ^ m := fun x y c h => by
      rw [_root_.mul_assoc, ← _root_.mul_pow, h, _root_.one_pow, _root_.mul_one]
    exact key _ _ _ hb
  choose a ha using loc
  have hga : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ X.basicOpen (s.f j) →
      gs r z _ (ρ.f j) = gs r z _ (a j) * gs r z _ (s.f j) ^ m := fun r z j hz => by
    have e := congrArg (gs r z _) (ha j)
    have e1 := gs_res r z (X.basicOpen_le (s.f j)) hz (ρ.f j)
    have e2 := gs_res r z (X.basicOpen_le (s.f j)) hz (s.f j)
    have e3 := gs_mul r z _ hz (a j) (resG X (X.basicOpen_le (s.f j)) (s.f j) ^ m)
    have e4 := GlobalTheory.LBGerm.gs_pow r z _ hz (resG X (X.basicOpen_le (s.f j)) (s.f j)) m
    exact e1.symm.trans (e.trans (e3.trans (congrArg _ (e4.trans (congrArg (· ^ m) e2)))))
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (s.f j)) (nonzeroLocus s)
    (fun j => homOfLE (GlobalTheory.basicOpen_le_nonzeroLocus s j)) le_rfl a (fun i j => fn_ext fun y hy => by
      have hi : y ∈ ch1 L i := X.basicOpen_le _ hy.1
      have hj : y ∈ ch1 L j := X.basicOpen_le _ hy.2
      refine (gs_res (𝟙 X) y inf_le_left hy (a i)).trans
        (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy (a j)).symm)
      have u : IsUnit (gs (𝟙 X) y _ (s.f i) ^ m) :=
        ((GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y _ hi _).2 hy.1).pow m
      refine u.mul_right_cancel ?_
      rw [← hga (𝟙 X) y i hy.1, gs_compat ρ (𝟙 X) y hi hj, gs_compat s (𝟙 X) y hi hj, hga (𝟙 X) y j hy.2,
        germ_finOnePowerLineBundle_transition_eq_pow (k * m) (𝟙 X) y i j hi hj, germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y i j hi hj, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val]
      ring)
  refine ⟨f, fun r z i hi hz => ?_⟩
  have hz' : r z ∈ X.basicOpen (s.f fun _ => i) := (mem_nonzeroLocus_iff_basicOpen s (k := fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi)).1 hz
  rw [hga r z _ hz', ← hf (fun _ => i)]
  exact congrArg (· * _) (gs_res r z (GlobalTheory.basicOpen_le_nonzeroLocus s _) hz' f)

theorem valR_secM_eq_mul_pow : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j₀ → ∀ (k : ℕ) (s : SecM (𝟙 X) L k), ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus s → (∀ f : Γ(X, Out.nonzeroLocus s), ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N, valR ξ _ (c.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m) ∧ ∀ m N : ℕ, N = k * m → ∀ ρ : SecM (𝟙 X) L N, ∃ f : Γ(X, Out.nonzeroLocus s), valR ξ _ (ρ.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m := by
  intro X _ _ L hL F _ ξ j₀ hj₀ k s hs
  have hc : ⊤ ≤ ξ ⁻¹ᵁ ch1 L (fun _ => j₀) := fun z hz => mem_finOnePowerChartOpen_iff.2 (hj₀ hz)
  refine ⟨fun f => ?_, fun m N hN ρ => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := extend_part hL s f
    refine ⟨m₀, fun m N hm hN => ?_⟩
    obtain ⟨c, hc'⟩ := hm₀ m N hm hN
    exact ⟨c, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hc' ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩
  · obtain ⟨f, hf⟩ := quot_part s m N hN ρ
    exact ⟨f, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hf ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩

end GlobalTheory.SecQuot
