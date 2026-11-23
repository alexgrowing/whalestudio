import Development.EtaleCohomology.KummerTheory.LHCutGlue

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem lcv_cls_of_d {R : Type} [CommRing R] (hD : Dict) {I : Cx R} {X : Scheme.{0}} (n n' : ℤ) (h : n + 1 = n')
    (a : Sec (I.X n) X) (ha : Sec.map (I.d n n') a = 0) : ∃ x, IsCls x a := by
  subst h; exact (hD R I X n).1 a ha

theorem lcv_d_of_cls {R : Type} [CommRing R] (hD : Dict) {I : Cx R} {X : Scheme.{0}} {n : ℤ} (n' : ℤ) (h : n + 1 = n')
    x (a : Sec (I.X n) X) (ha : IsCls x a) : Sec.map (I.d n n') a = 0 := by
  subst h; exact ((hD R I X n).2.2.1 x a ha).1

section
variable {Λ : Type} [CommRing Λ] {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ}
  (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem lcv_cD_fst (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).1 = dS (j + 1) (j' + 1) x.1 := rfl

theorem lcv_cD_snd (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).2 = Phi μ p γ (j + 1) j' h U x.1 - Sec.map (K.d j j') x.2 := rfl

theorem lcv_cres_fst {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) :
    (cres g x).1 = fun a s => Sec.res g.left (x.1 a s) := rfl

theorem lcv_cres_snd {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) :
    (cres g x).2 = Sec.res (rst p g) x.2 := rfl
end

theorem lcv_step1 (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ : ℤ) (hK : KerLoc q p i r c M N (j₀ + 1 + 1)) (U : Over S)
    (x1 : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1 + 1) U.left) (k : Sec ((res _ (tw q i)).X (j₀ + 1)) (pullback p U.hom))
    (hx1 : dS (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) x1 = 0)
    (hx2 : Phi (mu q i) p γ (j₀ + 1 + 1) (j₀ + 1 + 1) rfl U x1 = Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) k)
    (u : U.left) : ∃ (V1 : Over S) (g1 : V1 ⟶ U), Nbhd g1 u ∧ ∃ b : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1) V1.left,
      dS (j₀ + 1) (j₀ + 1 + 1) b = fun a s => N • Sec.res g1.left (x1 a s) := by
  have hCM := clsMore_of hD
  have hb : ∀ (a : Fin (M + 1)) (s : Fin (r a)),
      Sec.map ((res _ (tw q 0)).d (j₀ + 1 + 1 - ((a : ℕ) : ℤ)) (j₀ + 1 + 1 + 1 - ((a : ℕ) : ℤ))) (x1 a s) = 0 := by
    intro a s
    have h0 := congrFun (congrFun hx1 a) s
    have := congrArg (fun v => ((a : ℕ) : ℤ).negOnePow • v) h0
    simpa only [dS, Pi.zero_apply, smul_smul, Int.units_mul_self, one_smul, smul_zero] using this
  choose y hy using fun a s => lcv_cls_of_d hD _ _ (by omega) _ (hb a s)
  have hl := hL q p i r c γ hc M (j₀ + 1 + 1) U y x1 hy
  have hly : lh q p U.hom i r c M (j₀ + 1 + 1) y = 0 :=
    ((hCM _ _ _ _).2.2.2 (j₀ + 1) rfl _ 0 _ 0 hl (hCM _ _ _ _).1).2 ⟨k, by rw [sub_zero]; exact hx2.symm⟩
  obtain ⟨V1, g1, hg1, hk1⟩ := hK U u y hly
  have hcl1 : ∀ (a : Fin (M + 1)) (s : Fin (r a)),
      IsCls (N • pull _ (sch.map g1.left) _ _ (y a s)) (N • Sec.res g1.left (x1 a s)) :=
    fun a s => (hCM _ _ _ _).2.1 N _ _ ((hD _ _ _ _).2.2.2.2 g1.left _ _ (hy a s))
  choose b1 hb1 using fun (a : Fin (M + 1)) (s : Fin (r a)) =>
    ((hCM _ _ _ _).2.2.2 (j₀ + 1 - ((a : ℕ) : ℤ)) (by omega) _ 0 _ 0 (hcl1 a s) (hCM _ _ _ _).1).1 (hk1 a s)
  refine ⟨V1, g1, hg1, fun a s => ((a : ℕ) : ℤ).negOnePow • b1 a s, ?_⟩
  funext a s
  simp only [dS, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  exact (hb1 a s).trans (sub_zero _)

theorem lcv_step2 (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ : ℤ) (hC : CokLoc q p i r c M N (j₀ + 1)) (V1 : Over S) (v1 : V1.left)
    (k : Sec ((res _ (tw q i)).X (j₀ + 1)) (pullback p V1.hom))
    (hk : Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) k = 0) :
    ∃ (V2 : Over S) (g2 : V2 ⟶ V1), Nbhd g2 v1 ∧ ∃ (b2 : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1) V2.left)
      (k' : Sec ((res _ (tw q i)).X j₀) (pullback p V2.hom)), dS (j₀ + 1) (j₀ + 1 + 1) b2 = 0 ∧
      Phi (mu q i) p γ (j₀ + 1) (j₀ + 1) rfl V2 b2 - Sec.map ((res _ (tw q i)).d j₀ (j₀ + 1)) k' =
        N • Sec.res (rst p g2) k := by
  have hCM := clsMore_of hD
  obtain ⟨κ, hκ⟩ := (hD _ _ _ _).1 k hk
  obtain ⟨V2, g2, hg2, y2, hy2⟩ := hC V1 v1 κ
  choose b2 hb2 using fun (a : Fin (M + 1)) (s : Fin (r a)) => (hD _ _ _ _).2.1 (y2 a s)
  have hl2 := hL q p i r c γ hc M (j₀ + 1) V2 y2 b2 hb2
  have hcl2 : IsCls (N • pull _ (sch.map (rst p g2)) _ _ κ) (N • Sec.res (rst p g2) k) :=
    (hCM _ _ _ _).2.1 N _ _ ((hD _ _ _ _).2.2.2.2 (rst p g2) _ _ hκ)
  obtain ⟨k', hk'⟩ := ((hCM _ _ _ _).2.2.2 j₀ rfl _ _ _ _ hl2 hcl2).1 hy2
  refine ⟨V2, g2, hg2, b2, k', ?_, ?_⟩
  · funext a s
    simp only [dS, Pi.zero_apply]
    rw [lcv_d_of_cls hD _ (by omega) _ _ (hb2 a s), smul_zero]
  · rw [hk', sub_sub_cancel]

section
variable {Λ : Type} [CommRing Λ] {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ}
  (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem etale_leray_hirsch_cone_comparison_map_degree_cast (n w : ℤ) (h : n = w) (U : Over S) : Phi (J := J) (M := M) μ p γ n w h U 0 = 0 := by
  simp [Phi]

theorem etale_leray_hirsch_cone_source_component_vanishes_after_correction (j₀ : ℤ) {U V1 : Over S} (g1 : V1 ⟶ U) (x : Cone J K p r M (j₀ + 1) U) (N : ℕ)
    (b1 : FinalTheorems J r M (j₀ + 1) V1.left) (hb1 : dS (j₀ + 1) (j₀ + 1 + 1) b1 = fun a s => N • Sec.res g1.left (x.1 a s)) :
    (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 (b1, 0)).1 = 0 := by
  rw [Prod.fst_sub, Prod.smul_fst, lcv_cres_fst, lcv_cD_fst, hb1]
  funext a s
  simp only [Pi.sub_apply, Pi.smul_apply, sub_self, Pi.zero_apply]

theorem etale_leray_hirsch_cone_cycle_with_zero_source_has_closed_complex_part (j₀ : ℤ) {V1 : Over S} (z : Cone J K p r M (j₀ + 1) V1) (hz1 : z.1 = 0)
    (hzc : cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl V1 z = 0) : Sec.map (K.d (j₀ + 1) (j₀ + 1 + 1)) z.2 = 0 := by
  have := congrArg Prod.snd hzc
  rw [lcv_cD_snd, hz1, etale_leray_hirsch_cone_comparison_map_degree_cast, zero_sub, Prod.snd_zero, neg_eq_zero] at this
  exact this

theorem lcv_bk (j₀ : ℤ) {V1 V2 : Over S} (g2 : V2 ⟶ V1) (z : Cone J K p r M (j₀ + 1) V1) (hz1 : z.1 = 0) (N : ℕ)
    (b2 : FinalTheorems J r M (j₀ + 1) V2.left) (k' : Sec (K.X j₀) (pullback p V2.hom)) (hdb2 : dS (j₀ + 1) (j₀ + 1 + 1) b2 = 0)
    (hk' : Phi μ p γ (j₀ + 1) (j₀ + 1) rfl V2 b2 - Sec.map (K.d j₀ (j₀ + 1)) k' = N • Sec.res (rst p g2) z.2) :
    cD μ p γ j₀ (j₀ + 1) rfl V2 (b2, k') = N • cres g2 z := by
  refine Prod.ext ?_ ?_
  · rw [lcv_cD_fst, Prod.smul_fst, lcv_cres_fst, hz1]
    exact hdb2.trans (by funext a s; simp)
  · rw [lcv_cD_snd, Prod.smul_snd, lcv_cres_snd]
    exact hk'

theorem lcv_nbhd {U V1 V2 : Over S} (g1 : V1 ⟶ U) (g2 : V2 ⟶ V1) (u : U.left) (hg1 : Nbhd g1 u) (v1 : V1.left)
    (hv1 : g1.left v1 = u) (hg2 : Nbhd g2 v1) : Nbhd (g2 ≫ g1) u := by
  refine ⟨?_, ?_⟩
  · have := hg1.1; have := hg2.1
    rw [Over.comp_left]; infer_instance
  · obtain ⟨v2, hv2⟩ := hg2.2
    exact ⟨v2, by simp [hv2, hv1]⟩

theorem lcv_alg (hA : ConeAlg) (hγ : Closed γ) (j₀ : ℤ) {U V1 V2 : Over S} (g1 : V1 ⟶ U) (g2 : V2 ⟶ V1)
    (x : Cone J K p r M (j₀ + 1) U) (N : ℕ)
    (w0 : Cone J K p r M j₀ V1) (y2 : Cone J K p r M j₀ V2)
    (hy2 : cD μ p γ j₀ (j₀ + 1) rfl V2 y2 = N • cres g2 (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 w0)) :
    cD μ p γ j₀ (j₀ + 1) rfl V2 (N • cres g2 w0 + y2) = N ^ 2 • cres (g2 ≫ g1) x := by
  obtain ⟨-, -, nat1⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V1
  obtain ⟨-, -, nat2⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl V1
  obtain ⟨-, -, natU⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl U
  obtain ⟨linV2, -, -⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V2
  have e1 := (map_add (IsLinearMap.mk' _ linV2) (N • cres g2 w0) y2).trans
    (congrArg (· + _) (map_nsmul (IsLinearMap.mk' _ linV2) N (cres g2 w0)))
  simp only [IsLinearMap.mk'_apply] at e1
  have e2 := map_sub (IsLinearMap.mk' _ (nat2 V2 g2).1) (N • cres g1 x) (cD μ p γ j₀ (j₀ + 1) rfl V1 w0)
  have e3 := map_nsmul (IsLinearMap.mk' _ (nat2 V2 g2).1) N (cres g1 x)
  simp only [IsLinearMap.mk'_apply] at e2 e3
  rw [e1, hy2, e2, e3, (nat1 V2 g2).2.1 w0, smul_sub, add_sub_cancel, smul_smul, ← pow_two,
    (natU V1 g1).2.2 V2 g2 x]

theorem lcv_zc (hA : ConeAlg) (hγ : Closed γ) (j₀ : ℤ) {U V1 : Over S} (g1 : V1 ⟶ U)
    (x : Cone J K p r M (j₀ + 1) U) (hx : cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x = 0) (N : ℕ)
    (w0 : Cone J K p r M j₀ V1) :
    cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl V1 (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 w0) = 0 := by
  obtain ⟨-, sq1, -⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V1
  obtain ⟨lin2, -, -⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl V1
  obtain ⟨-, -, natU⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl U
  have c0 : cres g1 (0 : Cone J K p r M (j₀ + 1 + 1) U) = 0 :=
    map_zero (IsLinearMap.mk' _ ((hA _ μ p r M γ hγ (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) rfl U).2.2 V1 g1).1)
  have e := (map_sub (IsLinearMap.mk' _ lin2) (N • cres g1 x) (cD μ p γ j₀ (j₀ + 1) rfl V1 w0)).trans
    (congrArg (· - _) (map_nsmul (IsLinearMap.mk' _ lin2) N (cres g1 x)))
  simp only [IsLinearMap.mk'_apply] at e
  rw [e, sq1 _ rfl w0, ← (natU V1 g1).2.1 x, hx, c0, smul_zero, sub_zero]
end

theorem etale_leray_hirsch_cone_cycle_locally_bounded_boundary (hD : Dict) (hL : LhSec) (hA : ConeAlg) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ j : ℤ) (h : j₀ + 1 = j) (hK : KerLoc q p i r c M N (j + 1)) (hC : CokLoc q p i r c M N j)
    (U : Over S) (x : Cone (res _ (tw q 0)) (res _ (tw q i)) p r M j U)
    (hx : cD (mu q i) p γ j (j + 1) rfl U x = 0) (u : U.left) :
    ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧
      ∃ y : Cone (res _ (tw q 0)) (res _ (tw q i)) p r M j₀ V, cD (mu q i) p γ j₀ j h V y = N ^ 2 • cres g x := by
  subst h
  have hγ : Closed γ := fun a s => ((hD _ _ X _).2.2.1 _ _ (hc a s)).1
  have hx1 : dS (J := res _ (tw q 0)) (r := r) (M := M) (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) x.1 = 0 :=
    ((lcv_cD_fst (mu q i) p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x).symm.trans (congrArg Prod.fst hx)).trans Prod.fst_zero
  have hx2 : Phi (mu q i) p γ (j₀ + 1 + 1) (j₀ + 1 + 1) rfl U x.1 =
      Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) x.2 :=
    sub_eq_zero.1 (((lcv_cD_snd (mu q i) p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x).symm.trans (congrArg Prod.snd hx)).trans
      Prod.snd_zero)
  obtain ⟨V1, g1, hg1, b1, hb1⟩ := lcv_step1 hD hL q p i r c γ hc M N j₀ hK U x.1 x.2 hx1 hx2 u
  have hz1 := etale_leray_hirsch_cone_source_component_vanishes_after_correction (mu q i) p γ j₀ g1 x N b1 hb1
  have hzc := lcv_zc (mu q i) p γ hA hγ j₀ g1 x hx N (b1, 0)
  have hz2 := etale_leray_hirsch_cone_cycle_with_zero_source_has_closed_complex_part (mu q i) p γ j₀ _ hz1 hzc
  obtain ⟨v1, hv1⟩ := hg1.2
  obtain ⟨V2, g2, hg2, b2, k', hdb2, hk'⟩ := lcv_step2 hD hL q p i r c γ hc M N j₀ hC V1 v1 _ hz2
  exact ⟨V2, g2 ≫ g1, lcv_nbhd g1 g2 u hg1 v1 hv1 hg2, N • cres g2 (b1, 0) + (b2, k'),
    lcv_alg (mu q i) p γ hA hγ j₀ g1 g2 x N (b1, 0) (b2, k') (lcv_bk (mu q i) p γ j₀ g2 _ hz1 N b2 k' hdb2 hk')⟩

theorem locCone_of (hD : Dict) (hL : LhSec) (hA : ConeAlg) : LocCone := by
  intro q X S p i r c γ hc M N j hK hC U x hx u
  exact etale_leray_hirsch_cone_cycle_locally_bounded_boundary hD hL hA q p i r c γ hc M N (j - 1) j (by omega) hK hC U x hx u
end LateralTheory.KummerTheory.LHCut
