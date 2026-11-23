import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points GlobalTheory.ZM

namespace GlobalTheory.SiegTh.PullO1

theorem top_le_wchart {X : Scheme.{0}} (L : LB X) {K : Type} [Field K] (x : Sp K ⟶ X) (p : L.ι)
    (hp : ⊤ ≤ x ⁻¹ᵁ L.U p) : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ (L.pull x).U (fun _ => p) :=
  fun w _ => Set.mem_iInter.2 fun _ => hp (Set.mem_univ w)

theorem valR_id_resG_inv {K : Type} [Field K] {W : (Sp K).Opens} (hW : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ W) (a : K) :
    valR (𝟙 (Sp K)) W (resG (Sp K) le_top ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) = a := by
  rw [valR_res _ le_top hW]
  have := valR_specMap (C := K) (𝟙 (CommRingCat.of K)) a
  simpa using this

theorem valR_resG' {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f :=
  valR_res x e h f

theorem valR_unit_ne_zero {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) {W : X.Opens} (hW : ⊤ ≤ x ⁻¹ᵁ W)
    (u : Γ(X, W)ˣ) : valR x W (u : Γ(X, W)) ≠ 0 := by
  rw [valR_eq x W hW]
  exact (u.isUnit.map (valMap x W hW).hom).ne_zero

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

theorem secCoord_vals {X : Scheme.{0}} {L : LB X} {I : Type} {σ : I → L.Sec} {K : Type} [Field K] {x : Sp K ⟶ X}
    {v : I → K} (hs : SecCoord L σ x v) :
    ∃ c : L.ι → K, (∀ p, ⊤ ≤ x ⁻¹ᵁ L.U p → c p ≠ 0 ∧ ∀ i, valF x (L.U p) ((σ i).f p) = v i * c p) ∧
      ∀ p p', ⊤ ≤ x ⁻¹ᵁ (L.U p ⊓ L.U p') →
        valF x (L.U p ⊓ L.U p') (L.g p p' : Γ(X, L.U p ⊓ L.U p')) * c p' = c p := by
  obtain ⟨τ, hτ, hv⟩ := hs
  refine ⟨fun p => valR (𝟙 (Sp K)) ((L.pull x).U (fun _ => p)) (τ.s (fun _ => p) : Γ(Sp K, _)), ?_, ?_⟩
  · intro p hp
    have hW := top_le_wchart L x p hp
    refine ⟨valR_unit_ne_zero _ hW _, fun i => ?_⟩
    have e := congrArg (valR (𝟙 (Sp K)) _) (hv i (fun _ => p) (LB.wchart_le L (fun _ => x) (fun _ => p) PUnit.unit))
    dsimp only at e
    have e2 := valR_appLE (𝟙 (Sp K)) x (LB.wchart_le L (fun _ => x) (fun _ => p) PUnit.unit) hW ((σ i).f p)
    rw [Category.id_comp] at e2
    rw [valF_eq_valR, ← e2]
    refine e.trans ?_
    rw [valR_mul _ _ hW, valR_id_resG_inv hW]
  · intro p p' hpp
    have hp : ⊤ ≤ x ⁻¹ᵁ L.U p := fun w hw => (hpp hw).1
    have hp' : ⊤ ≤ x ⁻¹ᵁ L.U p' := fun w hw => (hpp hw).2
    have hW := top_le_wchart L x p hp
    have hW' := top_le_wchart L x p' hp'
    have hWW : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ((L.pull x).U (fun _ => p) ⊓ (L.pull x).U (fun _ => p')) :=
      fun w hw => ⟨hW hw, hW' hw⟩
    have e0 := congrArg Units.val (hτ (fun _ => p) (fun _ => p'))
    have e := congrArg (valR (𝟙 (Sp K)) _) e0
    simp only [Units.val_mul] at e
    rw [valR_mul _ _ hWW] at e
    simp only [res, Units.coe_map, MonoidHom.coe_coe] at e
    rw [valR_res _ _ hWW, valR_res _ _ hWW] at e
    show _ * valR _ _ _ = valR _ _ _
    rw [e]
    congr 1
    rw [ProjSpace.linComb_punit_g, zpow_one]
    change valF x _ _ = valR (𝟙 (Sp K)) _ (resG (Sp K) _ ((x.app (L.U p ⊓ L.U p')).hom (L.g p p' : Γ(X, _))))
    refine Eq.symm ((valR_resG' (𝟙 (Sp K)) _ hWW _).trans ?_)
    refine (valR_comp (𝟙 (Sp K)) x _ _).symm.trans ?_
    rw [Category.id_comp]
    rfl

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem coe_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (a : Γ(X, U)) := rfl

theorem coe_res_mul {X : Scheme.{0}} {V P Q R : X.Opens} (a : Γ(X, P)ˣ) (b : Γ(X, Q)ˣ) (c : Γ(X, R)ˣ) (ha : V ≤ P)
    (hb : V ≤ Q) (hc : V ≤ R) :
    ((res ha a * (res hb b)⁻¹ * res hc c : Γ(X, V)ˣ) : Γ(X, V)) =
      resG X ha (a : Γ(X, P)) * resG X hb (↑b⁻¹ : Γ(X, Q)) * resG X hc (c : Γ(X, R)) := rfl

theorem valF_pt_mul (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) (f g : Γ(M.Z, V)) :
    valF M.pt V (f * g) = valF M.pt V f * valF M.pt V g := by
  rw [← M.res_apply V hV, ← M.res_apply V hV, ← M.res_apply V hV, map_mul]

theorem valF_pt_one (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) :
    valF M.pt V (1 : Γ(M.Z, V)) = 1 := by
  rw [← M.res_apply V hV, map_one]

theorem valF_pt_inv (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) (u : Γ(M.Z, V)ˣ) :
    valF M.pt V (↑u⁻¹ : Γ(M.Z, V)) = (valF M.pt V (u : Γ(M.Z, V)))⁻¹ := by
  rw [← M.res_apply V hV, ← M.res_apply V hV]
  exact map_units_inv (M.res V hV) u

theorem valF_pt_ne_zero (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) (u : Γ(M.Z, V)ˣ) :
    valF M.pt V (u : Γ(M.Z, V)) ≠ 0 := by
  rw [← M.res_apply V hV]
  exact (u.isUnit.map (M.res V hV)).ne_zero

theorem exists_unit_of_val (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) {w : Ω} (h0 : w ≠ 0)
    (h : ∀ z ∈ V, w ∈ M.O z ∧ w⁻¹ ∈ M.O z) : ∃ u : Γ(M.Z, V)ˣ, valF M.pt V (u : Γ(M.Z, V)) = w := by
  obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hV).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).1)
  obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists hV).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).2)
  have hfg : f * g = 1 := M.valF_injective hV (by rw [valF_pt_mul M hV, valF_pt_one M hV, hf, hg, mul_inv_cancel₀ h0])
  exact ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, hf⟩

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem lbIso_of_vals (M : RatModel o Ω) {L A : LB M.Z} (cL : L.ι → Ω) (cA : A.ι → Ω)
    (hL0 : ∀ q, (L.U q : Set M.Z).Nonempty → cL q ≠ 0) (hA0 : ∀ p, (A.U p : Set M.Z).Nonempty → cA p ≠ 0)
    (hLg : ∀ q q', ((L.U q ⊓ L.U q' : M.Z.Opens) : Set M.Z).Nonempty →
      valF M.pt _ (L.g q q' : Γ(M.Z, L.U q ⊓ L.U q')) * cL q' = cL q)
    (hAg : ∀ p p', ((A.U p ⊓ A.U p' : M.Z.Opens) : Set M.Z).Nonempty →
      valF M.pt _ (A.g p p' : Γ(M.Z, A.U p ⊓ A.U p')) * cA p' = cA p)
    (hloc : ∀ p q z, z ∈ A.U p → z ∈ L.U q → cA p / cL q ∈ M.O z ∧ cL q / cA p ∈ M.O z) :
    LBIso L A := by
  have key : ∀ pq : A.ι × L.ι, ∃ u : Γ(M.Z, A.U pq.1 ⊓ L.U pq.2)ˣ,
      ((A.U pq.1 ⊓ L.U pq.2 : M.Z.Opens) : Set M.Z).Nonempty →
        valF M.pt _ (u : Γ(M.Z, A.U pq.1 ⊓ L.U pq.2)) = cA pq.1 / cL pq.2 := by
    intro pq
    by_cases hV : ((A.U pq.1 ⊓ L.U pq.2 : M.Z.Opens) : Set M.Z).Nonempty
    · have h0 : cA pq.1 / cL pq.2 ≠ 0 :=
        div_ne_zero (hA0 _ (hV.mono fun _ h => h.1)) (hL0 _ (hV.mono fun _ h => h.2))
      obtain ⟨u, hu⟩ := exists_unit_of_val M hV h0 fun z hz => by
        rw [inv_div]; exact hloc pq.1 pq.2 z hz.1 hz.2
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hV⟩
  choose u hu using key
  refine ⟨⟨u⟩, fun pq pq' => ?_⟩
  by_cases hV : (((A.U pq.1 ⊓ L.U pq.2) ⊓ (A.U pq'.1 ⊓ L.U pq'.2) : M.Z.Opens) : Set M.Z).Nonempty
  · have h1 : ((A.U pq.1 ⊓ L.U pq.2 : M.Z.Opens) : Set M.Z).Nonempty := hV.mono fun _ h => h.1
    have h2 : ((A.U pq'.1 ⊓ L.U pq'.2 : M.Z.Opens) : Set M.Z).Nonempty := hV.mono fun _ h => h.2
    have hAA : ((A.U pq.1 ⊓ A.U pq'.1 : M.Z.Opens) : Set M.Z).Nonempty := hV.mono fun _ h => ⟨h.1.1, h.2.1⟩
    have hLL : ((L.U pq.2 ⊓ L.U pq'.2 : M.Z.Opens) : Set M.Z).Nonempty := hV.mono fun _ h => ⟨h.1.2, h.2.2⟩
    have cA' := hA0 _ (h2.mono fun _ h => h.1)
    have cL' := hL0 _ (h2.mono fun _ h => h.2)
    have cL0 := hL0 _ (h1.mono fun _ h => h.2)
    have eA := hAg pq.1 pq'.1 hAA
    have eL := hLg pq.2 pq'.2 hLL
    have gL0 : valF M.pt _ (L.g pq.2 pq'.2 : Γ(M.Z, L.U pq.2 ⊓ L.U pq'.2)) ≠ 0 := valF_pt_ne_zero M hLL _
    dsimp only [LB.div]
    refine Units.ext (M.valF_injective hV ?_)
    erw [coe_res_mul, coe_res]
    rw [valF_pt_mul M hV, valF_pt_mul M hV, M.valF_resG _ hV, M.valF_resG _ hV]
    erw [M.valF_resG _ hV, M.valF_resG _ hV]
    rw [valF_pt_inv M hLL, hu _ h1, hu _ h2, ← eA, ← eL]
    field_simp
  · exact unit_ext fun x hx => absurd ⟨x, hx⟩ hV

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem valF_pt_zpow (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) (u : Γ(M.Z, V)ˣ) (n : ℤ) :
    valF M.pt V (↑(u ^ n) : Γ(M.Z, V)) = (valF M.pt V (u : Γ(M.Z, V))) ^ n := by
  rw [← M.res_apply V hV, ← M.res_apply V hV]
  have h1 : ∀ w : Γ(M.Z, V)ˣ, M.res V hV (w : Γ(M.Z, V)) = ((Units.map (M.res V hV : Γ(M.Z, V) →* Ω) w : Ωˣ) : Ω) :=
    fun _ => rfl
  rw [h1, h1, map_zpow, Units.val_zpow_eq_zpow_val]

theorem valF_linComb_g (M : RatModel o Ω) {Y : Scheme.{0}} (L : LB Y) (φ : M.Z ⟶ Y) (n : ℤ) (P P' : PUnit → L.ι)
    (hV : (((LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).U P ⊓
      (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).U P' : M.Z.Opens) : Set M.Z).Nonempty) :
    valF M.pt ((LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).U P ⊓
      (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).U P')
      (((LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).g P P' : Γ(M.Z, _)ˣ) : Γ(M.Z, _)) =
      valF (M.pt ≫ φ) (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit) : Γ(Y, _)) ^ n := by
  rw [ProjSpace.linComb_punit_g]
  erw [valF_pt_zpow M hV]
  congr 1
  erw [coe_res, M.valF_resG _ hV]
  exact (valR_comp M.pt φ (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit) : Γ(Y, _))).symm

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

theorem lbIso_pull_O1_lbPow : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (I : Type) [Finite I]
    (th : I → Ω) (δ : LB M.Z) (t : I → δ.Sec) (N D : ℕ) (e : Fin (N + 1) → Ω) (h : M.Z ⟶ PSpace o N), δ.IsLB →
    (⨆ a, nonzeroLocus (t a)) = ⊤ → SecCoord δ t M.pt th → PCrd (M.pt ≫ h) e → SameScale M th e D →
    LBIso ((GlobalTheory.ProjSpace.O1 o N).pull h) (lbPow δ D) := by
  intro k Ω o _ _ _ _ M I _ th δ t N D e h _ hcov hsc hpc hss
  obtain ⟨c, hc0, hcg⟩ := secCoord_vals hsc
  obtain ⟨d, hd0, hdg⟩ := secCoord_vals hpc
  have ptU : ∀ {U : M.Z.Opens}, (U : Set M.Z).Nonempty → ⊤ ≤ M.pt ⁻¹ᵁ U := fun hU => M.top_le_preimage_pt hU
  refine lbIso_of_vals M (fun Q => d (Q PUnit.unit)) (fun P => c (P PUnit.unit) ^ D) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    exact (hd0 _ (fun w hw => LB.wchart_le _ (fun _ => h) Q PUnit.unit (ptU hQ hw))).1
  · intro P hP
    exact pow_ne_zero _ (hc0 _ (fun w hw => LB.wchart_le δ (fun _ => 𝟙 M.Z) P PUnit.unit (ptU hP hw))).1
  · intro Q Q' hQQ
    rw [valF_linComb_g M _ h 1 Q Q' hQQ, zpow_one]
    exact hdg _ _ (fun w hw => ⟨LB.wchart_le _ (fun _ => h) Q PUnit.unit (ptU hQQ hw).1,
      LB.wchart_le _ (fun _ => h) Q' PUnit.unit (ptU hQQ hw).2⟩)
  · intro P P' hPP
    rw [valF_linComb_g M δ (𝟙 M.Z) (D : ℤ) P P' hPP, zpow_natCast, Category.comp_id, ← mul_pow]
    rw [hcg _ _ (fun w hw => ⟨LB.wchart_le δ (fun _ => 𝟙 M.Z) P PUnit.unit (ptU hPP hw).1,
      LB.wchart_le δ (fun _ => 𝟙 M.Z) P' PUnit.unit (ptU hPP hw).2⟩)]
  · intro P Q z hzP hzQ
    show c (P PUnit.unit) ^ D / d (Q PUnit.unit) ∈ M.O z ∧ d (Q PUnit.unit) / c (P PUnit.unit) ^ D ∈ M.O z
    have hzp : z ∈ δ.U (P PUnit.unit) := LB.wchart_le δ (fun _ => 𝟙 M.Z) P PUnit.unit hzP
    have hzq : z ∈ h ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o N).U (Q PUnit.unit) := LB.wchart_le _ (fun _ => h) Q PUnit.unit hzQ
    generalize P PUnit.unit = p at hzp ⊢
    generalize Q PUnit.unit = q at hzq ⊢
    have hUp : ⊤ ≤ M.pt ⁻¹ᵁ δ.U p := ptU ⟨z, hzp⟩
    have hUq : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o N).U q := ptU (U := h ⁻¹ᵁ _) ⟨z, hzq⟩
    obtain ⟨cp0, hcv⟩ := hc0 p hUp
    obtain ⟨dq0, hdv⟩ := hd0 q hUq
    have hed : ∀ i, e i * d q ∈ M.O z := fun i => by
      rw [← hdv i, valF_eq_valR, valR_comp]
      exact RatModel.valF_mem_O hzq _
    have heq1 : e q * d q = 1 := by
      have h11 : (ProjSpace.coord o N q).f q = 1 := ProjSpace.ratioOn_self (hi := le_rfl)
      rw [← hdv q, h11, valF_eq_valR]
      exact valR_one _ _ hUq
    obtain ⟨a, ha⟩ : ∃ a, z ∈ nonzeroLocus (t a) := by
      have hz : z ∈ (⨆ a, nonzeroLocus (t a)) := hcov ▸ trivial
      exact TopologicalSpace.Opens.mem_iSup.1 hz
    obtain ⟨kk, hk⟩ : ∃ kk, z ∈ M.Z.basicOpen ((t a).f kk) := TopologicalSpace.Opens.mem_iSup.1 ha
    have hzk : z ∈ δ.U kk := M.Z.basicOpen_le _ hk
    have hbo : z ∈ M.Z.basicOpen ((t a).f p) := by
      have e1 := congrArg M.Z.basicOpen ((t a).compat p kk)
      rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, Scheme.basicOpen_res,
        Scheme.basicOpen_of_isUnit _ (δ.g p kk).isUnit] at e1
      have hz : z ∈ (δ.U p ⊓ δ.U kk) ⊓ ((δ.U p ⊓ δ.U kk) ⊓ M.Z.basicOpen ((t a).f kk)) :=
        ⟨⟨hzp, hzk⟩, ⟨hzp, hzk⟩, hk⟩
      rw [← e1] at hz
      exact hz.2
    have hua : th a * c p ≠ 0 ∧ (th a * c p)⁻¹ ∈ M.O z := by
      have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hzp ((t a).f p)).2 hbo)
      simpa only [hcv a] using hu
    have hmem : ∀ b, th b * c p ∈ M.O z := fun b => by
      rw [← hcv b]
      exact RatModel.valF_mem_O hzp _
    have tha0 : th a ≠ 0 := left_ne_zero_of_mul hua.1
    have hdiv : M.Div th a z := ⟨tha0, fun b => by
      have hb : th b / th a = (th b * c p) * (th a * c p)⁻¹ := by field_simp
      rw [hb]
      exact mul_mem (hmem b) hua.2⟩
    obtain ⟨j, hj, h1, h2⟩ := hss z a hdiv
    have ej0 : e j ≠ 0 := hj.1
    have heq : e q = (d q)⁻¹ := eq_inv_of_mul_eq_one_left heq1
    have key : c p ^ D / d q = (th a * c p) ^ D * (e j / th a ^ D) * (e q / e j) := by
      rw [heq]
      field_simp
      ring
    have U3 : (e q / e j)⁻¹ ∈ M.O z := by
      rw [inv_div, heq, div_inv_eq_mul]
      exact hed j
    have hx : c p ^ D / d q ∈ M.O z :=
      key ▸ mul_mem (mul_mem (pow_mem (hmem a) D) h2) (hj.2 q)
    have hy : (c p ^ D / d q)⁻¹ ∈ M.O z := by
      rw [key, mul_inv, mul_inv, ← inv_pow, inv_div (e j) (th a ^ D)]
      exact mul_mem (mul_mem (pow_mem hua.2 D) h1) U3
    exact ⟨hx, by rwa [inv_div] at hy⟩

end GlobalTheory.SiegTh.PullO1
