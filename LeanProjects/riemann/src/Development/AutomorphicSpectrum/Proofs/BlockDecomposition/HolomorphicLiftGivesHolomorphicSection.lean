import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.Holo

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

open GlobalTheory.QCoh.Qcqs in

theorem baseRingHom_toSpecΓ {Y : Scheme.{0}} {B : CommRingCat.{0}} (ψ : B ⟶ Γ(Y, ⊤)) :
    baseRingHom (Y.toSpecΓ ≫ Spec.map ψ) ⊤ = ψ := by
  rw [baseRingHom_comp_SpecMap, baseRingHom_top, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

section Chart

variable (c : ∀ k, Bk n k)

abbrev CoordIdx := {q : Σ k, Bk n k // q.2 ≠ c q.1}

abbrev CRing := MvPolynomial (CoordIdx c) ℤ

abbrev CSpec : Scheme.{0} := Spec (.of (CRing c))

def coordVal (k : Fin (m + 1)) (j : Bk n k) : CRing c :=
  if h : j = c k then 1 else X ⟨⟨k, j⟩, h⟩

def chartMap (k : Fin (m + 1)) : CSpec c ⟶ PSpace ℤ (n k) :=
  ofChartHom (c k) (CommRingCat.ofHom (R := Γ(PSpace ℤ (n k), chart ℤ (n k) (c k))) (S := CRing c)
    (chartLift (c k) (Int.castRingHom _) (coordVal c k)) ≫ (Scheme.ΓSpecIso (.of (CRing c))).inv)

theorem chartMap_top (k : Fin (m + 1)) : ⊤ ≤ chartMap c k ⁻¹ᵁ chart ℤ (n k) (c k) := ofChartHom_preimage _ _

theorem coordVal_self (k : Fin (m + 1)) : coordVal c k (c k) = 1 := dif_pos rfl

theorem pullRatio_chartMap (k : Fin (m + 1)) (j : Bk n k) :
    pullRatio (chartMap c k) ⊤ (c k) (chartMap_top c k) j =
      (Scheme.ΓSpecIso (.of (CRing c))).inv.hom (coordVal c k j) :=
  by
  have e : (chartMap c k).appLE (chart ℤ (n k) (c k)) ⊤ (chartMap_top c k) = _ := ofChartHom_appLE (c k) _
  unfold pullRatio
  rw [e]
  exact congrArg (Scheme.ΓSpecIso (.of (CRing c))).inv.hom (chartLift_ratio (c k) _ (coordVal_self c k) j)

open GlobalTheory.QCoh.Qcqs in
theorem pullRatio_comp_chartMap {Z : Scheme.{0}} (w : Z ⟶ CSpec c) (k : Fin (m + 1))
    (h : ⊤ ≤ (w ≫ chartMap c k) ⁻¹ᵁ chart ℤ (n k) (c k)) (j : Bk n k) :
    pullRatio (w ≫ chartMap c k) ⊤ (c k) h j = (baseRingHom w ⊤).hom (coordVal c k j) := by
  have := appLE_pullRatio (φ := chartMap c k) (W := ⊤) (i := c k) (hi := chartMap_top c k) (j := j) w
    (T := ⊤) le_top
  rw [pullRatio_chartMap] at this
  exact this.symm

def tau : CSpec c ⟶ MP ℤ m n :=
  GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (specZIsTerminal.from _) (chartMap c)
    fun _ => specZIsTerminal.hom_ext _ _

theorem tau_pr (k : Fin (m + 1)) : tau c ≫ prB n k = chartMap c k :=
  GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr m n _ _ _ k

theorem tau_le : ⊤ ≤ tau c ⁻¹ᵁ mchart c := fun x _ => Set.mem_iInter.2 fun k => by
  have h := chartMap_top c k (Set.mem_univ x)
  rw [← tau_pr] at h
  exact h

def rho : CRing c →+* Γ(MP ℤ m n, mchart c) :=
  (dehomog c).comp (rename (R := ℤ) (Subtype.val : CoordIdx c → Σ k, Bk n k)).toRingHom

theorem rho_coordVal (k : Fin (m + 1)) (j : Bk n k) :
    rho c (coordVal c k j) = pullRatio (prB n k) (mchart c) (c k) (mchart_le c k) j := by
  by_cases h : j = c k
  · subst h
    rw [coordVal_self, map_one, pullRatio_self]
  · rw [coordVal, dif_neg h]
    simp only [rho, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, dehomog, eval₂Hom_X']
    exact resG_pullRatio _

theorem tau_rho_coordVal (k : Fin (m + 1)) (j : Bk n k) :
    ((tau c).appLE (mchart c) ⊤ (tau_le c)).hom (rho c (coordVal c k j)) =
      (Scheme.ΓSpecIso (.of (CRing c))).inv.hom (coordVal c k j) := by
  rw [rho_coordVal, appLE_pullRatio, ← pullRatio_chartMap]
  exact pullRatio_of_eq (tau_pr c k) _ _

theorem tau_comp_rho :
    CommRingCat.ofHom (rho c) ≫ (tau c).appLE (mchart c) ⊤ (tau_le c) =
      (Scheme.ΓSpecIso (.of (CRing c))).inv := by
  ext1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
  · have e : (C r : CRing c) = ((r : ℤ) : CRing c) := map_intCast C r
    rw [e]
    exact (map_intCast _ r).trans (map_intCast _ r).symm
  · obtain ⟨⟨k, j⟩, h⟩ := q
    have e : (X ⟨⟨k, j⟩, h⟩ : CRing c) = coordVal c k j := by
      rw [coordVal, dif_neg (show ¬ j = c k from h)]
    rw [e]
    exact tau_rho_coordVal c k j

def toC : (mchart c).toScheme ⟶ CSpec c :=
  (mchart c).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (rho c) ≫ (mchart c).ι.appLE (mchart c) ⊤ (mchart c).ι_preimage_self.ge)

open GlobalTheory.QCoh.Qcqs in
theorem baseRingHom_toC : baseRingHom (toC c) ⊤ =
    CommRingCat.ofHom (rho c) ≫ (mchart c).ι.appLE (mchart c) ⊤ (mchart c).ι_preimage_self.ge :=
  baseRingHom_toSpecΓ _

open GlobalTheory.QCoh.Qcqs in
theorem toC_tau : toC c ≫ tau c = (mchart c).ι := by
  refine GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_
  have e : (toC c ≫ tau c) ≫ prB n k = toC c ≫ chartMap c k := by rw [Category.assoc, tau_pr]
  have h₀ : ⊤ ≤ (toC c ≫ chartMap c k) ⁻¹ᵁ chart ℤ (n k) (c k) :=
    le_trans le_top ((toC c).preimage_mono (chartMap_top c k))
  have h₂ : ⊤ ≤ ((mchart c).ι ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) (c k) :=
    le_trans (mchart c).ι_preimage_self.ge ((mchart c).ι.preimage_mono (mchart_le c k))
  refine GlobalTheory.ProjSpace.hom_ext (specZIsTerminal.hom_ext _ _) fun _ => ⟨⊤, trivial, c k, e ▸ h₀, h₂, fun j => ?_⟩
  rw [pullRatio_of_eq e _ h₀, pullRatio_comp_chartMap, baseRingHom_toC]
  refine (congrArg ((mchart c).ι.appLE (mchart c) ⊤ (mchart c).ι_preimage_self.ge).hom (rho_coordVal c k j)).trans ?_
  exact appLE_pullRatio _ _

end Chart

open GlobalTheory.QCoh.Qcqs in

theorem affine_surj (c : ∀ k, Bk n k) : IsAffineOpen (mchart c) ∧ Function.Surjective (dehomog c) := by
  have hr : Set.range (tau c) ⊆ Set.range (mchart c).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact tau_le c (Set.mem_univ x)
  let τ' : CSpec c ⟶ (mchart c).toScheme := IsOpenImmersion.lift (mchart c).ι (tau c) hr
  have hτ : τ' ≫ (mchart c).ι = tau c := IsOpenImmersion.lift_fac _ _ _
  have h1 : toC c ≫ τ' = 𝟙 _ := by
    rw [← cancel_mono (mchart c).ι, Category.assoc, hτ, toC_tau, Category.id_comp]
  have h2 : τ' ≫ toC c = 𝟙 _ := by
    refine eq_of_baseRingHom_top ?_
    have a : baseRingHom (τ' ≫ toC c) ⊤ = (Scheme.ΓSpecIso (.of (CRing c))).inv := by
      have hle : (⊤ : (CSpec c).Opens) ≤ τ' ⁻¹ᵁ (⊤ : (mchart c).toScheme.Opens) := fun _ _ => trivial
      rw [← baseRingHom_appLE (toC c) τ' ⊤ ⊤ hle, baseRingHom_toC, Category.assoc,
        Scheme.Hom.appLE_comp_appLE]
      refine Eq.trans ?_ (tau_comp_rho c)
      exact congrArg _ (appLE_of_eq hτ _ _ _ _)
    rw [a, baseRingHom_top]
    simp
  have hi : IsIso (toC c) := ⟨τ', h1, h2⟩
  have hb : IsIso (baseRingHom (toC c) ⊤) := by
    rw [baseRingHom_top]
    have : IsIso (toC c).appTop := inferInstanceAs (IsIso (Scheme.Γ.map (toC c).op))
    infer_instance
  refine ⟨IsAffine.of_isIso (toC c), ?_⟩
  have hρ : IsIso (CommRingCat.ofHom (rho c)) := by
    rw [baseRingHom_toC] at hb
    exact IsIso.of_isIso_comp_right _ ((mchart c).ι.appLE (mchart c) ⊤ (mchart c).ι_preimage_self.ge)
  intro b
  obtain ⟨P, rfl⟩ := (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (rho c))).2 b
  exact ⟨rename Subtype.val P, rfl⟩

theorem mem_ptsIn_mchart {y : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} (c : ∀ k, Bk n k) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) ↔ ∀ k, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
  ⟨fun h k => GlobalTheory.CxPts.ptsIn_mono (mchart_le c k) h,
    fun h => GlobalTheory.CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => GlobalTheory.CxPts.mem_ptsIn.1 (h k))⟩

theorem ev_dehomog {y : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : IsUnder y z) (c : ∀ k, Bk n k)
    (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)) (P : Pol n) :
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c P) y =
      eval₂Hom (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) P := by
  have e : (evHom hy).comp (dehomog c) =
      eval₂Hom (Int.castRingHom ℂ) (fun q : (Σ k, Bk n k) => z q / z ⟨q.1, c q.1⟩) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, map_intCast, eval₂Hom_C]
      have : (C r : Pol n) = (r : Pol n) := map_intCast C r
      rw [this, map_intCast, map_intCast]
      rfl
    · obtain ⟨k, j⟩ := q
      have hk := (mem_ptsIn_mchart c).1 hy k
      simp only [RingHom.comp_apply, eval₂Hom_X', dehomog]
      rw [← ev_eq hy, GlobalTheory.CxPts.ev_res _ hy]
      exact (H k (c k)).2 j hk
  rw [ev_eq hy]
  exact congrArg (fun f => f P) e

theorem differentiableOn_eval₂ {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : Set E} {g : E → ι → ℂ}
    (hg : ∀ q, DifferentiableOn ℂ (fun v => g v q) T) (P : MvPolynomial ι ℤ) :
    DifferentiableOn ℂ (fun v => eval₂Hom (Int.castRingHom ℂ) (g v) P) T := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa only [eval₂Hom_C] using differentiableOn_const _
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p q hp => simpa only [map_mul, eval₂Hom_X'] using hp.fun_mul (hg q)

theorem holo_near (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (s : (Fin D → ℂ) → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (hO : IsOpen O) (hγ : DifferentiableOn ℂ γ O) (hU : ∀ v ∈ O, IsUnder (PtsOver.map i rfl _ (s v)) (γ v))
    (v₀ : Fin D → ℂ) (hv₀ : v₀ ∈ O) :
    ∃ O' : Set (Fin D → ℂ), IsOpen O' ∧ v₀ ∈ O' ∧ O' ⊆ O ∧ ContinuousOn s O' ∧ ∀ (W : X.Opens) (f : Γ(X, W)),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ s) (O' ∩ s ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) := by
  have hc : ∀ k, ∃ j, γ v₀ ⟨k, j⟩ ≠ 0 := fun k =>
    ⟨ptChart _ k, ((hU v₀ hv₀) k _).1.1 (GlobalTheory.CxPts.mem_ptsIn.2 (mem_ptChart _ k))⟩
  choose c hc using hc
  have hq : ∀ q, DifferentiableOn ℂ (fun v => γ v q) O := fun q => differentiableOn_pi.1 hγ q
  let O' : Set (Fin D → ℂ) := ⋂ k, (O ∩ (fun v => γ v ⟨k, c k⟩) ⁻¹' {0}ᶜ)
  have hO' : IsOpen O' := isOpen_iInter_of_finite fun k =>
    (hq _).continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hsub : O' ⊆ O := fun v hv => (Set.mem_iInter.1 hv 0).1
  have hne : ∀ v ∈ O', ∀ k, γ v ⟨k, c k⟩ ≠ 0 := fun v hv k => (Set.mem_iInter.1 hv k).2
  have hv₀' : v₀ ∈ O' := Set.mem_iInter.2 fun k => ⟨hv₀, hc k⟩
  obtain ⟨haff, hsurj⟩ := affine_surj c
  have hUa : IsAffineOpen (i ⁻¹ᵁ mchart c) := haff.preimage i
  have hm : ∀ v ∈ O', PtsOver.map i rfl _ (s v) ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := fun v hv =>
    (mem_ptsIn_mchart c).2 fun k => ((hU v (hsub hv)) k (c k)).1.2 (hne v hv k)
  have hs : ∀ v ∈ O', s v ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) := fun v hv => hm v hv
  have hd : ∀ a : Γ(X, i ⁻¹ᵁ mchart c),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) a ∘ s) O' := by
    intro a
    obtain ⟨b, rfl⟩ := i.app_surjective (mchart c) haff a
    obtain ⟨P, rfl⟩ := hsurj b
    refine (differentiableOn_eval₂ (g := fun v q => γ v q / γ v ⟨q.1, c q.1⟩)
      (fun q => by
        simpa only [div_eq_mul_inv] using ((hq q).mono hsub).fun_mul (((hq _).mono hsub).fun_inv fun v hv => hne v hv q.1)) P).congr fun v hv => ?_
    exact (ev_app i rfl (mchart c) _ (s v)).trans (ev_dehomog (hU v (hsub hv)) c (hm v hv) P)
  obtain ⟨h1, h2⟩ := GlobalTheory.CxPts.holo_of_affine hUa hO' hs hd
  exact ⟨O', hO', hv₀', hsub, h1, h2⟩

theorem holo (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (s : (Fin D → ℂ) → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (hO : IsOpen O) (hγ : DifferentiableOn ℂ γ O) (hU : ∀ v ∈ O, IsUnder (PtsOver.map i rfl _ (s v)) (γ v)) :
    ContinuousOn s O ∧ ∀ (W : X.Opens) (f : Γ(X, W)),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ s) (O ∩ s ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) := by
  refine ⟨fun v hv => ?_, fun W f v hv => ?_⟩
  · obtain ⟨O', h1, h2, -, h4, -⟩ := holo_near m n X i D O γ s hO hγ hU v hv
    exact (h4.continuousAt (h1.mem_nhds h2)).continuousWithinAt
  · obtain ⟨O', h1, h2, -, -, h5⟩ := holo_near m n X i D O γ s hO hγ hU v hv.1
    exact (h5 W f v ⟨h2, hv.2⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨O', h1, h2, fun x hx => ⟨hx.1, hx.2.2⟩⟩)

end GlobalTheory.CompanionTheory.MixZ.Holo
