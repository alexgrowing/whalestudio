import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatios
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibility
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfA

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel

namespace PositivityTheory.UnitarySelfGeneration.FrameHeightScaling

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem surj_desc (M : RatModel o Ω) (q : Sp Ω ⟶ M.Z) (hq : q = M.pt) :
    Function.Surjective (Scheme.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) q)).hom := by
  subst hq
  intro x
  obtain ⟨U, f, hne, hf⟩ := M.onto x
  have hgen : genericPoint M.Z ∈ U :=
    ((genericPoint_spec M.Z).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hc : M.pt (IsLocalRing.closedPoint (CommRingCat.of Ω)) ∈ U := by
    have hr : M.pt (IsLocalRing.closedPoint (CommRingCat.of Ω)) ∈ Set.range M.pt := ⟨_, rfl⟩
    rw [M.gen] at hr
    rw [hr]
    exact hgen
  refine ⟨(M.Z.residue _).hom (M.Z.presheaf.germ U _ hc f), ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_descResidueField, ← CommRingCat.comp_apply,
    Scheme.germ_stalkClosedPointTo, ← hf]
  have htop : ⊤ ≤ M.pt ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem M.pt hc).ge
  unfold valF
  rw [dif_pos htop]
  simp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, CommRingCat.comp_apply]
  rfl

theorem pt_comp {Z M : RatModel o Ω} {π : M.Z ⟶ Z.Z} (h : Z.IsHom M (AlgHom.id o Ω) π) : M.pt ≫ π = Z.pt := by
  unfold RatModel.IsHom at h
  rw [h]
  simp [spMap]

theorem map_generic {Z M : RatModel o Ω} {π : M.Z ⟶ Z.Z} (h : Z.IsHom M (AlgHom.id o Ω) π) :
    π (genericPoint M.Z) = genericPoint Z.Z := by
  have hg : genericPoint M.Z ∈ Set.range M.pt := by rw [M.gen]; rfl
  obtain ⟨p, hp⟩ := hg
  have h2 : Z.pt p ∈ Set.range Z.pt := ⟨p, rfl⟩
  rw [Z.gen] at h2
  rw [← hp, ← Scheme.Hom.comp_apply, pt_comp h]
  exact h2

theorem residueDegree_eq_one {Z M : RatModel o Ω} {π : M.Z ⟶ Z.Z} (h : Z.IsHom M (AlgHom.id o Ω) π) :
    π.residueDegree (genericPoint M.Z) = 1 := by
  have hg : genericPoint M.Z ∈ Set.range M.pt := by rw [M.gen]; rfl
  obtain ⟨p, hp⟩ := hg
  have hpc : p = IsLocalRing.closedPoint (CommRingCat.of Ω) := Subsingleton.elim _ _
  subst hpc
  rw [← hp]
  have hcomp : π.residueFieldMap (M.pt (IsLocalRing.closedPoint (CommRingCat.of Ω))) ≫
      M.Z.descResidueField (Scheme.stalkClosedPointTo M.pt) =
      Z.Z.descResidueField (Scheme.stalkClosedPointTo (M.pt ≫ π)) := by
    refine (cancel_epi (Z.Z.residue _)).1 ?_
    simp only [Scheme.residue_residueFieldMap_assoc, Scheme.residue_descResidueField,
      Scheme.stalkClosedPointTo_comp]
    exact CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  have hZ := surj_desc Z (M.pt ≫ π) (pt_comp h)
  rw [← hcomp] at hZ
  have hsurj : Function.Surjective (π.residueFieldMap (M.pt (IsLocalRing.closedPoint (CommRingCat.of Ω)))).hom := by
    intro y
    obtain ⟨z, hz⟩ := hZ ((M.Z.descResidueField (Scheme.stalkClosedPointTo M.pt)).hom y)
    refine ⟨z, (M.Z.descResidueField (Scheme.stalkClosedPointTo M.pt)).hom.injective ?_⟩
    rw [← hz]
    rfl
  unfold Scheme.Hom.residueDegree
  letI := (π.residueFieldMap (M.pt (IsLocalRing.closedPoint (CommRingCat.of Ω)))).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (Z.Z.residueField (π (M.pt (IsLocalRing.closedPoint (CommRingCat.of Ω)))))
      (M.Z.residueField (M.pt (IsLocalRing.closedPoint (CommRingCat.of Ω))))) :=
    ⟨RingHom.injective _, hsurj⟩
  rw [← (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv.finrank_eq]
  exact Module.finrank_self _

private theorem valF_pt_mul' (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty)
    (a b : Γ(M.Z, V)) : valF M.pt V (a * b) = valF M.pt V a * valF M.pt V b := by
  have hgen : genericPoint M.Z ∈ V :=
    ((genericPoint_spec M.Z).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have htop : ⊤ ≤ M.pt ⁻¹ᵁ V := by
    intro w _
    have hw : M.pt w ∈ Set.range M.pt := ⟨w, rfl⟩
    rw [M.gen] at hw
    show M.pt w ∈ V
    rw [hw]
    exact hgen
  unfold valF
  rw [dif_pos htop, dif_pos htop, dif_pos htop]
  simp only [map_mul]

private theorem valF_pt_one' (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) :
    valF M.pt V 1 = 1 := by
  have hgen : genericPoint M.Z ∈ V :=
    ((genericPoint_spec M.Z).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have htop : ⊤ ≤ M.pt ⁻¹ᵁ V := by
    intro w _
    have hw : M.pt w ∈ Set.range M.pt := ⟨w, rfl⟩
    rw [M.gen] at hw
    show M.pt w ∈ V
    rw [hw]
    exact hgen
  unfold valF
  rw [dif_pos htop]
  simp only [map_one]

private theorem exists_unit_valF_pt_eq_of_mem_O (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty)
    {x : Ω} (hx0 : x ≠ 0) (h1 : ∀ z ∈ V, x ∈ M.O z) (h2 : ∀ z ∈ V, x⁻¹ ∈ M.O z) :
    ∃ u : (Γ(M.Z, V))ˣ, valF M.pt V ↑u = x := by
  obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hV).1 (RatModel.mem_ringOn.2 h1)
  obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists hV).1 (RatModel.mem_ringOn.2 h2)
  have hfg : f * g = 1 := RatModel.valF_injective M hV (by
    rw [valF_pt_mul' M hV, valF_pt_one' M hV, hf, hg, mul_inv_cancel₀ hx0])
  exact ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, hf⟩

private theorem valF_pt_unit_inv (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty)
    (v : (Γ(M.Z, V))ˣ) : valF M.pt V ↑v⁻¹ = (valF M.pt V ↑v)⁻¹ := by
  have h := valF_pt_mul' M hV ↑v ↑v⁻¹
  rw [Units.mul_inv, valF_pt_one' M hV] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem valF_pt_res (M : RatModel o Ω) {U V : M.Z.Opens} (h : V ≤ U)
    (hV : (V : Set M.Z).Nonempty) (v : (Γ(M.Z, U))ˣ) :
    valF M.pt V ↑(Semi.res h v) = valF M.pt U ↑v :=
  RatModel.valF_resG M h hV _

private theorem res_eq_mul_of_valF_eq (M : RatModel o Ω) {A B C D W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) (hA : W ≤ A) (hB : W ≤ B) (hC : W ≤ C) (hD : W ≤ D)
    (x : (Γ(M.Z, A))ˣ) (g₁ : (Γ(M.Z, B))ˣ) (g₂ : (Γ(M.Z, C))ˣ) (y : (Γ(M.Z, D))ˣ)
    (h : valF M.pt A ↑x = valF M.pt B ↑g₁ * (valF M.pt C ↑g₂)⁻¹ * valF M.pt D ↑y) :
    Semi.res hA x = Semi.res hB g₁ * (Semi.res hC g₂)⁻¹ * Semi.res hD y := by
  apply Units.ext
  apply RatModel.valF_injective M hW
  rw [Units.val_mul, Units.val_mul, valF_pt_mul' M hW, valF_pt_mul' M hW,
    valF_pt_unit_inv M hW, valF_pt_res M hA hW, valF_pt_res M hB hW,
    valF_pt_res M hC hW, valF_pt_res M hD hW]
  exact h

theorem isometric_of_genTriv (M : RatModel o Ω) (L L' : HermLB M.s) (e : L.B.ι → Ω) (e' : L'.B.ι → Ω)
    (he : M.GenTriv L.B e) (he' : M.GenTriv L'.B e')
    (h1 : ∀ a b, ∀ z ∈ L'.B.U a ⊓ L.B.U b, e b / e' a ∈ M.O z)
    (h2 : ∀ a b, ∀ z ∈ L'.B.U a ⊓ L.B.U b, (e b / e' a)⁻¹ ∈ M.O z)
    (hφ : ∀ (σ : o →+* ℂ) a b (y : CxPts M.s σ), y ∈ ptsIn M.s σ (L'.B.U a) → y ∈ ptsIn M.s σ (L.B.U b) →
      (L'.φ σ).φ a y = (L.φ σ).φ b y + Real.log (‖M.val y.1 (e b / e' a)‖ ^ 2)) : L.Isometric L' := by
  classical
  have hex : ∀ a b, ∃ u : (Γ(M.Z, L'.B.U a ⊓ L.B.U b))ˣ,
      (((L'.B.U a ⊓ L.B.U b : M.Z.Opens)) : Set M.Z).Nonempty →
        valF M.pt (L'.B.U a ⊓ L.B.U b) (u : Γ(M.Z, L'.B.U a ⊓ L.B.U b)) = e b / e' a := by
    intro a b
    by_cases hne : (((L'.B.U a ⊓ L.B.U b : M.Z.Opens)) : Set M.Z).Nonempty
    · have hx0 : e b / e' a ≠ 0 := div_ne_zero (he.ne b) (he'.ne a)
      obtain ⟨u, hu⟩ := exists_unit_valF_pt_eq_of_mem_O M hne hx0 (h1 a b) (h2 a b)
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hne⟩
  choose u hu using hex
  refine ⟨⟨fun p => u p.1 p.2⟩, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨a', b'⟩
    by_cases hW : (((L'.B.U a ⊓ L.B.U b) ⊓ (L'.B.U a' ⊓ L.B.U b') : M.Z.Opens) : Set M.Z).Nonempty
    · obtain ⟨z, hz⟩ := id hW
      have key : valF M.pt (L'.B.U a ⊓ L.B.U b) ↑(u a b) =
          valF M.pt (L'.B.U a ⊓ L'.B.U a') ↑(L'.B.g a a') *
            (valF M.pt (L.B.U b ⊓ L.B.U b') ↑(L.B.g b b'))⁻¹ *
              valF M.pt (L'.B.U a' ⊓ L.B.U b') ↑(u a' b') := by
        rw [hu a b ⟨z, hz.1⟩, hu a' b' ⟨z, hz.2⟩, he'.g_eq a a' ⟨z, hz.1.1, hz.2.1⟩,
          he.g_eq b b' ⟨z, hz.1.2, hz.2.2⟩]
        have := he.ne b
        have := he.ne b'
        have := he'.ne a
        have := he'.ne a'
        field_simp
      exact res_eq_mul_of_valF_eq M hW _ _ _ _ _ _ _ _ key
    · have hbot : ((L'.B.U a ⊓ L.B.U b) ⊓ (L'.B.U a' ⊓ L.B.U b') : M.Z.Opens) = ⊥ := by
        rw [← TopologicalSpace.Opens.coe_eq_empty]
        exact Set.not_nonempty_iff_eq_empty.mp hW
      exact Units.ext (@Subsingleton.elim _
        (CommRingCat.subsingleton_of_isTerminal (M.Z.sheaf.isTerminalOfEqEmpty hbot)) _ _)
  · intro σ a b y hya hyb
    rw [hφ σ a b y hya hyb]
    have hr : Set.range y.1 ⊆ ((L'.B.U a ⊓ L.B.U b : M.Z.Opens) : Set M.Z) := by
      rintro _ ⟨w, rfl⟩
      exact ⟨hya (show w ∈ (⊤ : (Sp ℂ).Opens) from trivial), hyb (show w ∈ (⊤ : (Sp ℂ).Opens) from trivial)⟩
    have hne : ((L'.B.U a ⊓ L.B.U b : M.Z.Opens) : Set M.Z).Nonempty := ⟨_, hr ⟨IsLocalRing.closedPoint ℂ, rfl⟩⟩
    have hev : ev M.s σ (L'.B.U a ⊓ L.B.U b) ↑(u a b) y = M.val y.1 (e b / e' a) :=
      (RatModel.val_eq hr (hu a b hne)).symm
    show _ = _ + Real.log (‖ev M.s σ (L'.B.U a ⊓ L.B.U b) ↑(u a b) y‖ ^ 2)
    rw [hev]

theorem exists_bundle (Z : RatModel o Ω) {m : ℕ} (t : Fin m → Ω) (ht : Z.HasDiv t) :
    ∃ (H : LB Z.Z) (_ : H.IsLB) (e : H.ι → Ω) (s : Fin m → H.Sec), Z.GenTriv H e ∧ (∀ k, Z.HasVal e (s k) (t k)) ∧
      ⨆ k, nonzeroLocus (s k) = ⊤ := by
  classical
  let d : Fin m → Ω := fun i => if t i = 0 then 1 else t i
  have hd : ∀ i, t i ≠ 0 → d i = t i := fun i hi => if_neg hi
  have hdne : ∀ i, d i ≠ 0 := by
    intro i
    by_cases h : t i = 0
    · simp [d, h]
    · rw [hd i h]; exact h
  have hopen : ∀ i, IsOpen {z : Z.Z | Z.Div t i z} := by
    intro i
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨hz1, hz2⟩ := (show Z.Div t i z from hz)
    choose V f hzV hf using fun j => RatModel.mem_O.mp (hz2 j)
    refine ⟨⋂ j, (V j : Set Z.Z), ?_, ?_, ?_⟩
    · intro z' hz'
      exact (show Z.Div t i z' from ⟨hz1, fun j => RatModel.mem_O.mpr ⟨V j, f j, Set.mem_iInter.mp hz' j, hf j⟩⟩)
    · exact isOpen_iInter_of_finite fun j => (V j).isOpen
    · exact Set.mem_iInter.mpr hzV
  let U : Fin m → Z.Z.Opens := fun i => ⟨{z | Z.Div t i z}, hopen i⟩
  have hmem : ∀ i z, z ∈ U i ↔ Z.Div t i z := fun _ _ => Iff.rfl
  have hcov : ⨆ k, U k = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨i, hi⟩ := ht z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hmem i z).2 hi⟩
  have hrat : ∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ Z.O z := by
    intro k k' z hz
    obtain ⟨hk1, hk2⟩ := (hmem k z).1 hz.1
    obtain ⟨hk'1, _⟩ := (hmem k' z).1 hz.2
    rw [hd k hk1, hd k' hk'1]
    exact hk2 k'
  obtain ⟨g, hLB, hGT⟩ := RatModel.exists_isLB_genTriv_of_ratios o Ω Z (Fin m) U d hcov hdne hrat
  have hsec : ∀ k, ∃ σ : LB.Sec (⟨Fin m, U, g⟩ : LB Z.Z), Z.HasVal d σ (t k) := by
    intro k
    apply hGT.exists_sec_hasVal
    intro l z hz
    obtain ⟨hl1, hl2⟩ := (hmem l z).1 hz
    rw [hd l hl1]
    exact hl2 k
  choose s hs using hsec
  have hloc : ∀ (l : Fin m), ∀ z ∈ U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ Z.O z := by
    intro l z hz
    obtain ⟨hl1, _⟩ := (hmem l z).1 hz
    refine ⟨l, hl1, ?_⟩
    rw [hd l hl1, div_self hl1]
    exact one_mem _
  refine ⟨⟨Fin m, U, g⟩, hLB, d, s, hGT, hs, ?_⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨i, hi⟩ := ht z
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (RatModel.mem_nonzeroLocus_iff_div hLB hGT hs hloc i z).2 hi⟩

private theorem valF_mul_var (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty)
    (a b : Γ(M.Z, V)) : valF M.pt V (a * b) = valF M.pt V a * valF M.pt V b := by
  have hgen : genericPoint M.Z ∈ V :=
    ((genericPoint_spec M.Z).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have htop : ⊤ ≤ M.pt ⁻¹ᵁ V := by
    intro w _
    have hw : M.pt w ∈ Set.range M.pt := ⟨w, rfl⟩
    rw [M.gen] at hw
    show M.pt w ∈ V
    rw [hw]
    exact hgen
  unfold valF
  rw [dif_pos htop, dif_pos htop, dif_pos htop]
  simp only [map_mul]

private theorem valF_one_var (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) :
    valF M.pt V 1 = 1 := by
  have hgen : genericPoint M.Z ∈ V :=
    ((genericPoint_spec M.Z).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have htop : ⊤ ≤ M.pt ⁻¹ᵁ V := by
    intro w _
    have hw : M.pt w ∈ Set.range M.pt := ⟨w, rfl⟩
    rw [M.gen] at hw
    show M.pt w ∈ V
    rw [hw]
    exact hgen
  unfold valF
  rw [dif_pos htop]
  simp only [map_one]

theorem exists_unit {M : RatModel o Ω} {H : LB M.Z} {e : H.ι → Ω} (he : M.GenTriv H e) {m : ℕ}
    {s : Fin m → H.Sec} {t : Fin m → Ω} (hv : ∀ k, M.HasVal e (s k) (t k)) (hs : ⨆ k, nonzeroLocus (s k) = ⊤)
    (i : H.ι) (z : M.Z) (hz : z ∈ H.U i) : ∃ k, t k ≠ 0 ∧ e i / t k ∈ M.O z := by
  have hzt : z ∈ (⊤ : M.Z.Opens) := trivial
  rw [← hs] at hzt
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hzt
  unfold nonzeroLocus at hk
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hk
  have hVl : M.Z.basicOpen ((s k).f l) ≤ H.U l := M.Z.basicOpen_le _
  have hVne : ((M.Z.basicOpen ((s k).f l) : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hl⟩
  have hu : IsUnit (resG M.Z hVl ((s k).f l)) := M.Z.toRingedSpace.isUnit_res_basicOpen _
  obtain ⟨u, hu'⟩ := hu
  have hval : valF M.pt _ (resG M.Z hVl ((s k).f l)) = t k / e l := by
    rw [RatModel.valF_resG M hVl hVne, hv k l ⟨z, hVl hl⟩]
  have h1 : valF M.pt _ (↑u⁻¹ : Γ(M.Z, M.Z.basicOpen ((s k).f l))) * (t k / e l) = 1 := by
    rw [← hval, ← hu', ← valF_mul_var M hVne, Units.inv_mul, valF_one_var M hVne]
  have htk : t k ≠ 0 := by
    intro h0
    rw [h0, zero_div, mul_zero] at h1
    exact zero_ne_one h1
  have hinv : e l / t k ∈ M.O z := by
    have he1 := (eq_one_div_of_mul_eq_one_left h1).trans (one_div_div _ _)
    rw [← he1]
    exact RatModel.valF_mem_O hl _
  have hzli : z ∈ H.U l ⊓ H.U i := ⟨hVl hl, hz⟩
  have hil : e i / e l ∈ M.O z := by
    rw [← he.g_eq l i ⟨z, hzli⟩]
    exact RatModel.valF_mem_O hzli _
  refine ⟨k, htk, ?_⟩
  have hmul : e i / t k = e i / e l * (e l / t k) := by
    have := he.ne l
    field_simp
  rw [hmul]
  exact mul_mem hil hinv

theorem mem_of_hasVal {M : RatModel o Ω} {H : LB M.Z} {e : H.ι → Ω} {s : H.Sec} {x : Ω} (hv : M.HasVal e s x)
    {i : H.ι} {z : M.Z} (hz : z ∈ H.U i) : x / e i ∈ M.O z := by
  exact RatModel.mem_O.mpr ⟨H.U i, s.f i, hz, hv i ⟨z, hz⟩⟩

theorem valR_sec {M : RatModel o Ω} {H : LB M.Z} {e : H.ι → Ω} {s : H.Sec} {x : Ω} (hv : M.HasVal e s x)
    {σ : o →+* ℂ} {i : H.ι} {y : CxPts M.s σ} (hy : y ∈ ptsIn M.s σ (H.U i)) :
    valR y.1 (H.U i) (s.f i) = M.val y.1 (x / e i) := by
  have hr : Set.range y.1 ⊆ (H.U i : Set M.Z) := by
    rintro _ ⟨w, rfl⟩
    exact hy (show w ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hne : ((H.U i : Set M.Z)).Nonempty := ⟨_, hr ⟨IsLocalRing.closedPoint ℂ, rfl⟩⟩
  exact (RatModel.val_eq hr (hv i hne)).symm

private theorem div_mem_O_of_div_of_genTriv (N : RatModel o Ω) {m : ℕ} {H : LB N.Z} {e : H.ι → Ω}
    (he : N.GenTriv H e) {s : Fin m → H.Sec} {t : Fin m → Ω} (hv : ∀ k, N.HasVal e (s k) (t k))
    (hs : ⨆ k, nonzeroLocus (s k) = ⊤) {a : H.ι} {z : N.Z} (hz : z ∈ H.U a) {k : Fin m}
    (hk : N.Div t k z) : e a / t k ∈ N.O z ∧ t k / e a ∈ N.O z := by
  obtain ⟨k0, hk0, h0⟩ := exists_unit he hv hs a z hz
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨?_, mem_of_hasVal (hv k) hz⟩
  have hmul : e a / t k = e a / t k0 * (t k0 / t k) := by field_simp
  rw [hmul]
  exact mul_mem h0 (hk2 k0)

private theorem val_ne_zero_of_unit_mem_O (N : RatModel o Ω) (y : Sp ℂ ⟶ N.Z) {x : Ω}
    (hx : x ∈ N.O (y (IsLocalRing.closedPoint ℂ))) (hx' : x⁻¹ ∈ N.O (y (IsLocalRing.closedPoint ℂ)))
    (hx0 : x ≠ 0) : N.val y x ≠ 0 := by
  have hsp : ∀ w, y w ⤳ y (IsLocalRing.closedPoint ℂ) := by
    intro w
    have hw := Subsingleton.elim w (IsLocalRing.closedPoint ℂ)
    subst hw
    exact specializes_rfl
  intro h0
  have h := RatModel.val_mul hsp hx hx'
  rw [mul_inv_cancel₀ hx0, RatModel.val_one, h0, zero_mul] at h
  exact one_ne_zero h

theorem isometric_pull_fs {Z M : RatModel o Ω} {π : M.Z ⟶ Z.Z} (hπ : Z.IsHom M (AlgHom.id o Ω) π) {m : ℕ}
    {t : Fin m → Ω} {H' : LB Z.Z} (hH' : H'.IsLB) {e' : H'.ι → Ω} (he' : Z.GenTriv H' e') {s' : Fin m → H'.Sec}
    (hv' : ∀ k, Z.HasVal e' (s' k) (t k)) (hs' : ⨆ k, nonzeroLocus (s' k) = ⊤)
    {H : LB M.Z} (hH : H.IsLB) {e : H.ι → Ω} (he : M.GenTriv H e) {s : Fin m → H.Sec}
    (hv : ∀ k, M.HasVal e (s k) (t k)) (hs : ⨆ k, nonzeroLocus (s k) = ⊤)
    (Mt Mt' : (o →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) (hdet hc hdet' hc') (r : ℝ)
    (hM : ∀ σ, Mt' σ = ((Real.exp r : ℝ) : ℂ) • Mt σ) :
    ((HermLB.fs Z.s hH' s' hs' Mt' hdet' hc').pull π hπ.inducedModelMorphism_comp_structureMap).Isometric
      ((HermLB.fs M.s hH s hs Mt hdet hc).shift (fun _ => r) (fun _ => rfl)) := by
  have hloc' : ∀ (l : H'.ι), ∀ z ∈ H'.U l, ∃ i, t i ≠ 0 ∧ e' l / t i ∈ Z.O z :=
    fun l z hz => exists_unit he' hv' hs' l z hz
  have hunit : ∀ (a : H.ι) (b0 : H'.ι) (z : M.Z), z ∈ H.U a → π z ∈ H'.U b0 →
      e' b0 / e a ∈ M.O z ∧ e a / e' b0 ∈ M.O z := by
    intro a b0 z hza hzb
    have hzt : π z ∈ (⊤ : Z.Z.Opens) := trivial
    rw [← hs'] at hzt
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hzt
    have hkZ : Z.Div t k (π z) := (RatModel.mem_nonzeroLocus_iff_div hH' he' hv' hloc' k (π z)).1 hk
    have hkM : M.Div t k z := hπ.div hkZ
    obtain ⟨hZ1, hZ2⟩ := div_mem_O_of_div_of_genTriv Z he' hv' hs' hzb hkZ
    obtain ⟨hM1, hM2⟩ := div_mem_O_of_div_of_genTriv M he hv hs hza hkM
    have hZ1' : e' b0 / t k ∈ M.O z := hπ.map_mem_O hZ1
    have hZ2' : t k / e' b0 ∈ M.O z := hπ.map_mem_O hZ2
    have htk : t k ≠ 0 := hkM.1
    have hb0 := he'.ne b0
    have ha0 := he.ne a
    have h1 : e' b0 / e a = e' b0 / t k * (t k / e a) := by field_simp
    have h2 : e a / e' b0 = e a / t k * (t k / e' b0) := by field_simp
    refine ⟨?_, ?_⟩
    · rw [h1]; exact mul_mem hZ1' hM2
    · rw [h2]; exact mul_mem hM1 hZ2'
  refine isometric_of_genTriv M _ _ (fun k => e' (k PUnit.unit)) e (he'.pull hπ) he ?_ ?_ ?_
  · intro a b z hz
    exact (hunit a (b PUnit.unit) z hz.1 (Set.mem_iInter.1 hz.2 PUnit.unit)).1
  · intro a b z hz
    rw [inv_div]
    exact (hunit a (b PUnit.unit) z hz.1 (Set.mem_iInter.1 hz.2 PUnit.unit)).2
  · intro σ a b y hya hyb
    simp only [HermLB.shift, HermLB.pull, HermLB.fs, Weight.addFn, Weight.linComb, Weight.pull, Weight.fsBasis,
      Weight.fs, Weight.combVal, Finset.univ_unique, Finset.sum_singleton, Int.cast_one, one_mul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hya' : y ∈ ptsIn M.s σ (H.U a) := hya
    have hmemb : ∀ w, π (y.1 w) ∈ H'.U (b default) := fun w =>
      Set.mem_iInter.1 (hyb (show w ∈ (⊤ : (Sp ℂ).Opens) from trivial)) default
    generalize hy' : Points.PtsOver.map π hπ.inducedModelMorphism_comp_structureMap (spMap σ) y = y'
    have hy1 : y'.1 = y.1 ≫ π := by rw [← hy']; rfl
    have hy'b : y' ∈ ptsIn Z.s σ (H'.U (b default)) := by
      intro w _
      show y'.1 w ∈ H'.U (b default)
      rw [hy1, Scheme.Hom.comp_apply]
      exact hmemb w
    have hz0a : y.1 (IsLocalRing.closedPoint ℂ) ∈ H.U a :=
      hya' (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    have hz0b : π (y.1 (IsLocalRing.closedPoint ℂ)) ∈ H'.U (b default) := hmemb _
    have hsp : ∀ w, y.1 w ⤳ y.1 (IsLocalRing.closedPoint ℂ) := by
      intro w
      have hw := Subsingleton.elim w (IsLocalRing.closedPoint ℂ)
      subst hw
      exact specializes_rfl
    have hV : ∀ j, (secVal M.s σ) (s j) a y = M.val y.1 (t j / e a) := fun j => valR_sec (hv j) hya'
    have hW : ∀ j, (secVal Z.s σ) (s' j) (b default) y' = M.val y.1 (t j / e' (b default)) := by
      intro j
      have h1 : (secVal Z.s σ) (s' j) (b default) y' = Z.val y'.1 (t j / e' (b default)) :=
        valR_sec (hv' j) hy'b
      rw [h1, hy1]
      exact hπ.val_comp y.1 (IsLocalRing.closedPoint ℂ) (mem_of_hasVal (hv' j) hz0b)
    have hcu := hunit a (b default) _ hz0a hz0b
    have hc0 : M.val y.1 (e' (b default) / e a) ≠ 0 := by
      apply val_ne_zero_of_unit_mem_O M y.1 hcu.1 (by rw [inv_div]; exact hcu.2)
      exact div_ne_zero (he'.ne _) (he.ne a)
    have hfac : ∀ j, M.val y.1 (t j / e a) =
        M.val y.1 (t j / e' (b default)) * M.val y.1 (e' (b default) / e a) := by
      intro j
      have hmem : t j / e' (b default) ∈ M.O (y.1 (IsLocalRing.closedPoint ℂ)) :=
        hπ.map_mem_O (mem_of_hasVal (hv' j) hz0b)
      rw [← RatModel.val_mul hsp hmem hcu.1]
      congr 1
      have := he'.ne (b default)
      field_simp
    have hWne : ∃ k, M.val y.1 (t k / e' (b default)) ≠ 0 := by
      have hzt : π (y.1 (IsLocalRing.closedPoint ℂ)) ∈ (⊤ : Z.Z.Opens) := trivial
      rw [← hs'] at hzt
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hzt
      have hkZ : Z.Div t k (π (y.1 (IsLocalRing.closedPoint ℂ))) :=
        (RatModel.mem_nonzeroLocus_iff_div hH' he' hv' hloc' k _).1 hk
      obtain ⟨hZ1, hZ2⟩ := div_mem_O_of_div_of_genTriv Z he' hv' hs' hz0b hkZ
      refine ⟨k, val_ne_zero_of_unit_mem_O M y.1 (hπ.map_mem_O hZ2) ?_ (div_ne_zero hkZ.1 (he'.ne _))⟩
      rw [inv_div]
      exact hπ.map_mem_O hZ1
    have hT : (∑ x, ‖∑ j, Mt σ j x * M.val y.1 (t j / e' (b default))‖ ^ 2) ≠ 0 := by
      intro h0
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at h0
      apply hdet σ
      rw [← Matrix.exists_vecMul_eq_zero_iff]
      refine ⟨fun j => M.val y.1 (t j / e' (b default)), ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hWne
        intro h
        exact hk (congrFun h k)
      · funext x
        have hx := h0 x (Finset.mem_univ x)
        have hx' := (pow_eq_zero_iff (n := 2) (by norm_num)).1 hx
        rw [norm_eq_zero] at hx'
        simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
        rw [← hx']
        apply Finset.sum_congr rfl
        intro j _
        ring
    simp only [hV, hW, hfac, hM σ, Matrix.smul_apply, smul_eq_mul]
    have hL : ∀ x, ‖∑ j, Mt σ j x * (M.val y.1 (t j / e' (b default)) * M.val y.1 (e' (b default) / e a))‖ ^ 2
        = ‖∑ j, Mt σ j x * M.val y.1 (t j / e' (b default))‖ ^ 2 * ‖M.val y.1 (e' (b default) / e a)‖ ^ 2 := by
      intro x
      rw [← mul_pow, ← norm_mul, Finset.sum_mul]
      congr 2
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hR : ∀ x, ‖∑ j, ((Real.exp r : ℝ) : ℂ) * Mt σ j x * M.val y.1 (t j / e' (b default))‖ ^ 2
        = Real.exp r ^ 2 * ‖∑ j, Mt σ j x * M.val y.1 (t j / e' (b default))‖ ^ 2 := by
      intro x
      rw [show Real.exp r ^ 2 = ‖((Real.exp r : ℝ) : ℂ)‖ ^ 2 by
        rw [Complex.norm_of_nonneg (Real.exp_pos r).le], ← mul_pow, ← norm_mul, Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [hL, hR, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [Real.log_mul hT (pow_ne_zero 2 (norm_ne_zero_iff.2 hc0)),
      Real.log_mul (pow_ne_zero 2 (Real.exp_pos r).ne') hT,
      show Real.log (Real.exp r ^ 2) = 2 * r by rw [Real.log_pow, Real.log_exp]; push_cast; ring]
    ring

end PositivityTheory.UnitarySelfGeneration.FrameHeightScaling
