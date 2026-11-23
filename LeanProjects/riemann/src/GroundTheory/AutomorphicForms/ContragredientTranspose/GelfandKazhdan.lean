import Mathlib
import GroundTheory.AutomorphicForms.WhittakerOrbit
import GroundTheory.AutomorphicForms.WhittakerCriterion
import GroundTheory.AutomorphicForms.WhittakerGroups
import GroundTheory.AutomorphicForms.WhittakerDistribution
import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity

namespace GroundTheory.Automorphic.ContragredientTranspose

open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker

section ConjActTop

variable {G : Type*} [Group G] [TopologicalSpace G]

scoped instance conjActTopology : TopologicalSpace (ConjAct G) := ‹TopologicalSpace G›

theorem continuous_ofConjAct : Continuous (ConjAct.ofConjAct : ConjAct G → G) := continuous_id

theorem continuous_toConjAct : Continuous (ConjAct.toConjAct : G → ConjAct G) := continuous_id

scoped instance [IsTopologicalGroup G] : IsTopologicalGroup (ConjAct G) :=
  inferInstanceAs (IsTopologicalGroup G)

scoped instance [LocallyCompactSpace G] : LocallyCompactSpace (ConjAct G) :=
  inferInstanceAs (LocallyCompactSpace G)

scoped instance [T2Space G] : T2Space (ConjAct G) := inferInstanceAs (T2Space G)

scoped instance [TotallyDisconnectedSpace G] : TotallyDisconnectedSpace (ConjAct G) :=
  inferInstanceAs (TotallyDisconnectedSpace G)

scoped instance [SigmaCompactSpace G] : SigmaCompactSpace (ConjAct G) :=
  inferInstanceAs (SigmaCompactSpace G)

scoped instance [IsTopologicalGroup G] : ContinuousSMul (ConjAct G) G where
  continuous_smul := by
    have e : (fun p : ConjAct G × G => p.1 • p.2) =
        fun p => ConjAct.ofConjAct p.1 * p.2 * (ConjAct.ofConjAct p.1)⁻¹ := by
      funext p
      exact ConjAct.smul_def _ _
    rw [e]
    have h1 : Continuous fun p : ConjAct G × G => ConjAct.ofConjAct p.1 :=
      continuous_ofConjAct.comp continuous_fst
    exact (h1.mul continuous_snd).mul h1.inv

end ConjActTop

section Transpose

variable {F : Type*} [Field F] {n : ℕ}

def transposeGL (g : GL (Fin n) F) : GL (Fin n) F :=
  ⟨(g : Matrix (Fin n) (Fin n) F)ᵀ, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

@[simp]
theorem coe_transposeGL (g : GL (Fin n) F) :
    (transposeGL g : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F)ᵀ := rfl

@[simp]
theorem transposeGL_transposeGL (g : GL (Fin n) F) : transposeGL (transposeGL g) = g :=
  Units.ext (transpose_transpose _)

theorem transposeGL_mul (g h : GL (Fin n) F) :
    transposeGL (g * h) = transposeGL h * transposeGL g :=
  Units.ext (by simp [transpose_mul])

@[simp]
theorem transposeGL_one : transposeGL (1 : GL (Fin n) F) = 1 :=
  Units.ext (by simp)

theorem transposeGL_inv (g : GL (Fin n) F) : transposeGL g⁻¹ = (transposeGL g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← transposeGL_mul, mul_inv_cancel, transposeGL_one]

def thetaT : GL (Fin n) F ≃* GL (Fin n) F where
  toFun g := (transposeGL g)⁻¹
  invFun g := (transposeGL g)⁻¹
  left_inv g := by simp [← transposeGL_inv]
  right_inv g := by simp [← transposeGL_inv]
  map_mul' g h := by rw [transposeGL_mul, _root_.mul_inv_rev]

theorem thetaT_apply (g : GL (Fin n) F) : thetaT g = (transposeGL g)⁻¹ := rfl

theorem transposeGL_smul (h : ConjAct (GL (Fin n) F)) (x : GL (Fin n) F) :
    transposeGL (h • x) = ConjAct.toConjAct (thetaT (ConjAct.ofConjAct h)) • transposeGL x := by
  rw [ConjAct.smul_def, ConjAct.toConjAct_smul, thetaT_apply, transposeGL_mul, transposeGL_mul,
    transposeGL_inv, inv_inv, mul_assoc]

variable [TopologicalSpace F]

theorem continuous_transposeGL :
    Continuous (transposeGL : GL (Fin n) F → GL (Fin n) F) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_transpose,
    Units.continuous_coe_inv.matrix_transpose⟩

def transposeHomeo : GL (Fin n) F ≃ₜ GL (Fin n) F where
  toFun := transposeGL
  invFun := transposeGL
  left_inv := transposeGL_transposeGL
  right_inv := transposeGL_transposeGL
  continuous_toFun := continuous_transposeGL
  continuous_invFun := continuous_transposeGL

@[simp]
theorem transposeHomeo_apply (g : GL (Fin n) F) : transposeHomeo g = transposeGL g := rfl

theorem continuous_thetaT [IsTopologicalRing F] : Continuous (thetaT : GL (Fin n) F → GL (Fin n) F) :=
  continuous_transposeGL.inv

end Transpose

section Baire

variable {H X : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H] [TopologicalSpace X]
  [T2Space X] [LocallyCompactSpace X] [MulAction H X] [ContinuousSMul H X]

theorem exists_isClosed_diff_orbit {Z : Set X} (hZ : IsClosed Z) (hZne : Z.Nonempty)
    (hZinv : ∀ h : H, ∀ x ∈ Z, h • x ∈ Z) {s : Set X} (hs : s.Countable)
    (hcov : Z ⊆ ⋃ x ∈ s, orbit H x) :
    ∃ x₀ ∈ Z, IsClosed (Z \ orbit H x₀) := by
  have : LocallyCompactSpace Z := hZ.locallyCompactSpace
  have : Nonempty Z := hZne.to_subtype
  have hsc : (s ∩ Z).Countable := hs.mono inter_subset_left
  have : Countable ↥(s ∩ Z) := hsc.to_subtype
  let f : (s ∩ Z : Set X) × ℕ → Set Z := fun i =>
    Subtype.val ⁻¹' ((fun h : H => h • (i.1 : X)) '' compactCovering H i.2)
  have hfc : ∀ i, IsClosed (f i) := fun i =>
    (((isCompact_compactCovering H i.2).image
      (continuous_id.smul continuous_const)).isClosed).preimage continuous_subtype_val
  have hfU : ⋃ i, f i = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨x, hxs, hzx⟩ := mem_iUnion₂.1 (hcov z.2)
    obtain ⟨h, hh⟩ := hzx
    have hxZ : x ∈ Z := by
      have := hZinv h⁻¹ _ z.2
      rwa [← hh, inv_smul_smul] at this
    obtain ⟨k, hk⟩ := mem_iUnion.1 ((iUnion_compactCovering H).symm ▸ mem_univ h :
      h ∈ ⋃ k, compactCovering H k)
    exact mem_iUnion.2 ⟨(⟨x, hxs, hxZ⟩, k), ⟨h, hk, hh⟩⟩
  obtain ⟨⟨⟨x, hxs, hxZ⟩, k⟩, hint⟩ := nonempty_interior_of_iUnion_of_closed hfc hfU
  obtain ⟨W, hWo, hW⟩ := isOpen_induced_iff.1 (isOpen_interior (s := f (⟨x, hxs, hxZ⟩, k)))
  obtain ⟨w, hw⟩ := hint
  have hwW : (w : X) ∈ W := by
    have : w ∈ Subtype.val ⁻¹' W := hW ▸ hw
    exact this
  have hsub : ∀ z : Z, (z : X) ∈ W → (z : X) ∈ orbit H x := by
    intro z hz
    have : z ∈ interior (f (⟨x, hxs, hxZ⟩, k)) := hW ▸ (show z ∈ Subtype.val ⁻¹' W from hz)
    obtain ⟨h, -, hh⟩ := interior_subset this
    exact ⟨h, hh⟩
  refine ⟨x, hxZ, ?_⟩
  have hwO : (w : X) ∈ orbit H x := hsub w hwW
  have key : Z \ orbit H x = Z ∩ ⋂ h : H, (fun z => h • z) ⁻¹' Wᶜ := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_iInter, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨hzZ, hzO⟩
      refine ⟨hzZ, fun h hhz => hzO ?_⟩
      have := hsub ⟨h • z, hZinv h z hzZ⟩ hhz
      obtain ⟨k', hk'⟩ := this
      have hk'' : k' • x = h • z := hk'
      refine ⟨h⁻¹ * k', ?_⟩
      show (h⁻¹ * k') • x = z
      rw [mul_smul, hk'', inv_smul_smul]
    · rintro ⟨hzZ, hzW⟩
      refine ⟨hzZ, fun hzO => ?_⟩
      obtain ⟨a, ha⟩ := hzO
      obtain ⟨b, hb⟩ := hwO
      have ha' : a • x = z := ha
      have hb' : b • x = (w : X) := hb
      apply hzW (b * a⁻¹)
      rw [mul_smul, ← ha', inv_smul_smul, hb']
      exact hwW
  rw [key]
  exact hZ.inter (isClosed_iInter fun h =>
    hWo.isClosed_compl.preimage (continuous_const_smul h))

end Baire

section Relations

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}

def tauSpan (U : Set (GL (Fin n) F)) : Submodule ℂ (GL (Fin n) F → ℂ) :=
  Submodule.span ℂ {r | ∃ f ∈ supportedIn U, r = f + fun x => f (transposeGL x)}

def relT (U : Set (GL (Fin n) F)) : Submodule ℂ (GL (Fin n) F → ℂ) :=
  relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) U ⊔ tauSpan U

omit [IsTopologicalRing F] in
theorem comp_transposeGL_mem {U : Set (GL (Fin n) F)}
    (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) {f : GL (Fin n) F → ℂ} (hf : f ∈ supportedIn U) :
    (fun x => f (transposeGL x)) ∈ supportedIn U :=
  ⟨⟨hf.1.1.comp_continuous continuous_transposeGL, hf.1.2.comp_homeomorph transposeHomeo⟩,
    fun x hx => (hUτ x).1 (hf.2 hx)⟩

omit [IsTopologicalRing F] in
theorem tauSpan_le {U : Set (GL (Fin n) F)} (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) :
    tauSpan U ≤ supportedIn U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  exact (supportedIn U).add_mem hf (comp_transposeGL_mem hUτ hf)

theorem relT_le {U : Set (GL (Fin n) F)} (hUinv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ U, h • x ∈ U)
    (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) : relT U ≤ supportedIn U :=
  sup_le (relSpan_le_supportedIn _ hUinv) (tauSpan_le hUτ)

omit [IsTopologicalRing F] in
theorem relT_mono {U V : Set (GL (Fin n) F)} (hUV : U ⊆ V) : relT U ≤ relT V := by
  refine sup_le_sup (Submodule.span_mono ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨h, f, hf, rfl⟩
    exact ⟨h, f, supportedIn_mono hUV hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f, supportedIn_mono hUV hf, rfl⟩

end Relations

section OneClass

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem supportedIn_le_relT_sup {U C : Set (GL (Fin n) F)} (hU : IsOpen U) (hC : IsClosed C)
    {x₀ : GL (Fin n) F} (hO : U ∩ C = orbit (ConjAct (GL (Fin n) F)) x₀)
    (hUinv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ U, h • x ∈ U)
    (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) {S : GL (Fin n) F} (hS : transposeGL S = S)
    (hSx : S * x₀ * S⁻¹ = transposeGL x₀) :
    supportedIn U ≤ relT U ⊔ (supportedIn U ⊓ vanishingOn C) := by
  classical

  let Φ : GL (Fin n) F → GL (Fin n) F := fun g => S⁻¹ * thetaT g * S
  have hθS : thetaT S = S⁻¹ := by rw [thetaT_apply, hS]
  have hθS' : thetaT S⁻¹ = S := by rw [map_inv, hθS, inv_inv]
  have hθθ : ∀ g : GL (Fin n) F, thetaT (thetaT g) = g := fun g => by
    rw [thetaT_apply, thetaT_apply, transposeGL_inv, transposeGL_transposeGL, inv_inv]
  have hΦΦ : ∀ g, Φ (Φ g) = g := fun g => by
    simp only [Φ, map_mul, hθS, hθS', hθθ]
    group
  have hΦc : Continuous Φ := (continuous_const.mul continuous_thetaT).mul continuous_const

  have hτk : ∀ k : GL (Fin n) F, transposeGL (ConjAct.toConjAct k • x₀) =
      ConjAct.toConjAct (S * Φ k) • x₀ := by
    intro k
    rw [transposeGL_smul, ConjAct.ofConjAct_toConjAct, ← hSx, ← ConjAct.toConjAct_smul,
      ← mul_smul, ← map_mul]
    congr 2
    simp only [Φ]
    group

  let ΦH : ConjAct (GL (Fin n) F) → ConjAct (GL (Fin n) F) :=
    fun l => ConjAct.toConjAct (Φ (ConjAct.ofConjAct l))
  have hΦHc : Continuous ΦH := continuous_toConjAct.comp (hΦc.comp continuous_ofConjAct)
  have hΦHmul : ∀ a b, ΦH (a * b) = ΦH a * ΦH b := fun a b => by
    simp only [ΦH]
    rw [← map_mul]
    congr 1
    simp only [Φ, map_mul]
    group
  have hΦHinv : ∀ a, ΦH a⁻¹ = (ΦH a)⁻¹ := fun a => by
    simp only [ΦH]
    rw [← map_inv]
    congr 1
    simp only [Φ, map_inv]
    group
  have hΦHone : ΦH 1 = 1 := by
    simp only [ΦH, Φ, map_one, mul_one, inv_mul_cancel]
  obtain ⟨L, hLc⟩ := exists_compactOpenSubgroup (G := ConjAct (GL (Fin n) F))
  let L₀ : Subgroup (ConjAct (GL (Fin n) F)) :=
    { carrier := {l | l ∈ L ∧ ΦH l ∈ L}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨L.mul_mem ha hb, ?_⟩
        rw [hΦHmul]
        exact L.mul_mem ha' hb'
      one_mem' := by
        refine ⟨L.one_mem, ?_⟩
        rw [hΦHone]
        exact L.one_mem
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨L.inv_mem ha, ?_⟩
        rw [hΦHinv]
        exact L.inv_mem ha' }
  have hL₀o : IsOpen (L₀ : Set (ConjAct (GL (Fin n) F))) :=
    L.isOpen.inter (L.isOpen.preimage hΦHc)
  have hL₀c : IsCompact (L₀ : Set (ConjAct (GL (Fin n) F))) :=
    hLc.of_isClosed_subset (Subgroup.isClosed_of_isOpen L₀ hL₀o) (fun l hl => hl.1)
  have hΦL₀ : ∀ l ∈ L₀, ΦH l ∈ L₀ := by
    rintro l ⟨hl, hl'⟩
    refine ⟨hl', ?_⟩
    have : ΦH (ΦH l) = l := by
      simp only [ΦH, ConjAct.ofConjAct_toConjAct, hΦΦ, ConjAct.toConjAct_ofConjAct]
    rw [this]
    exact hl

  have hP : ∀ x, transposeGL x ∈ orbitPiece L₀ x₀ ↔ (ConjAct.toConjAct S)⁻¹ • x ∈ orbitPiece L₀ x₀ := by
    intro x
    constructor
    · rintro ⟨l, hl, hlx⟩
      have hlx' : l • x₀ = transposeGL x := hlx
      have hx : x = ConjAct.toConjAct (S * Φ (ConjAct.ofConjAct l)) • x₀ := by
        rw [← hτk, ConjAct.toConjAct_ofConjAct, hlx', transposeGL_transposeGL]
      refine ⟨ΦH l, hΦL₀ l hl, ?_⟩
      show ΦH l • x₀ = _
      rw [hx, ← mul_smul, ← ConjAct.toConjAct_inv, ← ConjAct.toConjAct_mul, inv_mul_cancel_left]
    · rintro ⟨l, hl, hlx⟩
      have hlx' : l • x₀ = (ConjAct.toConjAct S)⁻¹ • x := hlx
      have hx : x = ConjAct.toConjAct (S * ConjAct.ofConjAct l) • x₀ := by
        rw [ConjAct.toConjAct_mul, mul_smul, ConjAct.toConjAct_ofConjAct, hlx', smul_inv_smul]
      have e : S * Φ (S * ConjAct.ofConjAct l) = Φ (ConjAct.ofConjAct l) := by
        simp only [Φ, map_mul, hθS]
        group
      refine ⟨ΦH l, hΦL₀ l hl, ?_⟩
      show ΦH l • x₀ = transposeGL x
      rw [hx, hτk, e]

  have hx₀ : x₀ ∈ orbit (ConjAct (GL (Fin n) F)) x₀ := mem_orbit_self x₀
  obtain ⟨f₀, hf₀, hf₀O⟩ := exists_lift_orbit_piece hU hC hO hL₀c hL₀o hx₀
  set T := relT U ⊔ (supportedIn U ⊓ vanishingOn C)
  have hτO : ∀ x ∈ orbit (ConjAct (GL (Fin n) F)) x₀,
      transposeGL x ∈ orbit (ConjAct (GL (Fin n) F)) x₀ := by
    rintro _ ⟨h, rfl⟩
    have e : h • x₀ = ConjAct.toConjAct (ConjAct.ofConjAct h) • x₀ := by
      rw [ConjAct.toConjAct_ofConjAct]
    change transposeGL (h • x₀) ∈ _
    rw [e, hτk]
    exact mem_orbit _ _
  have ha : (f₀ + fun x => f₀ (transposeGL x)) ∈ T :=
    le_sup_left (b := supportedIn U ⊓ vanishingOn C)
      (le_sup_right (a := relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) U)
        (Submodule.subset_span ⟨f₀, hf₀, rfl⟩))
  have hb : transl (ConjAct.toConjAct S) f₀ - f₀ ∈ T := by
    have := sub_mem_relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) (ConjAct.toConjAct S) hf₀
    rw [MonoidHom.one_apply, one_smul] at this
    exact le_sup_left (b := supportedIn U ⊓ vanishingOn C)
      (le_sup_left (b := tauSpan U) this)
  have hc : (fun x => f₀ (transposeGL x)) - transl (ConjAct.toConjAct S) f₀ ∈ T := by
    refine le_sup_right (a := relT U) (sub_mem_of_eqOn_orbit hO (comp_transposeGL_mem hUτ hf₀)
      (transl_mem_supportedIn hUinv _ hf₀) fun x hx => ?_)
    rw [transl_apply, hf₀O _ (hτO x hx), hf₀O _ (mem_orbit_of_mem_orbit _ hx)]
    by_cases h : transposeGL x ∈ orbitPiece L₀ x₀
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hP x).1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hP x).2 h'))]
  have h2 : (2 : ℂ) • f₀ ∈ T := by
    have e : (2 : ℂ) • f₀ = (f₀ + fun x => f₀ (transposeGL x)) -
        ((fun x => f₀ (transposeGL x)) - transl (ConjAct.toConjAct S) f₀) -
        (transl (ConjAct.toConjAct S) f₀ - f₀) := by
      rw [two_smul]
      abel
    rw [e]
    exact T.sub_mem (T.sub_mem ha hc) hb
  have hbase : f₀ ∈ T := by
    have := T.smul_mem (1 / 2 : ℂ) h2
    rwa [smul_smul, one_div, inv_mul_cancel₀ two_ne_zero, one_smul] at this
  exact supportedIn_le_of_base hU hC hO hUinv (1 : ConjAct (GL (Fin n) F) →* ℂ)
    (relT_le hUinv hUτ) le_sup_left L₀ hL₀c hL₀o (fun l _ => MonoidHom.one_apply l) f₀ hf₀O hbase

end OneClass

section Stability

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}

def thetaC (h : ConjAct (GL (Fin n) F)) : ConjAct (GL (Fin n) F) :=
  ConjAct.toConjAct (thetaT (ConjAct.ofConjAct h))

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem thetaC_thetaC (h : ConjAct (GL (Fin n) F)) : thetaC (thetaC h) = h := by
  simp only [thetaC, ConjAct.ofConjAct_toConjAct, thetaT_apply, transposeGL_inv,
    transposeGL_transposeGL, inv_inv, ConjAct.toConjAct_ofConjAct]

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem thetaC_inv (h : ConjAct (GL (Fin n) F)) : thetaC h⁻¹ = (thetaC h)⁻¹ := by
  simp only [thetaC, map_inv]

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem transposeGL_smul' (h : ConjAct (GL (Fin n) F)) (x : GL (Fin n) F) :
    transposeGL (h • x) = thetaC h • transposeGL x :=
  transposeGL_smul h x

omit [TopologicalSpace F] [IsTopologicalRing F] in

theorem transl_comp_transposeGL (h : ConjAct (GL (Fin n) F)) (f : GL (Fin n) F → ℂ) :
    (fun x => transl h f (transposeGL x)) = transl (thetaC h) (fun x => f (transposeGL x)) := by
  funext x
  rw [transl_apply, transl_apply, transposeGL_smul', thetaC_inv, thetaC_thetaC]

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem univ_conj_stable : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ (univ : Set (GL (Fin n) F)),
    h • x ∈ (univ : Set (GL (Fin n) F)) := fun _ _ _ => mem_univ _

theorem transl_mem_relT_univ (h : ConjAct (GL (Fin n) F)) {f : GL (Fin n) F → ℂ}
    (hf : f ∈ relT (univ : Set (GL (Fin n) F))) : transl h f ∈ relT (univ : Set (GL (Fin n) F)) := by
  let m : (GL (Fin n) F → ℂ) →ₗ[ℂ] (GL (Fin n) F → ℂ) :=
    { toFun := transl h
      map_add' := transl_add h
      map_smul' := fun c f => transl_smul h c f }
  have hτrel : ∀ k : ConjAct (GL (Fin n) F), ∀ f ∈ supportedIn (univ : Set (GL (Fin n) F)),
      (fun x => (transl k f - f) (transposeGL x)) ∈ relT (univ : Set (GL (Fin n) F)) := by
    intro k f hf
    have e : (fun x => (transl k f - f) (transposeGL x)) =
        transl (thetaC k) (fun x => f (transposeGL x)) - (fun x => f (transposeGL x)) := by
      rw [← transl_comp_transposeGL]
      rfl
    rw [e]
    have := sub_mem_relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) (thetaC k)
      (comp_transposeGL_mem (fun _ => Iff.rfl) hf)
    rw [MonoidHom.one_apply, one_smul] at this
    exact le_sup_left (b := tauSpan univ) this
  suffices relT (univ : Set (GL (Fin n) F)) ≤ (relT univ).comap m from this hf
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨k, f, hf, rfl⟩
    show transl h (transl k f - (1 : ConjAct (GL (Fin n) F) →* ℂ) k • f) ∈ relT univ
    rw [MonoidHom.one_apply, one_smul, transl_sub, ← transl_mul]
    have e : h * k = (h * k * h⁻¹) * h := by group
    rw [e, transl_mul]
    have := sub_mem_relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) (h * k * h⁻¹)
      (transl_mem_supportedIn univ_conj_stable h hf)
    rw [MonoidHom.one_apply, one_smul] at this
    exact le_sup_left (b := tauSpan univ) this
  · rintro _ ⟨f, hf, rfl⟩
    show transl h (f + fun x => f (transposeGL x)) ∈ relT univ
    have hf' := transl_mem_supportedIn univ_conj_stable h hf
    have e : transl h (f + fun x => f (transposeGL x)) =
        (transl h f + fun x => transl h f (transposeGL x)) +
        ((fun x => (transl (thetaC h) f - f) (transposeGL x)) -
          (fun x => (transl h f - f) (transposeGL x))) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, transl_apply, transposeGL_smul', thetaC_inv]
      ring
    rw [e]
    refine add_mem (le_sup_right (a := relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) univ)
      (Submodule.subset_span ⟨transl h f, hf', rfl⟩)) (sub_mem (hτrel _ f hf) (hτrel h f hf))

omit [IsTopologicalRing F] in

theorem comp_transposeGL_mem_relT_univ {f : GL (Fin n) F → ℂ}
    (hf : f ∈ relT (univ : Set (GL (Fin n) F))) :
    (fun x => f (transposeGL x)) ∈ relT (univ : Set (GL (Fin n) F)) := by
  let m : (GL (Fin n) F → ℂ) →ₗ[ℂ] (GL (Fin n) F → ℂ) := LinearMap.funLeft ℂ ℂ transposeGL
  suffices relT (univ : Set (GL (Fin n) F)) ≤ (relT univ).comap m from this hf
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨k, f, hf, rfl⟩
    show (fun x => (transl k f - (1 : ConjAct (GL (Fin n) F) →* ℂ) k • f) (transposeGL x)) ∈ relT univ
    rw [MonoidHom.one_apply, one_smul]
    have e : (fun x => (transl k f - f) (transposeGL x)) =
        transl (thetaC k) (fun x => f (transposeGL x)) - (fun x => f (transposeGL x)) := by
      rw [← transl_comp_transposeGL]
      rfl
    rw [e]
    have := sub_mem_relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) (thetaC k)
      (comp_transposeGL_mem (fun _ => Iff.rfl) hf)
    rw [MonoidHom.one_apply, one_smul] at this
    exact le_sup_left (b := tauSpan univ) this
  · rintro _ ⟨f, hf, rfl⟩
    show (fun x => (f + fun x => f (transposeGL x)) (transposeGL x)) ∈ relT univ
    have e : (fun x => (f + fun x => f (transposeGL x)) (transposeGL x)) =
        (fun x => f (transposeGL x)) + fun x => (fun x => f (transposeGL x)) (transposeGL x) := by
      funext x
      simp only [Pi.add_apply, transposeGL_transposeGL]
    rw [e]
    exact le_sup_right (a := relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) univ)
      (Submodule.subset_span ⟨_, comp_transposeGL_mem (fun _ => Iff.rfl) hf, rfl⟩)

end Stability

section Fibre

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem exists_symm_conj_transposeGL (x : GL (Fin n) F) :
    ∃ S : GL (Fin n) F, transposeGL S = S ∧ S * x * S⁻¹ = transposeGL x := by
  obtain ⟨S, hS, hSx⟩ := exists_isSymm_mul_eq_transpose_mul (x : Matrix (Fin n) (Fin n) F)
  refine ⟨S, Units.ext hS.eq, Units.ext ?_⟩
  simp only [Units.val_mul, coe_transposeGL]
  rw [hSx, mul_assoc, Units.mul_inv, mul_one]

theorem mem_relT_sup_vanishingOn {Z : Set (GL (Fin n) F)} (hZ : IsClosed Z)
    (hZinv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ Z, h • x ∈ Z)
    (hZτ : ∀ x, transposeGL x ∈ Z ↔ x ∈ Z) {s : Set (GL (Fin n) F)} (hs : s.Countable)
    (hcov : Z ⊆ ⋃ x ∈ s, orbit (ConjAct (GL (Fin n) F)) x) {g : GL (Fin n) F → ℂ}
    (hg : g ∈ supportedIn (univ : Set (GL (Fin n) F))) :
    g ∈ relT (univ : Set (GL (Fin n) F)) ⊔ (supportedIn univ ⊓ vanishingOn Z) := by
  classical
  set M := relT (univ : Set (GL (Fin n) F)) ⊔ (supportedIn univ ⊓ vanishingOn Z) with hMdef

  have hMt : ∀ h : ConjAct (GL (Fin n) F), ∀ f ∈ M, transl h f ∈ M := by
    intro h f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    rw [transl_add]
    refine add_mem (le_sup_left (b := supportedIn univ ⊓ vanishingOn Z)
      (transl_mem_relT_univ h ha)) (le_sup_right (a := relT univ)
      ⟨transl_mem_supportedIn univ_conj_stable h hb.1, fun x hxZ => ?_⟩)
    rw [transl_apply]
    exact hb.2 _ (hZinv _ _ hxZ)
  have hMτ : ∀ f ∈ M, (fun x => f (transposeGL x)) ∈ M := by
    intro f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    refine add_mem (le_sup_left (b := supportedIn univ ⊓ vanishingOn Z)
      (comp_transposeGL_mem_relT_univ ha)) (le_sup_right (a := relT univ)
      ⟨comp_transposeGL_mem (fun _ => Iff.rfl) hb.1, fun x hxZ => hb.2 _ ((hZτ x).2 hxZ)⟩)

  set U := ⋃₀ {V : Set (GL (Fin n) F) | IsOpen V ∧ supportedIn V ≤ M} with hUdef
  have hUo : IsOpen U := isOpen_sUnion fun V hV => hV.1
  have hUM : supportedIn U ≤ M := supportedIn_le_of_local fun x hx => by
    obtain ⟨V, hV, hxV⟩ := mem_sUnion.1 hx
    exact ⟨V, hV.1, hxV, hV.2⟩
  have hUt : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ U, h • x ∈ U := by
    intro h x hx
    obtain ⟨V, ⟨hVo, hVM⟩, hxV⟩ := mem_sUnion.1 hx
    refine mem_sUnion.2 ⟨(fun y => h⁻¹ • y) ⁻¹' V, ⟨hVo.preimage (continuous_const_smul _),
      fun f hf => ?_⟩, by simpa using hxV⟩
    have h1 : transl h⁻¹ f ∈ supportedIn V := by
      refine ⟨(transl_mem_supportedIn univ_conj_stable h⁻¹ ⟨hf.1, subset_univ _⟩).1,
        fun y hy => ?_⟩
      have := hf.2 hy
      simpa [transl_apply] using this
    have := hMt h _ (hVM h1)
    rwa [← transl_mul, mul_inv_cancel, transl_one] at this
  have hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U := by
    have key : ∀ x ∈ U, transposeGL x ∈ U := by
      intro x hx
      obtain ⟨V, ⟨hVo, hVM⟩, hxV⟩ := mem_sUnion.1 hx
      refine mem_sUnion.2 ⟨transposeGL ⁻¹' V, ⟨hVo.preimage continuous_transposeGL,
        fun f hf => ?_⟩, by simpa using hxV⟩
      have h1 : (fun x => f (transposeGL x)) ∈ supportedIn V := by
        refine ⟨(comp_transposeGL_mem (fun _ => Iff.rfl) ⟨hf.1, subset_univ _⟩).1,
          fun y hy => ?_⟩
        have := hf.2 hy
        simpa using this
      have := hMτ _ (hVM h1)
      simpa using this
    exact fun x => ⟨fun h => by simpa using key _ h, key x⟩

  have hsplit : ∀ j ∈ supportedIn (univ : Set (GL (Fin n) F)),
      (∀ x ∈ Z, j x ≠ 0 → x ∈ U) → j ∈ M := by
    intro j hj hjZ
    have hA : IsCompact (Z ∩ Function.support j) := (isCompact_support hj.1).inter_left hZ
    obtain ⟨B, hBc, hBo, hAB, hBU⟩ :=
      exists_isCompact_isOpen_between hA hUo (fun x hx => hjZ x hx.1 hx.2)
    have hBcl : IsClopen B := ⟨hBc.isClosed, hBo⟩
    have e : j = (fun x => B.indicator 1 x * j x) + (fun x => Bᶜ.indicator 1 x * j x) := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [e]
    refine M.add_mem (hUM ⟨(indicator_mul_mem hBcl hj).1,
      fun x hx => hBU (support_indicator_mul_subset hx).1⟩) ?_
    refine le_sup_right (a := relT univ) ⟨indicator_mul_mem hBcl.compl hj, fun x hxZ => ?_⟩
    by_cases hxB : x ∈ B
    · simp [hxB]
    · have : j x = 0 := by
        by_contra h
        exact hxB (hAB ⟨hxZ, h⟩)
      simp [this]

  by_cases hZ' : (Z \ U).Nonempty
  · exfalso
    have hZ'c : IsClosed (Z \ U) := hZ.sdiff hUo
    have hZ'inv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ Z \ U, h • x ∈ Z \ U := by
      rintro h x ⟨hxZ, hxU⟩
      refine ⟨hZinv h x hxZ, fun hU' => hxU ?_⟩
      have := hUt h⁻¹ _ hU'
      rwa [inv_smul_smul] at this
    have hZ'τ : ∀ x, transposeGL x ∈ Z \ U ↔ x ∈ Z \ U := fun x => by
      simp only [Set.mem_sdiff, hZτ, hUτ]
    obtain ⟨x₀, hx₀, hcl⟩ := exists_isClosed_diff_orbit hZ'c hZ' hZ'inv hs
      (Set.sdiff_subset.trans hcov)
    set O := orbit (ConjAct (GL (Fin n) F)) x₀ with hOdef
    have hOZ' : O ⊆ Z \ U := by
      rintro _ ⟨h, rfl⟩
      exact hZ'inv h x₀ hx₀
    obtain ⟨S, hS, hSx⟩ := exists_symm_conj_transposeGL x₀
    have hOτ : ∀ x ∈ O, transposeGL x ∈ O := by
      rintro _ ⟨h, rfl⟩
      refine ⟨thetaC h * ConjAct.toConjAct S, ?_⟩
      show (thetaC h * ConjAct.toConjAct S) • x₀ = transposeGL (h • x₀)
      rw [transposeGL_smul', mul_smul, ConjAct.toConjAct_smul, hSx]
    set U' := ((Z \ U) \ O)ᶜ with hU'def
    have hU'o : IsOpen U' := hcl.isOpen_compl
    have hU'inv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ U', h • x ∈ U' := by
      intro h x hx hhx
      apply hx
      refine ⟨?_, fun hxO => hhx.2 (mem_orbit_of_mem_orbit h hxO)⟩
      have := hZ'inv h⁻¹ _ hhx.1
      rwa [inv_smul_smul] at this
    have hU'τ : ∀ x, transposeGL x ∈ U' ↔ x ∈ U' := by
      intro x
      simp only [hU'def, mem_compl_iff, Set.mem_sdiff, hZ'τ, not_and, not_not]
      constructor
      · intro h hx
        have := hOτ _ (h hx)
        rwa [transposeGL_transposeGL] at this
      · intro h hx
        exact hOτ _ (h hx)
    have hU'O : U' ∩ (Z \ U) = O := by
      ext x
      simp only [hU'def, mem_inter_iff, mem_compl_iff, Set.mem_sdiff, not_and, not_not]
      exact ⟨fun ⟨h1, h2⟩ => h1 h2, fun hx => ⟨fun _ => hx, hOZ' hx⟩⟩
    have horb := supportedIn_le_relT_sup hU'o hZ'c hU'O hU'inv hU'τ hS hSx
    have hgood : supportedIn U' ≤ M := by
      refine horb.trans (sup_le (le_sup_left.trans' (relT_mono (subset_univ _))) ?_)
      rintro j ⟨hj, hjv⟩
      refine hsplit j (supportedIn_mono (subset_univ _) hj) fun x hxZ hjx => ?_
      by_contra hxU
      exact hjx (hjv x ⟨hxZ, hxU⟩)
    have hx₀U' : x₀ ∈ U' := fun h => h.2 (mem_orbit_self x₀)
    exact hx₀.2 (mem_sUnion.2 ⟨U', ⟨hU'o, hgood⟩, hx₀U'⟩)
  · refine hsplit g hg fun x hxZ _ => ?_
    by_contra hxU
    exact hZ' ⟨x, hxZ, hxU⟩

end Fibre

section Global

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

noncomputable def charCoeffs (x : GL (Fin n) F) : Fin (n + 1) → F :=
  fun k => (x : Matrix (Fin n) (Fin n) F).charpoly.coeff k

theorem continuous_charCoeffs : Continuous (charCoeffs : GL (Fin n) F → Fin (n + 1) → F) :=
  continuous_pi fun k => (continuous_charpoly_coeff (k : ℕ)).comp Units.continuous_val

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem charCoeffs_smul (h : ConjAct (GL (Fin n) F)) (x : GL (Fin n) F) :
    charCoeffs (h • x) = charCoeffs x := by
  funext k
  simp only [charCoeffs, ConjAct.smul_def, Units.val_mul]
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem charCoeffs_transposeGL (x : GL (Fin n) F) : charCoeffs (transposeGL x) = charCoeffs x := by
  funext k
  simp only [charCoeffs, coe_transposeGL, Matrix.charpoly_transpose]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem charpoly_eq_of_charCoeffs_eq {x y : GL (Fin n) F} (h : charCoeffs x = charCoeffs y) :
    (x : Matrix (Fin n) (Fin n) F).charpoly = (y : Matrix (Fin n) (Fin n) F).charpoly := by
  ext k
  by_cases hk : k ≤ n
  · exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
  · push Not at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt] <;>
      simpa using hk

theorem mem_relT_univ {g : GL (Fin n) F → ℂ}
    (hg : g ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    g ∈ relT (univ : Set (GL (Fin n) F)) := by
  classical
  have : TotallyDisconnectedSpace F := totallyDisconnectedSpace_localField
  refine mem_of_forall_fiber isClosed_univ continuous_charCoeffs ?_ ?_ ⟨hg, subset_univ _⟩ ?_
  · rintro j ⟨-, hj⟩
    have : j = 0 := funext fun x => hj x (mem_univ x)
    rw [this]
    exact zero_mem _
  · intro V hV w hw
    set φ : GL (Fin n) F → ℂ := (charCoeffs ⁻¹' V).indicator 1 with hφ
    have hφc : IsClopen (charCoeffs ⁻¹' V : Set (GL (Fin n) F)) := hV.preimage continuous_charCoeffs
    let m : (GL (Fin n) F → ℂ) →ₗ[ℂ] (GL (Fin n) F → ℂ) :=
      { toFun := fun w x => φ x * w x
        map_add' := fun a b => funext fun x => mul_add _ _ _
        map_smul' := fun c a => by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
    have hφs : ∀ (h : ConjAct (GL (Fin n) F)) x, φ (h • x) = φ x := fun h x => by
      simp only [hφ, Set.indicator, mem_preimage, charCoeffs_smul, Pi.one_apply]
    have hφτ : ∀ x, φ (transposeGL x) = φ x := fun x => by
      simp only [hφ, Set.indicator, mem_preimage, charCoeffs_transposeGL, Pi.one_apply]
    suffices relT (univ : Set (GL (Fin n) F)) ≤ (relT univ).comap m from this hw
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, f, hf, rfl⟩
      have hf' : (fun x => φ x * f x) ∈ supportedIn (univ : Set (GL (Fin n) F)) :=
        indicator_mul_mem hφc hf
      have e : m (transl k f - (1 : ConjAct (GL (Fin n) F) →* ℂ) k • f) =
          transl k (fun x => φ x * f x) - (1 : ConjAct (GL (Fin n) F) →* ℂ) k •
            (fun x => φ x * f x) := by
        funext x
        simp only [m, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
          transl_apply, MonoidHom.one_apply, one_smul, hφs]
        ring
      show m _ ∈ relT univ
      rw [e]
      exact le_sup_left (b := tauSpan univ) (sub_mem_relSpan _ k hf')
    · rintro _ ⟨f, hf, rfl⟩
      have hf' : (fun x => φ x * f x) ∈ supportedIn (univ : Set (GL (Fin n) F)) :=
        indicator_mul_mem hφc hf
      have e : m (f + fun x => f (transposeGL x)) =
          (fun x => φ x * f x) + fun x => (fun x => φ x * f x) (transposeGL x) := by
        funext x
        simp only [m, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, hφτ]
        ring
      show m _ ∈ relT univ
      rw [e]
      exact le_sup_right (a := relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) univ)
        (Submodule.subset_span ⟨_, hf', rfl⟩)
  · intro y
    have hZ : IsClosed ((univ : Set (GL (Fin n) F)) ∩ charCoeffs ⁻¹' {y}) :=
      isClosed_univ.inter (isClosed_singleton.preimage continuous_charCoeffs)
    by_cases hne : ((univ : Set (GL (Fin n) F)) ∩ charCoeffs ⁻¹' {y}).Nonempty
    · obtain ⟨x₁, -, hx₁⟩ := hne
      obtain ⟨s, hs, hsx⟩ :=
        exists_countable_conj_charpoly (n := n) (x₁ : Matrix (Fin n) (Fin n) F).charpoly
      refine mem_relT_sup_vanishingOn hZ (fun h x hx => ⟨mem_univ _, ?_⟩)
        (fun x => ?_) hs ?_ ⟨hg, subset_univ _⟩
      · have : charCoeffs (h • x) = y := (charCoeffs_smul h x).trans hx.2
        exact this
      · simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_singleton_iff,
          charCoeffs_transposeGL]
      · rintro x ⟨-, hx⟩
        have hxy : charCoeffs x = charCoeffs x₁ := (hx : charCoeffs x = y).trans hx₁.symm
        obtain ⟨y', hy's, g', hg'⟩ := hsx x (charpoly_eq_of_charCoeffs_eq hxy)
        refine mem_iUnion₂.2 ⟨y', hy's, ConjAct.toConjAct g', ?_⟩
        show ConjAct.toConjAct g' • y' = x
        rw [ConjAct.toConjAct_smul, hg']
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne]
      refine mem_relT_sup_vanishingOn isClosed_empty (fun _ _ hx => hx.elim) (fun x => ?_)
        countable_empty (empty_subset _) ⟨hg, subset_univ _⟩
      simp

theorem distribution_transpose_invariant
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ))
    (hD : ∀ (g : GL (Fin n) F) (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ),
      D (biTranslL g g f) = D f)
    (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    D (compHomeoL transposeHomeo f) = D f := by
  set E : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :=
    D - D ∘ₗ compHomeoL transposeHomeo with hE
  have hττ : ∀ f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ,
      compHomeoL transposeHomeo (compHomeoL transposeHomeo f) = f := fun f =>
    Subtype.ext (funext fun x => by simp [compHomeoL])
  have hτbi : ∀ (g : GL (Fin n) F) (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ),
      compHomeoL transposeHomeo (biTranslL g g f) =
        biTranslL (thetaT g) (thetaT g) (compHomeoL transposeHomeo f) := fun g f =>
    Subtype.ext (funext fun x => by
      simp only [compHomeoL, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        transposeHomeo_apply, coe_biTranslL, thetaT_apply, inv_inv, transposeGL_mul,
        transposeGL_inv, transposeGL_transposeGL]
      simp only [mul_assoc])

  set K : Submodule ℂ (GL (Fin n) F → ℂ) :=
    (LinearMap.ker E).map (locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ).subtype
  have hK : relT (univ : Set (GL (Fin n) F)) ≤ K := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, f, hf, rfl⟩
      let f' : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := ⟨f, hf.1⟩
      let g := ConjAct.ofConjAct k
      refine ⟨biTranslL g g f' - f', ?_, ?_⟩
      · show E _ = 0
        rw [map_sub, hE, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.comp_apply, hτbi, hD, hD]
        abel
      · funext x
        simp only [Submodule.subtype_apply, Submodule.coe_sub, coe_biTranslL, Pi.sub_apply,
          transl_apply, MonoidHom.one_apply, one_smul, ConjAct.smul_def, ConjAct.ofConjAct_inv,
          inv_inv, f', g]
    · rintro _ ⟨f, hf, rfl⟩
      let f' : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := ⟨f, hf.1⟩
      refine ⟨f' + compHomeoL transposeHomeo f', ?_, ?_⟩
      · show E _ = 0
        rw [map_add, hE, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.comp_apply, hττ]
        abel
      · rfl
  obtain ⟨k, hk, hkf⟩ := hK (mem_relT_univ f.2)
  have hkf' : k = f := Subtype.ext hkf
  rw [hkf'] at hk
  have : E f = 0 := hk
  rw [hE, LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero] at this
  exact this.symm

end Global

end GroundTheory.Automorphic.ContragredientTranspose
