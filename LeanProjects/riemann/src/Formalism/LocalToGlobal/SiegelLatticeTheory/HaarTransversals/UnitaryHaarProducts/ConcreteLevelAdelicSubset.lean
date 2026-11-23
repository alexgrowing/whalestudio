import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionB

noncomputable section

open MeasureTheory Set Topology Formalism.MainNotions.S Matrix
open scoped Pointwise

namespace Formalism.L2.SG.Pf

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem fund_nhd (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ s ∈ Γ, ∀ a ∈ V, ∀ b ∈ V, s = a * b⁻¹ → s = 1 := by
  have h1 : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 h1
  have hU1 : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' U := by rw [hUe]; rfl
    simpa using this
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (1 : G), ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ U := by
    have hc : Continuous fun p : G × G => p.1 * p.2⁻¹ := continuous_fst.mul continuous_snd.inv
    have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' U ∈ 𝓝 ((1 : G), (1 : G)) :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hU1)
    rw [nhds_prod_eq] at this
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.1 this
    exact ⟨A ∩ B, Filter.inter_mem hA hB, fun a ha b hb => hAB (show (a, b) ∈ A ×ˢ B from ⟨ha.1, hb.2⟩)⟩
  obtain ⟨W, hWV, hWo, hW1⟩ := mem_nhds_iff.1 hV
  refine ⟨W, hWo, hW1, fun s hs a ha b hb hsab => ?_⟩
  have hsU : s ∈ U := hsab ▸ hVU a (hWV ha) b (hWV hb)
  have : (⟨s, hs⟩ : Γ) ∈ ((↑) : Γ → G) ⁻¹' U := hsU
  rw [hUe] at this
  simpa using congrArg Subtype.val (Set.mem_singleton_iff.1 this)

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_strictFund (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ F : Set G, MeasurableSet F ∧ (∀ x, ∃ s ∈ Γ, s * x ∈ F) ∧ ∀ x ∈ F, ∀ s ∈ Γ, s * x ∈ F → s = 1 := by
  obtain ⟨V, hVo, hV1, hV⟩ := fund_nhd Γ
  have hnhd : ∀ x : G, (fun y => y * x⁻¹) ⁻¹' V ∈ 𝓝 x := fun x =>
    (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds (by simpa using hVo.mem_nhds hV1)
  obtain ⟨S, hSc, hSu⟩ := TopologicalSpace.countable_cover_nhds hnhd
  by_cases hG : S.Nonempty
  swap
  · exfalso
    have : (1 : G) ∈ ⋃ x ∈ S, (fun y => y * x⁻¹) ⁻¹' V := by rw [hSu]; trivial
    obtain ⟨x, hx, -⟩ := mem_iUnion₂.1 this
    exact hG ⟨x, hx⟩
  obtain ⟨xs, hxs⟩ := hSc.exists_eq_range hG
  set B : ℕ → Set G := fun n => (fun y => y * (xs n)⁻¹) ⁻¹' V with hB
  have hBo : ∀ n, IsOpen (B n) := fun n => hVo.preimage (continuous_id.mul continuous_const)
  have hcov : ∀ x : G, ∃ n, x ∈ B n := by
    intro x
    have : x ∈ ⋃ y ∈ S, (fun z => z * y⁻¹) ⁻¹' V := by rw [hSu]; trivial
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 this
    rw [hxs] at hy
    obtain ⟨n, rfl⟩ := hy
    exact ⟨n, hxy⟩
  have hBs : ∀ n x, x ∈ B n → ∀ s ∈ Γ, s * x ∈ B n → s = 1 := by
    intro n x hx s hs hsx
    refine hV s hs _ hsx _ hx ?_
    simp [mul_assoc]
  set O : ℕ → Set G := fun n => {y | ∃ s ∈ Γ, ∃ m < n, s * y ∈ B m} with hO
  have hOo : ∀ n, IsOpen (O n) := by
    intro n
    have : O n = ⋃ s ∈ Γ, ⋃ m < n, (fun y => s * y) ⁻¹' B m := by
      ext y; simp [hO]
    rw [this]
    exact isOpen_biUnion fun s _ => isOpen_biUnion fun m _ => (hBo m).preimage (continuous_const.mul continuous_id)
  refine ⟨⋃ n, B n \ O n, MeasurableSet.iUnion fun n => (hBo n).measurableSet.diff (hOo n).measurableSet, ?_, ?_⟩
  · intro x
    classical
    have hex : ∃ n, ∃ s ∈ Γ, s * x ∈ B n := by
      obtain ⟨n, hn⟩ := hcov x
      exact ⟨n, 1, Γ.one_mem, by simpa using hn⟩
    obtain ⟨s, hs, hsx⟩ := Nat.find_spec hex
    refine ⟨s, hs, mem_iUnion.2 ⟨Nat.find hex, hsx, ?_⟩⟩
    rintro ⟨t, ht, m, hm, htm⟩
    apply Nat.find_min hex hm
    exact ⟨t * s, Γ.mul_mem ht hs, by simpa [mul_assoc] using htm⟩
  · intro x hx s hs hsx
    obtain ⟨n, hxn, hxO⟩ := mem_iUnion.1 hx
    obtain ⟨k, hsk, hsO⟩ := mem_iUnion.1 hsx
    rcases lt_trichotomy n k with h | h | h
    · exact absurd ⟨s⁻¹, Γ.inv_mem hs, n, h, by simpa [← mul_assoc] using hxn⟩ hsO
    · subst h
      exact hBs n x hxn s hs hsk
    · exact absurd ⟨s, hs, k, h, hsk⟩ hxO

theorem countable_of_discrete (Γ : Subgroup G) [DiscreteTopology Γ] : Countable Γ :=
  (TopologicalSpace.separableSpace_iff_countable).1 inferInstance

theorem isFund_of_strict (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : MeasurableSet F)
    (h1 : ∀ x, ∃ s ∈ Γ, s * x ∈ F) (h2 : ∀ x ∈ F, ∀ s ∈ Γ, s * x ∈ F → s = 1) (μ : Measure G) :
    IsFundamentalDomain Γ F μ := by
  refine IsFundamentalDomain.mk' hF.nullMeasurableSet fun x => ?_
  obtain ⟨s, hs, hsx⟩ := h1 x
  refine ⟨⟨s, hs⟩, hsx, fun t ht => ?_⟩
  have := h2 _ hsx ((t : G) * s⁻¹) (Γ.mul_mem t.2 (Γ.inv_mem hs)) (by simpa [mul_assoc, Subgroup.smul_def] using ht)
  ext
  simpa [mul_inv_eq_one] using this

theorem exists_isFund (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ F : Set G, MeasurableSet F ∧ ∀ μ : Measure G, IsFundamentalDomain Γ F μ := by
  obtain ⟨F, hF, h1, h2⟩ := exists_strictFund Γ
  have := countable_of_discrete Γ
  exact ⟨F, hF, isFund_of_strict Γ hF h1 h2⟩

end Gen

section Flag

variable {R : Type*} [CommRing R] {n r : ℕ} (e : Fin r → Fin n → R)

def spL (a : ℕ) : Submodule R (Fin n → R) := Submodule.span R (e '' {b | b.1 < a})

theorem spL_mono {a b : ℕ} (h : a ≤ b) : spL e a ≤ spL e b :=
  Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => lt_of_lt_of_le hc h)

theorem e_mem_spL {a : ℕ} {b : Fin r} (h : b.1 < a) : e b ∈ spL e a :=
  Submodule.subset_span ⟨b, h, rfl⟩

variable {e}

theorem fl_map_le {g : Matrix (Fin n) (Fin n) R} (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spL e a.1) (a : ℕ) :
    spL e a ≤ (spL e a).comap (Matrix.mulVecLin g) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  show g *ᵥ e b ∈ spL e a
  have h1 : g *ᵥ e b = e b + (g - 1) *ᵥ e b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [h1]
  exact add_mem (e_mem_spL e hb) (spL_mono e (le_of_lt hb) (hg b))

theorem fl_le_map {g : Matrix (Fin n) (Fin n) R} (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spL e a.1) (a : ℕ) :
    spL e a ≤ (spL e a).map (Matrix.mulVecLin g) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨w, hw, hgw⟩ := Submodule.mem_map.1 (ih b.1 hb (hg b))
    refine Submodule.mem_map.2 ⟨e b - w, sub_mem (e_mem_spL e hb) (spL_mono e (le_of_lt hb) hw), ?_⟩
    simp only [Matrix.mulVecLin_apply] at hgw ⊢
    rw [Matrix.mulVec_sub, hgw, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel

theorem fl_mul {g h : Matrix (Fin n) (Fin n) R} {W : Submodule R (Fin n → R)}
    (hgW : W ≤ W.comap (Matrix.mulVecLin g)) {v : Fin n → R} (hg : (g - 1) *ᵥ v ∈ W) (hh : (h - 1) *ᵥ v ∈ W) :
    (g * h - 1) *ᵥ v ∈ W := by
  have : (g * h - 1) *ᵥ v = g *ᵥ ((h - 1) *ᵥ v) + (g - 1) *ᵥ v := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]; abel
  rw [this]
  exact add_mem (hgW hh) hg

theorem fl_inv {g h : Matrix (Fin n) (Fin n) R} (hhg : h * g = 1) {W : Submodule R (Fin n → R)}
    (hW : W ≤ W.map (Matrix.mulVecLin g)) {v : Fin n → R} (hg : (g - 1) *ᵥ v ∈ W) :
    (h - 1) *ᵥ v ∈ W := by
  obtain ⟨w, hw, hgw⟩ := Submodule.mem_map.1 (hW hg)
  simp only [Matrix.mulVecLin_apply] at hgw
  have : (h - 1) *ᵥ v = -w := by
    have e1 : h *ᵥ ((g - 1) *ᵥ v) = w := by rw [← hgw, Matrix.mulVec_mulVec, hhg, Matrix.one_mulVec]
    have e2 : h *ᵥ ((g - 1) *ᵥ v) = v - h *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hhg, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← e1, e2]; abel
  rw [this]
  exact neg_mem hw

def InFl (z : Fin n → R) (g : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spL e a.1) ∧ (g - 1) *ᵥ z ∈ spL e r

theorem inFl_one (z : Fin n → R) : InFl (e := e) z 1 :=
  ⟨fun a => by simp, by simp⟩

theorem inFl_mul {z : Fin n → R} {g h : Matrix (Fin n) (Fin n) R} (hg : InFl (e := e) z g) (hh : InFl (e := e) z h) :
    InFl (e := e) z (g * h) :=
  ⟨fun a => fl_mul (fl_map_le hg.1 a.1) (hg.1 a) (hh.1 a), fl_mul (fl_map_le hg.1 r) hg.2 hh.2⟩

theorem inFl_inv {z : Fin n → R} {g h : Matrix (Fin n) (Fin n) R} (hhg : h * g = 1) (hg : InFl (e := e) z g) :
    InFl (e := e) z h :=
  ⟨fun a => fl_inv hhg (fl_le_map hg.1 a.1) (hg.1 a), fl_inv hhg (fl_le_map hg.1 r) hg.2⟩

end Flag

section Bessel

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH

variable (I : AutInst) {r : ℕ}

theorem range_eq_image_lt {α : Type*} (f : Fin r → α) : Set.range f = f '' {b : Fin r | b.1 < r} := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩; exact ⟨b, b.2, rfl⟩
  · rintro ⟨b, -, rfl⟩; exact ⟨b, rfl⟩

theorem sfin_iff (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (x : I.Gf) :
    x ∈ Sfin I e z ↔ InFl (e := fun b => incl I (e b)) (incl I z) (I.fmat x) := by
  unfold Sfin InFl spL
  rw [← range_eq_image_lt]
  rfl

def SinfSub (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Subgroup I.Ginf where
  carrier := Sinf I e z
  one_mem' := fun v => by
    show InS _ _ (uMat ((1 : I.Ginf) v))
    have : uMat ((1 : I.Ginf) v) = 1 := by simp [uMat]
    rw [this]; exact inFl_one _
  mul_mem' := by
    intro s t hs ht v
    show InS _ _ (uMat ((s * t) v))
    have : uMat ((s * t) v) = uMat (s v) * uMat (t v) := by simp [uMat]
    rw [this]; exact inFl_mul (hs v) (ht v)
  inv_mem' := by
    intro s hs v
    show InS _ _ (uMat (s⁻¹ v))
    have : uMat (s⁻¹ v) * uMat (s v) = 1 := by simp [uMat]
    exact inFl_inv this (hs v)

def SfinSub (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Subgroup I.Gf where
  carrier := Sfin I e z
  one_mem' := by
    show (1 : I.Gf) ∈ Sfin I e z
    rw [sfin_iff]
    have : I.fmat 1 = 1 := by simp [AutInst.fmat]
    rw [this]; exact inFl_one _
  mul_mem' := by
    intro a b ha hb
    rw [sfin_iff] at ha hb ⊢
    have : I.fmat (a * b) = I.fmat a * I.fmat b := by simp [AutInst.fmat]
    rw [this]; exact inFl_mul ha hb
  inv_mem' := by
    intro a ha
    rw [sfin_iff] at ha ⊢
    have : I.fmat a⁻¹ * I.fmat a = 1 := by simp [AutInst.fmat]
    exact inFl_inv this ha

end Bessel

section Transv

variable {G : Type*} [Group G]

theorem exists_rightTransversal (Γ S : Subgroup G) (hS : S ≤ Γ) :
    ∃ D : Set G, Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D := by
  classical
  let st : Setoid G := QuotientGroup.rightRel S
  let rep : G → G := fun g => (Quotient.mk st g).out
  have hrel : ∀ g, g * (rep g)⁻¹ ∈ S := fun g => by
    have : st (rep g) g := Quotient.mk_out (s := st) g
    simpa [st, QuotientGroup.rightRel_apply] using this
  have hmem : ∀ g ∈ Γ, rep g ∈ Γ := fun g hg => by
    have h1 := hS (hrel g)
    have := Γ.mul_mem (Γ.inv_mem h1) hg
    simpa [mul_assoc] using this
  refine ⟨rep '' Γ, fun x ⟨g, hg, hx⟩ => hx ▸ hmem g hg, fun γ hγ => ?_⟩
  refine ⟨(⟨γ * (rep γ)⁻¹, hrel γ⟩, ⟨rep γ, γ, hγ, rfl⟩), by simp, ?_⟩
  rintro ⟨⟨s, hs⟩, ⟨d, hd⟩⟩ hp
  obtain ⟨g, hg, rfl⟩ := hd
  simp only at hp
  have hsγ : γ * (rep g)⁻¹ = s := by rw [← hp]; group
  have h1 : (Quotient.mk st (rep g) : Quotient st) = Quotient.mk st γ :=
    Quotient.sound (show QuotientGroup.rightRel S (rep g) γ by rw [QuotientGroup.rightRel_apply, hsγ]; exact hs)
  have h2 : (Quotient.mk st (rep g) : Quotient st) = Quotient.mk st g := Quotient.out_eq _
  have hr : rep g = rep γ := by
    show (Quotient.mk st g).out = (Quotient.mk st γ).out
    rw [← h2, h1]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext hr)
  show s = γ * (rep γ)⁻¹
  rw [← hsγ, hr]

end Transv

section SGroupSec

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

def SAsub : Subgroup X.B.I.GA :=
  (SinfSub X.B.I X.eR (X.zR u)).prod (SfinSub X.B.I X.eR (X.zR u))

theorem SAsub_coe : ((SAsub X u : Subgroup X.B.I.GA) : Set X.B.I.GA) =
    {y : X.B.I.GA | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u} := rfl

theorem srat_eq : Srat X u = Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ SAsub X u := by
  unfold Srat
  rw [← SAsub_coe, Subgroup.closure_eq]

theorem srat_discrete [DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)] : DiscreteTopology (Srat X u) :=
  DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion (inf_le_left : Srat X u ≤ _))
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)

theorem exists_fund_srat (hR : Formalism.L2.SG.Count.FoldReady X.B.I) :
    ∃ Fs : Set X.B.I.GA, MeasurableSet Fs ∧ ∀ μ : Measure X.B.I.GA, IsFundamentalDomain (Srat X u) Fs μ := by
  have := hR.2.1
  have := hR.2.2.2.1
  have := hR.2.2.2.2
  have := srat_discrete X u
  exact exists_isFund (Srat X u)

end SGroupSec

section NT

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

variable (I : AutInst)

theorem nt_mulStar (a : I.E) : ∃ c : I.F, algebraMap I.F I.E c = a * star a :=
  (I.cm.fixed (a * star a)).1 (by rw [star_mul, star_star])

theorem nt_normSq (σ : I.E →+* ℂ) (a : I.E) : ((Complex.normSq (σ a) : ℝ) : ℂ) = σ (a * star a) := by
  rw [map_mul, I.cm.cmUnram.2.1 σ a, Complex.mul_conj]

theorem nt_absEmb (σ : I.E →+* ℂ) : ∃ v : InfinitePlace I.F, ∀ a : I.E, ‖σ a‖ = ‖I.φ v a‖ := by
  set w := InfinitePlace.mk (σ.comp (algebraMap I.F I.E))
  refine ⟨w, fun a => ?_⟩
  obtain ⟨c, hc⟩ := nt_mulStar I a
  have h1 := nt_normSq I σ a
  have h2 := nt_normSq I (I.φ w) a
  rw [← hc] at h1 h2
  rw [I.φ_over] at h2
  have h3 : w.embedding c = σ (algebraMap I.F I.E c) := by
    rcases InfinitePlace.embedding_mk_eq (σ.comp (algebraMap I.F I.E)) with h | h
    · rw [h]; rfl
    · rw [h]
      show starRingEnd ℂ (σ (algebraMap I.F I.E c)) = σ (algebraMap I.F I.E c)
      rw [← h1, Complex.conj_ofReal]
  have h4 : Complex.normSq (σ a) = Complex.normSq (I.φ w a) := by
    exact_mod_cast h1.trans (h3.symm.trans h2.symm)
  have h5 : ‖σ a‖ ^ 2 = ‖I.φ w a‖ ^ 2 := by rw [Complex.sq_norm, Complex.sq_norm, h4]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h5

theorem nt_int_eq_zero (a : 𝓞 I.E) (h : ∀ v, ‖I.φ v (a : I.E)‖ < 1) : a = 0 := by
  classical
  have hσ : ∀ σ : I.E →ₐ[ℚ] ℂ, ‖σ (a : I.E)‖ < 1 := fun σ => by
    obtain ⟨v, hv⟩ := nt_absEmb I σ.toRingHom
    exact (hv a).trans_lt (h v)
  have hn := Algebra.norm_eq_prod_embeddings ℚ ℂ (a : I.E)
  let σ0 : I.E →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hlt : ‖∏ σ : I.E →ₐ[ℚ] ℂ, σ (a : I.E)‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ0)]
    have hle : ∏ σ ∈ Finset.univ.erase σ0, ‖σ (a : I.E)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun σ _ => (hσ σ).le)
    calc ‖σ0 (a : I.E)‖ * ∏ σ ∈ Finset.univ.erase σ0, ‖σ (a : I.E)‖ ≤ ‖σ0 (a : I.E)‖ * 1 :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hσ σ0
  rw [← hn, ← Algebra.coe_norm_int] at hlt
  have hz : Algebra.norm ℤ a = 0 := by
    have : |(Algebra.norm ℤ a : ℝ)| < 1 := by
      have e : ‖(algebraMap ℚ ℂ ((Algebra.norm ℤ a : ℤ) : ℚ))‖ = |(Algebra.norm ℤ a : ℝ)| := by
        rw [map_intCast, Complex.norm_intCast]
      rw [← e]; exact hlt
    have : |Algebra.norm ℤ a| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.1 this
  exact (Algebra.norm_eq_zero_iff).1 hz

def trC (x : I.E) : I.E ⊗[I.F] Af I.F →ₗ[I.F] Af I.F :=
  TensorProduct.lift ((LinearMap.lsmul I.F (Af I.F)).comp ((Algebra.trace I.F I.E).comp (LinearMap.mulLeft I.F x)))

theorem trC_tmul (x y : I.E) (a : Af I.F) : trC I x (y ⊗ₜ a) = Algebra.trace I.F I.E (x * y) • a := rfl

theorem nt_trace_int (x : 𝓞 I.E) : Algebra.trace I.F I.E (x : I.E) ∈ (algebraMap (𝓞 I.F) I.F).range := by
  have : IsIntegral ℤ (Algebra.trace I.F I.E (x : I.E)) := Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe x)
  exact ⟨⟨_, this⟩, rfl⟩

theorem nt_intAd_of_int (t : 𝓞 I.F) : algebraMap I.F (Af I.F) (t : I.F) ∈ Formalism.UG.intAd I.F := by
  intro v
  show (algebraMap I.F (Af I.F) (t : I.F)) v ∈ _
  rw [FiniteAdeleRing.algebraMap_apply]
  exact coe_mem_adicCompletionIntegers v t

theorem nt_int_of_intAd (c : I.F) (h : algebraMap I.F (Af I.F) c ∈ Formalism.UG.intAd I.F) :
    c ∈ (algebraMap (𝓞 I.F) I.F).range := by
  refine mem_integers_of_valuation_le_one (R := 𝓞 I.F) (K := I.F) _ fun v => ?_
  rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
  have h2 := h v
  rw [FiniteAdeleRing.algebraMap_apply] at h2
  exact h2

def phiInt : 𝓞 I.E ⊗[ℤ] Formalism.UG.intAd I.F →ₐ[ℤ] I.E ⊗[I.F] Af I.F :=
  Algebra.TensorProduct.productMap
    { (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap (𝓞 I.E) I.E)) with
      commutes' := fun z => by simp }
    { (Algebra.TensorProduct.includeRight.toRingHom.comp (Formalism.UG.intAd I.F).subtype) with
      commutes' := fun z => by simp }

theorem phiInt_tmul (o : 𝓞 I.E) (r : Formalism.UG.intAd I.F) :
    phiInt I (o ⊗ₜ r) = (o : I.E) ⊗ₜ[I.F] (r : Af I.F) := by
  rw [phiInt, Algebra.TensorProduct.productMap_apply_tmul]
  show (o : I.E) ⊗ₜ[I.F] (1 : Af I.F) * ((1 : I.E) ⊗ₜ[I.F] (r : Af I.F)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem intAf_le_range : (IntAf I.F I.E : Set (I.E ⊗[I.F] Af I.F)) ⊆ Set.range (phiInt I) := by
  have : IntAf I.F I.E ≤ (phiInt I).range.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨o, rfl⟩ := hx
      refine ⟨o ⊗ₜ 1, ?_⟩
      show phiInt I (o ⊗ₜ 1) = _
      rw [phiInt_tmul]; rfl
    · refine ⟨1 ⊗ₜ y, ?_⟩
      show phiInt I (1 ⊗ₜ y) = _
      rw [phiInt_tmul]; simp
  intro w hw
  obtain ⟨t, ht⟩ := this hw
  exact ⟨t, ht⟩

theorem trC_phi (x : 𝓞 I.E) (t : 𝓞 I.E ⊗[ℤ] Formalism.UG.intAd I.F) : trC I x (phiInt I t) ∈ Formalism.UG.intAd I.F := by
  induction t using TensorProduct.induction_on with
  | zero => simpa using (Formalism.UG.intAd I.F).zero_mem
  | tmul o r =>
    rw [phiInt_tmul, trC_tmul]
    obtain ⟨s, hs⟩ := nt_trace_int I (x * o)
    have : ((x : I.E) * (o : I.E)) = ((x * o : 𝓞 I.E) : I.E) := by simp
    rw [this, ← hs, Algebra.smul_def]
    exact mul_mem (nt_intAd_of_int I s) r.2
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

theorem nt_trace_of_intAf (a : I.E) (ha : Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E) (x : 𝓞 I.E) :
    Algebra.trace I.F I.E ((x : I.E) * a) ∈ (algebraMap (𝓞 I.F) I.F).range := by
  obtain ⟨t, ht⟩ := intAf_le_range I ha
  have h := trC_phi I x t
  rw [ht] at h
  have e : trC I x (Formalism.UG.inclE (F := I.F) (Af I.F) a) = algebraMap I.F (Af I.F) (Algebra.trace I.F I.E ((x : I.E) * a)) := by
    show trC I x (a ⊗ₜ 1) = _
    rw [trC_tmul, Algebra.smul_def, mul_one]
  rw [e] at h
  exact nt_int_of_intAd I _ h

end NT

section NT2

open NumberField IsDedekindDomain
open scoped TensorProduct

variable (I : AutInst)

theorem nt_int_mul_of (x : I.E) : ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : I.E) * x) := by
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ I.E).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, by rwa [zsmul_eq_mul] at hi⟩

theorem nt_dual : ∃ c : ℤ, c ≠ 0 ∧ ∀ a : I.E,
    (∀ x : 𝓞 I.E, Algebra.trace I.F I.E ((x : I.E) * a) ∈ (algebraMap (𝓞 I.F) I.F).range) →
      IsIntegral ℤ ((c : I.E) * a) := by
  classical
  let b0 := Module.finBasis I.F I.E
  choose n hn0 hnI using fun i => nt_int_mul_of I (b0 i)
  let b := b0.isUnitSMul (w := fun i => ((n i : ℤ) : I.F)) (fun i => (Int.cast_ne_zero.2 (hn0 i)).isUnit)
  have hb : ∀ i, b i = ((n i : ℤ) : I.E) * b0 i := by
    intro i
    simp only [b, Module.Basis.isUnitSMul_apply, Algebra.smul_def, map_intCast]
  have hbI : ∀ i, IsIntegral ℤ (b i) := fun i => (hb i) ▸ hnI i
  have hB : (Algebra.traceForm I.F I.E).Nondegenerate := traceForm_nondegenerate I.F I.E
  let d := (Algebra.traceForm I.F I.E).dualBasis hB b
  choose m hm0 hmI using fun i => nt_int_mul_of I (d i)
  refine ⟨∏ i, m i, Finset.prod_ne_zero_iff.2 fun i _ => hm0 i, fun a ha => ?_⟩
  have hcoef : ∀ i, d.repr a i ∈ (algebraMap (𝓞 I.F) I.F).range := by
    intro i
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm]
    exact ha ⟨b i, hbI i⟩
  rw [← d.sum_repr a, Finset.mul_sum]
  refine (integralClosure ℤ I.E).sum_mem fun i _ => ?_
  obtain ⟨s, hs⟩ := hcoef i
  have e : ((∏ j, m j : ℤ) : I.E) * (d.repr a i • d i) =
      algebraMap I.F I.E (d.repr a i) * (((∏ j ∈ Finset.univ.erase i, m j : ℤ) : I.E) * ((m i : I.E) * d i)) := by
    rw [Algebra.smul_def, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    push_cast
    ring
  rw [e, ← hs]
  refine mul_mem ?_ (mul_mem ?_ (hmI i))
  · exact (RingOfIntegers.isIntegral_coe s).algebraMap
  · exact isIntegral_algebraMap

theorem nt_denom : ∃ c : ℤ, c ≠ 0 ∧ ∀ a : I.E, Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E →
    IsIntegral ℤ ((c : I.E) * a) := by
  obtain ⟨c, hc, h⟩ := nt_dual I
  exact ⟨c, hc, fun a ha => h a (nt_trace_of_intAf I a ha)⟩

end NT2

section NT3

open NumberField IsDedekindDomain
open scoped TensorProduct

variable (I : AutInst)

theorem nt_isIntegral_iff (a : I.E) : IsIntegral ℤ a ↔ a ∈ Formalism.UG.intOE I.E :=
  ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨o, ho⟩ => ho ▸ RingOfIntegers.isIntegral_coe o⟩

theorem nt_L_denom : ∃ c : ℤ, c ≠ 0 ∧ ∀ l ∈ I.L, ∀ i, IsIntegral ℤ ((c : I.E) * l i) := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  choose m hm0 hmI using fun (g : Fin I.n → I.E) (i : Fin I.n) => nt_int_mul_of I (g i)
  refine ⟨∏ g ∈ s, ∏ i, m g i, Finset.prod_ne_zero_iff.2 fun g _ => Finset.prod_ne_zero_iff.2 fun i _ => hm0 g i,
    fun l hl => ?_⟩
  rw [← hs] at hl
  induction hl using Submodule.span_induction with
  | mem g hg =>
    intro i
    have e : ((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * g i =
        (((∏ g' ∈ s.erase g, ∏ i, m g' i) * ∏ j ∈ Finset.univ.erase i, m g j : ℤ) : I.E) * ((m g i : I.E) * g i) := by
      rw [← Finset.mul_prod_erase _ _ hg, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      push_cast; ring
    rw [e]
    exact isIntegral_algebraMap.mul (hmI g i)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy => intro i; rw [Pi.add_apply, mul_add]; exact (hx i).add (hy i)
  | smul o x _ hx =>
    intro i
    have e : ((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * (o • x) i = (o : I.E) * (((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * x i) := by
      rw [Pi.smul_apply, Algebra.smul_def]
      change _ * ((o : I.E) * x i) = _
      ring
    rw [e]
    exact (RingOfIntegers.isIntegral_coe o).mul (hx i)

theorem nt_inclE_mem (a : I.E) (h : IsIntegral ℤ a) : Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨a, (nt_isIntegral_iff I a).1 h⟩, rfl⟩)

theorem nt_Lf_denom : ∃ c : ℤ, c ≠ 0 ∧ ∀ y : Fin I.n → I.E, Formalism.L2.SG.HidaSetting.incl I y ∈ I.Lf →
    ∀ i, IsIntegral ℤ ((c : I.E) * y i) := by
  obtain ⟨c1, hc1, h1⟩ := nt_L_denom I
  obtain ⟨c2, hc2, h2⟩ := nt_denom I
  have hLf : ∀ w ∈ I.Lf, ∀ i, Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * w i ∈ IntAf I.F I.E := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨l, hl⟩, rfl⟩ := hg
      intro i
      rw [← map_mul]
      exact nt_inclE_mem I _ (h1 l hl i)
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)
    | smul r x _ hx =>
      intro i
      have e : Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * (r • x) i =
          (r : I.E ⊗[I.F] Af I.F) * (Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * x i) := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
      rw [e]
      exact mul_mem r.2 (hx i)
  refine ⟨c2 * c1, mul_ne_zero hc2 hc1, fun y hy i => ?_⟩
  have := h2 _ (by rw [map_mul]; exact hLf _ hy i)
  have e : ((c2 * c1 : ℤ) : I.E) * y i = (c2 : I.E) * ((c1 : I.E) * y i) := by push_cast; ring
  rw [e]; exact this

end NT3

section Disc

open NumberField
open scoped TensorProduct

variable (I : AutInst)

theorem kset_open : IsOpen I.Kset := by
  have h := I.topf_open 1 le_rfl
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨hx, fun y hy => ⟨(((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) - 1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) *ᵥ y, ?_, ?_⟩⟩
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem ((hx y).1 hy) hy
    · simp
  · exact fun hx => hx.1

theorem one_mem_kset : (1 : I.Gf) ∈ I.Kset := by
  intro y
  show y ∈ I.Lf ↔ ((((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ y ∈ I.Lf
  simp

theorem mat_eq_one_of_fix {s : Set (Fin I.n → I.E)} (hspan : Submodule.span I.E s = ⊤)
    {M : Matrix (Fin I.n) (Fin I.n) I.E} (h : ∀ l ∈ s, M *ᵥ l = l) : M = 1 := by
  have hall : ∀ x, M *ᵥ x = x := by
    intro x
    have hx : x ∈ Submodule.span I.E s := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem l hl => exact h l hl
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, ha, hb]
    | smul r a _ ha => rw [Matrix.mulVec_smul, ha]
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem psi_eq (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E) (y : I.Ginf)
    (hy : uMat (y v) = (I.P v)⁻¹ * M.map (I.φ v) * I.P v) (l : Fin I.n → I.E) (i : Fin I.n) (c : ℤ) :
    I.φ v ((c : I.E) * ((M *ᵥ l) i - l i)) =
      (c : ℂ) * ((I.P v * (uMat (y v) - 1) * (I.P v)⁻¹) *ᵥ (fun k => I.φ v (l k))) i := by
  have hP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hP' : ∀ X : Matrix (Fin I.n) (Fin I.n) ℂ, I.P v * ((I.P v)⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
  have hM : I.P v * (uMat (y v) - 1) * (I.P v)⁻¹ = M.map (I.φ v) - 1 := by
    rw [hy]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, hP, hP']
  rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec, map_mul, map_sub, RingHom.map_mulVec, map_intCast]
  rfl

theorem gf_discrete : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF I) := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  obtain ⟨c, hc0, hc⟩ := nt_Lf_denom I
  have hsL : ∀ l ∈ s, l ∈ I.L := fun l hl => hs ▸ Submodule.subset_span hl
  have hspan : Submodule.span I.E (s : Set (Fin I.n → I.E)) = ⊤ := by
    rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, ← hs] at hx
    exact Submodule.span_le_restrictScalars (𝓞 I.E) I.E _ hx
  let Ψ : InfinitePlace I.F → (Fin I.n → I.E) → Fin I.n → I.Ginf → ℂ := fun v l i y =>
    (c : ℂ) * ((I.P v * (uMat (y v) - 1) * (I.P v)⁻¹) *ᵥ (fun k => I.φ v (l k))) i
  have hΨc : ∀ v l i, Continuous (Ψ v l i) := by
    intro v l i
    have hu : Continuous fun y : I.Ginf => uMat (y v) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
    have hm : Continuous fun y : I.Ginf => I.P v * (uMat (y v) - 1) * (I.P v)⁻¹ :=
      (continuous_const.matrix_mul (hu.sub continuous_const)).matrix_mul continuous_const
    exact continuous_const.mul ((continuous_apply i).comp (hm.matrix_mulVec continuous_const))
  have hΨ1 : ∀ v l i, Ψ v l i 1 = 0 := by
    intro v l i
    simp [Ψ, uMat]
  let U : Set I.GA := {x | (∀ v, ∀ l ∈ s, ∀ i, ‖Ψ v l i x.1‖ < 1) ∧ x.2 ∈ I.Kset}
  have hUo : IsOpen U := by
    have e : U = (⋂ v, ⋂ l ∈ s, ⋂ i, {x : I.GA | ‖Ψ v l i x.1‖ < 1}) ∩ Prod.snd ⁻¹' I.Kset := by
      ext x; simp [U]
    rw [e]
    refine IsOpen.inter ?_ ((kset_open I).preimage continuous_snd)
    refine isOpen_iInter_of_finite fun v => isOpen_biInter_finset fun l _ => isOpen_iInter_of_finite fun i => ?_
    exact isOpen_lt ((hΨc v l i).norm.comp continuous_fst) continuous_const
  have h1U : (1 : I.GA) ∈ U := ⟨fun v l _ i => by rw [Prod.fst_one, hΨ1]; simp, one_mem_kset I⟩
  have key : ∀ γ ∈ I.GFset, γ ∈ U → γ = 1 := by
    rintro γ ⟨M, -, h1, h2⟩ hU
    have hLf : ∀ l ∈ I.L, Formalism.L2.SG.HidaSetting.incl I l ∈ I.Lf := fun l hl =>
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    have hML : ∀ l ∈ I.L, Formalism.L2.SG.HidaSetting.incl I ((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) ∈ I.Lf := by
      intro l hl
      have e : Formalism.L2.SG.HidaSetting.incl I ((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) =
          I.fmat γ.2 *ᵥ Formalism.L2.SG.HidaSetting.incl I l := by
        rw [h2]; funext i
        simp only [Formalism.L2.SG.HidaSetting.incl, RingHom.map_mulVec]
        rfl
      rw [e]
      exact (hU.2 (Formalism.L2.SG.HidaSetting.incl I l)).1 (hLf l hl)
    have hfix : ∀ l ∈ (s : Set (Fin I.n → I.E)), (M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l = l := by
      intro l hl
      funext i
      have hint : IsIntegral ℤ ((c : I.E) * (((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) i - l i)) := by
        rw [mul_sub]
        exact (hc _ (hML l (hsL l hl)) i).sub (hc _ (hLf l (hsL l hl)) i)
      have h0 := nt_int_eq_zero I ⟨_, hint⟩ fun v => by
        show ‖I.φ v ((c : I.E) * (((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) i - l i))‖ < 1
        rw [psi_eq I v _ γ.1 (h1 v) l i c]
        exact hU.1 v l hl i
      have h0' : (c : I.E) * (((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) i - l i) = 0 :=
        congrArg Subtype.val h0
      have hc' : (c : I.E) ≠ 0 := Int.cast_ne_zero.2 hc0
      exact sub_eq_zero.1 ((mul_eq_zero.1 h0').resolve_left hc')
    have hM1 := mat_eq_one_of_fix I hspan hfix
    refine Prod.ext (funext fun v => ?_) ?_
    · apply Subtype.ext; apply Units.ext
      have := h1 v
      rw [hM1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
      rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))] at this
      exact this
    · apply Subtype.ext; apply Units.ext
      have : I.fmat γ.2 = 1 := by
        rw [h2, hM1, Matrix.map_one _ (map_zero _) (map_one _)]
      exact this
  apply discreteTopology_of_isOpen_singleton_one
  have e : ({1} : Set (Formalism.MainNotions.LeviCoordinates.rr_GF I)) = Subtype.val ⁻¹' U := by
    ext ⟨x, hx⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      rw [this]; exact h1U
    · intro h
      exact Subtype.ext (key x hx h)
  rw [e]
  exact hUo.preimage continuous_subtype_val

end Disc

section T2

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

theorem wz_lemma (γ δ : WithZero (Multiplicative ℤ)) (h : γ < 1) (hδ : ∀ k : ℕ, δ ≤ γ ^ k) : δ = 0 := by
  by_contra hδ0
  obtain ⟨d, rfl⟩ := WithZero.ne_zero_iff_exists.1 hδ0
  rcases eq_or_ne γ 0 with hγ | hγ
  · have := hδ 1
    rw [hγ, pow_one] at this
    exact WithZero.coe_ne_zero (le_antisymm this zero_le')
  obtain ⟨t, rfl⟩ := WithZero.ne_zero_iff_exists.1 hγ
  have ht : Multiplicative.toAdd t < 0 := by
    have h1 : t < 1 := by exact_mod_cast h
    exact h1
  have hk := hδ ((-(Multiplicative.toAdd d)).toNat + 1)
  rw [← WithZero.coe_pow, WithZero.coe_le_coe] at hk
  have h2 : Multiplicative.toAdd d ≤ (((-(Multiplicative.toAdd d)).toNat + 1 : ℕ) : ℤ) * Multiplicative.toAdd t := by
    have := Multiplicative.toAdd_le.2 hk
    rwa [toAdd_pow, nsmul_eq_mul] at this
  have h3 : (0 : ℤ) ≤ ((-(Multiplicative.toAdd d)).toNat : ℤ) := Nat.cast_nonneg _
  have h4 : -(Multiplicative.toAdd d) ≤ ((-(Multiplicative.toAdd d)).toNat : ℤ) := Int.self_le_toNat _
  push_cast at h2
  nlinarith

theorem af_iInter (F : Type) [Field F] [NumberField F] (a : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ g : ℕ, 1 ≤ g → ∃ r : FiniteAdeleRing (𝓞 F) F, (∀ v, r v ∈ v.adicCompletionIntegers F) ∧
      a = algebraMap F (FiniteAdeleRing (𝓞 F) F) (g : F) * r) : a = 0 := by
  ext v
  suffices hv : a v = 0 by rw [hv]; rfl
  set p : ℕ := Ideal.absNorm v.asIdeal
  have hp0 : p ≠ 0 := by
    simp only [p, ne_eq, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hpv : v.valuation F ((p : 𝓞 F) : F) < 1 := (valuation_lt_one_iff_mem v _).2 (Ideal.absNorm_mem _)
  clear_value p
  have hval : ∀ k : ℕ, Valued.v (a v) ≤ (v.valuation F ((p : 𝓞 F) : F)) ^ k := by
    intro k
    obtain ⟨r, hr, hra⟩ := h (p ^ k) (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hp0))
    have e : a v = ((((p ^ k : ℕ) : F)) : v.adicCompletion F) * r v := by
      rw [hra]; rfl
    rw [e, Valued.v.map_mul]
    have h1 : Valued.v ((((p ^ k : ℕ) : F)) : v.adicCompletion F) = (v.valuation F ((p : 𝓞 F) : F)) ^ k := by
      rw [valuedAdicCompletion_eq_valuation', ← map_pow]; push_cast; rfl
    rw [h1]
    exact mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).1 (hr v))
  exact (Valued.v.zero_iff).1 (wz_lemma _ _ hpv hval)

variable (I : AutInst)

theorem nt_intBasis : ∃ b : Module.Basis (Fin (Module.finrank I.F I.E)) I.F I.E, ∀ i, IsIntegral ℤ (b i) := by
  classical
  let b0 := Module.finBasis I.F I.E
  choose n hn0 hnI using fun i => nt_int_mul_of I (b0 i)
  refine ⟨b0.isUnitSMul (w := fun i => ((n i : ℤ) : I.F)) (fun i => (Int.cast_ne_zero.2 (hn0 i)).isUnit), fun i => ?_⟩
  have : b0.isUnitSMul (w := fun i => ((n i : ℤ) : I.F)) (fun i => (Int.cast_ne_zero.2 (hn0 i)).isUnit) i =
      ((n i : ℤ) : I.E) * b0 i := by
    simp only [Module.Basis.isUnitSMul_apply, Algebra.smul_def, map_intCast]
  rw [this]; exact hnI i

theorem trC_intAf (x : 𝓞 I.E) {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ IntAf I.F I.E) : trC I x t ∈ Formalism.UG.intAd I.F := by
  obtain ⟨t', rfl⟩ := intAf_le_range I ht
  exact trC_phi I x t'

theorem trC_nondeg (u : I.E ⊗[I.F] Af I.F) (h : ∀ x : 𝓞 I.E, trC I x u = 0) : u = 0 := by
  classical
  obtain ⟨b, hbI⟩ := nt_intBasis I
  have hB : (Algebra.traceForm I.F I.E).Nondegenerate := traceForm_nondegenerate I.F I.E
  let d := (Algebra.traceForm I.F I.E).dualBasis hB b
  have hrep : ∀ w : I.E ⊗[I.F] Af I.F, ∃ a : Fin (Module.finrank I.F I.E) → Af I.F, w = ∑ j, d j ⊗ₜ[I.F] a j := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul e a =>
      refine ⟨fun j => d.repr e j • a, ?_⟩
      conv_lhs => rw [← d.sum_repr e]
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨a', rfl⟩ := hy
      exact ⟨a + a', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  obtain ⟨a, rfl⟩ := hrep u
  have ha : ∀ i, a i = 0 := by
    intro i
    let bi : 𝓞 I.E := ⟨b i, hbI i⟩
    have hbi : (bi : I.E) = b i := rfl
    have h1 := h bi
    rw [map_sum] at h1
    simp only [trC_tmul, hbi] at h1
    have e : ∀ j, Algebra.trace I.F I.E (b i * d j) = if i = j then 1 else 0 := by
      intro j
      have := LinearMap.BilinForm.apply_dualBasis_left hB b j i
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact this
    simp only [e, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    exact h1
  simp [ha]

theorem nt_Lf_int : ∃ c : ℤ, c ≠ 0 ∧ ∀ w ∈ I.Lf, ∀ i,
    Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) * w i ∈ IntAf I.F I.E := by
  obtain ⟨c1, hc1, h1⟩ := nt_L_denom I
  refine ⟨c1, hc1, fun w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hg
    intro i
    rw [← map_mul]
    exact nt_inclE_mem I _ (h1 l hl i)
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)
  | smul r x _ hx =>
    intro i
    have e : Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * (r • x) i =
        (r : I.E ⊗[I.F] Af I.F) * (Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * x i) := by
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
    rw [e]
    exact mul_mem r.2 (hx i)

theorem one_mem_Kg (g : ℕ) : (1 : I.Gf) ∈ I.Kg g :=
  ⟨one_mem_kset I, fun y _ => ⟨0, zero_mem _, by simp [AutInst.fmat]⟩⟩

theorem sepK (x : I.Gf) (hx : ∀ g : ℕ, 1 ≤ g → x ∈ I.Kg g) : x = 1 := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  have hsL : ∀ l ∈ s, l ∈ I.L := fun l hl => hs ▸ Submodule.subset_span hl
  have hspan : Submodule.span I.E (s : Set (Fin I.n → I.E)) = ⊤ := by
    rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, ← hs] at hx
    exact Submodule.span_le_restrictScalars (𝓞 I.E) I.E _ hx
  obtain ⟨c1, hc1, hLf⟩ := nt_Lf_int I
  have hLfI : ∀ l ∈ I.L, Formalism.L2.SG.HidaSetting.incl I l ∈ I.Lf := fun l hl =>
    Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
  have hunit : IsUnit (Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E)) :=
    (Ne.isUnit (Int.cast_ne_zero.2 hc1)).map _
  have hfix : ∀ l ∈ (s : Set (Fin I.n → I.E)), I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl I l = Formalism.L2.SG.HidaSetting.incl I l := by
    intro l hl
    funext i
    have hu : ∀ x' : 𝓞 I.E, trC I x' (Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) *
        ((I.fmat x - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I l) i) = 0 := by
      intro x'
      apply af_iInter
      intro g hg
      obtain ⟨z, hz, hwz⟩ := (hx g hg).2 (Formalism.L2.SG.HidaSetting.incl I l) (hLfI l (hsL l hl))
      refine ⟨trC I x' (Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * z i), trC_intAf I x' (hLf z hz i), ?_⟩
      have e1 : ((I.fmat x - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I l) i = (g : I.E ⊗[I.F] Af I.F) * z i := by
        rw [hwz]; rfl
      rw [e1, mul_left_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, map_natCast]
    have hu0 := trC_nondeg I _ hu
    have hw0 : ((I.fmat x - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I l) i = 0 := hunit.mul_right_eq_zero.1 hu0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at hw0
    exact hw0
  have hall : ∀ y : Fin I.n → I.E, I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl I y = Formalism.L2.SG.HidaSetting.incl I y := by
    intro y
    have hy : y ∈ Submodule.span I.E (s : Set (Fin I.n → I.E)) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem l hl => exact hfix l hl
    | zero =>
      have : Formalism.L2.SG.HidaSetting.incl I (0 : Fin I.n → I.E) = 0 := by funext i; simp [Formalism.L2.SG.HidaSetting.incl]
      rw [this, Matrix.mulVec_zero]
    | add a b _ _ ha hb =>
      have : Formalism.L2.SG.HidaSetting.incl I (a + b) = Formalism.L2.SG.HidaSetting.incl I a + Formalism.L2.SG.HidaSetting.incl I b := by
        funext i; simp [Formalism.L2.SG.HidaSetting.incl]
      rw [this, Matrix.mulVec_add, ha, hb]
    | smul r a _ ha =>
      have : Formalism.L2.SG.HidaSetting.incl I (r • a) = Formalism.UG.inclE (F := I.F) (Af I.F) r • Formalism.L2.SG.HidaSetting.incl I a := by
        funext i; simp [Formalism.L2.SG.HidaSetting.incl]
      rw [this, Matrix.mulVec_smul, ha]
  have hX : I.fmat x = 1 := by
    ext i j
    have h1 := congrFun (hall (Pi.single j 1)) i
    have e : Formalism.L2.SG.HidaSetting.incl I (Pi.single j (1 : I.E)) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk; simp [Formalism.L2.SG.HidaSetting.incl]
      · simp [Formalism.L2.SG.HidaSetting.incl, hk]
    rw [e, Matrix.mulVec_single_one] at h1
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1
  apply Subtype.ext; apply Units.ext
  exact hX

theorem finite_adeles_group_t2 : T2Space I.Gf :=
  IsTopologicalGroup.t2Space_of_one_sep fun x hx => by
    by_contra hcon
    push Not at hcon
    exact hx (sepK I x fun g hg => hcon _ ((I.topf_open g hg).mem_nhds (one_mem_Kg I g)))

end T2

section Fold

open MeasureTheory

variable (I : AutInst)

def KCompact : Prop := IsCompact I.Kset

def KCountIdx : Prop := ∃ C : Set I.Gf, C.Countable ∧ ∀ x : I.Gf, ∃ c ∈ C, c⁻¹ * x ∈ I.Kset

theorem gf_lc (hK : KCompact I) : LocallyCompactSpace I.Gf :=
  IsCompact.locallyCompactSpace_of_mem_nhds_of_group hK ((kset_open I).mem_nhds (one_mem_kset I))

theorem gf_sigmaCompact (hK : KCompact I) (hC : KCountIdx I) : SigmaCompactSpace I.Gf := by
  obtain ⟨C, hCc, hCx⟩ := hC
  refine SigmaCompactSpace.of_countable ((fun c => (fun y => c * y) '' I.Kset) '' C) (hCc.image _) ?_ ?_
  · rintro _ ⟨c, -, rfl⟩
    exact hK.image (continuous_const.mul continuous_id)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨c, hc, hx⟩ := hCx x
    exact Set.mem_sUnion.2 ⟨_, ⟨c, hc, rfl⟩, c⁻¹ * x, hx, by simp⟩

theorem gf_sc (hK : KCompact I) (hC : KCountIdx I) : SecondCountableTopology I.Gf := by
  have := gf_lc I hK
  have := gf_sigmaCompact I hK hC
  have : SigmaFinite (Measure.haar : Measure I.Gf) := Measure.IsHaarMeasure.sigmaFinite _
  exact Formalism.MainNotions.LeviCoordinates.rr_secondCountable I Measure.haar

theorem foldReady_of (hK : KCompact I) (hC : KCountIdx I) : Formalism.L2.SG.Count.FoldReady I := by
  have := gf_lc I hK
  have := finite_adeles_group_t2 I
  have := gf_sc I hK hC
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, gf_discrete I⟩

end Fold

section NLamGrp

open Formalism.MainNotions.S.Lat NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} (Λ : Submodule (𝓞 E) S.V)
  {r : ℕ} {T : E} (F : LFlag S r T)

theorem le_mul_app (a b : S.V ≃ₗ[E] S.V) (x : S.V) : (a * b) x = a (b x) := rfl

theorem le_inv_app (a : S.V ≃ₗ[E] S.V) (x : S.V) : a⁻¹ x = a.symm x := rfl

theorem gmap_mul (a b : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩

theorem gmap_one (L : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap (1 : S.V ≃ₗ[E] S.V) L = L := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨x, hx, rfl⟩

theorem gmap_inv {a : S.V ≃ₗ[E] S.V} {L L' : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap a L' = L) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ L = L' := by
  rw [← h, ← gmap_mul, inv_mul_cancel, gmap_one]

theorem xflag_zero : Xflag F 0 = ⊥ := by
  show Submodule.span E (F.fl.e '' {i | i.1 < 0}) = ⊥
  simp

theorem xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) :=
  Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => Nat.lt_succ_of_lt hi)

theorem xsp_eq : Xsp F = Xflag F r := by
  show Submodule.span E (Set.range F.fl.e) = Submodule.span E (F.fl.e '' {i | i.1 < r})
  congr 1
  ext x; constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩

variable {Λ F}

theorem nlam_pres {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, n x ∈ Xflag F j := by
  cases j with
  | zero =>
    intro x hx
    rw [xflag_zero, Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
  | succ j =>
    intro x hx
    have h := hn.2.1 j x hx
    have : n x = x + (n x - x) := by abel
    rw [this]
    exact add_mem hx (xflag_mono F j h)

theorem nlam_presX {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  rw [xsp_eq]; exact nlam_pres hn r

theorem equiv_symm_pres (n : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (h : ∀ x ∈ U, n x ∈ U) :
    ∀ y ∈ U, n.symm y ∈ U := by
  have hle : U.map (n : S.V →ₗ[E] S.V) ≤ U := by
    rintro _ ⟨x, hx, rfl⟩; exact h x hx
  have heq : U.map (n : S.V →ₗ[E] S.V) = U :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n U)
  intro y hy
  rw [← heq] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

variable (Λ F)

theorem nlam_one : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F :=
  ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).one_mem, gmap_one Λ⟩, fun j x _ => by
    rw [show (1 : S.V ≃ₗ[E] S.V) x = x from rfl, sub_self]; exact zero_mem _, fun x _ => by
    rw [show (1 : S.V ≃ₗ[E] S.V) x = x from rfl, sub_self]; exact zero_mem _⟩

variable {Λ F}

theorem nlam_mul {a b : S.V ≃ₗ[E] S.V} (ha : a ∈ NLam Λ F) (hb : b ∈ NLam Λ F) : a * b ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem ha.1.1 hb.1.1, by rw [gmap_mul, hb.1.2, ha.1.2]⟩, fun j x hx => ?_, fun x hx => ?_⟩
  · have e : (a * b) x - x = a (b x - x) + (a x - x) := by rw [le_mul_app, map_sub]; abel
    rw [e]
    exact add_mem (nlam_pres ha j _ (hb.2.1 j x hx)) (ha.2.1 j x hx)
  · have e : (a * b) x - x = a (b x - x) + (a x - x) := by rw [le_mul_app, map_sub]; abel
    rw [e]
    exact add_mem (nlam_presX ha _ (hb.2.2 x hx)) (ha.2.2 x hx)

theorem nlam_inv {a : S.V ≃ₗ[E] S.V} (ha : a ∈ NLam Λ F) : a⁻¹ ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).inv_mem ha.1.1, gmap_inv ha.1.2⟩, fun j x hx => ?_, fun x hx => ?_⟩
  · have e : a⁻¹ x - x = -(a.symm (a x - x)) := by rw [le_inv_app, map_sub]; simp
    rw [e]
    exact neg_mem (equiv_symm_pres a _ (nlam_pres ha j) _ (ha.2.1 j x hx))
  · have e : a⁻¹ x - x = -(a.symm (a x - x)) := by rw [le_inv_app, map_sub]; simp
    rw [e]
    exact neg_mem (equiv_symm_pres a _ (nlam_presX ha) _ (ha.2.2 x hx))

def NLamSub (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) : Subgroup (S.V ≃ₗ[E] S.V) where
  carrier := NLam Λ F
  one_mem' := nlam_one Λ F
  mul_mem' := nlam_mul
  inv_mem' := nlam_inv

end NLamGrp

section GinfDisc

open NumberField

variable (I : AutInst)

theorem ginf_disc_of_lat (Sg : Subgroup I.Ginf) (s : Finset (Fin I.n → I.E))
    (hspan : Submodule.span I.E (s : Set (Fin I.n → I.E)) = ⊤) (c : ℤ) (hc0 : c ≠ 0)
    (hS : ∀ y ∈ Sg, ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ v, uMat (y v) = (I.P v)⁻¹ * M.map (I.φ v) * I.P v) ∧
      ∀ l ∈ s, ∀ i, IsIntegral ℤ ((c : I.E) * ((M *ᵥ l) i - l i))) : DiscreteTopology Sg := by
  classical
  let Ψ : InfinitePlace I.F → (Fin I.n → I.E) → Fin I.n → I.Ginf → ℂ := fun v l i y =>
    (c : ℂ) * ((I.P v * (uMat (y v) - 1) * (I.P v)⁻¹) *ᵥ (fun k => I.φ v (l k))) i
  have hΨc : ∀ v l i, Continuous (Ψ v l i) := by
    intro v l i
    have hu : Continuous fun y : I.Ginf => uMat (y v) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
    have hm : Continuous fun y : I.Ginf => I.P v * (uMat (y v) - 1) * (I.P v)⁻¹ :=
      (continuous_const.matrix_mul (hu.sub continuous_const)).matrix_mul continuous_const
    exact continuous_const.mul ((continuous_apply i).comp (hm.matrix_mulVec continuous_const))
  have hΨ1 : ∀ v l i, Ψ v l i 1 = 0 := by
    intro v l i
    simp [Ψ, uMat]
  let U : Set I.Ginf := ⋂ v, ⋂ l ∈ s, ⋂ i, {y : I.Ginf | ‖Ψ v l i y‖ < 1}
  have hUo : IsOpen U :=
    isOpen_iInter_of_finite fun v => isOpen_biInter_finset fun l _ => isOpen_iInter_of_finite fun i =>
      isOpen_lt (hΨc v l i).norm continuous_const
  have h1U : (1 : I.Ginf) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
    intro v l _ i; rw [hΨ1]; simp
  have key : ∀ y ∈ Sg, y ∈ U → y = 1 := by
    intro y hy hU
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at hU
    obtain ⟨M, h1, hint⟩ := hS y hy
    have hfix : ∀ l ∈ (s : Set (Fin I.n → I.E)), M *ᵥ l = l := by
      intro l hl
      funext i
      have h0 := nt_int_eq_zero I ⟨_, hint l hl i⟩ fun v => by
        show ‖I.φ v ((c : I.E) * ((M *ᵥ l) i - l i))‖ < 1
        rw [psi_eq I v _ y (h1 v) l i c]
        exact hU v l hl i
      have h0' : (c : I.E) * ((M *ᵥ l) i - l i) = 0 := congrArg Subtype.val h0
      exact sub_eq_zero.1 ((mul_eq_zero.1 h0').resolve_left (Int.cast_ne_zero.2 hc0))
    have hM1 := mat_eq_one_of_fix I hspan hfix
    funext v
    apply Subtype.ext; apply Units.ext
    have := h1 v
    rw [hM1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))] at this
    exact this
  apply discreteTopology_of_isOpen_singleton_one
  have e : ({1} : Set Sg) = Subtype.val ⁻¹' U := by
    ext ⟨x, hx⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      rw [this]; exact h1U
    · intro h
      exact Subtype.ext (key x hx h)
  rw [e]
  exact hUo.preimage continuous_subtype_val

theorem isSFund_of_discrete (Sg : Subgroup I.Ginf) [DiscreteTopology Sg] :
    ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund I (Sg : Set I.Ginf) Ω := by
  obtain ⟨F, hF, h1, h2⟩ := exists_strictFund Sg
  exact ⟨F, hF, h1, h2⟩

end GinfDisc

section Terms

open Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.TermDef NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem fvec_mapFlag {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) :
    (mapFlag γ hγ F).fvec = fun a => γ (F.fvec a) := by
  funext a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

theorem xa_mapFlag {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (j : ℕ) :
    (mapFlag γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V) := by
  show Submodule.span E ((fun a => γ (F.e a)) '' _) = _
  rw [FlagG.Xa, Submodule.map_span, ← Set.image_comp]
  rfl

theorem x_mapFlag {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) :
    (mapFlag γ hγ F).X = F.X.map (γ : S.V →ₗ[E] S.V) := by
  show Submodule.span E (Set.range fun a => γ (F.e a)) = _
  rw [FlagG.X, Submodule.map_span, ← Set.range_comp]
  rfl

theorem mem_orth_iff (U : Submodule E S.V) (x : S.V) : x ∈ orth S U ↔ ∀ u ∈ U, S.hT u x = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem orth_map (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U : Submodule E S.V) (x : S.V)
    (hx : x ∈ orth S (U.map (γ : S.V →ₗ[E] S.V))) : γ.symm x ∈ orth S U := by
  rw [mem_orth_iff] at hx ⊢
  intro u hu
  have h1 := hγ u (γ.symm x)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  exact hx _ ⟨u, hu, rfl⟩

theorem dcrel_of {Λ Λ' : Submodule (𝓞 E) S.V} {T T' : E} (F : LFlag S r T) (F' : LFlag S r T')
    {γ γ₂ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ₂ : γ₂ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hΛ : Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ) {n n' : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hn' : n' ∈ NLam Λ' F')
    (h : γ₂ = n * γ * n') : DCRel Λ F (mapLF γ F') (mapLF γ₂ F') := by
  have hm : γ * n' * γ⁻¹ ∈ NLam Λ (mapLF γ F') := by
    rw [mapLF, dif_pos hγ]
    refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem ((Formalism.HermitianLatticesTheory.isom S.hT).mul_mem hγ hn'.1.1) ((Formalism.HermitianLatticesTheory.isom S.hT).inv_mem hγ),
      by rw [gmap_mul, gmap_mul, gmap_inv hΛ, hn'.1.2, hΛ]⟩, fun j x hx => ?_, fun x hx => ?_⟩
    · change x ∈ (mapFlag γ hγ F'.fl).Xa (j + 1) at hx
      change _ ∈ (mapFlag γ hγ F'.fl).Xa j
      rw [xa_mapFlag] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨n' y - y, hn'.2.1 j y hy, ?_⟩
      simp [le_mul_app, le_inv_app, map_sub]
    · change x ∈ orth S (mapFlag γ hγ F'.fl).X at hx
      change _ ∈ (mapFlag γ hγ F'.fl).X
      rw [x_mapFlag] at hx ⊢
      have hy := orth_map γ hγ _ x hx
      refine ⟨n' (γ.symm x) - γ.symm x, hn'.2.2 _ hy, ?_⟩
      simp [le_mul_app, le_inv_app, map_sub]
  refine ⟨n, hn, γ * n' * γ⁻¹, hm, fun a => ?_, ?_⟩
  · rw [mapLF, mapLF, dif_pos hγ, dif_pos hγ₂]
    show (mapFlag γ₂ hγ₂ F'.fl).fvec a = n ((γ * n' * γ⁻¹) ((mapFlag γ hγ F'.fl).fvec a))
    rw [fvec_mapFlag, fvec_mapFlag, h]
    simp [le_mul_app, le_inv_app]
  · rw [mapLF, mapLF, dif_pos hγ, dif_pos hγ₂]
    show γ₂ F'.zt = n ((γ * n' * γ⁻¹) (γ F'.zt))
    rw [h]
    simp [le_mul_app, le_inv_app]

end Gen

variable {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))

theorem toTermRel_holds : ToTermRel X u u' F0 F0' := by
  rintro Λ Λ' p q ⟨n, hn, n', hn', h⟩
  exact dcrel_of (lf D F0) (lf D F0') p.2.2.1 q.2.2.1 p.2.2.2.1 hn hn' h

end Terms

section Closed

variable (I : AutInst)

theorem gf_locallyCompact : LocallyCompactSpace I.Gf := gf_lc I (PI.WAU.maximal_compact_isCompact I)

theorem gf_secondCountable : SecondCountableTopology I.Gf :=
  gf_sc I (PI.WAU.maximal_compact_isCompact I) (PI.WAU.compact_countable I)

theorem foldReady_holds : Formalism.L2.SG.Count.FoldReady I :=
  foldReady_of I (PI.WAU.maximal_compact_isCompact I) (PI.WAU.compact_countable I)

theorem exists_fund_srat_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) :
    ∃ Fs : Set X.B.I.GA, MeasurableSet Fs ∧
      ∀ μ : Measure X.B.I.GA, IsFundamentalDomain (Formalism.L2.SG.PoincareInHH.PoincareSetting.Srat X u) Fs μ :=
  exists_fund_srat X u (foldReady_holds X.B.I)

end Closed

section NO

open NumberField Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Formalism.L2.SG.PoincareInHH.PoincareSetting

variable (I : AutInst)

theorem gf_key : ∃ W : Set I.Ginf, IsOpen W ∧ (1 : I.Ginf) ∈ W ∧
    ∀ γ ∈ I.GFset, γ.1 ∈ W → γ.2 ∈ I.Kset → γ = 1 := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  obtain ⟨c, hc0, hc⟩ := nt_Lf_denom I
  have hsL : ∀ l ∈ s, l ∈ I.L := fun l hl => hs ▸ Submodule.subset_span hl
  have hspan : Submodule.span I.E (s : Set (Fin I.n → I.E)) = ⊤ := by
    rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, ← hs] at hx
    exact Submodule.span_le_restrictScalars (𝓞 I.E) I.E _ hx
  let Ψ : InfinitePlace I.F → (Fin I.n → I.E) → Fin I.n → I.Ginf → ℂ := fun v l i y =>
    (c : ℂ) * ((I.P v * (uMat (y v) - 1) * (I.P v)⁻¹) *ᵥ (fun k => I.φ v (l k))) i
  have hΨc : ∀ v l i, Continuous (Ψ v l i) := by
    intro v l i
    have hu : Continuous fun y : I.Ginf => uMat (y v) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
    have hm : Continuous fun y : I.Ginf => I.P v * (uMat (y v) - 1) * (I.P v)⁻¹ :=
      (continuous_const.matrix_mul (hu.sub continuous_const)).matrix_mul continuous_const
    exact continuous_const.mul ((continuous_apply i).comp (hm.matrix_mulVec continuous_const))
  have hΨ1 : ∀ v l i, Ψ v l i 1 = 0 := by
    intro v l i
    simp [Ψ, uMat]
  refine ⟨⋂ v, ⋂ l ∈ s, ⋂ i, {y : I.Ginf | ‖Ψ v l i y‖ < 1},
    isOpen_iInter_of_finite fun v => isOpen_biInter_finset fun l _ => isOpen_iInter_of_finite fun i =>
      isOpen_lt (hΨc v l i).norm continuous_const, ?_, ?_⟩
  · simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro v l _ i; rw [hΨ1]; simp
  rintro γ ⟨M, -, h1, h2⟩ hU hK
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hU
  have hLf : ∀ l ∈ I.L, incl I l ∈ I.Lf := fun l hl => Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
  have hML : ∀ l ∈ I.L, incl I ((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) ∈ I.Lf := by
    intro l hl
    have e : incl I ((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) = I.fmat γ.2 *ᵥ incl I l := by
      rw [h2]; funext i
      simp only [incl, RingHom.map_mulVec]
      rfl
    rw [e]
    exact (hK (incl I l)).1 (hLf l hl)
  have hfix : ∀ l ∈ (s : Set (Fin I.n → I.E)), (M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l = l := by
    intro l hl
    funext i
    have hint : IsIntegral ℤ ((c : I.E) * (((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) i - l i)) := by
      rw [mul_sub]
      exact (hc _ (hML l (hsL l hl)) i).sub (hc _ (hLf l (hsL l hl)) i)
    have h0 := nt_int_eq_zero I ⟨_, hint⟩ fun v => by
      show ‖I.φ v ((c : I.E) * (((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) i - l i))‖ < 1
      rw [psi_eq I v _ γ.1 (h1 v) l i c]
      exact hU v l hl i
    have h0' : (c : I.E) * (((M : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ l) i - l i) = 0 :=
      congrArg Subtype.val h0
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0').resolve_left (Int.cast_ne_zero.2 hc0))
  have hM1 := mat_eq_one_of_fix I hspan hfix
  refine Prod.ext (funext fun v => ?_) ?_
  · apply Subtype.ext; apply Units.ext
    have := h1 v
    rw [hM1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))] at this
    exact this
  · apply Subtype.ext; apply Units.ext
    have : I.fmat γ.2 = 1 := by
      rw [h2, hM1, Matrix.map_one _ (map_zero _) (map_one _)]
    exact this

variable {I} {r : ℕ}

def NinfSub (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Subgroup I.Ginf where
  carrier := Ninf I e z
  one_mem' := fun v => by
    show InN _ _ _ (uMat ((1 : I.Ginf) v))
    have : uMat ((1 : I.Ginf) v) = 1 := by simp [uMat]
    rw [this]; exact ⟨inFl_one _, fun y _ => by simp⟩
  mul_mem' := by
    intro s t hs ht v
    show InN _ _ _ (uMat ((s * t) v))
    have : uMat ((s * t) v) = uMat (s v) * uMat (t v) := by simp [uMat]
    rw [this]
    exact ⟨inFl_mul (hs v).1 (ht v).1, fun y hy => fl_mul (fl_map_le (hs v).1.1 r) ((hs v).2 y hy) ((ht v).2 y hy)⟩
  inv_mem' := by
    intro s hs v
    show InN _ _ _ (uMat (s⁻¹ v))
    have : uMat (s⁻¹ v) * uMat (s v) = 1 := by simp [uMat]
    exact ⟨inFl_inv this (hs v).1, fun y hy => fl_inv this (fl_le_map (hs v).1.1 r) ((hs v).2 y hy)⟩

theorem nfin_iff (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (x : I.Gf) :
    x ∈ Nfin I e z ↔ InFl (e := fun b => incl I (e b)) (incl I z) (I.fmat x) ∧
      ∀ y : VA I, (∀ a, hA I (incl I (e a)) y = 0) → (I.fmat x - 1) *ᵥ y ∈ spL (fun b => incl I (e b)) r := by
  unfold Nfin InFl spL
  rw [← range_eq_image_lt]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

def NfinSub (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Subgroup I.Gf where
  carrier := Nfin I e z
  one_mem' := by
    show (1 : I.Gf) ∈ Nfin I e z
    rw [nfin_iff]
    have : I.fmat 1 = 1 := by simp [AutInst.fmat]
    rw [this]; exact ⟨inFl_one _, fun y _ => by simp⟩
  mul_mem' := by
    intro a b ha hb
    rw [nfin_iff] at ha hb ⊢
    have : I.fmat (a * b) = I.fmat a * I.fmat b := by simp [AutInst.fmat]
    rw [this]
    exact ⟨inFl_mul ha.1 hb.1, fun y hy => fl_mul (fl_map_le ha.1.1 r) (ha.2 y hy) (hb.2 y hy)⟩
  inv_mem' := by
    intro a ha
    rw [nfin_iff] at ha ⊢
    have : I.fmat a⁻¹ * I.fmat a = 1 := by simp [AutInst.fmat]
    exact ⟨inFl_inv this ha.1, fun y hy => fl_inv this (fl_le_map ha.1.1 r) (ha.2 y hy)⟩

variable {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

def concreteLevelAdelicSubset (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf := Formalism.L2.SG.Count.levelSubgroupOfCharacter X hK

def NOA (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.GA :=
  Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (NinfSub X.eR (X.zR u)).prod
    (NfinSub X.eR (X.zR u) ⊓ (concreteLevelAdelicSubset X hK).map (MulAut.conj (X.xu u)).toMonoidHom)

def NOsub (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Ginf := (NOA X u hK).map (MonoidHom.fst _ _)

theorem NOsub_coe (hK : X.LevelSubgroupCharacter) : ((NOsub X u hK : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) = NOinf X u := by
  ext s
  simp only [NOsub, NOA, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Subgroup.mem_inf,
    Subgroup.mem_prod, Subgroup.mem_map, MonoidHom.coe_fst, NOinf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨γ, ⟨hγ, h1, h2, k, hk, hkγ⟩, rfl⟩
    refine ⟨γ, hγ, rfl, h1, h2, ?_⟩
    rw [← hkγ]
    have e : (X.xu u)⁻¹ * ((MulAut.conj (X.xu u)).toMonoidHom k) * X.xu u = k := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]; exact hk
  · rintro ⟨γ, hγ, rfl, h1, h2, h3⟩
    refine ⟨γ, ⟨hγ, h1, h2, (X.xu u)⁻¹ * γ.2 * X.xu u, h3, ?_⟩, rfl⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem kset_mul {a b : X.B.I.Gf} (ha : a ∈ X.B.I.Kset) (hb : b ∈ X.B.I.Kset) : a * b ∈ X.B.I.Kset :=
  (Formalism.UG.stabGL X.B.I.Lf).mul_mem ha hb

theorem kset_inv {a : X.B.I.Gf} (ha : a ∈ X.B.I.Kset) : a⁻¹ ∈ X.B.I.Kset :=
  (Formalism.UG.stabGL X.B.I.Lf).inv_mem ha

theorem NOsub_discrete (hK : X.LevelSubgroupCharacter) : DiscreteTopology (NOsub X u hK) := by
  obtain ⟨W, hWo, hW1, hW⟩ := gf_key X.B.I
  apply discreteTopology_of_isOpen_singleton_one
  have e : ({1} : Set (NOsub X u hK)) = Subtype.val ⁻¹' W := by
    ext ⟨s, hs⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      rw [this]; exact hW1
    · intro h
      apply Subtype.ext
      have hs' : s ∈ NOinf X u := by rw [← NOsub_coe X u hK]; exact hs
      obtain ⟨γ, hγ, rfl, -, -, h3⟩ := hs'
      have hk : (X.xu u)⁻¹ * γ.2 * X.xu u ∈ X.B.I.Kset := h3.1
      have hxu := X.xu_K u
      have hγK : γ.2 ∈ X.B.I.Kset := by
        have := kset_mul X (kset_mul X hxu hk) (kset_inv X hxu)
        simpa [mul_assoc] using this
      have := hW γ hγ h hγK
      simp [this]
  rw [e]
  exact hWo.preimage continuous_subtype_val

theorem fundNC_holds : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupCharacter →
    ∀ u : D.what₂.Word, ∃ FN : Set X.B.I.Ginf, IsSFund X.B.I (NOinf X u) FN := by
  intro D X hK u
  have := NOsub_discrete X u hK
  obtain ⟨Ω, hΩ⟩ := isSFund_of_discrete X.B.I (NOsub X u hK)
  rw [NOsub_coe] at hΩ
  exact ⟨Ω, hΩ⟩

end NO

section RO

open NumberField Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ratLink_one : RatLink X 1 1 := by
  refine ⟨1, (Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J).one_mem, fun v => ?_, ?_, fun y => ?_⟩
  · have : uMat ((1 : X.B.I.GA).1 v) = 1 := by simp [uMat]
    rw [this, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v))]
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [AutInst.fmat]
  · simp

theorem ratLink_mul {x₁ x₂ : X.B.I.GA} {n₁ n₂ : (Formalism.MainNotions.S.VS D).V ≃ₗ[D.host.E] (Formalism.MainNotions.S.VS D).V}
    (h₁ : RatLink X x₁ n₁) (h₂ : RatLink X x₂ n₂) : RatLink X (x₁ * x₂) (n₁ * n₂) := by
  obtain ⟨M₁, hM₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨M₂, hM₂, a₂, b₂, c₂⟩ := h₂
  refine ⟨M₁ * M₂, (Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J).mul_mem hM₁ hM₂, fun v => ?_, ?_, fun y => ?_⟩
  · have e : uMat ((x₁ * x₂).1 v) = uMat (x₁.1 v) * uMat (x₂.1 v) := by simp [uMat]
    have hP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v))
    rw [e, a₁, a₂, Units.val_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (X.B.I.P v) (X.B.I.P v)⁻¹, hP, Matrix.one_mul]
  · have e : X.B.I.fmat (x₁ * x₂).2 = X.B.I.fmat x₁.2 * X.B.I.fmat x₂.2 := by simp [AutInst.fmat]
    rw [e, b₁, b₂, Units.val_mul, Matrix.map_mul]
  · show X.crd (n₁ (n₂ y)) = _
    rw [c₁, c₂, Matrix.mulVec_mulVec, Units.val_mul]

theorem ratLink_inv {x : X.B.I.GA} {n : (Formalism.MainNotions.S.VS D).V ≃ₗ[D.host.E] (Formalism.MainNotions.S.VS D).V}
    (h : RatLink X x n) : RatLink X x⁻¹ n⁻¹ := by
  obtain ⟨M, hM, a, b, c⟩ := h
  have hMM : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)) * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = 1 :=
    Units.mul_inv M
  have hMM' : ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = 1 :=
    Units.inv_mul M
  refine ⟨M⁻¹, (Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J).inv_mem hM, fun v => ?_, ?_, fun y => ?_⟩
  · have e1 : uMat (x⁻¹.1 v) * uMat (x.1 v) = 1 := by simp [uMat]
    have hP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v))
    have hP' : (X.B.I.P v)⁻¹ * X.B.I.P v = 1 :=
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v))
    have e2 : uMat (x.1 v) * ((X.B.I.P v)⁻¹ * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
        X.B.I.P v) = 1 := by
      rw [a v]
      calc (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v * ((X.B.I.P v)⁻¹ *
            ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v)
          = (X.B.I.P v)⁻¹ * ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) *
            ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)) * X.B.I.P v := by
            simp only [Matrix.mul_assoc]
        _ = (X.B.I.P v)⁻¹ * ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)).map
            (X.B.I.φ v) * X.B.I.P v := by rw [hP, Matrix.mul_one, Matrix.map_mul]
        _ = 1 := by rw [hMM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, hP']
    calc uMat (x⁻¹.1 v) = uMat (x⁻¹.1 v) * (uMat (x.1 v) * ((X.B.I.P v)⁻¹ *
          ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v)) := by rw [e2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  · have e1 : X.B.I.fmat x⁻¹.2 * X.B.I.fmat x.2 = 1 := by simp [AutInst.fmat]
    have e2 : X.B.I.fmat x.2 * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
        (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) = 1 := by
      rw [b, ← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)]
    calc X.B.I.fmat x⁻¹.2 = X.B.I.fmat x⁻¹.2 * (X.B.I.fmat x.2 * ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) := by rw [e2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  · have e : X.crd y = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (n⁻¹ y) := by
      rw [← c]; congr 1; exact (n.apply_symm_apply y).symm
    rw [e, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]

variable {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))

def ROsub (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Subgroup X.B.I.Ginf where
  carrier := ROset X F0 F0' Λ Λ' γ
  one_mem' := ⟨1, 1, ratLink_one X, rfl, nlam_one _ _, by
    rw [mul_one, inv_mul_cancel]; exact nlam_one _ _⟩
  mul_mem' := by
    rintro _ _ ⟨x₁, n₁, h₁, rfl, hn₁, hn₁'⟩ ⟨x₂, n₂, h₂, rfl, hn₂, hn₂'⟩
    refine ⟨x₁ * x₂, n₁ * n₂, ratLink_mul X h₁ h₂, rfl, nlam_mul hn₁ hn₂, ?_⟩
    have e : γ⁻¹ * (n₁ * n₂) * γ = (γ⁻¹ * n₁ * γ) * (γ⁻¹ * n₂ * γ) := by group
    rw [e]; exact nlam_mul hn₁' hn₂'
  inv_mem' := by
    rintro _ ⟨x, n, h, rfl, hn, hn'⟩
    refine ⟨x⁻¹, n⁻¹, ratLink_inv X h, rfl, nlam_inv hn, ?_⟩
    have e : γ⁻¹ * n⁻¹ * γ = (γ⁻¹ * n * γ)⁻¹ := by group
    rw [e]; exact nlam_inv hn'

theorem crd_add (v w : (VS D).V) : X.crd (v + w) = X.crd v + X.crd w := by
  funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

theorem crd_smul (a : D.host.E) (v : (VS D).V) : X.crd (a • v) = X.ιE.symm a • X.crd v := by
  funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

theorem crd_zero : X.crd 0 = 0 := by
  funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

theorem crd_surj (x : Fin X.B.I.n → X.B.I.E) : ∃ v, X.crd v = x :=
  ⟨X.bas.repr.symm (Finsupp.equivFunOnFinite.symm fun i => X.ιE (x i)), by
    funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]⟩

theorem crd_lat (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ) :
    ∃ s : Finset (Fin X.B.I.n → X.B.I.E), (∀ l ∈ s, ∃ w ∈ Λ, X.crd w = l) ∧
      Submodule.span X.B.I.E (s : Set (Fin X.B.I.n → X.B.I.E)) = ⊤ ∧
      ∃ c : ℤ, c ≠ 0 ∧ ∀ w ∈ Λ, ∀ i, IsIntegral ℤ ((c : X.B.I.E) * X.crd w i) := by
  classical
  obtain ⟨g, hg⟩ := hΛ.fg
  have hgΛ : ∀ w ∈ g, w ∈ Λ := fun w hw => hg ▸ Submodule.subset_span hw
  refine ⟨g.image X.crd, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hl
    exact ⟨w, hgΛ w hw, rfl⟩
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ := crd_surj X x
    have hv : v ∈ Submodule.span D.host.E (g : Set (VS D).V) := by
      have h1 : v ∈ Submodule.span D.host.E (Λ : Set (VS D).V) := hΛ.span_eq_top ▸ Submodule.mem_top
      refine (Submodule.span_le.2 ?_) h1
      intro w hw
      rw [← hg] at hw
      exact Submodule.span_le_restrictScalars (𝓞 D.host.E) D.host.E _ hw
    induction hv using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span (by simpa using ⟨w, hw, rfl⟩)
    | zero => rw [crd_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [crd_add]; exact add_mem ha hb
    | smul a b _ hb => rw [crd_smul]; exact Submodule.smul_mem _ _ hb
  · choose m hm0 hmI using fun (w : (VS D).V) (i : Fin X.B.I.n) => nt_int_mul_of X.B.I (X.crd w i)
    refine ⟨∏ w ∈ g, ∏ i, m w i, Finset.prod_ne_zero_iff.2 fun w _ => Finset.prod_ne_zero_iff.2 fun i _ => hm0 w i,
      fun w hw => ?_⟩
    rw [← hg] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      intro i
      have e : ((∏ w ∈ g, ∏ i, m w i : ℤ) : X.B.I.E) * X.crd w i =
          (((∏ w' ∈ g.erase w, ∏ i, m w' i) * ∏ j ∈ Finset.univ.erase i, m w j : ℤ) : X.B.I.E) *
            ((m w i : X.B.I.E) * X.crd w i) := by
        rw [← Finset.mul_prod_erase _ _ hw, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        push_cast; ring
      rw [e]
      exact isIntegral_algebraMap.mul (hmI w i)
    | zero => intro i; rw [crd_zero]; simpa using isIntegral_zero
    | add a b _ _ ha hb => intro i; rw [crd_add, Pi.add_apply, mul_add]; exact (ha i).add (hb i)
    | smul o a _ ha =>
      intro i
      have e1 : o • a = ((o : D.host.E)) • a := (algebraMap_smul D.host.E o a).symm
      rw [e1, crd_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      refine IsIntegral.mul ?_ (ha i)
      exact (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm.toRingHom.toIntAlgHom)

theorem ROsub_discrete (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ)
    (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : DiscreteTopology (ROsub X F0 F0' Λ Λ' γ) := by
  obtain ⟨s, hsΛ, hspan, c, hc0, hc⟩ := crd_lat X Λ hΛ
  refine ginf_disc_of_lat X.B.I _ s hspan c hc0 ?_
  rintro _ ⟨x, n, ⟨M, -, h1, -, h3⟩, rfl, hn, -⟩
  refine ⟨M, h1, fun l hl i => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hsΛ l hl
  have hnw : n w ∈ Λ := by
    have : n w ∈ Formalism.HermitianLatticesTheory.gmap n Λ := ⟨w, hw, rfl⟩
    rwa [hn.1.2] at this
  rw [← h3, mul_sub]
  exact (hc _ hnw i).sub (hc _ hw i)

theorem fundExists_of_lat (what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (hL : ∀ Λ ∈ what₂, Submodule.IsLattice D.host.E Λ) : FundExists X u u' F0 F0' what₂ rows' := by
  intro t
  have := ROsub_discrete X F0 F0' t.lam t.lam' (hL _ t.mem) t.lin
  exact isSFund_of_discrete X.B.I (ROsub X F0 F0' t.lam t.lam' t.lin)

theorem fundExistsC_holds : Formalism.L2.SG.Full.FundExistsC := by
  intro D X Y u u'
  exact fundExists_of_lat X (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') fun Λ hΛ => ((Y.rowsOK u).1 Λ hΛ).1.1

end RO

end Formalism.L2.SG.Pf
