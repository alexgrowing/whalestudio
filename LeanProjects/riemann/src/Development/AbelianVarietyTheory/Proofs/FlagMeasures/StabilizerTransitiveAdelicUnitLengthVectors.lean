import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbedding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSplitUnitVectorOrthComplement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDualStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinOrbit

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Pi.star_apply, starRingEnd_apply, Finset.mul_sum, mul_assoc]

theorem form_mulVec {E : Type} [Field E] [StarRing E] {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin n) (Fin m) E) (v w : Fin m → E) :
    star (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w)) = star v ⬝ᵥ ((Aᴴ * J * A) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem exists_perp_basis {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hd : J.det ≠ 0) (x : Fin n → E) (hx : star x ⬝ᵥ (J *ᵥ x) ≠ 0) :
    ∃ (m : ℕ) (A : Matrix (Fin n) (Fin m) E), m + 1 = n ∧ star x ᵥ* (J * A) = 0 ∧ (Aᴴ * J * A).det ≠ 0 := by
  classical

  set r : Fin n → E := star x ᵥ* J with hr
  let φ : (Fin n → E) →ₗ[E] E :=
    { toFun := fun y => r ⬝ᵥ y
      map_add' := fun a c => dotProduct_add r a c
      map_smul' := fun t a => by simp [dotProduct_smul] }
  have hφ : ∀ y, φ y = star x ⬝ᵥ (J *ᵥ y) := fun y => by
    show r ⬝ᵥ y = _
    rw [hr, Matrix.dotProduct_mulVec]
  have hφx : φ x ≠ 0 := by rw [hφ]; exact hx
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    exact ⟨(t / φ x) • x, by rw [LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ hφx]⟩
  have hdim : Module.finrank E (LinearMap.ker φ) + 1 = n := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
    omega
  set W := LinearMap.ker φ
  let b := Module.finBasis E W
  let A : Matrix (Fin n) (Fin (Module.finrank E W)) E := Matrix.of fun i j => (b j : Fin n → E) i
  have hAv : ∀ d, A *ᵥ d = ∑ j, d j • (b j : Fin n → E) := fun d => by
    ext i
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hxA : star x ᵥ* (J * A) = 0 := by
    ext j
    rw [← Matrix.vecMul_vecMul, ← hr]
    have hb : φ (b j) = 0 := (b j).2
    simpa [Matrix.vecMul, dotProduct, A, φ] using hb
  refine ⟨_, A, hdim, hxA, ?_⟩
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hy : φ (A *ᵥ c) = 0 := by
    rw [hφ, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hxA, zero_dotProduct]

  have hperp : ∀ z : Fin n → E, star z ⬝ᵥ (J *ᵥ (A *ᵥ c)) = 0 := by
    intro z
    set t := φ z / φ x
    have hw : z - t • x ∈ W := by
      show φ (z - t • x) = 0
      rw [map_sub, LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ hφx, sub_self]
    have hd : A *ᵥ (fun j => b.repr ⟨_, hw⟩ j) = z - t • x := by
      rw [hAv]
      have h := congrArg (Subtype.val) (b.sum_repr ⟨_, hw⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
    have hz : z = t • x + A *ᵥ (fun j => b.repr ⟨_, hw⟩ j) := by rw [hd]; abel
    rw [hz, star_add, add_dotProduct, star_smul, smul_dotProduct, ← hφ, hy, smul_zero, zero_add,
      form_mulVec, hc, dotProduct_zero]
  have hJ : J *ᵥ (A *ᵥ c) = 0 := by
    ext i
    have h := hperp (Pi.single i 1)
    simpa [dotProduct, Pi.single_apply, apply_ite star] using h
  have hAc : A *ᵥ c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd hJ
  rw [hAv] at hAc
  have hli := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  apply hc0
  ext j
  exact Fintype.linearIndependent_iff.mp hli c (by simpa using hAc) j

variable (I : AutInst) (s : Bool) (x : Fin I.n → I.E) {m : ℕ} (A : Matrix (Fin I.n) (Fin m) I.E)

theorem exists_sib (hm : m + 1 = I.n) (hx : star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s)
    (hxA : star x ᵥ* (I.J * A) = 0) (hd : (Aᴴ * I.J * A).det ≠ 0) (xf : I.Gf) (hxf : x ∈ lamX I (1, xf))
    (L : Submodule (𝓞 I.E) (Fin m → I.E)) (hL : ∀ y, y ∈ L ↔ A *ᵥ y ∈ lamX I (1, xf)) :
    Submodule.span I.E (L : Set (Fin m → I.E)) = ⊤ ∧ L.FG ∧ ∀ w : Fin m → I.E, w ∈ L ↔
      ∀ v ∈ L, Formalism.UG.hform (starRingEnd I.E) (Aᴴ * I.J * A) v w ∈ (algebraMap (𝓞 I.E) I.E).range := by
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  have hs : sgn I.E s ≠ 0 := by cases s <;> simp [sgn]

  have hinj : ∀ v, A *ᵥ v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hd (by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero])
  have hperpA : ∀ v, star x ⬝ᵥ (I.J *ᵥ (A *ᵥ v)) = 0 := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hxA, zero_dotProduct]
  have hpair : ∀ (t : I.E) v, star x ⬝ᵥ (I.J *ᵥ (t • x + A *ᵥ v)) = t * sgn I.E s := fun t v => by
    rw [Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_smul, dotProduct_smul, hx, hperpA, add_zero,
      smul_eq_mul]

  have hsurj : ∀ y : Fin I.n → I.E, ∃ t : I.E, ∃ v : Fin m → I.E, y = t • x + A *ᵥ v := by
    let f : (I.E × (Fin m → I.E)) →ₗ[I.E] (Fin I.n → I.E) :=
      (LinearMap.toSpanSingleton I.E _ x).coprod (Matrix.toLin' A)
    have hf : ∀ p, f p = p.1 • x + A *ᵥ p.2 := fun p => by
      simp [f, LinearMap.coprod_apply, Matrix.toLin'_apply]
    have hfi : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      rw [hf] at hp
      have h1 := congrArg (fun y => star x ⬝ᵥ (I.J *ᵥ y)) hp
      simp only [hpair, Matrix.mulVec_zero, dotProduct_zero, mul_eq_zero, hs, or_false] at h1
      rw [h1, zero_smul, zero_add] at hp
      exact Prod.ext h1 (hinj _ hp)
    have hdim : Module.finrank I.E (I.E × (Fin m → I.E)) = Module.finrank I.E (Fin I.n → I.E) := by
      rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun, Module.finrank_fin_fun]
      omega
    intro y
    obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hfi y
    exact ⟨p.1, p.2, by rw [← hp, hf]⟩

  have hdec : ∀ y ∈ lamX I (1, xf), ∃ a : 𝓞 I.E, ∃ v ∈ L, y = algebraMap (𝓞 I.E) I.E a • x + A *ᵥ v := by
    intro y hy
    obtain ⟨t, v, rfl⟩ := hsurj y
    have hint := (hdual _).1 hy x hxf
    rw [hform_eq, hpair] at hint
    obtain ⟨o, ho⟩ := hint
    have ht : ∃ a : 𝓞 I.E, algebraMap (𝓞 I.E) I.E a = t := by
      cases s
      · refine ⟨-o, ?_⟩
        simp only [sgn, Bool.false_eq_true, if_false, mul_neg, mul_one] at ho
        rw [map_neg, ho, neg_neg]
      · refine ⟨o, ?_⟩
        simpa [sgn] using ho
    obtain ⟨a, rfl⟩ := ht
    refine ⟨a, v, ?_, rfl⟩
    rw [hL]
    have hax : algebraMap (𝓞 I.E) I.E a • x ∈ lamX I (1, xf) := by
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ a hxf
    have h := Submodule.sub_mem _ hy hax
    rwa [add_sub_cancel_left] at h
  have hform_A : ∀ v w, Formalism.UG.hform (starRingEnd I.E) (Aᴴ * I.J * A) v w =
      Formalism.UG.hform (starRingEnd I.E) I.J (A *ᵥ v) (A *ᵥ w) := fun v w => by
    rw [hform_eq, hform_eq, form_mulVec]
  refine ⟨?_, ?_, ?_⟩
  ·
    have key : ∀ y ∈ Submodule.span I.E (lamX I (1, xf) : Set (Fin I.n → I.E)),
        ∃ t : I.E, ∃ v ∈ Submodule.span I.E (L : Set (Fin m → I.E)), y = t • x + A *ᵥ v := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, v, hv, rfl⟩ := hdec y hy
        exact ⟨_, v, Submodule.subset_span hv, rfl⟩
      | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨t1, v1, hv1, rfl⟩ := hy
        obtain ⟨t2, v2, hv2, rfl⟩ := hz
        refine ⟨t1 + t2, v1 + v2, Submodule.add_mem _ hv1 hv2, ?_⟩
        rw [add_smul, Matrix.mulVec_add]
        abel
      | smul c y _ hy =>
        obtain ⟨t, v, hv, rfl⟩ := hy
        refine ⟨c * t, c • v, Submodule.smul_mem _ c hv, ?_⟩
        rw [smul_add, smul_smul, Matrix.mulVec_smul]
    rw [eq_top_iff]
    intro v _
    obtain ⟨t, v', hv', he⟩ := key (A *ᵥ v) (by rw [hspan]; trivial)
    have h1 := congrArg (fun y => star x ⬝ᵥ (I.J *ᵥ y)) he
    simp only [hpair, hperpA] at h1
    have ht : t = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hs
    rw [ht, zero_smul, zero_add] at he
    have hvv : v - v' = 0 := hinj _ (by rw [Matrix.mulVec_sub, he, sub_self])
    rw [sub_eq_zero] at hvv
    rw [hvv]
    exact hv'
  ·
    let f : (Fin m → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) := (Matrix.toLin' A).restrictScalars (𝓞 I.E)
    have hfv : ∀ v, f v = A *ᵥ v := fun v => by simp [f, Matrix.toLin'_apply]
    have hfi : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      rw [hfv] at hv
      exact hinj v hv
    have hle : L.map f ≤ lamX I (1, xf) := by
      rw [Submodule.map_le_iff_le_comap]
      intro v hv
      rw [Submodule.mem_comap, hfv, ← hL]
      exact hv
    haveI := isNoetherian_of_fg_of_noetherian _ hfg
    exact Submodule.fg_of_fg_map_injective f hfi (isNoetherian_submodule.mp inferInstance _ hle)
  ·
    intro w
    constructor
    · intro hw v hv
      rw [hform_A]
      exact (hdual _).1 ((hL w).1 hw) _ ((hL v).1 hv)
    · intro hw
      rw [hL, hdual]
      intro z hz
      obtain ⟨a, v, hv, rfl⟩ := hdec z hz
      rw [hform_eq, star_add, add_dotProduct, star_smul, smul_dotProduct, hperpA, smul_zero, zero_add,
        ← hform_eq, ← hform_A]
      exact hw v hv

def perpSib (hm : m + 1 = I.n) (hx : star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s)
    (hxA : star x ᵥ* (I.J * A) = 0) (hd : (Aᴴ * I.J * A).det ≠ 0) (xf : I.Gf) (hxf : x ∈ lamX I (1, xf)) :
    Sib I :=
  have hH : Formalism.UG.IsHerm (starRingEnd I.E) (Aᴴ * I.J * A) := by
    have hJ : I.Jᴴ = I.J := I.J_herm
    change (Aᴴ * I.J * A)ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
      Matrix.mul_assoc]
  have h := fun v : InfinitePlace I.F =>
    GlobalTheory.AutInhab.exists_frame (GlobalTheory.AutInhab.isHerm_map I.cm hH (I.φ v))
      (GlobalTheory.AutInhab.isUnit_det_map hd (I.φ v))
  have hl := exists_sib I s x A hm hx hxA hd xf hxf
    ((lamX I (1, xf)).comap ((Matrix.toLin' A).restrictScalars (𝓞 I.E))) fun _ => Iff.rfl
  { n := m
    J := Aᴴ * I.J * A
    J_herm := hH
    J_det := hd
    L := (lamX I (1, xf)).comap ((Matrix.toLin' A).restrictScalars (𝓞 I.E))
    L_span := hl.1
    L_fg := hl.2.1
    L_dual := hl.2.2
    ε := fun v => (h v).choose
    P := fun v => (h v).choose_spec.choose
    P_unit := fun v => (h v).choose_spec.choose_spec.1
    P_spec := fun v => (h v).choose_spec.choose_spec.2 }

theorem isPerp_perpSib (hm : m + 1 = I.n) (hx : star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s)
    (hxA : star x ᵥ* (I.J * A) = 0) (hd : (Aᴴ * I.J * A).det ≠ 0) (xf : I.Gf) (hxf : x ∈ lamX I (1, xf)) :
    IsPerp (perpSib I s x A hm hx hxA hd xf hxf) s x A xf :=
  ⟨hm, hx, hxA, rfl, hxf, fun _ => Iff.rfl⟩

theorem lamX_le_of_split (D : Sib I) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hP : IsPerp D s x A xf)
    (jf : D.inst.Gf →* I.Gf) (hj : IsFinEmb D x A jf) (c : D.inst.Gf) (w : Fin D.n → I.E)
    (hw : w ∈ lamX D.inst (1, c)) : x ∈ lamX I (1, jf c * xf) ∧ A *ᵥ w ∈ lamX I (1, jf c * xf) := by
  have hmem := fun (y : Fin I.n → I.E) (g : I.Gf) => (GlobalTheory.PointLattice.lamX_selfDual I (1, g)).1 y

  have hfix : I.fmat (jf c)⁻¹ *ᵥ afVec I x = afVec I x := by
    have h := (hj c⁻¹).1
    rwa [map_inv] at h
  have hact : I.fmat (jf c)⁻¹ * afMat I A = afMat I A * D.inst.fmat c⁻¹ := by
    have h := (hj c⁻¹).2
    rwa [map_inv] at h
  have hsplit : ∀ z, I.fmat (jf c * xf)⁻¹ *ᵥ z = I.fmat xf⁻¹ *ᵥ (I.fmat (jf c)⁻¹ *ᵥ z) := fun z => by
    rw [_root_.mul_inv_rev, Matrix.mulVec_mulVec]
    rfl
  have hx1 : I.fmat xf⁻¹ *ᵥ afVec I x ∈ I.Lf := (hmem x xf).1 hP.2.2.2.2.1
  constructor
  · rw [hmem]
    show I.fmat (jf c * xf)⁻¹ *ᵥ afVec I x ∈ I.Lf
    rw [hsplit, hfix]
    exact hx1
  · rw [hmem]
    show I.fmat (jf c * xf)⁻¹ *ᵥ afVec I (A *ᵥ w) ∈ I.Lf
    have hw' : D.inst.fmat c⁻¹ *ᵥ afVec D.inst w ∈ D.inst.Lf :=
      ((GlobalTheory.PointLattice.lamX_selfDual D.inst (1, c)).1 w).1 hw
    rw [hsplit]
    apply (adelicLattice_split I D s x A xf hP _).2
    refine ⟨0, (IntAf I.F I.E).zero_mem, D.inst.fmat c⁻¹ *ᵥ afVec D.inst w, hw', ?_⟩
    rw [zero_smul, zero_add, afVec_mulVec_eq_afMat_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hact]
    rfl

theorem inv_mul_mem_of_le (a b : I.Gf) (hle : lamX I (1, b) ≤ lamX I (1, a)) : a⁻¹ * b ∈ I.Kset := by

  have hA := (GlobalTheory.PointLattice.lamX_selfDual I (1, a)).2.2.2.1
  have hB := (GlobalTheory.PointLattice.lamX_selfDual I (1, b)).2.2.2.1
  have h1 : ((1, a) * (1, a⁻¹ * b) : I.GA) = (1, b) := by
    rw [Prod.mk_mul_mk, one_mul, mul_inv_cancel_left]
  have heq : lamX I ((1, a) * (1, a⁻¹ * b)) = lamX I (1, a) := by
    rw [h1]
    apply le_antisymm hle
    intro y hy
    rw [hB]
    intro z hz
    exact (hA y).1 hy z (hle hz)
  exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff (I := I) (x := (1, a)) (k := (1, a⁻¹ * b))).2 heq

theorem exists_of_split (D : Sib I) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hP : IsPerp D s x A xf)
    (Λ : Submodule (𝓞 I.E) (Fin D.n → I.E)) (hfg : Λ.FG)
    (hsp : Submodule.span I.E (Λ : Set (Fin D.n → I.E)) = ⊤)
    (hdual : ∀ w, w ∈ Λ ↔ ∀ v ∈ Λ, Formalism.UG.hform (starRingEnd I.E) D.J v w ∈ (algebraMap (𝓞 I.E) I.E).range)
    (g : I.Gf) (hg : ∀ y ∈ lamX I (1, g), ∃ a : 𝓞 I.E, ∃ w ∈ Λ, y = a • x + A *ᵥ w) :
    ∃ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x ∧ ∃ k ∈ I.Kset, g = h * xf * k := by

  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual D.inst Λ ⟨hfg, hsp⟩ hdual
  obtain ⟨jf, hj, -⟩ := exists_finEmb I D s x A xf hP

  have hle : lamX I (1, g) ≤ lamX I (1, jf c * xf) := by
    intro y hy
    obtain ⟨a, w, hw, rfl⟩ := hg y hy
    have hw' : w ∈ lamX D.inst (1, c) := by rw [hc]; exact hw
    obtain ⟨h1, h2⟩ := lamX_le_of_split I s x D A xf hP jf hj c w hw'
    exact Submodule.add_mem _ (Submodule.smul_mem _ a h1) h2
  exact ⟨jf c, (hj c).1, _, inv_mul_mem_of_le I (jf c * xf) g hle, (mul_inv_cancel_left _ _).symm⟩

theorem exists_stab_mul_level : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E) (xf g : I.Gf), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → x ∈ lamX I (1, xf) → x ∈ lamX I (1, g) → ∃ h : I.Gf, (I.fmat h *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) ∧ ∃ k ∈ I.Kset, g = h * xf * k := by
  intro I s x xf g hx hxf hxg
  have hs : sgn I.E s ≠ 0 := by cases s <;> simp [sgn]
  have hx0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by rw [hx]; exact hs
  obtain ⟨m, A, hm, hxA, hd⟩ := exists_perp_basis I.J I.J_det x hx0
  have hP := isPerp_perpSib I s x A hm hx hxA hd xf hxf
  have hPg := isPerp_perpSib I s x A hm hx hxA hd g hxg
  have hl := exists_sib I s x A hm hx hxA hd g hxg
    ((lamX I (1, g)).comap ((Matrix.toLin' A).restrictScalars (𝓞 I.E))) fun _ => Iff.rfl
  exact exists_of_split I s x (perpSib I s x A hm hx hxA hd xf hxf) A xf hP
    ((lamX I (1, g)).comap ((Matrix.toLin' A).restrictScalars (𝓞 I.E))) hl.2.1 hl.1 hl.2.2 g
    fun y hy => hPg.exists_split hy

end GlobalTheory.FinOrbit
