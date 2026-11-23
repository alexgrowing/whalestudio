import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap

noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.AdelicOrthFrame

section CM

open GlobalTheory.SelfDualGenus ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

local notation "𝔽" => maximalRealSubfield E
local notation "𝔸" => E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E)
local notation "𝕆" => Formalism.L2.Herm.intAf (maximalRealSubfield E) E

def ev (v : HeightOneSpectrum (𝓞 𝔽)) : 𝔸 →+* LocAlg v :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV 𝔽 v) (AlgHom.id 𝔽 E)).toRingHom.comp
    (Algebra.TensorProduct.comm 𝔽 E (Formalism.L2.Herm.Af 𝔽)).toAlgHom.toRingHom

omit [IsCMField E] in
theorem ev_tmul (v : HeightOneSpectrum (𝓞 𝔽)) (x : E) (a : Formalism.L2.Herm.Af 𝔽) :
    ev v (x ⊗ₜ a) = (a v) ⊗ₜ x := rfl

omit [IsCMField E] in
theorem ev_ext {z z' : 𝔸} (h : ∀ v, ev v z = ev v z') : z = z' :=
  (Algebra.TensorProduct.comm 𝔽 E (Formalism.L2.Herm.Af 𝔽)).injective
    (GlobalTheory.LatticeLocalGlobal.ext_components _ _ h)

omit [IsCMField E] in
theorem ev_inclE (v : HeightOneSpectrum (𝓞 𝔽)) (x : E) :
    ev v (Formalism.UG.inclE (F := 𝔽) (Formalism.L2.Herm.Af 𝔽) x) = locEmb v x := rfl

theorem ev_sigR (hc : CMData 𝔽 E) (v : HeightOneSpectrum (𝓞 𝔽)) (z : 𝔸) :
    ev v (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af 𝔽) z) = locConj v (ev v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x a => rfl

theorem ev_mem (v : HeightOneSpectrum (𝓞 𝔽)) {z : 𝔸} (hz : z ∈ 𝕆) : ev v z ∈ locOrder v := by
  have : 𝕆 ≤ (locOrder v).toSubring.comap (ev v) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact locEmb_mem_locOrder v a
    · exact (locOrder v).algebraMap_mem ⟨a.1 v, a.2 v⟩
  exact this hz

omit [IsCMField E] in
theorem tmul_mem (x : 𝓞 E) (a : Formalism.L2.Herm.Af 𝔽) (ha : a ∈ Formalism.UG.intAd 𝔽) : ((x : E) ⊗ₜ a : 𝔸) ∈ 𝕆 := by
  have e : ((x : E) ⊗ₜ a : 𝔸) = ((x : E) ⊗ₜ 1) * (1 ⊗ₜ a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨x, x, rfl⟩, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))

theorem exists_coeff {k : ℕ} (x : Fin k → 𝓞 E) (hx : Submodule.span ℤ (Set.range x) = ⊤)
    (v : HeightOneSpectrum (𝓞 𝔽)) {z : LocAlg v} (hz : z ∈ locOrder v) :
    ∃ a : Fin k → v.adicCompletionIntegers 𝔽, z = ∑ j, ((a j : v.adicCompletion 𝔽) ⊗ₜ (x j : E) : LocAlg v) := by
  let M : Submodule (v.adicCompletionIntegers 𝔽) (LocAlg v) :=
    Submodule.span _ (Set.range fun j => locEmb v (x j : E))
  have h1 : ∀ y : 𝓞 E, locEmb v (y : E) ∈ M := by
    intro y
    have : y ∈ Submodule.span ℤ (Set.range x) := hx ▸ Submodule.mem_top
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
    have e : ((∑ j, n j • x j : 𝓞 E) : E) = ∑ j, n j • (x j : E) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
      exact Finset.sum_congr rfl fun j _ => map_zsmul _ _ _
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun j => locEmb v (x j : E)) j)) _
  have h2 : ∀ w ∈ M, z * w ∈ M := by
    induction hz using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨y, rfl⟩ := hy
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨j, rfl⟩ := hw
        have := h1 (y * x j)
        rwa [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul] at this
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
    | algebraMap r => intro w hw; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ r hw
    | add a b _ _ ha hb => intro w hw; rw [add_mul]; exact add_mem (ha w hw) (hb w hw)
    | mul a b _ _ ha hb => intro w hw; rw [mul_assoc]; exact ha _ (hb w hw)
  have h3 : z ∈ M := by
    have := h2 _ (h1 1)
    rwa [RingOfIntegers.coe_eq_algebraMap, map_one, map_one, mul_one] at this
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h3
  refine ⟨a, ha.symm.trans (Finset.sum_congr rfl fun j _ => ?_)⟩
  rw [locEmb_apply, TensorProduct.smul_tmul']
  congr 1
  exact mul_one _

theorem exists_of_components (z : ∀ v : HeightOneSpectrum (𝓞 𝔽), LocAlg v) (hz : ∀ v, z v ∈ locOrder v) :
    ∃ Z : 𝕆, ∀ v, ev v Z = z v := by
  obtain ⟨k, x, hx⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  choose a ha using fun v => exists_coeff x hx v (hz v)
  let A : Fin k → Formalism.L2.Herm.Af 𝔽 := fun j =>
    ⟨fun v => a v j, Filter.Eventually.of_forall fun v => (a v j).2⟩
  refine ⟨⟨∑ j, (x j : E) ⊗ₜ A j, Subring.sum_mem _ fun j _ => tmul_mem _ _ fun v => (a v j).2⟩, fun v => ?_⟩
  rw [ha v]
  exact map_sum (ev v) (fun j => (x j : E) ⊗ₜ A j) Finset.univ

variable {n : ℕ}

theorem ev_mem_locLattice (v : HeightOneSpectrum (𝓞 𝔽)) {Λ : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → 𝔸}
    (hx : x ∈ Formalism.L2.Herm.hatL (F := 𝔽) Λ) : (fun i => ev v (x i)) ∈ locLattice v Λ := by
  refine Submodule.span_induction (p := fun x _ => (fun i => ev v (x i)) ∈ locLattice v Λ) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  · simp only [Pi.zero_apply, map_zero]
    exact zero_mem _
  · intro a b _ _ ha hb
    simp only [Pi.add_apply, map_add]
    exact add_mem ha hb
  · intro c a _ ha
    have := smul_mem_locLattice v (ev_mem v c.2) ha
    convert this using 1
    funext i
    exact map_mul (ev v) _ _

theorem frame_loc (v : HeightOneSpectrum (𝓞 𝔽)) {Λ : Submodule (𝓞 E) (Fin n → E)} {β : GL (Fin n) 𝔸}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {x : Fin n → LocAlg v} (hx : x ∈ locLattice v Λ) (i : Fin n) :
    ((β⁻¹).1.map (ev v) *ᵥ x) i ∈ locOrder v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have := ev_mem v ((hβ _).1 (Submodule.subset_span ⟨y, hy, rfl⟩) i)
    rwa [RingHom.map_mulVec] at this
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Subalgebra.smul_mem _ hx c

theorem one_entry_mem {R : Type} [CommRing R] {σ : Type} [SetLike σ R] [SubringClass σ R] (S : σ) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) R) i j ∈ S := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem exists_orth (hc : CMData 𝔽 E) {G : Matrix (Fin n) (Fin n) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ)
    (hsd : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm Gᵀ x y)) {β : GL (Fin n) 𝔸} (hβ : Formalism.L2.DIV.IsFrame β Λ) :
    ∃ u : GL (Fin n) 𝕆, Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af 𝔽)) (β * Formalism.L2.DIV.intGL 𝔽 E n u).val *
      G.map (Formalism.UG.inclE (F := 𝔽) (Formalism.L2.Herm.Af 𝔽)) * (β * Formalism.L2.DIV.intGL 𝔽 E n u).val = 1 := by
  have := GlobalTheory.PlaceComp.unramified hc
  choose h h1 h2 using exists_orthonormal_frame (G := Gᵀ) (fun a b => hG b a) (by rwa [Matrix.det_transpose]) hL hsd
  have ha : ∀ i j v, ((β⁻¹).1.map (ev v) * (h v).1) i j ∈ locOrder v := fun i j v =>
    frame_loc v hβ (x := fun k => (h v).1 k j) ((h2 v _).2 fun k => by
      have := one_entry_mem (locOrder v) k j
      rwa [← Units.inv_mul (h v)] at this) i
  have hb : ∀ i j v, (((h v)⁻¹).1 * β.1.map (ev v)) i j ∈ locOrder v := fun i j v =>
    (h2 v _).1 (ev_mem_locLattice v (x := fun k => β.1 k j) ((hβ _).2 fun k => by
      have := one_entry_mem 𝕆 k j
      rwa [← Units.inv_mul β] at this)) i
  choose A hA using fun i j => exists_of_components _ (ha i j)
  choose B hB using fun i j => exists_of_components _ (hb i j)
  have ext : ∀ M M' : Matrix (Fin n) (Fin n) 𝔸, (∀ v, M.map (ev v) = M'.map (ev v)) → M = M' := fun M M' H =>
    Matrix.ext fun i j => ev_ext fun v => congrFun (congrFun (H v) i) j
  let A' : Matrix (Fin n) (Fin n) 𝕆 := A
  let B' : Matrix (Fin n) (Fin n) 𝕆 := B
  have eA : ∀ v, (A'.map (Subring.subtype 𝕆)).map (ev v) = (β⁻¹).1.map (ev v) * (h v).1 :=
    fun v => Matrix.ext fun i j => hA i j v
  have eB : ∀ v, (B'.map (Subring.subtype 𝕆)).map (ev v) = ((h v)⁻¹).1 * β.1.map (ev v) :=
    fun v => Matrix.ext fun i j => hB i j v
  have o : ∀ v, (1 : Matrix (Fin n) (Fin n) 𝔸).map (ev v) = 1 := fun v => Matrix.map_one _ (map_zero _) (map_one _)
  have p1 : A' * B' = 1 := by
    apply Matrix.map_injective (f := Subring.subtype 𝕆) Subtype.val_injective
    change (A' * B').map _ = Matrix.map 1 _
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ext _ _ fun v => ?_
    rw [Matrix.map_mul, eA, eB, Matrix.mul_assoc, ← Matrix.mul_assoc (h v).1, Units.mul_inv, Matrix.one_mul,
      ← Matrix.map_mul, Units.inv_mul]
  refine ⟨⟨A', B', p1, mul_eq_one_comm.1 p1⟩, ext _ _ fun v => ?_⟩
  have e : (β * Formalism.L2.DIV.intGL 𝔽 E n ⟨A', B', p1, mul_eq_one_comm.1 p1⟩).val.map (ev v) = (h v).1 := by
    change (β.1 * A'.map (Subring.subtype 𝕆)).map (ev v) = _
    rw [Matrix.map_mul, eA, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv, o, Matrix.one_mul]
  have e2 : ∀ M : Matrix (Fin n) (Fin n) 𝔸, (Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af 𝔽)) M).map (ev v) =
      ((M.map (ev v)).map (locConj v))ᵀ := fun M => Matrix.ext fun i j => ev_sigR hc v _
  have h3 := congrArg Matrix.transpose (h1 v)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  rw [Matrix.map_mul, Matrix.map_mul, e2, e, o]
  exact h3

theorem isLattice_of_commensurable (V : HSpace E) {Λ : Submodule (𝓞 E) (Fin V.rank → E)} {N : ℕ} (hN : 0 < N)
    (h1 : ∀ x : Fin V.rank → E, ∑ i, x i • V.frame i ∈ V.L0 → (N : E) • x ∈ Λ)
    (h2 : ∀ x ∈ Λ, ∑ i, ((N : E) • x) i • V.frame i ∈ V.L0) : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ := by
  obtain ⟨hfg, hsp⟩ := GlobalTheory.LocalConjugacy.isLattice_coordLat V V.L0 V.standardTuple_isLattice
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have mem : ∀ x : Fin V.rank → E, x ∈ GlobalTheory.LocalConjugacy.coordLat V V.L0 ↔ ∑ i, x i • V.frame i ∈ V.L0 := by
    intro x
    rw [← Module.Basis.equivFun_symm_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : V.frame.equivFun.symm (V.frame.equivFun y) = y := V.frame.equivFun.symm_apply_apply y
      exact this.symm ▸ hy
    · exact fun hx => ⟨_, hx, V.frame.equivFun.apply_symm_apply x⟩
  constructor
  · let f : (Fin V.rank → E) →ₗ[𝓞 E] (Fin V.rank → E) :=
      (((N : E)⁻¹ • LinearMap.id : (Fin V.rank → E) →ₗ[E] (Fin V.rank → E))).restrictScalars (𝓞 E)
    refine (hfg.map f).of_le fun x hx => ⟨_, (mem _).2 (h2 x hx), ?_⟩
    change (N : E)⁻¹ • (N : E) • x = x
    rw [smul_smul, inv_mul_cancel₀ hN', one_smul]
  · rw [eq_top_iff, ← hsp]
    refine Submodule.span_le.2 fun x hx => ?_
    have := Submodule.smul_mem (Submodule.span E (Λ : Set (Fin V.rank → E))) (N : E)⁻¹
      (Submodule.subset_span (h1 x ((mem x).1 hx)))
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at this

theorem selfDual_iff (hc : CMData 𝔽 E) (V : HSpace E) {Λ : Submodule (𝓞 E) (Fin V.rank → E)}
    (h : Formalism.L2.Herm.dualL hc V Λ = Λ) (x : Fin V.rank → E) :
    x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm V.gramᵀ x y) := by
  have e : ∀ x y, herm V.gramᵀ x y = Formalism.UG.hform (hc.sig : E →+* E) V.gram y x := by
    intro x y
    rw [herm, Formalism.UG.hform, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change x j * V.gram i j * star (y i) = star (y i) * V.gram i j * x j
    ring
  constructor
  · intro hx y hy
    rw [← h] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha⟩ := hx y hy
      rw [e, ← ha]
      exact a.2
    | zero => simpa [herm] using isIntegral_zero
    | add a b _ _ ha hb =>
      have : herm V.gramᵀ (a + b) y = herm V.gramᵀ a y + herm V.gramᵀ b y := by
        simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [this]; exact ha.add hb
    | smul c a _ ha =>
      have : herm V.gramᵀ (c • a) y = (c : E) * herm V.gramᵀ a y := by
        simp only [herm, Pi.smul_apply, Finset.mul_sum, Algebra.smul_def, mul_assoc]
      rw [this]; exact IsIntegral.mul c.2 ha
  · intro H
    rw [← h]
    exact Submodule.subset_span fun y hy => ⟨⟨_, H y hy⟩, e x y⟩

theorem exists_orth_space (hc : CMData 𝔽 E) (V : HSpace E) {β : GL (Fin V.rank) 𝔸}
    {Λ : Submodule (𝓞 E) (Fin V.rank → E)} {N : ℕ} (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (h : Formalism.L2.Herm.dualL hc V Λ = Λ) (hN : 0 < N)
    (h1 : ∀ x : Fin V.rank → E, ∑ i, x i • V.frame i ∈ V.L0 → (N : E) • x ∈ Λ)
    (h2 : ∀ x ∈ Λ, ∑ i, ((N : E) • x) i • V.frame i ∈ V.L0) :
    ∃ u : GL (Fin V.rank) 𝕆, Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af 𝔽))
      (β * Formalism.L2.DIV.intGL 𝔽 E V.rank u).val * V.gram.map (Formalism.UG.inclE (F := 𝔽) (Formalism.L2.Herm.Af 𝔽)) *
      (β * Formalism.L2.DIV.intGL 𝔽 E V.rank u).val = 1 :=
  exists_orth hc (fun a b => V.herm.eq (V.frame a) (V.frame b)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
    (isLattice_of_commensurable V hN h1 h2) (selfDual_iff hc V h) hβ

end CM

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

theorem exists_orthonormal_baseFrame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ u : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (β * intGL D.host.F D.host.E V.rank u).val * V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (β * intGL D.host.F D.host.E V.rank u).val = 1 :=
  fun {D} V _ _ _ h =>
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    exists_orth_space (E := D.host.E) D.sp.cm V h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

end GlobalTheory.AdelicOrthFrame

end
