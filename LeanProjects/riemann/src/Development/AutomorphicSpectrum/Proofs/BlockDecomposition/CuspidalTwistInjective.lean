import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg Matrix

namespace GlobalTheory.CompanionTheory.SegNu

theorem exists_ne_zero_of_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra h
  push_neg at h
  haveI := hi
  refine (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective ?_)
  show (⊥ : Submodule ℂ V) = ⊤
  ext v
  simp [h v]

theorem eq_smul_of_eigenvector {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) {z : G} (hz : ∀ g, z * g = g * z) {c : ℂ} {w : V}
    (hw : w ≠ 0) (hc : π z w = c • w) (v : V) : π z v = c • v := by
  haveI := hi
  let E : Subrepresentation π :=
    { toSubmodule := LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      apply_mem_toSubmodule := fun g v hv => by
        have hv' : π z v = c • v := by
          simpa [sub_eq_zero] using hv
        have h1 : π z (π g v) = π g (π z v) := by
          rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
        simp [sub_eq_zero, h1, hv'] }
  have hE : E ≠ ⊥ := fun h => hw (by
    have h1 : w ∈ E.toSubmodule := by
      show w ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      simp [sub_eq_zero, hc]
    rw [h] at h1
    exact (Submodule.mem_bot ℂ).1 h1)
  have hT : E = ⊤ := (eq_bot_or_eq_top E).resolve_left hE
  have h2 : v ∈ E.toSubmodule := by
    rw [hT]
    exact Submodule.mem_top
  have h3 : v ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V)) := h2
  simpa [sub_eq_zero] using h3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_scalar {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
    (ha : IsAdmissible π) (hi : π.IsIrreducible) {z : GL (Fin n) k} (hz : ∀ g, z * g = g * z) :
    ∃ ω : ℂ, ∀ v, π z v = ω • v := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr hi
  let S : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show π 1 v = v
        simp
      inv_mem' := fun {a} ha => by
        have ha' : π a v = v := ha
        show π a⁻¹ v = v
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSo : IsOpen (S : Set (GL (Fin n) k)) := ha.1 v
  let K : Subgroup (GL (Fin n) k) := S ⊓ KO k (Fin n)
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact (K : Set (GL (Fin n) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) Set.inter_subset_right
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hKo hKc
  have hvK : v ∈ fixed π K := fun h => by
    have h' : π (h : GL (Fin n) k) v = v := h.2.1
    simpa using h'
  haveI : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun e => hv (congrArg Subtype.val e)⟩⟩
  have hst : ∀ u ∈ fixed π K, π z u ∈ fixed π K := fun u hu h => by
    have hu' := hu h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hu' ⊢
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply, hu']
  let T : Module.End ℂ (fixed π K) := (π z).restrict hst
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have h1 : π z (w : V) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have h2 : (w : V) ≠ 0 := fun e => hw.2 (Subtype.ext e)
  exact ⟨c, eq_smul_of_eigenvector hi hz h2 h1⟩

theorem eq_zero_of_nu_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (hd : 0 < x.1) {s : ℝ}
    (hs : x.nu (s : ℂ) = x) : s = 0 := by
  have h1 := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr (absPow k (s : ℂ)) (isSmoothChar_absPow _)
  rw [IrrGL.of_rep] at h1
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 (h1.symm.trans (hs.trans (IrrGL.of_rep x).symm))
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  let z : GL (Fin x.1) k := GeneralLinearGroup.scalar (Fin x.1) ϖ
  have hz : ∀ g, z * g = g * z := fun g => by
    ext i j
    simp [z, GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hdet : GeneralLinearGroup.det z = ϖ ^ x.1 := by
    ext
    simp [z, GeneralLinearGroup.scalar]
  obtain ⟨ω, hω⟩ := exists_scalar (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr hz
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr x.2.rep.irr
  have hω0 : ω ≠ 0 := fun e => hv (by
    have h2 : x.rep z⁻¹ (x.rep z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hω, e, zero_smul, map_zero] at h2
    exact h2.symm)
  have h3 := LinearMap.congr_fun (φ.isIntertwining' z) v
  have hLv : φ.toLinearEquiv v ≠ 0 := fun e => hv (φ.toLinearEquiv.map_eq_zero_iff.1 e)
  have h4 : φ.toLinearEquiv (((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) • x.rep z v) = x.rep z (φ.toLinearEquiv v) := by
    have h5 : φ.toLinearEquiv ((twist x.rep (detChar _ (absPow k (s : ℂ)))) z v) = x.rep z (φ.toLinearEquiv v) := h3
    rwa [twist_apply, detChar_apply, hdet] at h5
  rw [hω, hω, map_smul, map_smul, smul_smul] at h4
  have h6 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) * ω = ω := smul_left_injective ℂ hLv h4
  have h7 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) = 1 := mul_right_cancel₀ hω0 (h6.trans (one_mul ω).symm)
  have h8 : ((absPow k (s : ℂ) ϖ : ℂˣ) : ℂ) ^ x.1 = 1 := by
    rw [← h7, map_pow, Units.val_pow_eq_pow_val]
  rw [val_absPow_ofReal] at h8
  have h9 : (nabs k ϖ ^ s) ^ x.1 = 1 := by exact_mod_cast h8
  have hpos : 0 < nabs k ϖ := nabs_pos' k ϖ
  have h10 : nabs k ϖ ^ s = 1 := (pow_eq_one_iff_of_nonneg (Real.rpow_nonneg hpos.le s) hd.ne').1 h9
  have hne : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have h11 := congrArg Real.log h10
  rw [Real.log_rpow hpos, Real.log_one] at h11
  exact (mul_eq_zero.1 h11).resolve_right (Real.log_ne_zero_of_pos_of_ne_one hpos hne)

theorem nu_natCast_inj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (hx : x.IsCusp) (a b : ℕ)
    (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  intro k _ _ _ _ hA x hx a b h
  have h1 : x.nu (((a : ℝ) - (b : ℝ) : ℝ) : ℂ) = x := by
    have h2 := congrArg (fun y => IrrGL.nu y (-(b : ℂ))) h
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
    rw [← h2]
    congr 1
    push_cast
    ring
  have h3 := eq_zero_of_nu_eq hA x hx.1 h1
  exact_mod_cast sub_eq_zero.1 h3

end GlobalTheory.CompanionTheory.SegNu
