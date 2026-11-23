import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjParahoric

open Filter Topology

section blocks
open ValuativeRel Matrix GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem inv_blocks {r t : ℕ} (h : GL (Fin (r + t)) k) (hK : h ∈ KO k (Fin (r + t)))
    (hlow : ∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) :
    (∀ (i : Fin t) (j : Fin r), valuation k ((h⁻¹).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) ∧
    valuation k ((h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      ((h⁻¹).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
  obtain ⟨u, rfl⟩ := hK
  set f := IsLocalRing.residue 𝒪[k]
  set Hb := (f.mapMatrix u.val).submatrix finSumFinEquiv finSumFinEquiv with hHb
  set Gb := (f.mapMatrix (u⁻¹).val).submatrix finSumFinEquiv finSumFinEquiv with hGb
  have hz : Hb.toBlocks₂₁ = 0 := by
    ext i j'
    exact (residue_eq_zero_iff_val _).2 (hlow i j')
  have hHG : Hb * Gb = 1 := by
    rw [hHb, hGb, submatrix_mul_equiv, ← map_mul, Units.mul_inv, map_one, submatrix_one_equiv]
  have hb := hHG
  rw [← fromBlocks_toBlocks Hb, ← fromBlocks_toBlocks Gb, fromBlocks_multiply, hz, ← fromBlocks_one,
    fromBlocks_inj] at hb
  obtain ⟨-, -, h21, h22⟩ := hb
  simp only [Matrix.zero_mul, zero_add] at h21 h22
  have h22' : Gb.toBlocks₂₂ * Hb.toBlocks₂₂ = 1 := mul_eq_one_comm.1 h22
  have hG : Gb.toBlocks₂₁ = 0 := by
    rw [← Matrix.one_mul Gb.toBlocks₂₁, ← h22', Matrix.mul_assoc, h21, Matrix.mul_zero]
  rw [← map_inv]
  refine ⟨fun i j => (residue_eq_zero_iff_val ((u⁻¹).val _ _)).1 (congrFun (congrFun hG i) j), ?_⟩
  have e : ((GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      ((GeneralLinearGroup.map (algebraMap 𝒪[k] k) u⁻¹).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 =
      algebraMap 𝒪[k] k ((u.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
        ((u⁻¹).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) := by
    rw [map_sub, map_mul, map_one, RingHom.map_det, RingHom.map_det]; rfl
  rw [e]
  refine (residue_eq_zero_iff_val (k := k) _).1 ?_
  rw [map_sub, map_mul, map_one, RingHom.map_det, RingHom.map_det, ← det_mul, sub_eq_zero]
  exact (congrArg det h22).trans det_one

theorem exists_conj (r t : ℕ) : ∃ m : GL (Fin (r + t)) k, ∀ h : GL (Fin (r + t)) k,
    (∀ a b, valuation k (h.val a b) ≤ 1) →
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    (∀ a b, valuation k ((m * h * m⁻¹).val a b) ≤ 1) ∧
    (∀ a b : Fin (r + t), a.val < r → valuation k ((m * h * m⁻¹).val a b) < 1 ∨ b.val < r) ∧
    ∀ i j : Fin t, (m * h * m⁻¹).val (Fin.natAdd r i) (Fin.natAdd r j) = h.val (Fin.natAdd r i) (Fin.natAdd r j) := by
  obtain ⟨γ, hγ1, hγ⟩ := IsDiscrete.has_maximal_element (R := k)
  obtain ⟨ϖ, rfl⟩ := valuation_surjective γ
  have h0 : valuation k ϖ ≠ 0 := by
    obtain ⟨δ, h0, h1⟩ := IsNontrivial.exists_lt_one (R := k)
    exact (h0.trans_le (hγ δ h1)).ne'
  have h0' : ϖ ≠ 0 := by simpa using h0
  let e : Fin (r + t) → k := fun a => if a.val < r then ϖ else 1
  have he : ∀ a, e a ≠ 0 := fun a => by
    simp only [e]; split_ifs <;> simp [h0']
  let m : GL (Fin (r + t)) k := ⟨diagonal e, diagonal fun a => (e a)⁻¹,
    by rw [diagonal_mul_diagonal]; simp [he], by rw [diagonal_mul_diagonal]; simp [he]⟩
  refine ⟨m, fun h h1 h2 => ?_⟩
  have key : ∀ a b, (m * h * m⁻¹).val a b = e a * h.val a b * (e b)⁻¹ := fun a b => by
    change (diagonal e * h.val * diagonal fun a => (e a)⁻¹) a b = _
    rw [mul_diagonal, diagonal_mul]
  have hlt : ∀ a b : Fin (r + t), a.val < r → ¬ b.val < r → valuation k ((m * h * m⁻¹).val a b) < 1 := by
    intro a b ha hb
    rw [key]
    simp only [e, ha, hb, if_true, if_false, inv_one, mul_one, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (h1 a b)) hγ1
  refine ⟨fun a b => ?_, fun a b ha => ?_, fun i j => ?_⟩
  · by_cases ha : a.val < r <;> by_cases hb : b.val < r
    · rw [key]
      simp only [e, ha, hb, if_true]
      rw [mul_right_comm, mul_inv_cancel₀ h0', one_mul]
      exact h1 a b
    · exact (hlt a b ha hb).le
    · rw [key]
      simp only [e, ha, hb, if_true, if_false, one_mul, map_mul, map_inv₀]
      rw [mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul]
      have := h2 ⟨a.val - r, by omega⟩ ⟨b.val, hb⟩
      have ea : Fin.natAdd r (⟨a.val - r, by omega⟩ : Fin t) = a := by ext; simp; omega
      rw [ea] at this
      exact hγ _ this
    · rw [key]
      simp only [e, ha, hb, if_false, one_mul, inv_one, mul_one]
      exact h1 a b
  · by_cases hb : b.val < r
    · exact Or.inr hb
    · exact Or.inl (hlt a b ha hb)
  · rw [key]
    simp [e]

end blocks

section val

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  {p : HeightOneSpectrum (𝓞 F)} {q : HeightOneSpectrum (𝓞 E)}

theorem val_lt_one_map (f : p.adicCompletion F →+* q.adicCompletion E) (hf : Continuous f) {x : p.adicCompletion F}
    (hx : Valued.v x < 1) : Valued.v (f x) < 1 := by
  rw [← Valued.toNormedField.norm_lt_one_iff, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one] at hx ⊢
  have h := (hf.tendsto 0).comp hx
  rw [map_zero] at h
  simpa [Function.comp_def, map_pow] using h

theorem isEquiv_of_continuous (c : p.adicCompletion F ≃+* q.adicCompletion E) (hc : Continuous c) :
    ((Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).comap c.symm.toRingHom).IsEquiv
      (ValuativeRel.valuation (q.adicCompletion E)) := by
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F p
  have ho : IsOpenMap c := AddMonoidHom.isOpenMap_of_sigmaCompact c.toAddEquiv.toAddMonoidHom c.surjective hc
  have hc' : Continuous c.symm := c.toEquiv.continuous_symm_iff.2 ho
  haveI : (Valued.v : Valuation (q.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine Valuation.IsEquiv.trans ?_ (ValuativeRel.isEquiv
    (Valued.v : Valuation (q.adicCompletion E) (WithZero (Multiplicative ℤ))) _)
  rw [Valuation.isEquiv_iff_val_lt_one]
  intro x
  refine ⟨fun h => ?_, fun h => val_lt_one_map c.symm.toRingHom hc' h⟩
  simpa using val_lt_one_map c.toRingHom hc h

theorem exists_global (N : ℕ) (d : (p.adicCompletion F)ˣ) : ∃ y : F, y ≠ 0 ∧
    Valued.v (algebraMap F (p.adicCompletion F) y * ((d⁻¹ : (p.adicCompletion F)ˣ) : p.adicCompletion F) - 1) <
      WithZero.exp (-(N : ℤ)) := by
  obtain ⟨z, hz⟩ := p.valuedAdicCompletion_surjective F (WithZero.exp (-(N : ℤ)))
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hz.symm.trans (map_zero _))
  have hU : IsOpen {y : p.adicCompletion F | Valued.v (y * ((d⁻¹ : (p.adicCompletion F)ˣ) : p.adicCompletion F) - 1) <
      Valued.v z} := by
    have h1 := (Valued.isOpen_ball (p.adicCompletion F) (Valued.v.restrict z)).preimage
      ((continuous_mul_const ((d⁻¹ : (p.adicCompletion F)ˣ) : p.adicCompletion F)).sub (continuous_const (y := 1)))
    simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
  obtain ⟨y, hy'⟩ := (p.denseRange_algebraMap F).exists_mem_open hU ⟨d, by
    simpa [zero_lt_iff] using hz0⟩
  rw [Set.mem_setOf_eq, hz] at hy'
  refine ⟨y, ?_, hy'⟩
  rintro rfl
  simp only [map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at hy'
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy'
  omega

end val

theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

def lowerEquiv (r t : ℕ) : Fin t ≃ {x : Fin (r + t) // r ≤ x.val} where
  toFun i := ⟨Fin.natAdd r i, by simp⟩
  invFun x := ⟨x.1.val - r, by have := x.1.2; have := x.2; omega⟩
  left_inv i := by ext; simp
  right_inv x := by ext; have := x.2; simp; omega

theorem exists_parahoricVec : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → GlobalTheory.SplitWeil.IsTame μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = (μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))⁻¹) → ∀ u : W, u ≠ 0 → (∀ g h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → h.val = (g⁻¹).val.transpose → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom h) u = ((ξ d : ℂˣ) : ℂ) • u) → ∃ u' : W, u' ≠ 0 ∧ GlobalTheory.ThetaGL.IsParahoricVec μ π u' := by
  intro L _ _ _ s r t W _ _ π ξ μ c hc hci _ htame ⟨N, hN⟩ hglob u hu hvec
  have hE := isEquiv_of_continuous c hc
  have hlt : ∀ x, ValuativeRel.valuation _ x < 1 → Valued.v (c.symm x) < 1 := fun x hx =>
    (Valuation.isEquiv_iff_val_lt_one.1 hE).2 hx
  have hlt' : ∀ y, Valued.v y < 1 → ValuativeRel.valuation _ (c y) < 1 := fun y hy =>
    (Valuation.isEquiv_iff_val_lt_one.1 hE).1 (by simpa using hy)
  have hle : ∀ x, ValuativeRel.valuation _ x ≤ 1 →
      c.symm x ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun x hx =>
    (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx

  have hξ : ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ,
      ξ d = (μ (Units.map c.toRingHom.toMonoidHom d))⁻¹ := by
    intro d
    obtain ⟨y, hy0, hy⟩ := exists_global N d
    let k₀ : Lˣ := Units.mk0 (algebraMap (maximalRealSubfield L) L y) ((_root_.map_ne_zero _).2 hy0)
    let y' := Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k₀
    have hy' : (y' : s.v.adicCompletion (maximalRealSubfield L)) = algebraMap _ _ y := s.i.commutes y
    have hcy : Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k₀ =
        Units.map c.toRingHom.toMonoidHom y' := Units.ext (hci _).symm
    have h1 : ξ (y' * d⁻¹) = 1 := hN _ (by rw [Units.val_mul, hy']; exact hy.le)
    have h2 : μ (Units.map c.toRingHom.toMonoidHom (y' * d⁻¹)) = 1 := by
      refine htame _ ?_
      have := hlt' _ (hy.trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
      rw [map_sub, map_one, ← hy', ← Units.val_mul] at this
      exact this
    have h3 := hglob k₀
    rw [hcy] at h3
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h2
    rw [← h1, ← h2]
    exact h3
  obtain ⟨m, hm⟩ := exists_conj (k := s.w.adicCompletion L) r t
  refine ⟨π m⁻¹ u, fun h0 => hu ?_, fun h hK hlow x hx => ?_⟩
  · have := congrArg (π m) h0
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at this
  obtain ⟨hi1, hi2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff h).1 hK
  obtain ⟨hlow', hdet⟩ := inv_blocks h hK hlow
  obtain ⟨a1, -, -⟩ := hm h hi1 hlow
  obtain ⟨b1, b2, b3⟩ := hm h⁻¹ hi2 hlow'
  set p := m * h * m⁻¹ with hp
  have hq : m * h⁻¹ * m⁻¹ = p⁻¹ := by rw [hp]; group
  rw [hq] at b1 b2 b3
  let p' := Matrix.GeneralLinearGroup.map c.symm.toRingHom p
  let g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨(p'⁻¹).val.transpose, p'.val.transpose,
      by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  have hg : ∀ a b, g.val a b = c.symm ((p⁻¹).val b a) := fun a b => rfl
  have hg' : ∀ a b, (g⁻¹).val a b = c.symm (p.val b a) := fun a b => rfl
  have hpara : NG.ParaRT s r g := by
    refine ⟨mem_GLint_of_entries _ g (fun a b => hg a b ▸ hle _ (b1 b a)) (fun a b => hg' a b ▸ hle _ (a1 b a)),
      fun a b ha hb => ?_⟩
    rw [hg]
    exact hlt _ ((b2 b a hb).resolve_right (by omega))
  set e := ((h⁻¹).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det with he
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have hDD : c.symm e = NG.detDD s r g := by
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self (lowerEquiv r t), he, ← Matrix.det_transpose]
    refine (RingHom.map_det c.symm.toRingHom _).trans ?_
    congr 1
    refine Matrix.ext fun i j => ?_
    exact congrArg c.symm (b3 j i).symm
  have key := hvec g p' hpara rfl (Units.map c.symm.toRingHom.toMonoidHom (Units.mk0 e he0)) hDD
  have hpp : Matrix.GeneralLinearGroup.map c.toRingHom p' = p := by
    exact Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
  have hcc : Units.map c.toRingHom.toMonoidHom (Units.map c.symm.toRingHom.toMonoidHom (Units.mk0 e he0)) =
      Units.mk0 e he0 := Units.ext (c.apply_symm_apply _)
  have hμ : μ (x * Units.mk0 e he0) = 1 := htame _ (by rw [Units.val_mul, hx]; exact hdet)
  rw [map_mul, mul_eq_one_iff_eq_inv] at hμ
  rw [hpp, hξ, hcc, ← hμ] at key
  have hh : h * m⁻¹ = m⁻¹ * p := by rw [hp]; group
  rw [← Module.End.mul_apply, ← map_mul, hh, map_mul, Module.End.mul_apply, key, map_smul]

end GlobalTheory.ConjParahoric
