import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem cent_le (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (x : Matrix (Fin n) (Fin n) k) (hx : ∀ a ∈ Z, a * x = x * a) : x ∈ Z := by
  have hle : Subalgebra.toSubmodule Z ≤ Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    intro a ha
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    intro b hb
    exact hZ.1 b hb a ha
  have hfin : Module.finrank k (Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))))
      ≤ Module.finrank k (Subalgebra.toSubmodule Z) := Nat.sub_eq_zero_iff_le.1 h0
  have heq := Submodule.eq_of_le_of_finrank_le hle hfin
  have hxc : x ∈ Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    intro g hg
    exact hx g hg
  rw [← heq] at hxc
  exact hxc

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem prim_lemma (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hr : IsReduced Z) (c : Z) (hc0 : c ≠ 0) :
    ∃ b : Z, b * c * (b * c) = b * c ∧ b * c ≠ 0 := by
  letI : CommRing Z := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hc _ a.2 _ b.2) }
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  obtain ⟨m, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd c (1 : Z)
  simp only [smul_eq_mul, mul_one] at hy
  have hpow : ∀ j : ℕ, c ^ m * (c * y) ^ j = c ^ m := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc c ^ m * (c * y) ^ (j + 1) = c ^ (m + 1) * y * (c * y) ^ j := by ring
        _ = c ^ m := by rw [hy, ih]
  have hcm : c ^ m ≠ 0 := fun h0 => hc0 (IsReduced.eq_zero c ⟨m, h0⟩)
  have he : c ^ m * y ^ (m + 1) * c = (c * y) ^ (m + 1) := by ring
  refine ⟨c ^ m * y ^ (m + 1), ?_, ?_⟩
  · rw [he]
    calc (c * y) ^ (m + 1) * (c * y) ^ (m + 1) = c * y ^ (m + 1) * (c ^ m * (c * y) ^ (m + 1)) := by ring
      _ = (c * y) ^ (m + 1) := by rw [hpow]; ring
  · intro h0
    apply hcm
    rw [he] at h0
    rw [← hpow (m + 1), h0, mul_zero]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem prim_lemma_2 (f g : Matrix (Fin n) (Fin n) k) (hf : f * f = f) (hg : g * g = g)
    (hfg : f * g = 0) (hgf : g * f = 0) (hg0 : g ≠ 0) : f.rank < (f + g).rank := by
  have hle : LinearMap.range f.mulVecLin ≤ LinearMap.range (f + g).mulVecLin := by
    rintro y ⟨w, rfl⟩
    refine ⟨f *ᵥ w, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hf, hgf, add_zero]
  have hne : LinearMap.range f.mulVecLin ≠ LinearMap.range (f + g).mulVecLin := by
    intro heq
    obtain ⟨w, hw⟩ : ∃ w, g *ᵥ w ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hg0
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun w => ?_
      simp [Matrix.toLin'_apply, hall w]
    have hmem : g *ᵥ w ∈ LinearMap.range (f + g).mulVecLin := by
      refine ⟨g *ᵥ w, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hg, hfg, zero_add]
    rw [← heq] at hmem
    obtain ⟨w', hw'⟩ := hmem
    simp only [Matrix.mulVecLin_apply] at hw'
    apply hw
    calc g *ᵥ w = g *ᵥ (g *ᵥ w) := by rw [Matrix.mulVec_mulVec, hg]
      _ = g *ᵥ (f *ᵥ w') := by rw [hw']
      _ = 0 := by rw [Matrix.mulVec_mulVec, hgf, Matrix.zero_mulVec]
  exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem prim (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hr : IsReduced Z) (v : Fin n → k) (hv : v ≠ 0) :
    ∃ e ∈ Z, e * e = e ∧ e *ᵥ v ≠ 0 ∧
      ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e := by
  classical
  let P : ℕ → Prop := fun r => ∃ e ∈ Z, e * e = e ∧ e *ᵥ v ≠ 0 ∧ e.rank = r
  have hP : ∃ r, P r := ⟨_, 1, Z.one_mem, mul_one 1, by simpa using hv, rfl⟩
  obtain ⟨e, heZ, hee, hev, hre⟩ := Nat.find_spec hP
  refine ⟨e, heZ, hee, hev, ?_⟩
  intro u huZ hue hu0
  obtain ⟨b, hidem, hne⟩ := prim_lemma Z hc hr ⟨u, huZ⟩ (fun h => hu0 (congrArg Subtype.val h))
  have hidem' : (b : Matrix (Fin n) (Fin n) k) * u * ((b : Matrix (Fin n) (Fin n) k) * u) = (b : Matrix (Fin n) (Fin n) k) * u :=
    congrArg Subtype.val hidem
  have hne' : (b : Matrix (Fin n) (Fin n) k) * u ≠ 0 := fun h => hne (Subtype.ext h)
  have hbZ := b.2
  obtain ⟨f, hfdef⟩ : ∃ f, f = (b : Matrix (Fin n) (Fin n) k) * u := ⟨_, rfl⟩
  rw [← hfdef] at hidem' hne'
  have hfZ : f ∈ Z := hfdef ▸ Z.mul_mem hbZ huZ
  have hfe : f * e = f := by rw [hfdef, mul_assoc, hue]
  have hef : e * f = f := by rw [hc e heZ f hfZ, hfe]
  by_cases hfe' : f = e
  · refine ⟨(b : Matrix (Fin n) (Fin n) k) * e, Z.mul_mem hbZ heZ, by rw [mul_assoc, hee], ?_⟩
    calc (b : Matrix (Fin n) (Fin n) k) * e * u = b * (e * u) := mul_assoc _ _ _
      _ = b * (u * e) := by rw [hc e heZ u huZ]
      _ = b * u := by rw [hue]
      _ = e := by rw [← hfdef, hfe']
  · exfalso
    have hgZ : e - f ∈ Z := Z.sub_mem heZ hfZ
    have hgg : (e - f) * (e - f) = e - f := by
      rw [sub_mul, mul_sub, mul_sub, hee, hef, hfe, hidem', sub_self, sub_zero]
    have hfg : f * (e - f) = 0 := by rw [mul_sub, hfe, hidem', sub_self]
    have hgf : (e - f) * f = 0 := by rw [sub_mul, hef, hidem', sub_self]
    have hg0 : e - f ≠ 0 := sub_ne_zero.2 (Ne.symm hfe')
    by_cases hfv : f *ᵥ v = 0
    · have hgv : (e - f) *ᵥ v ≠ 0 := by rw [Matrix.sub_mulVec, hfv, sub_zero]; exact hev
      have hlt : (e - f).rank < e.rank := by
        have := prim_lemma_2 (e - f) f hgg hidem' hgf hfg hne'
        rwa [sub_add_cancel] at this
      have := Nat.find_min' hP ⟨e - f, hgZ, hgg, hgv, rfl⟩
      omega
    · have hlt : f.rank < e.rank := by
        have := prim_lemma_2 f (e - f) hidem' hgg hfg hgf hg0
        rwa [add_sub_cancel] at this
      have := Nat.find_min' hP ⟨f, hfZ, hidem', hfv, rfl⟩
      omega

theorem one_dim (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (w0 w : Fin n → k) (hw0 : e *ᵥ w0 = w0) (hw0' : w0 ≠ 0) (hw : e *ᵥ w = w) :
    ∃ u ∈ Z, u * e = u ∧ u *ᵥ w0 = w := by
  classical
  haveI hred : IsReduced Z := hZ.2
  letI : CommRing Z := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  haveI : IsSemisimpleRing Z := IsArtinianRing.isSemisimpleRing_of_isReduced Z
  let ρ : Z →+* Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toRingHom.comp
      Z.val.toRingHom
  letI : Module Z (Fin n → k) := Module.compHom (Fin n → k) ρ
  have hsmul : ∀ (z : Z) (v : Fin n → k), z • v = (z : Matrix (Fin n) (Fin n) k) *ᵥ v := fun _ _ => rfl
  have halg : ∀ (c : k) (v : Fin n → k), (algebraMap k Z c) • v = c • v := by
    intro c v
    rw [hsmul]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  let W : Submodule Z (Fin n → k) := Submodule.span Z {w0}
  obtain ⟨W', hWW'⟩ := exists_isCompl W
  let q := W'.projectionOnto W hWW'.symm
  let qk : (Fin n → k) →ₗ[k] (Fin n → k) :=
    { toFun := fun v => (q v : Fin n → k)
      map_add' := fun a b => by simp
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        calc (q (c • v) : Fin n → k) = (q (algebraMap k Z c • v) : Fin n → k) :=
              congrArg (fun x => (q x : Fin n → k)) (halg c v).symm
          _ = ((algebraMap k Z c • q v : W') : Fin n → k) := congrArg Subtype.val (q.map_smul _ _)
          _ = algebraMap k Z c • (q v : Fin n → k) := rfl
          _ = c • (q v : Fin n → k) := halg _ _ }
  have hX : ∀ v, LinearMap.toMatrix' qk *ᵥ v = (q v : Fin n → k) := fun v => LinearMap.toMatrix'_mulVec qk v
  have hcomm : ∀ a ∈ Z, a * LinearMap.toMatrix' qk = LinearMap.toMatrix' qk * a := by
    intro a ha
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hX]
    have h1 := congrArg Subtype.val (q.map_smul ⟨a, ha⟩ v)
    exact h1.symm
  have hXZ : LinearMap.toMatrix' qk ∈ Z := cent_le Z hZ h0 _ hcomm
  have hqW : ∀ x, (q x : Fin n → k) = 0 ↔ x ∈ W := by
    intro x
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hWW'.symm]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hXw0 : LinearMap.toMatrix' qk *ᵥ w0 = 0 := by
    rw [hX, hqW]
    exact Submodule.subset_span rfl
  have hXe : LinearMap.toMatrix' qk * e = 0 := by
    by_contra hne
    obtain ⟨u', hu'Z, hu'e, hu'⟩ := hprim _ (Z.mul_mem hXZ he) (by rw [mul_assoc, hee]) hne
    apply hw0'
    calc w0 = e *ᵥ w0 := hw0.symm
      _ = (u' * (LinearMap.toMatrix' qk * e)) *ᵥ w0 := by rw [hu']
      _ = u' *ᵥ (LinearMap.toMatrix' qk *ᵥ (e *ᵥ w0)) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
      _ = 0 := by rw [hw0, hXw0, Matrix.mulVec_zero]
  have hwW : w ∈ W := by
    rw [← hqW, ← hX, ← hw, Matrix.mulVec_mulVec, hXe, Matrix.zero_mulVec]
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 hwW
  refine ⟨(z : Matrix (Fin n) (Fin n) k) * e, Z.mul_mem z.2 he, by rw [mul_assoc, hee], ?_⟩
  rw [← Matrix.mulVec_mulVec, hw0]
  exact hz

end PositivityTheory.RgUd.T.Nil.BasePf
