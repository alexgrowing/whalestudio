import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SupPerp

noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}

theorem adj_closed (h : PosH φ) {ι : Type} (T : ι → Module.End ℂ V)
    (hT : ∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) :
    ∀ s ∈ Algebra.adjoin ℂ (Set.range T), ∃ s' ∈ Algebra.adjoin ℂ (Set.range T), ∀ v w, φ (s v) w = φ v (s' w) := by
  intro s hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hT i
    exact ⟨T j, Algebra.subset_adjoin ⟨j, rfl⟩, hj⟩
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ (star r), Subalgebra.algebraMap_mem _ _, fun v w => ?_⟩
    simp only [Module.algebraMap_end_apply]
    rw [h.smul_left, h.smul]
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨x' + y', add_mem hx' hy', fun v w => ?_⟩
    simp only [LinearMap.add_apply]
    rw [h.add_left, hx'', hy'', h.add]
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨y' * x', mul_mem hy' hx', fun v w => ?_⟩
    simp only [Module.End.mul_apply]
    rw [hx'', hy'']

theorem orbit [FiniteDimensional ℂ V] (h : PosH φ) {ι : Type} (T : ι → Module.End ℂ V)
    (hT : ∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) (x : Module.End ℂ V)
    (hx : ∀ t : Module.End ℂ V, (∀ i, t * T i = T i * t) → x * t = t * x) (v : V) :
    ∃ s ∈ Algebra.adjoin ℂ (Set.range T), x v = s v := by
  classical
  set S := Algebra.adjoin ℂ (Set.range T) with hS
  let M : Submodule ℂ V := (Subalgebra.toSubmodule S).map (LinearMap.applyₗ v)
  have hM : ∀ y, y ∈ M ↔ ∃ s ∈ S, s v = y := by
    intro y
    simp [M, Submodule.mem_map]
  have hMinv : ∀ s ∈ S, ∀ y ∈ M, s y ∈ M := by
    intro s hs y hy
    obtain ⟨t, ht, rfl⟩ := (hM y).1 hy
    exact (hM _).2 ⟨s * t, mul_mem hs ht, rfl⟩
  have hNinv : ∀ s ∈ S, ∀ u ∈ h.perp M, s u ∈ h.perp M := by
    intro s hs u hu m hm
    obtain ⟨s', hs', hs''⟩ := adj_closed h T hT s hs
    rw [h.herm (s u) m, hs'' u m, h.herm (s' m) u, star_star, hu _ (hMinv s' hs' m hm)]
  have hc : IsCompl M (h.perp M) := IsCompl.of_eq (h.inf_perp M) (h.sup_perp M)
  let P : Module.End ℂ V := M.subtype ∘ₗ Submodule.projectionOnto M (h.perp M) hc
  have hPdec : ∀ m ∈ M, ∀ u ∈ h.perp M, P (m + u) = m := by
    intro m hm u hu
    have e1 : Submodule.projectionOnto M (h.perp M) hc m = ⟨m, hm⟩ :=
      Submodule.projectionOnto_apply_left hc ⟨m, hm⟩
    have e2 : Submodule.projectionOnto M (h.perp M) hc u = 0 :=
      Submodule.projectionOnto_apply_right hc ⟨u, hu⟩
    simp only [P, LinearMap.comp_apply, map_add, e1, e2]
    simp
  have hdec : ∀ y : V, ∃ m ∈ M, ∃ u ∈ h.perp M, y = m + u := by
    intro y
    have hy : y ∈ M ⊔ h.perp M := by rw [h.sup_perp]; trivial
    obtain ⟨m, hm, u, hu, e⟩ := Submodule.mem_sup.1 hy
    exact ⟨m, hm, u, hu, e.symm⟩
  have hPT : ∀ i, P * T i = T i * P := by
    intro i
    have hTi : T i ∈ S := Algebra.subset_adjoin ⟨i, rfl⟩
    refine LinearMap.ext fun y => ?_
    obtain ⟨m, hm, u, hu, rfl⟩ := hdec y
    simp only [Module.End.mul_apply]
    rw [map_add (T i), hPdec _ (hMinv _ hTi m hm) _ (hNinv _ hTi u hu), hPdec m hm u hu]
  have hxP := hx P hPT
  have hvM : v ∈ M := (hM v).2 ⟨1, Subalgebra.one_mem S, rfl⟩
  have hPv : P v = v := by simpa using hPdec v hvM 0 (Submodule.zero_mem _)
  have hxv : x v = P (x v) := by
    rw [← Module.End.mul_apply, ← hxP, Module.End.mul_apply, hPv]
  have hmem : P (x v) ∈ M := by
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Submodule.coe_mem _
  obtain ⟨s, hs, hsv⟩ := (hM _).1 hmem
  exact ⟨s, hs, by rw [hxv, ← hsv]⟩

def diag (d : ℕ) : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Fin d → V) where
  toFun f := LinearMap.pi fun k => f ∘ₗ LinearMap.proj k
  map_one' := LinearMap.ext fun w => funext fun k => by simp
  map_mul' f g := LinearMap.ext fun w => funext fun k => by simp
  map_zero' := LinearMap.ext fun w => funext fun k => by simp
  map_add' f g := LinearMap.ext fun w => funext fun k => by simp
  commutes' r := LinearMap.ext fun w => funext fun k => by simp

theorem diag_apply (d : ℕ) (f : Module.End ℂ V) (w : Fin d → V) (k : Fin d) : diag d f w k = f (w k) := by
  simp [diag]

def amp (φ : V → V → ℂ) (d : ℕ) (v w : Fin d → V) : ℂ := ∑ k, φ (v k) (w k)

theorem amp_posH (h : PosH φ) (d : ℕ) : PosH (amp φ d) where
  add v w₁ w₂ := by simp only [amp, Pi.add_apply, h.add, Finset.sum_add_distrib]
  smul v w r := by simp only [amp, Pi.smul_apply, h.smul, Finset.mul_sum]
  herm v w := by simp only [amp, star_sum, ← h.herm]
  pos v hv := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
    simp only [amp, Complex.re_sum]
    calc 0 < (φ (v k) (v k)).re := h.pos _ hk
      _ ≤ ∑ l, (φ (v l) (v l)).re :=
        Finset.single_le_sum (f := fun l => (φ (v l) (v l)).re) (fun l _ => h.re_nonneg _) (Finset.mem_univ k)

end CoreA

open CoreA in
theorem bicomm : Bicomm := by
  intro V _ _ _ φ hadd hsmul hherm hpos ι T hT x hx
  classical
  have h : PosH φ := ⟨hadd, hsmul, hherm, hpos⟩
  set d := Module.finrank ℂ V
  let e := Module.finBasis ℂ V
  let T' : ι → Module.End ℂ (Fin d → V) := fun i => diag d (T i)
  have hT' : ∀ i, ∃ j, ∀ v w, amp φ d (T' i v) w = amp φ d v (T' j w) := by
    intro i
    obtain ⟨j, hj⟩ := hT i
    exact ⟨j, fun v w => by simp only [amp, T', diag_apply, hj]⟩
  have hx' : ∀ t : Module.End ℂ (Fin d → V), (∀ i, t * T' i = T' i * t) → diag d x * t = t * diag d x := by
    intro t ht
    let tt : Fin d → Fin d → Module.End ℂ V := fun k l => LinearMap.proj k ∘ₗ t ∘ₗ LinearMap.single ℂ (fun _ => V) l
    have htt : ∀ k l, x * tt k l = tt k l * x := by
      intro k l
      apply hx
      intro i
      refine LinearMap.ext fun u => ?_
      have hs : (Pi.single l (T i u) : Fin d → V) = T' i (Pi.single l u) := by
        funext l'
        simp only [T', diag_apply]
        by_cases hl : l' = l
        · subst hl; simp
        · simp [Pi.single_apply, hl]
      have := LinearMap.congr_fun (ht i) (Pi.single l u)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, tt, LinearMap.comp_apply, LinearMap.coe_single, LinearMap.coe_proj,
        Function.eval, hs, this]
      simp [T', diag_apply]
    have hsum : ∀ w : Fin d → V, ∀ k, t w k = ∑ l, tt k l (w l) := by
      intro w k
      conv_lhs => rw [← Finset.univ_sum_single w]
      simp [tt, map_sum]
    refine LinearMap.ext fun w => funext fun k => ?_
    simp only [Module.End.mul_apply, diag_apply, hsum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact LinearMap.congr_fun (htt k l) (w l)
  obtain ⟨s', hs', hs'E⟩ := orbit (amp_posH h d) T' hT' (diag d x) hx' (fun k => e k)
  have hmap : Algebra.adjoin ℂ (Set.range T') = (Algebra.adjoin ℂ (Set.range T)).map (diag d) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [hmap] at hs'
  obtain ⟨s, hs, rfl⟩ := Subalgebra.mem_map.1 hs'
  have hxs : x = s := by
    refine e.ext fun k => ?_
    have := congrFun hs'E k
    simpa [diag_apply] using this
  rw [hxs]
  exact hs

end PositivityTheory.Rg.Sw.LC
