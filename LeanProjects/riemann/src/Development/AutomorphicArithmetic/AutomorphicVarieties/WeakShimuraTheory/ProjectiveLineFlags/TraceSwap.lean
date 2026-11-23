import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrMap

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open scoped Matrix

private theorem irr_map {Γ E E' : Type} [Group Γ] [Field E] [Field E'] (f : E →+* E') {n : ℕ}
    (r : Γ →* Matrix (Fin n) (Fin n) E) (hr : Irr r) (N : Submodule E' (Fin n → E'))
    (hN : ∀ g, ∀ v ∈ N, (mapRep f r g) *ᵥ v ∈ N) : N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qi38.irr_map f r hr N hN

private theorem trace_swap {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (N M : Submodule K V) (hc : IsCompl N M) (T : Module.End K V)
    (h1 : ∀ v ∈ N, T v ∈ M) (h2 : ∀ v ∈ M, T v ∈ N) : LinearMap.trace K V T = 0 := by
  obtain ⟨p, hpN, hpM⟩ : ∃ p : Module.End K V, (∀ v ∈ N, p v = v) ∧ (∀ v ∈ M, p v = 0) :=
    ⟨N.subtype ∘ₗ N.linearProjOfIsCompl M hc, fun v hv =>
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩),
      fun v hv =>
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨v, hv⟩)⟩
  have key : T = (p * T) * (1 - p) + ((1 - p) * T) * p := by
    ext v
    have hv : v ∈ N ⊔ M := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    simp [hpN a ha, hpM b hb, hpN _ (h2 b hb), hpM _ (h1 a ha), add_comm]
  have hpp : p * p = p := by
    ext v
    have hv : v ∈ N ⊔ M := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    simp [hpN a ha, hpM b hb]
  rw [key, map_add, LinearMap.trace_mul_comm K (p * T), LinearMap.trace_mul_comm K ((1 - p) * T),
    ← mul_assoc, ← mul_assoc, sub_mul, mul_sub, hpp]
  simp

theorem UpperTheory.V.Ws.P1.irrTr :
    ∀ {Γ E E' : Type} [Group Γ] [Field E] [Field E'] (f : E →+* E') {n : ℕ} (H : Subgroup Γ) (r : Γ →* Matrix (Fin n) (Fin n) E), (2 : E) ≠ 0 → Irr r →
          (∀ a b, a ∉ H → b ∉ H → a * b ∈ H) → (H = ⊤ ∨ ∃ g, g ∉ H ∧ (r g).trace ≠ 0) → U3.MatIrr H (mapRep f r) := by
  intro Γ E E' _ _ _ f n H r _ hr hH hg N hN
  rcases hg with rfl | ⟨g, hg, ht⟩
  · exact irr_map f r hr N fun g => hN g trivial
  set ρ := mapRep f r with hρ
  let M : Submodule E' (Fin n → E') := N.map (Matrix.mulVecLin (ρ g))
  have hNM : ∀ a, a ∉ H → ∀ v ∈ N, ρ a *ᵥ v ∈ M := by
    intro a ha v hv
    have : g⁻¹ * a ∈ H := hH _ _ (fun h => hg (H.inv_mem_iff.1 h)) ha
    refine ⟨_, hN _ this v hv, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel_left]
  have hMN : ∀ a, a ∉ H → ∀ v ∈ M, ρ a *ᵥ v ∈ N := by
    rintro a ha _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul]
    exact hN _ (hH _ _ ha hg) v hv
  have hMM : ∀ a ∈ H, ∀ v ∈ M, ρ a *ᵥ v ∈ M := by
    rintro a ha _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul]
    exact hNM _ (fun h => hg ((H.mul_mem_cancel_left ha).1 h)) v hv
  by_contra hcon
  obtain ⟨hb, htop⟩ := not_or.1 hcon
  have hinf : N ⊓ M = ⊥ := by
    refine (irr_map f r hr (N ⊓ M) fun a v hv => ?_).resolve_right fun h => htop (top_le_iff.1 (h ▸ inf_le_left))
    by_cases ha : a ∈ H
    · exact ⟨hN a ha v hv.1, hMM a ha v hv.2⟩
    · exact ⟨hMN a ha v hv.2, hNM a ha v hv.1⟩
  have hsup : N ⊔ M = ⊤ := by
    refine (irr_map f r hr (N ⊔ M) fun a v hv => ?_).resolve_left fun h => hb (le_bot_iff.1 (h ▸ le_sup_left))
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Matrix.mulVec_add]
    by_cases ha : a ∈ H
    · exact Submodule.add_mem_sup (hN a ha x hx) (hMM a ha y hy)
    · rw [add_comm]
      exact Submodule.add_mem_sup (hMN a ha y hy) (hNM a ha x hx)
  have hc : IsCompl N M := ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩
  have h0 := trace_swap N M hc (Matrix.toLin' (ρ g)) (fun v hv => hNM g hg v hv) (fun v hv => hMN g hg v hv)
  rw [Matrix.trace_toLin'_eq] at h0
  apply ht
  apply f.injective
  rw [map_zero, ← h0]
  simp [Matrix.trace, hρ]
