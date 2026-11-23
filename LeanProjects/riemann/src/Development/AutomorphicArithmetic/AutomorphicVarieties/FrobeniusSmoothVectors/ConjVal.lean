import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}

private noncomputable def ee (F : Frame l k) (u : ℤˣ) : F.Γ := if u = 1 then 1 else F.c

private theorem ee_one : ee F 1 = 1 := if_pos rfl

private theorem ee_neg : ee F (-1) = F.c := if_neg (by decide)

private noncomputable def pr (hc : F.del F.c = -1) (s : F.Γ) : F.G0 :=
  ⟨s * ee F (F.del s), by
    rw [MonoidHom.mem_ker, map_mul]
    rcases Int.units_eq_one_or (F.del s) with h | h
    · rw [h, ee_one, map_one, mul_one]
    · rw [h, ee_neg, hc]; simp⟩

private theorem pr_val (hc : F.del F.c = -1) (s : F.Γ) : (pr hc s : F.Γ) = s * ee F (F.del s) := rfl

private theorem pr_coe (hc : F.del F.c = -1) (s : F.G0) : pr hc s = s := by
  apply Subtype.ext
  have h : F.del s = 1 := s.2
  rw [pr_val, h, ee_one, mul_one]

private theorem conj_val (s : F.G0) : (F.conj s : F.Γ) = F.c * s * F.c⁻¹ := rfl

private theorem del_lc (ho : IsOpen (F.del.ker : Set F.Γ)) : IsLocallyConstant F.del := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.del.ker : Set F.Γ)) := ho.preimage (by fun_prop)
  filter_upwards [h1.mem_nhds (show x⁻¹ * x ∈ F.del.ker by simp)] with y hy
  have h2 : F.del (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem pr_cont (hc : F.del F.c = -1) (ho : IsOpen (F.del.ker : Set F.Γ)) : Continuous (pr hc) :=
  Continuous.subtype_mk (continuous_id.mul ((del_lc ho).comp (ee F)).continuous) _

private theorem theta_r {n : ℕ} {C : Type} [CommRing C] (ρ : NRep F n C) (g : F.G0) :
    theta (ρ.r.toHomUnits g) = ρ.r.toHomUnits (F.conj g) := by
  apply Units.ext
  rw [theta_val, ← map_inv, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, ← ρ.pol, Frame.star, inv_inv]

private noncomputable def rp (hc : F.del F.c = -1) (hs : F.c * F.c = 1) {n : ℕ} {C : Type} [CommRing C]
    (ρ : NRep F n C) : F.Γ →* GG n C where
  toFun s := ⟨ρ.r.toHomUnits (pr hc s), F.del s⟩
  map_one' := by
    have h : pr hc (1 : F.Γ) = 1 := pr_coe hc 1
    ext1
    · simp [h]
    · simp
  map_mul' s t := by
    have hi : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hs
    have hs' : ∀ x, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, hs, one_mul]
    ext1
    · rw [SemidirectProduct.mul_left]
      dsimp only
      rcases Int.units_eq_one_or (F.del s) with h | h
      · rw [h, sgnAct_one, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, pr_val, pr_val, pr_val, map_mul, h, ee_one, one_mul, mul_one, mul_assoc]
      · rw [h, sgnAct_neg_one, theta_r, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, conj_val, pr_val, pr_val, pr_val, map_mul, h, ee_neg, hi]
        rcases Int.units_eq_one_or (F.del t) with h' | h'
        · rw [h', mul_one, ee_neg, ee_one]
          simp only [mul_assoc, mul_one, hs']
        · rw [h', neg_mul_neg, mul_one, ee_neg, ee_one]
          simp only [mul_assoc, mul_one, hs', hs]
    · simp

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_box :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (ρ : NRep F n C), ρ.Cont I → (∀ v, UpperTheory.V.W.HasFlag (ρ.r.comp (F.loc0 v)).toHomUnits (ρ.ψ v)) → ∃ B : Box F n C, B.Of ρ ∧ B.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I ρ hc hf
  choose g hg using hf
  have hm : ∀ s, (rp hF.del_c hF.c_sq ρ s).mat = ρ.r (pr hF.del_c s) := fun s => rfl
  refine ⟨⟨rp hF.del_c hF.c_sq ρ, fun s => rfl, g, fun v s i j h => ?_⟩, ⟨?_, fun s => ?_, fun v i s => ?_⟩,
    fun i j N => ?_⟩
  · have e : pr hF.del_c (F.loc v s) = F.loc0 v s := pr_coe hF.del_c (F.loc0 v s)
    rw [hm, e]
    exact (hg v s).1 i j h
  · have e : pr hF.del_c F.c = 1 := by
      apply Subtype.ext
      rw [pr_val, hF.del_c, ee_neg, hF.c_sq]
      rfl
    show (rp hF.del_c hF.c_sq ρ F.c).mat = 1
    rw [hm, e, map_one]
  · show (rp hF.del_c hF.c_sq ρ s).mat = _
    rw [hm, pr_coe]
  · exact (hg v s).2 i
  · exact (hc.1 i j N).comp_continuous (pr_cont hF.del_c hF.del_open)
