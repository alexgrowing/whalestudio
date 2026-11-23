import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exProj {k W : Type} [Field k] [AddCommGroup W] [Module k W] (b n : Submodule k W)
    (h : IsCompl b n) : ∃ P : W →ₗ[k] W, (∀ x, P x ∈ n) ∧ ∀ x, P x - x ∈ b := by
  refine ⟨n.projection b h.symm, fun x => Submodule.projection_apply_mem _ x, fun x => ?_⟩
  have e := Submodule.projection_add_projection_eq_self h.symm x
  have hm : b.projection n h x ∈ b := Submodule.projection_apply_mem _ x
  have : n.projection b h.symm x - x = -(b.projection n h x) := by
    calc n.projection b h.symm x - x
        = n.projection b h.symm x - (n.projection b h.symm x + b.projection n h x) := by rw [e]
      _ = -(b.projection n h x) := by abel
  rw [this]
  exact b.neg_mem hm

private theorem dimLem {k W T H A : Type} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    [AddCommGroup T] [Module k T] [AddCommGroup H] [Module k H] [AddCommGroup A] [Module k A] [Module.Finite k A]
    (t H0 : Submodule k W) (e : T →ₗ[k] W ⧸ t) (j : LinearMap.ker e →ₗ[k] A) (hj : Function.Injective j)
    (q : T →ₗ[k] H) (hq : Function.Surjective q) (f : W →ₗ[k] T) (hf : ∀ X, q (f X) = 0)
    (h0 : LinearMap.ker f ≤ H0) :
    Module.finrank k H + Module.finrank k t ≤ Module.finrank k A + Module.finrank k H0 := by
  haveI hK : Module.Finite k (LinearMap.ker e) := Module.Finite.of_injective j hj
  haveI hT : Module.Finite k T := by
    rw [← Module.rank_lt_aleph0_iff, ← LinearMap.rank_range_add_rank_ker e]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)
  have r1 := LinearMap.finrank_range_add_finrank_ker e
  have r2 := Submodule.finrank_le (LinearMap.range e)
  have r3 := Submodule.finrank_quotient_add_finrank t
  have r4 := LinearMap.finrank_le_finrank_of_injective hj
  have r5 := LinearMap.finrank_range_add_finrank_ker q
  have r6 : Module.finrank k (LinearMap.range q) = Module.finrank k H := by
    rw [LinearMap.range_eq_top.mpr hq, finrank_top]
  have hfq : LinearMap.range f ≤ LinearMap.ker q := by
    rintro _ ⟨X, rfl⟩
    exact hf X
  have r7 := Submodule.finrank_mono hfq
  have r8 := LinearMap.finrank_range_add_finrank_ker f
  have r9 := Submodule.finrank_mono h0
  omega

theorem UpperTheory.V.Ws.X1.coneTan :
    ∀ {k G W V : Type} [Field k] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module k W] [Module.Finite k W] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b n : V → Submodule k W) (g0 : G) (t : Submodule k W), (∀ X, IsLocallyConstant fun g => ρ g X) → (∀ v s, ∀ X ∈ b v, ρ (loc v s) X ∈ b v) → (∀ v, IsCompl (b v) (n v)) → Module.Finite k (TanC loc ρ b n g0 t) → Module.finrank k (Fr.H1C loc ρ b) + Module.finrank k t ≤ Module.finrank k (TanC loc ρ b n g0 t) + Module.finrank k (Fr.coneH0 ρ b) := by
  intro k G W V _ _ _ _ _ _ Gv _ loc ρ b n g0 t hlc hstab hcompl hfin
  choose P hPn hPb using fun v => exProj (b v) (n v) (hcompl v)
  have hPb' : ∀ v x, x - P v x ∈ b v := fun v x => by
    simpa using (b v).neg_mem (hPb v x)
  have hloc : ∀ v (s : Gv v) (y : W), y ∈ b v → ρ (loc v s) y - y ∈ b v := fun v s y hy =>
    (b v).sub_mem (hstab v s y hy) hy
  set S : Submodule k ((G → W) × (V → W)) :=
    Fr.Z1C loc ρ b ⊓ Submodule.comap (LinearMap.snd k (G → W) (V → W)) (Submodule.pi Set.univ n) with hSd
  let q : S →ₗ[k] Fr.H1C loc ρ b :=
    (Submodule.mkQ _) ∘ₗ Submodule.inclusion (inf_le_left : S ≤ Fr.Z1C loc ρ b)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨⟨c, x⟩, hz⟩ := z
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have hmem : ((c, fun v => P v (x v)) : (G → W) × (V → W)) ∈ S := by
      refine ⟨⟨hz1, hz2, fun v s => ?_⟩, ?_⟩
      · have h1 := hz3 v s
        have h2 := hloc v s _ (hPb v (x v))
        have e : c (loc v s) - (ρ (loc v s) (P v (x v)) - P v (x v)) =
            (c (loc v s) - (ρ (loc v s) (x v) - x v)) -
              (ρ (loc v s) (P v (x v) - x v) - (P v (x v) - x v)) := by
          rw [map_sub]; abel
        simp only at h1 ⊢
        rw [e]
        exact (b v).sub_mem h1 h2
      · simp [Submodule.mem_pi, hPn]
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨0, fun s => ?_, fun v => ?_⟩
    · simp
    · simpa using hPb v (x v)
  have fmem : ∀ X : W, ((fun s => ρ s X - X, fun v => P v X) : (G → W) × (V → W)) ∈ S := by
    intro X
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact (hlc X).sub (IsLocallyConstant.const X)
    · intro s u
      simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
    · intro v s
      have h2 := hloc v s _ (hPb' v X)
      have e : (ρ (loc v s) X - X) - (ρ (loc v s) (P v X) - P v X) =
          ρ (loc v s) (X - P v X) - (X - P v X) := by
        rw [map_sub]; abel
      simp only
      rw [e]
      exact h2
    · simp [Submodule.mem_pi, hPn]
  let f : W →ₗ[k] S :=
    { toFun := fun X => ⟨_, fmem X⟩
      map_add' := fun X Y => by
        apply Subtype.ext
        ext s <;> simp <;> abel
      map_smul' := fun a X => by
        apply Subtype.ext
        ext s <;> simp [smul_sub] }
  have hf : ∀ X, q (f X) = 0 := by
    intro X
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨X, fun s => rfl, fun v => hPb v X⟩
  have h0 : LinearMap.ker f ≤ Fr.coneH0 ρ b := by
    intro X hX
    rw [LinearMap.mem_ker] at hX
    have h1 := congrArg (fun z : S => z.1.1) hX
    have h2 := congrArg (fun z : S => z.1.2) hX
    refine ⟨fun g => ?_, fun v => ?_⟩
    · have := congrFun h1 g
      simp [f] at this
      exact sub_eq_zero.mp this
    · have := congrFun h2 v
      have hb := hPb v X
      simp [f] at this
      rw [this, zero_sub] at hb
      simpa using (b v).neg_mem hb
  let e : S →ₗ[k] W ⧸ t :=
    t.mkQ ∘ₗ (LinearMap.proj g0 ∘ₗ LinearMap.fst k (G → W) (V → W)) ∘ₗ S.subtype
  have jmem : ∀ z : LinearMap.ker e, (z.1.1 : (G → W) × (V → W)) ∈ TanC loc ρ b n g0 t := by
    rintro ⟨⟨z, hz1, hz2⟩, hze⟩
    rw [LinearMap.mem_ker] at hze
    refine ⟨hz1, ?_, ?_⟩
    · simpa [e, Submodule.Quotient.mk_eq_zero] using hze
    · exact hz2
  let j : LinearMap.ker e →ₗ[k] TanC loc ρ b n g0 t :=
    LinearMap.codRestrict _ (S.subtype ∘ₗ (LinearMap.ker e).subtype) jmem
  have hj : Function.Injective j := by
    intro z z' h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  haveI : Module.Finite k (TanC loc ρ b n g0 t) := hfin
  exact dimLem t (Fr.coneH0 ρ b) e j hj q hq f hf h0
