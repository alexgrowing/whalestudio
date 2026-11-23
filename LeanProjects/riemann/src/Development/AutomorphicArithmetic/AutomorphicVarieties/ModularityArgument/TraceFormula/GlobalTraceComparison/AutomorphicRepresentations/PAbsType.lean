import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

private lemma exists_projL {F : Type} [AddCommGroup F] [Module ℂ F] (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ)
    (hsym : ∀ a b, starRingEnd ℂ (B a b) = B b a) (hpos : ∀ a, a ≠ 0 → 0 < (B a a).re)
    (S : Submodule ℂ F) [FiniteDimensional ℂ S] :
    ∃ P : F →ₗ[ℂ] F, (∀ x, P x ∈ S) ∧ ∀ x, ∀ a ∈ S, B a (x - P x) = 0 := by
  let core : InnerProductSpace.Core ℂ F :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => hsym b a
      re_inner_nonneg := fun a => by
        by_cases h : a = 0
        · simp [h]
        · exact (hpos a h).le
      add_left := fun a b c => by simp
      smul_left := fun a b r => by simp
      definite := fun a h => by
        by_contra h0
        have h1 := hpos a h0
        have h2 : B a a = 0 := h
        simp [h2] at h1 }
  letI : NormedAddCommGroup F := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore core.toCore
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection.toLinearMap, fun x => S.starProjection_apply_mem x, fun x a ha => ?_⟩
  have h0 := S.starProjection_inner_eq_zero x a ha
  have h1 : B (x - S.starProjection x) a = 0 := h0
  have h2 := hsym (x - S.starProjection x) a
  rw [h1, map_zero] at h2
  exact h2.symm

private lemma orbit_stable {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) (g : Γ) :
    ∀ a ∈ Submodule.span ℂ (Set.range fun k => R k x),
      R g a ∈ Submodule.span ℂ (Set.range fun k => R k x) := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨k, rfl⟩ := h
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul, Module.End.mul_apply]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma self_mem_orbit {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) : x ∈ Submodule.span ℂ (Set.range fun k => R k x) :=
  Submodule.subset_span ⟨1, by simp⟩

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absType_pf :
    AbsType := by
  intro Γ F _ _ _ R B W V Y z hsym hpos hinv hW hV hVf hY hYV hzf hzt
  have hRR : ∀ k a, R k (R k⁻¹ a) = a := fun k a => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hadj : ∀ k a b, B a (R k b) = B (R k⁻¹ a) b := fun k a b => by
    have h := hinv k (R k⁻¹ a) b
    rwa [hRR] at h
  let T : Submodule ℂ F :=
    { carrier := {x | ∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k x)) ∈ W}
      add_mem' := fun {a b} ha hb l => by
        have h := W.add_mem (ha l) (hb l)
        convert h using 1
        ext k; simp
      zero_mem' := fun l => by
        have h := W.zero_mem
        convert h using 1
        ext k; simp
      smul_mem' := fun c x hx l => by
        have h := W.smul_mem c (hx l)
        convert h using 1
        ext k; simp }
  have hTR : ∀ g, ∀ x ∈ T, R g x ∈ T := fun g x hx l => by
    have h := hW _ (hx l) g
    convert h using 1
    ext k; simp [map_mul, Module.End.mul_apply]
  haveI : FiniteDimensional ℂ Y := hY
  haveI : FiniteDimensional ℂ (V ⊓ T : Submodule ℂ F) :=
    Submodule.finiteDimensional_of_le (S₂ := Y) fun x hx => hYV x hx.1 hx.2
  obtain ⟨P, hPm, hPo⟩ := exists_projL B hsym hpos (V ⊓ T)
  refine ⟨P z, (hPm z).1, hYV _ (hPm z).1 (hPm z).2, ?_⟩
  have hz1T : z - P z ∈ T := T.sub_mem hzt (hPm z).2
  have hZT : Submodule.span ℂ (Set.range fun k => R k (z - P z)) ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hTR k _ hz1T
  have hZperp : ∀ a ∈ V ⊓ T, ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), B a w = 0 := by
    intro a ha w hw
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨k, rfl⟩ := h
      show B a (R k (z - P z)) = 0
      rw [hadj]
      exact hPo z _ ⟨hV _ _ ha.1, hTR _ _ ha.2⟩
    | zero => simp
    | add a' b _ _ ha' hb => rw [map_add, ha', hb, add_zero]
    | smul c a' _ ha' => rw [map_smul, ha', smul_zero]
  intro v hv
  haveI := hVf v hv
  obtain ⟨Q, hQm, hQo⟩ := exists_projL B hsym hpos (Submodule.span ℂ (Set.range fun k => R k v))
  have hV0V : Submodule.span ℂ (Set.range fun k => R k v) ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hV k v hv
  have hzero : ∀ d, B d d = 0 → d = 0 := fun d h => by
    by_contra h0
    have h1 := hpos d h0
    simp [h] at h1
  have hQR : ∀ g x, Q (R g x) = R g (Q x) := fun g x => by
    have hd : Q (R g x) - R g (Q x) ∈ Submodule.span ℂ (Set.range fun k => R k v) :=
      Submodule.sub_mem _ (hQm _) (orbit_stable R v g _ (hQm x))
    have h1 := hQo (R g x) _ hd
    have h2 : B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) = 0 := by
      rw [← map_sub, hadj]
      exact hQo x _ (orbit_stable R v g⁻¹ _ hd)
    have h3 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) = 0 := by
      have h4 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) =
          B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) -
            B (Q (R g x) - R g (Q x)) (R g x - Q (R g x)) := by
        rw [← map_sub]
        congr 1
        abel
      rw [h4, h1, h2, sub_zero]
    exact sub_eq_zero.1 (hzero _ h3)
  have hQT : ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), Q w ∈ T := fun w hw l => by
    have h := hZT hw (l ∘ₗ Q)
    convert h using 1
    ext k; simp [hQR]
  have hQ0 : Q (z - P z) = 0 := by
    have hw := self_mem_orbit R (z - P z)
    have h1 := hZperp (Q (z - P z)) ⟨hV0V (hQm _), hQT _ hw⟩ _ hw
    have h2 := hQo (z - P z) _ (hQm (z - P z))
    rw [map_sub, h1, zero_sub, neg_eq_zero] at h2
    exact hzero _ h2
  have h := hQo (z - P z) v (self_mem_orbit R v)
  rwa [hQ0, sub_zero] at h
