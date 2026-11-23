import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplUniq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem precomplete_quot {R : Type} [CommRing R] (I K : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I (R ⧸ K) := by
  have hmap : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R).map K.mkQ = (I ^ n • ⊤ : Submodule R (R ⧸ K)) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  refine ⟨fun f hf => ?_⟩
  have hd : ∀ n, ∃ d ∈ (I ^ n • ⊤ : Submodule R R), K.mkQ d = f (n + 1) - f n := by
    intro n
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, ← hmap] at h
    exact h
  choose d hd hd' using hd
  obtain ⟨a, ha⟩ := K.mkQ_surjective (f 0)
  let g : ℕ → R := fun n => a + ∑ i ∈ Finset.range n, d i
  have hg : ∀ n, K.mkQ (g n) = f n := by
    intro n
    induction n with
    | zero => simpa [g] using ha
    | succ n ih =>
      have : g (n + 1) = g n + d n := by simp only [g, Finset.sum_range_succ, add_assoc]
      rw [this, map_add, ih, hd']; abel
  have hc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m n h
    induction h with
    | refl => rfl
    | @step n h ih =>
      have : g (n + 1) = g n + d n := by simp only [g, Finset.sum_range_succ, add_assoc]
      refine ih.trans ?_
      rw [SModEq.sub_mem, this, sub_add_cancel_left]
      exact neg_mem (Submodule.smul_mono_left (Ideal.pow_le_pow_right h) (hd n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hc
  refine ⟨K.mkQ L, fun n => ?_⟩
  rw [SModEq.sub_mem, ← hg, ← map_sub, ← hmap]
  exact Submodule.mem_map_of_mem (SModEq.sub_mem.1 (hL n))

theorem UpperTheory.V.CA.cpl_quot :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → ∀ (C' R' : Type) [CommRing C'] [CommRing R'] [Algebra C' R'] [IsLocalRing R'] (π : C →+* C') (x' : Ideal C'), Function.Surjective π → x'.comap π = x → IsCplAt x' R' → ∃ F : R →+* R', Function.Surjective F ∧ F.comp (algebraMap C R) = (algebraMap C' R').comp π ∧ RingHom.ker F = (RingHom.ker π).map (algebraMap C R) := by
  intro C R _ _ _ _ _ x hx hR C' R' _ _ _ _ π x' hπ hx' hR'
  haveI : IsNoetherianRing C' := isNoetherianRing_of_surjective C C' π hπ
  have hxm : x.map π = x' := by rw [← hx', Ideal.map_comap_of_surjective π hπ]
  haveI hx'm : x'.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective π hπ hx with h | h
    · rw [hxm] at h
      exact absurd (by rw [← hx', h, Ideal.comap_top]) hx.ne_top
    · rwa [hxm] at h
  haveI := hR.noeth
  haveI := hR.complete
  haveI := hR'.complete
  obtain ⟨hU, -, hm⟩ := cpl_uniq x hR
  obtain ⟨hU', -, hm'⟩ := cpl_uniq x' hR'
  have hx1 : x' ≤ (maximalIdeal R').comap (algebraMap C' R') := by
    rw [← Ideal.map_le_iff_le_comap, hm']
  obtain ⟨F, ⟨hF, hFm⟩, -⟩ := hU R' (maximalIdeal R') ((algebraMap C' R').comp π) (by
    rw [← Ideal.comap_comap, ← hx']; exact Ideal.comap_mono hx1)
  set K := (RingHom.ker π).map (algebraMap C R) with hK
  have hKF : K ≤ RingHom.ker F := by
    rw [hK, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [RingHom.mem_ker] at hc
    have := RingHom.congr_fun hF c
    simp only [RingHom.comp_apply, hc, map_zero] at this
    exact this
  set J := (maximalIdeal R).map (Ideal.Quotient.mk K) with hJ
  haveI : IsAdicComplete J (R ⧸ K) := by
    haveI := precomplete_quot (maximalIdeal R) K
    haveI : IsHausdorff (maximalIdeal R) (R ⧸ K) :=
      IsHausdorff.of_le_jacobson _ _ (by rw [jacobson_eq_maximalIdeal _ bot_ne_top])
    exact (IsAdicComplete.map_algebraMap_iff (S := R ⧸ K) (maximalIdeal R) (R ⧸ K)).2 ⟨⟩
  let g : C' →+* R ⧸ K := π.liftOfSurjective hπ ⟨(Ideal.Quotient.mk K).comp (algebraMap C R), fun c hc => by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hc⟩
  have hg : g.comp π = (Ideal.Quotient.mk K).comp (algebraMap C R) := RingHom.liftOfSurjective_comp _ _ _
  have hxJ : x ≤ J.comap ((Ideal.Quotient.mk K).comp (algebraMap C R)) := by
    rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_map, hm]
  obtain ⟨G, ⟨hG, hGm⟩, -⟩ := hU' (R ⧸ K) J g (by
    rw [← hxm, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hg]; exact hxJ)
  have h1 : G.comp F = Ideal.Quotient.mk K := by
    refine (hU (R ⧸ K) J _ hxJ).unique ⟨?_, ?_⟩ ⟨rfl, Ideal.le_comap_map⟩
    · rw [RingHom.comp_assoc, hF, ← RingHom.comp_assoc, hG, hg]
    · rw [← Ideal.comap_comap]; exact hFm.trans (Ideal.comap_mono hGm)
  let Fb : R ⧸ K →+* R' := Ideal.Quotient.lift K F hKF
  have hFb : Fb.comp (Ideal.Quotient.mk K) = F := RingHom.ext fun _ => rfl
  have h2 : Fb.comp G = RingHom.id R' := by
    refine (hU' R' (maximalIdeal R') _ hx1).unique ⟨?_, ?_⟩ ⟨rfl, le_rfl⟩
    · rw [RingHom.comp_assoc, hG, ← RingHom.cancel_right hπ, RingHom.comp_assoc, hg, ← RingHom.comp_assoc, hFb, hF]
    · rw [← Ideal.comap_comap]
      refine hGm.trans (Ideal.comap_mono ?_)
      rw [hJ, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hFb]
      exact hFm
  refine ⟨F, fun y => ?_, hF, le_antisymm (fun r hr => ?_) hKF⟩
  · obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (G y)
    refine ⟨r, ?_⟩
    have := RingHom.congr_fun h2 y
    rw [RingHom.comp_apply, ← hr] at this
    exact this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1, RingHom.comp_apply, (RingHom.mem_ker).1 hr, map_zero]
