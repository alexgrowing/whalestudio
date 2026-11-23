import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitActionStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv

open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ch

theorem mem_eig {K O V : Type} [Field K] [AddCommGroup V] [Module K V] (ρ : O → V →ₗ[K] V)
    (χ : O → K) (x : V) : x ∈ eig ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem comb_eig {K O V k : Type} [Field K] [Field k] [Algebra k K] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ : O → k) {x : V} (hx : x ∈ eig ρ fun a => algebraMap k K (χ a))
    {m : ℕ} (c : Fin m → k) (a : Fin m → O) :
    ∑ j, algebraMap k K (c j) • ρ (a j) x = algebraMap k K (∑ j, c j * χ (a j)) • x := by
  have h := (mem_eig ρ _ x).1 hx
  simp only [h, smul_smul, ← map_mul, ← Finset.sum_smul, ← map_sum]

theorem split_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ (ρ : O → V →ₗ[K] V) (ρ' : O →+* Module.End K V') (ρ'' : O → V'' →ₗ[K] V''), IsBun C L' → (∀ a, IsHom C L' L' (ρ' a)) → ShortExact C L L' L'' f g → (∀ a x, f (ρ a x) = ρ' a (f x)) → (∀ a y, g (ρ' a y) = ρ'' a (g y)) → ∀ s, subDeg C L' (eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a))) = subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) + subDeg C L'' (eig (fun a => ρ'' a) (fun a => algebraMap k K (χ s a))) := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g O k S _ _ _ _ _ χ hχ hv ρ ρ' ρ'' hL' hρ' hS hf hg s
  obtain ⟨e, he_hom, he_mem, -, -, he_comb⟩ :=
    SplitProj.split_proj K C V' L' O k S χ hχ hv ρ' hL' hρ'
  obtain ⟨m, c, a, hc, hes⟩ := he_comb s
  have key : ∀ y, g y ∈ eig ρ'' (fun a => algebraMap k K (χ s a)) → g (e s y) = g y := by
    intro y hy
    have h1 := comb_eig ρ'' (fun a => χ s a) hy c a
    rw [hes, LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smul_apply, map_smul, hg]
    rw [h1, hc s, if_pos rfl, map_one, one_smul]
  have hA : ∀ x, x ∈ eig ρ (fun a => algebraMap k K (χ s a)) ↔
      f x ∈ eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a)) := by
    intro x
    rw [mem_eig, mem_eig]
    constructor
    · intro h b
      rw [← hf, h b, map_smul]
    · intro h b
      apply hS.1
      rw [hf, h b, map_smul]
  have hB : ∀ z, z ∈ eig ρ'' (fun a => algebraMap k K (χ s a)) ↔
      ∃ y ∈ eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a)), g y = z := by
    intro z
    constructor
    · intro hz
      obtain ⟨y, rfl⟩ := hS.2.2.1 z
      exact ⟨e s y, he_mem s y, key y hz⟩
    · rintro ⟨y, hy, rfl⟩
      rw [mem_eig] at hy ⊢
      intro b
      rw [← hg, hy b, map_smul]
  obtain ⟨I, -, hdeg, hImem⟩ := ses_restrict hL' hS _ _ _ hA hB
  have hIeq : I = sub C L'' (eig ρ'' (fun a => algebraMap k K (χ s a))) := by
    funext i
    ext z
    rw [hImem]
    change _ ↔ (z : V'') ∈ L'' i
    constructor
    · rintro ⟨y, hy, -, hyz⟩
      exact (hS.2.2.2.2 i _).2 ⟨y, hy, hyz⟩
    · intro hz
      obtain ⟨y, hy, hyz⟩ := (hS.2.2.2.2 i _).1 hz
      refine ⟨e s y, he_hom s i y hy, he_mem s y, ?_⟩
      rw [key y (hyz ▸ z.2)]
      exact hyz
  rw [hdeg, hIeq]
  rfl

private theorem isBun_of_linearEquiv {K : Type} [Field K] {C : ACurve K} {V V' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} (e : V ≃ₗ[K] V') (hL' : IsBun C L')
    (h : ∀ i x, x ∈ L i ↔ e x ∈ L' i) : IsBun C L := by
  have hr : Module.finrank K V' = Module.finrank K V := e.finrank_eq.symm
  have key : ∀ i (b : Module.Basis (Fin (Module.finrank K V')) K V'), IsLatOf C i b (L' i) →
      IsLatOf C i ((b.map e.symm).reindex (finCongr hr)) (L i) := by
    intro i b hb x
    rw [h i x, hb (e x)]
    simp only [Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_symm]
    constructor
    · intro H q
      exact H _
    · intro H q
      simpa using H (finCongr hr q)
  obtain ⟨h1, b, hb⟩ := hL'
  refine ⟨fun i => ?_, (b.map e.symm).reindex (finCongr hr), hb.subset fun i hi hl => hi (key i b hl)⟩
  obtain ⟨b', hb'⟩ := h1 i
  exact ⟨_, key i b' hb'⟩

private theorem deg_eq_of_linearEquiv' {K : Type} [Field K] {C : ACurve K} {V V' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} (e : V ≃ₗ[K] V') (hL : IsBun C L)
    (hL' : IsBun C L') (h : ∀ i x, x ∈ L i ↔ e x ∈ L' i) : deg C L = deg C L' :=
  le_antisymm (deg_le_of_equiv e hL hL' fun i x hx => (h i x).1 hx)
    (deg_le_of_equiv e.symm hL' hL fun i x hx => (h i _).2 (by simpa using hx))

private theorem deg_eq_zero_of_finrank_eq_zero {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (h : Module.finrank K V = 0) :
    deg C L = 0 := by
  have : IsEmpty (Fin (Module.finrank K V)) := by
    rw [h]
    infer_instance
  unfold deg
  simp [Module.Basis.det_apply, Matrix.det_isEmpty]

private theorem subDeg_top_eq_sum_subDeg_of_all_eq_bot {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) {S : Type} [Fintype S]
    (W : S → Submodule K V) (e : S → Module.End K V) (he : ∀ s x, e s x ∈ W s)
    (hsum : ∀ x, ∑ s, e s x = x) (hall : ∀ s, W s = ⊥) :
    subDeg C L ⊤ = ∑ s, subDeg C L (W s) := by
  have hbot : subDeg C L ⊥ = 0 := deg_eq_zero_of_finrank_eq_zero C _ (by simp)
  have htop : (⊤ : Submodule K V) = ⊥ := by
    rw [eq_bot_iff]
    intro x _
    rw [Submodule.mem_bot, ← hsum x]
    exact Finset.sum_eq_zero fun s _ => by simpa [hall s] using he s x
  simp only [hall, htop, hbot, Finset.sum_const_zero]

private theorem subDeg_top_eq_sum_subDeg_eig_of_ncard_le (K : Type) [Field K] (C : ACurve K) (O k S : Type) [CommRing O]
    [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)) (hχ : IsSplit χ)
    (hv : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V)
      (ρ : O →+* Module.End K V), IsBun C L → (∀ a, IsHom C L L (ρ a)) →
      {s | eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)) ≠ ⊥}.ncard ≤ n →
      subDeg C L ⊤ = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) := by
  induction n with
  | zero =>
    intro V _ _ _ L ρ hL hρ hn
    obtain ⟨e, -, he_mem, -, he_sum, -⟩ := SplitProj.split_proj K C V L O k S χ hχ hv ρ hL hρ
    refine subDeg_top_eq_sum_subDeg_of_all_eq_bot C L (fun s => eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) e he_mem
      he_sum fun s => ?_
    by_contra hs
    have h0 := (Set.ncard_eq_zero (Set.toFinite _)).1 (Nat.le_zero.1 hn)
    have hmem : s ∈ ({s | eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)) ≠ ⊥} : Set S) := hs
    rw [h0] at hmem
    exact hmem
  | succ n ih =>
    intro V _ _ _ L ρ hL hρ hn
    obtain ⟨e, he_hom, he_mem, he_id, he_sum, he_comb⟩ :=
      SplitProj.split_proj K C V L O k S χ hχ hv ρ hL hρ
    by_cases hall : ∀ s, eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)) = ⊥
    · exact subDeg_top_eq_sum_subDeg_of_all_eq_bot C L (fun s => eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) e he_mem
        he_sum hall
    push_neg at hall
    obtain ⟨s0, hs0⟩ := hall
    have hcomm : ∀ s a x, e s (ρ a x) = ρ a (e s x) := by
      intro s a x
      obtain ⟨m, c, b, -, hes⟩ := he_comb s
      rw [hes, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hab : ρ (b j) (ρ a x) = ρ a (ρ (b j) x) := by
        show (ρ (b j) * ρ a) x = (ρ a * ρ (b j)) x
        rw [← map_mul, ← map_mul, mul_comm]
      rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hab]
    have hkill : ∀ s t, t ≠ s → ∀ x ∈ eig (fun a => ρ a) (fun a => algebraMap k K (χ t a)),
        e s x = 0 := by
      intro s t hts x hx
      obtain ⟨m, c, b, hc, hes⟩ := he_comb s
      have h1 : ∑ j, algebraMap k K (c j) • ρ (b j) x = algebraMap k K (∑ j, c j * χ t (b j)) • x :=
        comb_eig (fun a => ρ a) (fun a => χ t a) hx c b
      rw [hes, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
      rw [h1, hc t, if_neg hts, map_zero, zero_smul]
    set W0 := eig (fun a => ρ a) (fun a => algebraMap k K (χ s0 a)) with hW0
    set K0 := LinearMap.ker (e s0) with hK0
    have hidem : ∀ x, e s0 (e s0 x) = e s0 x := fun x => he_id s0 _ (he_mem s0 x)
    have hgmem : ∀ y, ((LinearMap.id : V →ₗ[K] V) - e s0) y ∈ K0 := by
      intro y
      rw [hK0, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hidem, sub_self]
    let g : V →ₗ[K] K0 := ((LinearMap.id : V →ₗ[K] V) - e s0).codRestrict K0 hgmem
    have hK0mem : ∀ z : K0, e s0 (z : V) = 0 := fun z => z.2
    have hS : ShortExact C (sub C L W0) L (sub C L K0) W0.subtype g := by
      refine ⟨Submodule.injective_subtype _, ?_, ?_, fun i x => Iff.rfl, ?_⟩
      · intro y
        constructor
        · intro h
          have h' : y - e s0 y = 0 := congrArg Subtype.val h
          have h'' : y = e s0 y := sub_eq_zero.1 h'
          exact ⟨⟨y, by rw [h'']; exact he_mem s0 y⟩, rfl⟩
        · rintro ⟨w, rfl⟩
          apply Subtype.ext
          show (w : V) - e s0 w = 0
          rw [he_id s0 _ w.2, sub_self]
      · intro z
        refine ⟨z, Subtype.ext ?_⟩
        show (z : V) - e s0 z = z
        rw [hK0mem z, sub_zero]
      · intro i z
        constructor
        · intro hz
          refine ⟨z, hz, Subtype.ext ?_⟩
          show (z : V) - e s0 z = z
          rw [hK0mem z, sub_zero]
        · rintro ⟨y, hy, rfl⟩
          show y - e s0 y ∈ L i
          exact (L i).sub_mem hy (he_hom s0 i y hy)
    obtain ⟨I, hI, hdegT, hImem⟩ :=
      ses_restrict hL hS ⊤ ⊤ ⊤ (fun x => by simp) (fun z => by simpa using hS.2.2.1 z)
    have hIeq : I = sub C (sub C L K0) ⊤ := by
      funext i
      ext z
      rw [hImem]
      change _ ↔ (z : K0) ∈ sub C L K0 i
      rw [hS.2.2.2.2 i]
      simp
    have hadd : subDeg C L ⊤ = subDeg C (sub C L W0) ⊤ + subDeg C (sub C L K0) ⊤ := by
      rw [hdegT, hIeq]
      rfl
    have hLK : IsBun C (sub C L K0) := by
      rw [hIeq] at hI
      exact isBun_of_linearEquiv (Submodule.topEquiv.symm) hI fun i x => Iff.rfl
    have hpresK : ∀ a (x : V), x ∈ K0 → ρ a x ∈ K0 := by
      intro a x hx
      show e s0 (ρ a x) = 0
      rw [hcomm, show e s0 x = 0 from hx, map_zero]
    have hpresW : ∀ a (x : V), x ∈ W0 → ρ a x ∈ W0 := by
      intro a x hx
      rw [← he_id s0 x hx, ← hcomm]
      exact he_mem s0 _
    let ρK : O →+* Module.End K K0 :=
      { toFun := fun a => ((ρ a).comp K0.subtype).codRestrict K0 fun x => hpresK a x x.2
        map_one' := by
          ext x
          simp
        map_mul' := by
          intro a b
          refine LinearMap.ext fun x => Subtype.ext ?_
          show ρ (a * b) (x : V) = ρ a (ρ b x)
          rw [map_mul]
          rfl
        map_zero' := by
          ext x
          simp
        map_add' := by
          intro a b
          refine LinearMap.ext fun x => Subtype.ext ?_
          show ρ (a + b) (x : V) = ρ a x + ρ b x
          rw [map_add]
          rfl }
    let ρW : O → Module.End K W0 := fun a =>
      ((ρ a).comp W0.subtype).codRestrict W0 fun x => hpresW a x x.2
    have hρK : ∀ a, IsHom C (sub C L K0) (sub C L K0) (ρK a) := by
      intro a i z hz
      show ρ a (z : V) ∈ L i
      exact hρ a i _ hz
    have hf : ∀ a (x : W0), W0.subtype (ρW a x) = ρ a (W0.subtype x) := fun a x => rfl
    have hg : ∀ a y, g (ρ a y) = ρK a (g y) := by
      intro a y
      apply Subtype.ext
      show ρ a y - e s0 (ρ a y) = ρ a (y - e s0 y)
      rw [map_sub, hcomm]
    have H3s := fun s => split_ses K C W0 V K0 (sub C L W0) L (sub C L K0) W0.subtype g O k S χ hχ hv
      ρW ρ (fun a => ρK a) hL hρ hS hf hg s
    have hWtop : eig ρW (fun a => algebraMap k K (χ s0 a)) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      rw [mem_eig]
      intro a
      apply Subtype.ext
      show ρ a (w : V) = algebraMap k K (χ s0 a) • (w : V)
      exact (mem_eig _ _ _).1 w.2 a
    have hWbot : ∀ s, s ≠ s0 → eig ρW (fun a => algebraMap k K (χ s a)) = ⊥ := by
      intro s hs
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      have hw' : (w : V) ∈ eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)) := by
        rw [mem_eig]
        intro a
        exact congrArg Subtype.val ((mem_eig _ _ _).1 hw a)
      apply Subtype.ext
      show (w : V) = 0
      rw [← he_id s0 _ w.2]
      exact hkill s0 s hs _ hw'
    have hKbot : eig (fun a => ρK a) (fun a => algebraMap k K (χ s0 a)) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      have hz' : (z : V) ∈ W0 := by
        rw [hW0, mem_eig]
        intro a
        exact congrArg Subtype.val ((mem_eig _ _ _).1 hz a)
      apply Subtype.ext
      show (z : V) = 0
      rw [← he_id s0 _ hz']
      exact hK0mem z
    have hKsub : ∀ s, eig (fun a => ρK a) (fun a => algebraMap k K (χ s a)) ≠ ⊥ →
        eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)) ≠ ⊥ := by
      intro s hs hbot
      apply hs
      rw [eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      have hz' : (z : V) ∈ eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)) := by
        rw [mem_eig]
        intro a
        exact congrArg Subtype.val ((mem_eig _ _ _).1 hz a)
      rw [hbot, Submodule.mem_bot] at hz'
      exact Subtype.ext hz'
    have hcount : {s | eig (fun a => ρK a) (fun a => algebraMap k K (χ s a)) ≠ ⊥}.ncard ≤ n := by
      have hss : {s | eig (fun a => ρK a) (fun a => algebraMap k K (χ s a)) ≠ ⊥} ⊂
          {s | eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)) ≠ ⊥} := by
        refine ⟨fun s hs => hKsub s hs, fun h => ?_⟩
        have hm : s0 ∈ {s | eig (fun a => ρK a) (fun a => algebraMap k K (χ s a)) ≠ ⊥} := h hs0
        exact hm hKbot
      have := Set.ncard_lt_ncard hss
      omega
    have hIH := ih K0 (sub C L K0) ρK hLK hρK hcount
    rw [hadd, hIH]
    simp only [H3s]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single s0]
    · rw [hWtop]
    · intro s _ hs
      rw [hWbot s hs]
      exact deg_eq_zero_of_finrank_eq_zero C _ (by simp)
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem split_deg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) := by
  intro K _ C V _ _ _ L O k S _ _ _ _ _ χ hχ hv ρ hL hρ
  have htop : subDeg C L ⊤ = deg C L :=
    deg_eq_of_linearEquiv' Submodule.topEquiv (isBun_of_linearEquiv Submodule.topEquiv hL fun _ _ => Iff.rfl) hL
      fun _ _ => Iff.rfl
  rw [← htop]
  exact subDeg_top_eq_sum_subDeg_eig_of_ncard_le K C O k S χ hχ hv _ V L ρ hL hρ le_rfl

end PositivityTheory.HtPt.Ch
