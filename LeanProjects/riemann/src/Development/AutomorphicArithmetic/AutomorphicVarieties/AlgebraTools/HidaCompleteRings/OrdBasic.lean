import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IsOrdProjZeroOfIsNilpotent

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.factIdem :
    ∀ {G : Type*} [Monoid G] [Finite G] (a : G), ∃ N : ℕ, IsIdempotentElem (a ^ N.factorial) ∧ ∀ j, N ≤ j → a ^ j.factorial = a ^ N.factorial := by
  intro G _ _ a
  obtain ⟨s, p, hp, h⟩ : ∃ s p : ℕ, 0 < p ∧ a ^ (s + p) = a ^ s := by
    obtain ⟨m, n, hmn, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
    rcases lt_or_gt_of_ne hmn with hl | hl
    · exact ⟨m, n - m, by omega, by rw [show m + (n - m) = n by omega]; exact h.symm⟩
    · exact ⟨n, m - n, by omega, by rw [show n + (m - n) = m by omega]; exact h⟩
  have h1 : ∀ m, s ≤ m → ∀ k, a ^ (m + p * k) = a ^ m := by
    intro m hm k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← ih, show m + p * (k + 1) = (s + p) + (m - s + p * k) by rw [Nat.mul_succ]; omega, pow_add, h,
        ← pow_add]
      congr 1; omega
  have hs : s ≤ (s + p).factorial := le_trans (Nat.le_add_right _ _) (Nat.self_le_factorial _)
  obtain ⟨c, hc⟩ : p ∣ (s + p).factorial := Nat.dvd_factorial hp (Nat.le_add_left _ _)
  refine ⟨s + p, ?_, fun j hj => ?_⟩
  · show _ * _ = _
    rw [← pow_add]
    nth_rewrite 2 [hc]
    exact h1 _ hs c
  · obtain ⟨d, hd⟩ := Nat.factorial_dvd_factorial hj
    have hd0 : d ≠ 0 := by rintro rfl; exact Nat.factorial_ne_zero j (by simpa using hd)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    rw [hd, Nat.mul_succ, add_comm]
    nth_rewrite 2 [hc]
    rw [mul_assoc]
    exact h1 _ hs _

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordCancel :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R} {U e : Module.End R M}, IsOrdProj I U e → ∀ (J : Ideal R) (n : ℕ) (z : M), e z = z → (U ^ n) z ∈ (J • ⊤ : Submodule R M) → z ∈ (J • ⊤ : Submodule R M) := by
  intro R _ M _ _ I U e h J n
  have hm : ∀ x ∈ LinearMap.range e, U x ∈ LinearMap.range e := fun x hx => h.bij.mapsTo hx
  have hb : Function.Bijective (U.restrict hm) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (h.bij.injOn x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx, hxy⟩ := h.bij.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let E := LinearEquiv.ofBijective _ hb
  let V : Module.End R M := (LinearMap.range e).subtype ∘ₗ E.symm.toLinearMap ∘ₗ e.rangeRestrict
  have hc : ∀ x, U (e x) = e (U x) := fun x => LinearMap.congr_fun h.comm.eq x
  have hV : ∀ z, e z = z → V (U z) = z := by
    intro z hz
    have : e.rangeRestrict (U z) = E ⟨z, z, hz⟩ := Subtype.ext (by
      show e (U z) = U z
      rw [← hc, hz])
    simp only [V, LinearMap.comp_apply, this]
    simp
  induction n with
  | zero => intro z _ hz; simpa using hz
  | succ n ih =>
    intro z hz hU
    have h1 : e (U z) = U z := by rw [← hc, hz]
    rw [pow_succ, Module.End.mul_apply] at hU
    have := map_mem_smul_top V J (ih (U z) h1 hU)
    rwa [hV z hz] at this

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordNat :
    ∀ {A A' : Type*} [CommRing A] [CommRing A'] {M : Type*} [AddCommGroup M] [Module A M] {M' : Type*} [AddCommGroup M'] [Module A' M'] {I : Ideal A} {I' : Ideal A'} [IsHausdorff I' M'] {U e : Module.End A M} {U' e' : Module.End A' M'}, IsOrdProj I U e → IsOrdProj I' U' e' → ∀ (f : M →+ M'), (∀ x, f (U x) = U' (f x)) → (∀ k : ℕ, ∃ l : ℕ, ∀ x ∈ (I ^ l • ⊤ : Submodule A M), f x ∈ (I' ^ k • ⊤ : Submodule A' M')) → ∀ x, f (e x) = e' (f x) := by
  intro A A' _ _ M _ _ M' _ _ I I' _ U e U' e' h h' f hf hc x
  have hp : ∀ (n : ℕ) y, f ((U ^ n) y) = (U' ^ n) (f y) := by
    intro n y
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hf, ih]
  have hz : ∀ z : M', (∀ k : ℕ, z ∈ (I' ^ k • ⊤ : Submodule A' M')) → z = 0 := fun z hz =>
    IsHausdorff.haus (I := I') inferInstance z fun k => by rw [SModEq.zero]; exact hz k
  have hc' : ∀ (n : ℕ) y, (U' ^ n) (e' y) = e' ((U' ^ n) y) := fun n y =>
    LinearMap.congr_fun (h'.comm.pow_left n).eq y
  have h1 : e' (f (x - e x)) = 0 := by
    refine hz _ fun k => ?_
    obtain ⟨l, hl⟩ := hc k
    obtain ⟨n, hn⟩ := h.nil l
    refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordCancel h' _ n _ (LinearMap.congr_fun h'.idem.eq _) ?_
    rw [hc', ← hp]
    exact map_mem_smul_top _ _ (hl _ (hn x))
  have h2 : f (e x) - e' (f (e x)) = 0 := by
    refine hz _ fun k => ?_
    obtain ⟨n, hn⟩ := h'.nil k
    obtain ⟨y, -, hy⟩ := (h.bij.iterate n).surjOn (show e x ∈ (LinearMap.range e : Set M) from ⟨x, rfl⟩)
    rw [← Module.End.coe_pow] at hy
    rw [← hy, hp, ← hc', ← map_sub]
    exact hn _
  rw [map_sub, map_sub] at h1
  rw [sub_eq_zero] at h1 h2
  rw [h1]; exact h2

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordNatLin :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {I : Ideal R} [IsHausdorff I N] {U e : Module.End R M} {U' e' : Module.End R N}, IsOrdProj I U e → IsOrdProj I U' e' → ∀ (f : M →ₗ[R] N), (∀ x, f (U x) = U' (f x)) → f ∘ₗ e = e' ∘ₗ f := by
  intro R _ M _ _ N _ _ I _ U e U' e' h h' f hf
  ext x
  exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordNat h h' f.toAddMonoidHom hf (fun k => ⟨k, fun y hy => map_mem_smul_top f _ hy⟩) x

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordRange :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R} [IsHausdorff I M] {U e : Module.End R M}, IsOrdProj I U e → LinearMap.range e = ordPart U ∧ LinearMap.ker e = nilPart I U ∧ IsCompl (ordPart U) (nilPart I U) := by
  intro R _ M _ _ I _ U e h
  have hz : ∀ z : M, (∀ k : ℕ, z ∈ (I ^ k • ⊤ : Submodule R M)) → z = 0 := fun z hz =>
    IsHausdorff.haus (I := I) inferInstance z fun k => by rw [SModEq.zero]; exact hz k
  have hc : ∀ (n : ℕ) y, (U ^ n) (e y) = e ((U ^ n) y) := fun n y =>
    LinearMap.congr_fun (h.comm.pow_left n).eq y
  have hi : ∀ y, e (e y) = e y := fun y => LinearMap.congr_fun h.idem.eq y
  have h1 : LinearMap.range e = ordPart U := by
    apply le_antisymm
    · intro x hx
      refine mem_ordPart.2 fun n => ?_
      obtain ⟨y, -, hy⟩ := (h.bij.iterate n).surjOn hx
      exact ⟨y, by rw [Module.End.coe_pow]; exact hy⟩
    · intro x hx
      refine ⟨x, (sub_eq_zero.1 (hz _ fun k => ?_)).symm⟩
      obtain ⟨n, hn⟩ := h.nil k
      obtain ⟨y, rfl⟩ := mem_ordPart.1 hx n
      rw [← hc, ← map_sub]; exact hn y
  have h2 : LinearMap.ker e = nilPart I U := by
    apply le_antisymm
    · intro x hx k
      obtain ⟨n, hn⟩ := h.nil k
      have := hn x
      rw [LinearMap.mem_ker.1 hx, sub_zero] at this
      exact ⟨n, this⟩
    · intro x hx
      refine hz _ fun k => ?_
      obtain ⟨n, hn⟩ := hx k
      refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordCancel h _ n _ (hi x) ?_
      rw [hc]; exact map_mem_smul_top _ _ hn
  refine ⟨h1, h2, ?_⟩
  rw [← h1, ← h2]
  exact LinearMap.IsIdempotentElem.isCompl h.idem

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordFinLen :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M], IsFiniteLength R M → ∀ (U : Module.End R M), ∃ (e : Module.End R M) (n : ℕ), (∀ I : Ideal R, IsOrdProj I U e) ∧ ∀ x, (U ^ n) (x - e x) = 0 := by
  intro R _ M _ _ hM U
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hM
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 (LinearMap.eventually_isCompl_ker_pow_range_pow U)
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 (LinearMap.eventually_iInf_range_pow_eq U)
  have hc := (hn (n + m) (by omega)).symm
  have hr : LinearMap.range (U ^ (n + m + 1)) = LinearMap.range (U ^ (n + m)) := by
    rw [← hm _ (by omega), ← hm _ (by omega)]
  set N := n + m
  let e : Module.End R M := Submodule.projection _ _ hc
  have he1 : ∀ x ∈ LinearMap.range (U ^ N), e x = x := fun x hx => Submodule.projection_apply_of_mem_left hc hx
  have he2 : ∀ x ∈ LinearMap.ker (U ^ N), e x = 0 := fun x hx => (Submodule.projection_apply_eq_zero_iff hc).2 hx
  have he3 : ∀ x, e x ∈ LinearMap.range (U ^ N) := fun x => Submodule.projection_apply_mem hc x
  have hcomm : ∀ y, U ((U ^ N) y) = (U ^ N) (U y) := fun y => LinearMap.congr_fun (Commute.self_pow U N).eq y
  have he4 : ∀ x, x - e x ∈ LinearMap.ker (U ^ N) := by
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top.ge (Submodule.mem_top (x := x)))
    rw [map_add, he1 a ha, he2 b hb]; simpa using hb
  have hre : LinearMap.range e = LinearMap.range (U ^ N) :=
    le_antisymm (by rintro _ ⟨x, rfl⟩; exact he3 x) fun x hx => ⟨x, he1 x hx⟩
  have hU1 : ∀ x ∈ LinearMap.range (U ^ N), U x ∈ LinearMap.range (U ^ N) := by
    rintro _ ⟨y, rfl⟩; exact ⟨U y, (hcomm y).symm⟩
  have hU2 : ∀ x ∈ LinearMap.ker (U ^ N), U x ∈ LinearMap.ker (U ^ N) := by
    intro x hx; rw [LinearMap.mem_ker, ← hcomm, LinearMap.mem_ker.1 hx, map_zero]
  refine ⟨e, N, fun I => ⟨?_, ?_, ?_, fun k => ⟨N, fun x => ?_⟩⟩, he4⟩
  · ext x; exact he1 _ (he3 x)
  · ext x
    have h1 := he2 _ (hU2 _ (he4 x))
    rw [map_sub, map_sub, he1 _ (hU1 _ (he3 x)), sub_eq_zero] at h1
    exact h1.symm
  · rw [hre]
    refine ⟨hU1, fun x hx y hy hxy => ?_, fun x hx => ?_⟩
    · obtain ⟨z, hz⟩ := sub_mem hx hy
      have h1 : x - y ∈ LinearMap.ker (U ^ (N + 1)) := by
        rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, map_sub, hxy, sub_self, map_zero]
      have h2 : x - y ∈ LinearMap.range (U ^ (N + 1)) := hr.ge (sub_mem hx hy)
      exact sub_eq_zero.1 ((Submodule.disjoint_def.1 (hn (N + 1) (by omega)).disjoint) _ h1 h2)
    · obtain ⟨z, hz⟩ := hr.ge hx
      exact ⟨(U ^ N) z, ⟨z, rfl⟩, by rw [← hz, pow_succ', Module.End.mul_apply]⟩
  · rw [LinearMap.mem_ker.1 (he4 x)]; exact zero_mem _

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordLimProj :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}, OrdAdm M I → ∀ (U : Module.End R M), ∃ e : Module.End R M, ∀ k : ℕ, ∃ (Uk ek : Module.End R (M ⧸ (I ^ k • ⊤ : Submodule R M))) (n : ℕ), (∀ x, Uk (Submodule.Quotient.mk x) = Submodule.Quotient.mk (U x)) ∧ IsOrdProj ⊥ Uk ek ∧ (∀ y, (Uk ^ n) (y - ek y) = 0) ∧ ∀ x, ek (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := by
  intro R _ M _ _ I h U
  haveI := h.complete
  let Uk : ∀ k : ℕ, Module.End R (M ⧸ (I ^ k • ⊤ : Submodule R M)) := fun k =>
    Submodule.mapQ _ _ U fun x hx => map_mem_smul_top U _ hx
  choose ek n h1 h2 using fun k => UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordFinLen (h.finLen k) (Uk k)
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), Submodule.factorPow I M hle ∘ₗ (ek n ∘ₗ Submodule.mkQ _) = ek m ∘ₗ Submodule.mkQ _ := by
    intro m n hle
    rw [← LinearMap.comp_assoc, UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordNatLin (h1 n ⊥) (h1 m ⊥) (Submodule.factorPow I M hle)
      (fun x => by obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x; rfl)]
    rfl
  exact ⟨IsAdicComplete.lift I _ hc, fun k => ⟨Uk k, ek k, n k, fun x => rfl, h1 k ⊥, h2 k,
    fun x => (IsAdicComplete.mk_lift I hc k x).symm⟩⟩

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordLimBij :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R} [IsAdicComplete I M] (U e : Module.End R M), (∀ k : ℕ, ∃ (Uk ek : Module.End R (M ⧸ (I ^ k • ⊤ : Submodule R M))) (n : ℕ), (∀ x, Uk (Submodule.Quotient.mk x) = Submodule.Quotient.mk (U x)) ∧ IsOrdProj ⊥ Uk ek ∧ (∀ y, (Uk ^ n) (y - ek y) = 0) ∧ ∀ x, ek (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x)) → IsOrdProj I U e := by
  intro R _ M _ _ I _ U e h
  choose Uk ek n hU hp hn he using h
  have hz : ∀ x y : M, (∀ k : ℕ, (Submodule.Quotient.mk x : M ⧸ (I ^ k • ⊤ : Submodule R M)) = Submodule.Quotient.mk y) → x = y :=
    fun x y hxy => sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun k => by
      rw [SModEq.zero]; exact (Submodule.Quotient.eq _).1 (hxy k))
  have hi : ∀ x, e (e x) = e x := fun x => hz _ _ fun k => by
    rw [← he, ← he]; exact LinearMap.congr_fun (hp k).idem.eq _
  have hc : ∀ x, U (e x) = e (U x) := fun x => hz _ _ fun k => by
    rw [← hU, ← he, ← he, ← hU]; exact LinearMap.congr_fun (hp k).comm.eq _
  have hr : ∀ k x, (Submodule.Quotient.mk (e x) : M ⧸ (I ^ k • ⊤ : Submodule R M)) ∈ (LinearMap.range (ek k) : Set _) :=
    fun k x => ⟨_, he k x⟩
  refine ⟨LinearMap.ext hi, LinearMap.ext hc, ⟨?_, ?_, ?_⟩, fun k => ⟨n k, fun x => ?_⟩⟩
  · rintro _ ⟨x, rfl⟩; exact ⟨U x, (hc x).symm⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact hz _ _ fun k => (hp k).bij.injOn (hr k x) (hr k y) (by rw [hU, hU, hxy])
  · rintro _ ⟨x, rfl⟩
    have : ∀ k : ℕ, ∃ y, (Submodule.Quotient.mk (U (e y)) : M ⧸ (I ^ k • ⊤ : Submodule R M)) = Submodule.Quotient.mk (e x) := by
      intro k
      obtain ⟨_, ⟨w, rfl⟩, hw⟩ := (hp k).bij.surjOn (hr k x)
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      exact ⟨y, by rw [← hU, ← he, hw]⟩
    choose y hy using this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance (f := fun k => e (y k)) (fun {a b} hab => by
      refine (hp a).bij.injOn (hr a _) (hr a _) ?_
      rw [hU, hU, hy a]
      exact (SModEq.mono (Submodule.smul_mono (Ideal.pow_le_pow_right hab) le_rfl) (hy b)).symm)
    have hL' : ∀ k : ℕ, (Submodule.Quotient.mk L : M ⧸ (I ^ k • ⊤ : Submodule R M)) = Submodule.Quotient.mk (e (y k)) :=
      fun k => (hL k).symm
    refine ⟨L, ⟨L, hz _ _ fun k => ?_⟩, hz _ _ fun k => ?_⟩
    · rw [← he, hL', he, hi]
    · rw [← hU, hL', hU, hy]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply,
      pow_intertwine (A' := R) (U' := Uk k) (f := Submodule.mkQ _) (fun x => (hU k x).symm), map_sub,
      Submodule.mkQ_apply, Submodule.mkQ_apply, ← he]
    exact hn k _

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}, OrdAdm M I → ∀ (U : Module.End R M), IsOrdProj I U (ordProj I U) ∧ LinearMap.range (ordProj I U) = ordPart U ∧ IsCompl (ordPart U) (nilPart I U) ∧ Set.BijOn U (ordPart U) (ordPart U) := by
  intro R _ M _ _ I h U
  haveI := h.complete
  obtain ⟨e, he⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordLimProj h U
  have h1 := isOrdProj_ordProj ⟨e, UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordLimBij U e he⟩
  obtain ⟨h2, -, h3⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordRange h1
  exact ⟨h1, h2, h3, by rw [← h2]; exact h1.bij⟩

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordFactFin :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Finite M] (U : Module.End R M), ∃ N : ℕ, ∀ j, N ≤ j → ∀ I : Ideal R, IsOrdProj I U (U ^ j.factorial) := by
  intro R _ M _ _ _ U
  haveI : Finite (Module.End R M) := Finite.of_injective _ (DFunLike.coe_injective (F := M →ₗ[R] M))
  obtain ⟨N, hN, h⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.factIdem U
  refine ⟨N, fun j hj I => ?_⟩
  rw [h j hj]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero N)
  have hi : ∀ x, (U ^ N.factorial) ((U ^ N.factorial) x) = (U ^ N.factorial) x :=
    fun x => LinearMap.congr_fun hN.eq x
  have hc : Commute U (U ^ N.factorial) := Commute.self_pow U _
  have hmap : Set.MapsTo U (LinearMap.range (U ^ N.factorial)) (LinearMap.range (U ^ N.factorial)) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨U y, (LinearMap.congr_fun hc.eq y).symm⟩
  have hinj : Set.InjOn U (LinearMap.range (U ^ N.factorial)) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have := congrArg (U ^ m) hxy
    rw [← Module.End.mul_apply, ← pow_succ, ← Module.End.mul_apply (U ^ m), ← pow_succ] at this
    rw [← hi x, ← hi y]
    nth_rewrite 1 [hm]
    nth_rewrite 2 [hm]
    exact this
  refine ⟨hN, hc, ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo hmap).1 hinj, fun k => ⟨N.factorial, fun x => ?_⟩⟩
  rw [map_sub, hi, sub_self]; exact zero_mem _

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordFactLim :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}, OrdAdm M I → (∀ k : ℕ, Finite (M ⧸ (I ^ k • ⊤ : Submodule R M))) → ∀ (U e : Module.End R M), IsFactLim I U e ↔ e = ordProj I U := by
  intro R _ M _ _ I h hf U e
  haveI := h.complete
  have h1 : IsFactLim I U (ordProj I U) := by
    intro k
    haveI := hf k
    let Uk : Module.End R (M ⧸ (I ^ k • ⊤ : Submodule R M)) :=
      Submodule.mapQ _ _ U fun x hx => map_mem_smul_top U _ hx
    haveI : IsHausdorff I (M ⧸ (I ^ k • ⊤ : Submodule R M)) := ⟨fun x hx => by
      have h0 := hx k
      rw [SModEq.zero, ← Submodule.range_mkQ, LinearMap.range_eq_map, ← Submodule.map_smul''] at h0
      obtain ⟨y, hy, rfl⟩ := h0
      exact (Submodule.Quotient.mk_eq_zero _).2 hy⟩
    obtain ⟨N, hN⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordFactFin Uk
    refine ⟨N, fun j hj x => ?_⟩
    have := LinearMap.congr_fun (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordNatLin (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists h U).1 (hN j hj I)
      (Submodule.mkQ _) (fun _ => rfl)) x
    simp only [LinearMap.comp_apply] at this
    rw [← pow_intertwine (A' := R) (U := U) (U' := Uk) (f := Submodule.mkQ _) (fun _ => rfl)] at this
    exact (Submodule.Quotient.eq _).1 this.symm
  refine ⟨fun h2 => ?_, fun h2 => h2 ▸ h1⟩
  ext x
  refine sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun k => ?_)
  obtain ⟨N, hN⟩ := h1 k
  obtain ⟨N', hN'⟩ := h2 k
  rw [SModEq.zero]
  have := sub_mem (hN (N + N') (by omega) x) (hN' (N + N') (by omega) x)
  rwa [sub_sub_sub_cancel_left] at this

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.admissible_of_finite_length_torsion :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R) (r : ℕ), IsFiniteLength R M → (I ^ r • ⊤ : Submodule R M) = ⊥ → OrdAdm M I := by
  intro R _ M _ _ I r hM hr
  have h0 : ∀ n, r ≤ n → (I ^ n • ⊤ : Submodule R M) = ⊥ := fun n hn =>
    eq_bot_iff.2 (hr ▸ Submodule.smul_mono (Ideal.pow_le_pow_right hn) le_rfl)
  refine ⟨{ haus' := fun x hx => ?_, prec' := fun f hf => ⟨f r, fun n => ?_⟩ },
    fun k => hM.of_surjective (Submodule.mkQ_surjective _)⟩
  · have := hx r
    rwa [hr, SModEq.bot] at this
  · rcases le_total n r with h | h
    · exact hf h
    · have := hf h
      rw [hr, SModEq.bot] at this
      rw [this]

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExact :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {Q : Type*} [AddCommGroup Q] [Module R Q] {I : Ideal R}, OrdAdm M I → OrdAdm N I → ∀ {U : Module.End R M} {V : Module.End R N} {W : Module.End R Q} (f : M →ₗ[R] N) (g : N →ₗ[R] Q) (hf : ∀ x, f (U x) = V (f x)) (hg : ∀ x, g (V x) = W (g x)), Function.Exact f g → Function.Exact (ordMap (A' := R) f hf) (ordMap (A' := R) g hg) := by
  intro R _ M _ _ N _ _ Q _ _ I hM hN U V W f g hf hg hx y
  haveI := hN.complete
  obtain ⟨a1, a2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hM U
  obtain ⟨b1, b2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hN V
  have hn := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordNatLin a1 b1 f hf
  constructor
  · intro hy
    obtain ⟨x, hx'⟩ := (hx y).1 (congrArg Subtype.val hy)
    refine ⟨⟨ordProj I U x, a2.le ⟨x, rfl⟩⟩, Subtype.ext ?_⟩
    have h2 : (y : N) ∈ LinearMap.range (ordProj I V) := b2.ge y.2
    obtain ⟨z, hz⟩ := h2
    have := LinearMap.congr_fun hn x
    simp only [LinearMap.comp_apply] at this
    rw [coe_ordMap, this, hx', ← hz]
    exact LinearMap.congr_fun b1.idem.eq z
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((hx _).2 ⟨x, rfl⟩)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordSurj :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {I : Ideal R}, OrdAdm M I → OrdAdm N I → ∀ {U : Module.End R M} {V : Module.End R N} (f : M →ₗ[R] N) (hf : ∀ x, f (U x) = V (f x)), Function.Surjective f → Function.Surjective (ordMap (A' := R) f hf) ∧ ∀ J : Ideal R, LinearMap.ker f = J • ⊤ → LinearMap.ker (ordMap (A' := R) f hf) = J • ⊤ := by
  intro R _ M _ _ N _ _ I hM hN U V f hf hs
  haveI := hN.complete
  obtain ⟨a1, a2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hM U
  obtain ⟨b1, b2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hN V
  have hn := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordNatLin a1 b1 f hf
  constructor
  · intro y
    obtain ⟨x, hx'⟩ := hs y
    refine ⟨⟨ordProj I U x, a2.le ⟨x, rfl⟩⟩, Subtype.ext ?_⟩
    obtain ⟨z, hz⟩ := b2.ge y.2
    have := LinearMap.congr_fun hn x
    simp only [LinearMap.comp_apply] at this
    rw [coe_ordMap, this, hx', ← hz]
    exact LinearMap.congr_fun b1.idem.eq z
  · intro J hJ
    let p : M →ₗ[R] ordPart U := LinearMap.codRestrict _ (ordProj I U) fun x => a2.le ⟨x, rfl⟩
    apply le_antisymm
    · intro x hx
      have h1 : (x : M) ∈ (J • ⊤ : Submodule R M) := by
        rw [← hJ]; exact congrArg Subtype.val (LinearMap.mem_ker.1 hx)
      have h2 : p x = x := by
        obtain ⟨z, hz⟩ := a2.ge x.2
        refine Subtype.ext ?_
        show ordProj I U x = x
        rw [← hz]; exact LinearMap.congr_fun a1.idem.eq z
      rw [← h2]; exact map_mem_smul_top p J h1
    · intro x hx
      have h1 := map_mem_smul_top (ordPart U).subtype J hx
      rw [← hJ] at h1
      exact Subtype.ext h1

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordKill :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {I : Ideal R}, OrdAdm M I → OrdAdm N I → ∀ {U : Module.End R M} {V : Module.End R N} (f : M →ₗ[R] N) (hf : ∀ x, f (U x) = V (f x)), Function.Surjective f → ∀ r : ℕ, (∀ x, f x = 0 → (U ^ r) x = 0) → Function.Bijective (ordMap (A' := R) f hf) := by
  intro R _ M _ _ N _ _ I hM hN U V f hf hs r hr
  refine ⟨?_, (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordSurj hM hN f hf hs).1⟩
  obtain ⟨-, -, -, hb⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hM U
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 := hr x (congrArg Subtype.val hx)
  refine Subtype.ext ((hb.iterate r).injOn x.2 (zero_mem _) ?_)
  rw [← Module.End.coe_pow, h1]
  simp

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordLevel :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {U : Module.End R M} {V : Module.End R N} (j : M →ₗ[R] N) (hj : ∀ x, j (U x) = V (j x)), Function.Injective j → LinearMap.range V ≤ LinearMap.range j → Function.Bijective (ordMap (A' := R) j hj) := by
  intro R _ M _ _ N _ _ U V j hj hi hr
  refine ⟨fun x y hxy => Subtype.ext (hi (congrArg Subtype.val hxy)), fun y => ?_⟩
  have h : ∀ n : ℕ, ∃ w, j ((U ^ n) w) = y := by
    intro n
    obtain ⟨z, hz⟩ := mem_ordPart.1 y.2 (n + 1)
    obtain ⟨w, hw⟩ := hr ⟨z, rfl⟩
    refine ⟨w, ?_⟩
    rw [pow_intertwine (A' := R) hj, hw, ← hz, pow_succ, Module.End.mul_apply]
  obtain ⟨x, hx⟩ := h 0
  simp only [pow_zero, Module.End.one_apply] at hx
  refine ⟨⟨x, mem_ordPart.2 fun n => ?_⟩, Subtype.ext hx⟩
  obtain ⟨w, hw⟩ := h n
  exact ⟨w, hi (hw.trans hx.symm)⟩

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordFactor :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {U : Module.End R M}, Set.BijOn U (ordPart U) (ordPart U) → ∀ (V W : Module.End R M) (_ : Commute V W) (_ : U = V * W) (h : Commute V U), Function.Bijective (ordEnd V h) := by
  intro R _ M _ _ U hb V W hVW hU h
  have hW : Commute W U := by rw [hU]; exact (hVW.symm.mul_right (Commute.refl W))
  have hWm : ∀ x ∈ ordPart U, W x ∈ ordPart U := fun x hx =>
    map_mem_ordPart (A' := R) (f := W) (fun y => LinearMap.congr_fun hW.eq y) hx
  constructor
  · intro x y hxy
    have h1 : V x = V y := congrArg Subtype.val hxy
    refine Subtype.ext (hb.injOn x.2 y.2 ?_)
    have : ∀ z, U z = W (V z) := fun z => by rw [hU, hVW.eq]; rfl
    rw [this, this, h1]
  · intro y
    obtain ⟨x, hx, hxy⟩ := hb.surjOn y.2
    exact ⟨⟨W x, hWm x hx⟩, Subtype.ext (by
      rw [coe_ordEnd, ← hxy]
      exact (LinearMap.congr_fun hU x).symm)⟩

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordProjective :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}, OrdAdm M I → ∀ (U : Module.End R M), (Module.Finite R M → Module.Finite R (ordPart U)) ∧ (Module.Projective R M → Module.Projective R (ordPart U)) := by
  intro R _ M _ _ I hM U
  obtain ⟨a1, a2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hM U
  let p : M →ₗ[R] ordPart U := LinearMap.codRestrict _ (ordProj I U) fun x => a2.le ⟨x, rfl⟩
  have h2 : ∀ x : ordPart U, p x = x := by
    intro x
    obtain ⟨z, hz⟩ := a2.ge x.2
    refine Subtype.ext ?_
    show ordProj I U x = x
    rw [← hz]; exact LinearMap.congr_fun a1.idem.eq z
  refine ⟨fun _ => Module.Finite.of_surjective p fun x => ⟨x, h2 x⟩, fun _ => ?_⟩
  exact Module.Projective.of_split (ordPart U).subtype p (LinearMap.ext h2)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.towerIso :
    ∀ {R : Type*} [CommRing R] {P : ℕ → Type*} [∀ b, AddCommGroup (P b)] [∀ b, Module R (P b)] {I : ℕ → Ideal R}, IsTowerComplete I → ∀ (t : ∀ b, P (b + 1) →ₗ[R] P b) {s : ℕ} (φ : ∀ b, (Fin s → R) →ₗ[R] P b) (h : ∀ b x, t b (φ (b + 1) x) = φ b x), (∀ b, Function.Surjective (φ b)) → (∀ b, LinearMap.ker (φ b) = I b • ⊤) → Function.Bijective (towerLift t φ h) := by
  intro R _ P _ _ I hI t s φ h hs hk
  have hmem : ∀ (J : Ideal R) (x : Fin s → R), x ∈ (J • ⊤ : Submodule R (Fin s → R)) ↔ ∀ i, x i ∈ J := by
    intro J x
    constructor
    · intro hx i
      simpa using map_mem_smul_top (LinearMap.proj (R := R) (φ := fun _ : Fin s => R) i) J hx
    · intro hx
      rw [pi_eq_sum_univ x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    have : x i ∈ ⨅ b, I b := Ideal.mem_iInf.2 fun b =>
      (hmem _ _).1 ((hk b).le (congrArg (towerProj t b) hx)) i
    rw [hI.sep] at this
    exact this
  · intro y
    choose a ha using fun b => hs b (y.1 b)
    have h1 : ∀ b i, a (b + 1) i - a b i ∈ I b := fun b =>
      (hmem _ (a (b + 1) - a b)).1 ((hk b).le (by rw [LinearMap.mem_ker, map_sub, ← h, ha, ha, y.2 b, sub_self]))
    choose L hL using fun i => hI.lim (fun b => a b i) (fun b => h1 b i)
    refine ⟨L, Subtype.ext (funext fun b => ?_)⟩
    have := (hk b).ge ((hmem _ (L - a b)).2 fun i => hL i b)
    rw [LinearMap.mem_ker, map_sub, ha, sub_eq_zero] at this
    exact this

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.adicIso :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] (I : Ideal R) [IsAdicComplete I M] [IsAdicComplete I N] (f : ∀ r : ℕ, M →ₗ[R] N ⧸ (I ^ r • ⊤ : Submodule R N)), (∀ r x, Submodule.factor (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ r)) le_rfl) (f (r + 1) x) = f r x) → (∀ r, Function.Surjective (f r)) → (∀ r, LinearMap.ker (f r) = I ^ r • ⊤) → ∃ F : M ≃ₗ[R] N, ∀ r x, Submodule.Quotient.mk (F x) = f r x := by
  intro R _ M _ _ N _ _ I _ _ f hf hs hk
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), Submodule.factorPow I N hle ∘ₗ f n = f m := by
    intro m n hle
    induction n, hle using Nat.le_induction with
    | base => ext x; simp
    | succ n hmn ih =>
      ext x
      rw [← ih, LinearMap.comp_apply, LinearMap.comp_apply, ← hf n x]
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f (n + 1) x)
      rw [← hy]; rfl
  let F := IsAdicComplete.lift I f hc
  have hF : ∀ r x, Submodule.Quotient.mk (F x) = f r x := fun r x => IsAdicComplete.mk_lift I hc r x
  refine ⟨LinearEquiv.ofBijective F ⟨?_, fun y => ?_⟩, hF⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine IsHausdorff.haus (I := I) inferInstance _ fun r => ?_
    rw [SModEq.zero, ← hk, LinearMap.mem_ker, ← hF, hx]; rfl
  · choose x hx using fun r => hs r (Submodule.Quotient.mk y)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance (f := x) (fun {a b} hab => by
      rw [SModEq.sub_mem, ← hk, LinearMap.mem_ker, map_sub, hx, ← hc hab, LinearMap.comp_apply, hx]
      exact sub_self _)
    refine ⟨L, sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun r => ?_)⟩
    have := hL r
    rw [SModEq.sub_mem, ← hk, LinearMap.mem_ker, map_sub, hx, ← hF, sub_eq_zero] at this
    rw [SModEq.zero]
    exact (Submodule.Quotient.eq _).1 this.symm

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordPerFin :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Finite M] (U : Module.End R M) (x : M), x ∈ ordPart U ↔ ∃ n : ℕ, (U ^ (n + 1)) x = x := by
  intro R _ M _ _ _ U x
  constructor
  · intro hx
    obtain ⟨N, hN⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordFactFin U
    have h := hN N le_rfl ⊥
    obtain ⟨y, hy⟩ := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordRange h).1.ge hx
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero N)
    refine ⟨m, ?_⟩
    rw [← Nat.succ_eq_add_one, ← hm, ← hy]
    exact LinearMap.congr_fun h.idem.eq y
  · rintro ⟨n, hn⟩
    have h : ∀ k : ℕ, (U ^ ((n + 1) * k)) x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hn, ih]
    refine mem_ordPart.2 fun k => ⟨(U ^ (n * k)) x, ?_⟩
    rw [← Module.End.mul_apply, ← pow_add, show k + n * k = (n + 1) * k by ring, h]

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordPer :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}, OrdAdm M I → (∀ k : ℕ, Finite (M ⧸ (I ^ k • ⊤ : Submodule R M))) → ∀ (U : Module.End R M) (x : M), x ∈ ordPart U ↔ ∀ k : ℕ, ∃ n : ℕ, (U ^ (n + 1)) x - x ∈ (I ^ k • ⊤ : Submodule R M) := by
  intro R _ M _ _ I h hf U x
  haveI := h.complete
  have h1 := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordFactLim h hf U _).2 rfl
  obtain ⟨a1, a2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists h U
  constructor
  · intro hx k
    obtain ⟨y, hy⟩ := a2.ge hx
    have he : ordProj I U x = x := by rw [← hy]; exact LinearMap.congr_fun a1.idem.eq y
    obtain ⟨N, hN⟩ := h1 k
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero N)
    have := hN N le_rfl x
    rw [he, hm] at this
    exact ⟨m, this⟩
  · intro hx
    refine a2.le ⟨x, (sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun k => ?_)).symm⟩
    obtain ⟨n, hn⟩ := hx k
    obtain ⟨N, hN⟩ := h1 k
    have h2 : ∀ j : ℕ, (U ^ ((n + 1) * j)) x - x ∈ (I ^ k • ⊤ : Submodule R M) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have := add_mem (map_mem_smul_top (U ^ ((n + 1) * j)) _ hn) ih
        rwa [map_sub, sub_add_sub_cancel, ← Module.End.mul_apply, ← pow_add, ← Nat.mul_succ] at this
    obtain ⟨c, hc⟩ : n + 1 ∣ (N + (n + 1)).factorial := Nat.dvd_factorial (by omega) (by omega)
    have := sub_mem (hN (N + (n + 1)) (by omega) x) (hc ▸ h2 c)
    rw [SModEq.zero]
    rwa [sub_sub_sub_cancel_left] at this
