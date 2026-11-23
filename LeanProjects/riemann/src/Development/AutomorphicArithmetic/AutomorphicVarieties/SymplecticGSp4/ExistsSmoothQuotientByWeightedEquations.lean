import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartCut
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem quot_facts {O X R R' : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (W : WPres O X R) (h : W.HasOrigin) (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (hh : IsHomog O W.wt (RingHom.ker (p.comp W.π))) (x' : R' →ₐ[O] O) (hx : x'.comp p = W.origin h) :
    ∃ h' : (W.quot p hp hh).HasOrigin, (W.quot p hp hh).origin h' = x' ∧
      (W.quot p hp hh).part = fun j => (W.part j).map p.toLinearMap := by
  have hq : ∀ f : MvPowerSeries W.σ O, p (W.π f) = 0 → MvPowerSeries.constantCoeff f = 0 := by
    intro f hf
    have h1 := congrArg (fun g => g (W.π f)) hx
    simp only [AlgHom.comp_apply, hf, map_zero, WPres.origin_π] at h1
    exact h1.symm
  refine ⟨hq, ?_, ?_⟩
  · ext y
    obtain ⟨z, rfl⟩ := hp y
    obtain ⟨f, rfl⟩ := W.surj z
    have e1 := WPres.origin_π (W.quot p hp hh) hq f
    have e2 := congrArg (fun g => g (W.π f)) hx
    simp only [AlgHom.comp_apply, WPres.origin_π] at e2
    exact e1.trans e2.symm
  · funext j
    show Submodule.map (p.comp W.π).toLinearMap _ = Submodule.map p.toLinearMap (Submodule.map W.π.toLinearMap _)
    rw [← Submodule.map_comp]
    rfl

private theorem der_sq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (D : A →ₗ[O] O) (hD : D ∈ PtDer x O) : ∀ g ∈ RingHom.ker x ^ 2, D g = 0 := by
  intro g hg
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
  · rw [RingHom.mem_ker] at ha hb
    rw [hD a b, ha, hb, zero_smul, zero_smul, add_zero]
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

private theorem indep {O A κ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [Fintype κ] (x : A →ₐ[O] O)
    (g : κ → A) (hd : ∀ k, ∃ δ ∈ PtDer x O, δ (g k) ≠ 0 ∧ ∀ k', k' ≠ k → δ (g k') = 0) :
    LinearIndependent O (fun i => (satSq x).mkQ (g i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hs : (satSq x).mkQ (∑ i, c i • g i) = 0 := by
    rw [map_sum]
    simpa only [map_smul] using hc
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hs
  obtain ⟨a, ha0, ha⟩ := hs
  obtain ⟨δ, hδ, hk, hk'⟩ := hd k
  have hz := der_sq x δ hδ _ ha
  rw [map_smul, map_sum] at hz
  simp only [map_smul, smul_eq_mul] at hz
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hk' j hj, mul_zero]) (by simp)] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h ha0
  · rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hk

private theorem der_desc {O A A' κ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
    (x : A →ₐ[O] O) (g : κ → A) (hg : ∀ k, x (g k) = 0) (p : A →ₐ[O] A') (hp : Function.Surjective p)
    (hk : RingHom.ker p = Ideal.span (Set.range g)) (x' : A' →ₐ[O] O) (hx : x'.comp p = x)
    (δ : A →ₗ[O] O) (hδ : δ ∈ PtDer x O) (h0 : ∀ k, δ (g k) = 0) :
    ∃ δ' ∈ PtDer x' O, ∀ y, δ' (p y) = δ y := by
  have hker : ∀ y, y ∈ Ideal.span (Set.range g) → x y = 0 ∧ δ y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact ⟨hg k, h0 k⟩
    | zero => simp
    | add a b _ _ ha hb => simp [ha.1, ha.2, hb.1, hb.2]
    | smul a z _ hz =>
      refine ⟨?_, ?_⟩
      · simp [hz.1]
      · rw [smul_eq_mul, hδ a z, hz.1, hz.2, smul_zero, zero_smul, add_zero]
  have hle : LinearMap.ker p.toLinearMap ≤ LinearMap.ker δ := by
    intro y hy
    have hy' : y ∈ RingHom.ker p := hy
    rw [hk] at hy'
    exact (hker y hy').2
  let e := LinearMap.quotKerEquivOfSurjective p.toLinearMap hp
  let δ' : A' →ₗ[O] O := ((LinearMap.ker p.toLinearMap).liftQ δ hle).comp e.symm.toLinearMap
  have hδ' : ∀ y, δ' (p y) = δ y := by
    intro y
    have : e.symm (p y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [δ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  refine ⟨δ', ?_, hδ'⟩
  intro f g'
  obtain ⟨a, rfl⟩ := hp f
  obtain ⟨b, rfl⟩ := hp g'
  rw [← map_mul, hδ', hδ', hδ', hδ a b]
  have ha : x' (p a) = x a := by rw [← hx]; rfl
  have hb : x' (p b) = x b := by rw [← hx]; rfl
  rw [ha, hb]

theorem UpperTheory.exists_smooth_quotient_by_weighted_equations :
    ∀ (O X : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X] (P : Type) [CommRing P] [Algebra O P] [IsCO O P] (W : WPres O X P) (h : W.HasOrigin) (n : X → ℕ), SmoothPt W.part (W.origin h) n → ∀ (κ : Type) [Fintype κ] (g : κ → P) (w : κ → X), (∀ k, g k ∈ W.part (w k) ∧ W.origin h (g k) = 0) → (∀ k, ∃ δ ∈ PtDer (W.origin h) O, δ (g k) ≠ 0 ∧ ∀ k', k' ≠ k → δ (g k') = 0) → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (_ : IsDomain R) (q : P →ₐ[O] R) (W' : WPres O X R) (h' : W'.HasOrigin) (n' : X → ℕ), Function.Surjective q ∧ (∀ s, ∃ s', W'.wt s = W.wt s') ∧ (∀ j, W'.part j = (W.part j).map q.toLinearMap) ∧ (W'.origin h').comp q = W.origin h ∧ (∀ k, q (g k) = 0) ∧ (∀ δ ∈ PtDer (W.origin h) O, (∀ k, δ (g k) = 0) → ∀ y, q y = 0 → δ y = 0) ∧ SmoothPt W'.gr (W'.originA h') n' ∧ ∀ j, n' j + Nat.card {k // w k = j} = n j := by
  intro O X _ _ _ _ _ _ _ _ _ P _ _ _ W h n hs κ _ g w hgw hd
  classical
  obtain ⟨τ, _, wt0, φ, hc, hn⟩ := hs
  set I : Ideal P := Ideal.span (Set.range g) with hI
  have hIx : ∀ a ∈ I, W.origin h a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker (W.origin h) := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact (hgw k).2
    exact hle ha
  let p : P →ₐ[O] P ⧸ I := Ideal.Quotient.mkₐ O I
  have hp : Function.Surjective p := Ideal.Quotient.mkₐ_surjective O I
  have hpker : RingHom.ker p = Ideal.span (Set.range g) := by
    rw [← hI]
    exact Ideal.Quotient.mkₐ_ker O I
  let x' : P ⧸ I →ₐ[O] O := Ideal.Quotient.liftₐ I (W.origin h) hIx
  have hx' : x'.comp p = W.origin h := by
    ext y
    rfl
  have hli := indep (W.origin h) g hd
  obtain ⟨τ', _, wt', φ', hc', hn'⟩ :=
    chart_cut O P X W.part (W.origin h) τ wt0 φ hc κ g w hgw hli (P ⧸ I) p x' hp hpker hx'
  have hgA : ∀ k, (⟨g k, W.part_le_A (hgw k).1⟩ : W.A) ∈ W.gr (w k) := fun k => (hgw k).1
  obtain ⟨hhom, -⟩ := homog_span O P X W κ (fun k => ⟨g k, W.part_le_A (hgw k).1⟩) w hgA
  have hh1 : IsHomog O W.wt (RingHom.ker (p.comp W.π)) := by
    have e : RingHom.ker (p.comp W.π) = Ideal.comap W.π (Ideal.span (Set.range fun k => g k)) := by
      ext f
      simp [p, Ideal.Quotient.eq_zero_iff_mem, hI]
    rw [e]
    exact hhom
  obtain ⟨h1, ho1, hpart1⟩ := quot_facts W h p hp hh1 x' hx'
  set W1 := W.quot p hp hh1 with hW1
  have hc1 : IsChart W1.part (W1.origin h1) wt' φ' := by
    rw [ho1, hpart1]
    exact hc'
  obtain ⟨hprime, hhom1, hkle, hdk, hdesc⟩ := chart_ker O X (P ⧸ I) W1 h1 τ' wt' φ' hc1
  set J : Ideal (P ⧸ I) := RingHom.ker φ' with hJ
  have hJx : ∀ a ∈ J, x' a = 0 := by
    intro a ha
    have := hkle ha
    rw [ho1] at this
    exact this
  let p2 : P ⧸ I →ₐ[O] (P ⧸ I) ⧸ J := Ideal.Quotient.mkₐ O J
  have hp2 : Function.Surjective p2 := Ideal.Quotient.mkₐ_surjective O J
  let x'' : (P ⧸ I) ⧸ J →ₐ[O] O := Ideal.Quotient.liftₐ J x' hJx
  let φ'' : (P ⧸ I) ⧸ J →ₐ[O] MvPowerSeries τ' (FractionRing O) :=
    Ideal.Quotient.liftₐ J φ' (fun a ha => ha)
  have hx'' : x''.comp p2 = W1.origin h1 := by
    rw [ho1]
    ext y
    rfl
  have hφ'' : φ''.comp p2 = φ' := by
    ext y
    rfl
  have hc2 := hdesc ((P ⧸ I) ⧸ J) p2 x'' φ'' hp2 hx'' hφ''
  have hh2 : IsHomog O W1.wt (RingHom.ker (p2.comp W1.π)) := by
    have e : RingHom.ker (p2.comp W1.π) = RingHom.ker (φ'.comp W1.π) := by
      ext f
      simp [p2, Ideal.Quotient.eq_zero_iff_mem, hJ]
    rw [e]
    exact hhom1
  obtain ⟨h2, ho2, hpart2⟩ := quot_facts W1 h1 p2 hp2 hh2 x'' hx''
  set W2 := W1.quot p2 hp2 hh2 with hW2
  have hc3 : IsChart W2.part (W2.origin h2) wt' φ'' := by
    rw [ho2, hpart2]
    exact hc2
  have hgr := chart_gr O X ((P ⧸ I) ⧸ J) W2 h2 τ' wt' φ'' hc3
  haveI : J.IsPrime := hprime
  let q : P →ₐ[O] (P ⧸ I) ⧸ J := p2.comp p
  have hq : Function.Surjective q := hp2.comp hp
  have hpartq : ∀ j, W2.part j = (W.part j).map q.toLinearMap := by
    intro j
    rw [hpart2, hpart1]
    show _ = Submodule.map (p2.toLinearMap.comp p.toLinearMap) _
    rw [Submodule.map_comp]
  refine ⟨(P ⧸ I) ⧸ J, inferInstance, inferInstance, co_quot O P _ q hq, inferInstance, q, W2, h2,
    fun j => Nat.card {i // wt' i = j}, hq, fun s => ⟨s, rfl⟩, hpartq, ?_, ?_, ?_,
    ⟨τ', inferInstance, wt', _, hgr, fun j => rfl⟩, ?_⟩
  · rw [ho2]
    ext y
    rfl
  · intro k
    show p2 (p (g k)) = 0
    have : p (g k) = 0 := by
      show Ideal.Quotient.mk I (g k) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hI]
      exact Ideal.subset_span ⟨k, rfl⟩
    rw [this, map_zero]
  · intro δ hδ h0 y hy
    obtain ⟨δ', hδ'mem, hδ'⟩ := der_desc (W.origin h) g (fun k => (hgw k).2) p hp hpker x' hx' δ hδ h0
    rw [← hδ' y]
    have hJy : p y ∈ J := by
      have : p2 (p y) = 0 := hy
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    apply hdk δ' (by rw [ho1]; exact hδ'mem) (p y) hJy
  · intro j
    rw [← hn j]
    exact hn' j
