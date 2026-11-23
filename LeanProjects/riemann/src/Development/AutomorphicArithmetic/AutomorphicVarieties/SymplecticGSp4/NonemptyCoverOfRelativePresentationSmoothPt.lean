import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem rp_coeff {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem rp_ext {O σ Q : Type} [CommRing O] [Fintype σ] [AddCommGroup Q] [Module O Q]
    (D E : MvPowerSeries σ O →ₗ[O] Q)
    (hD : ∀ f g, D (f * g) = MvPowerSeries.constantCoeff f • D g + MvPowerSeries.constantCoeff g • D f)
    (hE : ∀ f g, E (f * g) = MvPowerSeries.constantCoeff f • E g + MvPowerSeries.constantCoeff g • E f)
    (hX : ∀ s, D (MvPowerSeries.X s) = E (MvPowerSeries.X s)) (f : MvPowerSeries σ O) : D f = E f := by
  let W' := WPres.free O (fun _ : σ => (0 : ℤ))
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  have h0 := (der_extend O _ ℤ W' h' Q).2 (D - E) (fun f g => by
    rw [ho, ho]
    simp only [LinearMap.sub_apply]
    rw [hD, hE, smul_sub, smul_sub]
    abel) (fun (s : σ) => by
    show D (MvPowerSeries.X s) - E (MvPowerSeries.X s) = 0
    rw [hX, sub_self])
  rw [sub_eq_zero.1 h0]

private theorem rp_ex {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) :
    ∃ L : MvPowerSeries σ O →ₗ[O] O,
      (∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f) ∧
      (∀ s, L (MvPowerSeries.X s) = d s) ∧
      ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := by
  classical
  let L : MvPowerSeries σ O →ₗ[O] O :=
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries σ O →ₗ[O] O).smulRight (d s)
  have hL : ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := fun f => by
    simp [L]
  refine ⟨L, fun f g => ?_, fun s => ?_, hL⟩
  · rw [hL, hL, hL]
    simp only [rp_coeff, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  · rw [hL]
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

private theorem rp_lift {O X B R S Q : Type} [CommRing O] [AddCommGroup X] [CommRing B] [Algebra O B] [CommRing R]
    [Algebra O R] [CommRing S] [Algebra O S] [AddCommGroup Q] [Module O Q]
    (WB : WPres O X B) (hB : WB.HasOrigin) (W : WPres O X R) (h : W.HasOrigin) {τ : Type} (e : WB.σ ⊕ τ ≃ W.σ)
    (hwt : ∀ s, W.wt (e (.inl s)) = WB.wt s)
    (hker : RingHom.ker W.π = (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)))
    (qh : R →ₐ[O] S) (x₀ : S →ₐ[O] O) (hx : x₀.comp qh = W.origin h) (p : O →ₗ[O] Q) (hp : Function.Surjective p)
    (j : X) (D : S →ₗ[O] Q) (hD : D ∈ PtDer x₀ Q) (hDw : ∀ s, W.wt s ≠ j → D (qh (W.z s)) = 0)
    (D₁ : B →ₗ[O] O) (hD₁ : D₁ ∈ PtDer (WB.origin hB) O) (hD₁w : ∀ s, WB.wt s ≠ j → D₁ (WB.z s) = 0)
    (hpD : ∀ s, p (D₁ (WB.z s)) = D (qh (W.z (e (.inl s))))) :
    ∃ D' ∈ PtDer (W.origin h) O, HasWt W.part j D' ∧ ∀ f, p (D' f) = D (qh f) := by
  classical
  have hd : ∀ s : W.σ, ∃ d : O, (∀ t, s = e (.inl t) → d = D₁ (WB.z t)) ∧ (W.wt s ≠ j → d = 0) ∧
      p d = D (qh (W.z s)) := fun s => by
    obtain ⟨u, rfl⟩ := e.surjective s
    rcases u with t | t
    · refine ⟨D₁ (WB.z t), fun t' ht => ?_, fun hj => hD₁w t (by rwa [← hwt]), hpD t⟩
      rw [Sum.inl.inj (e.injective ht)]
    · by_cases hj : W.wt (e (.inr t)) = j
      · obtain ⟨a, ha⟩ := hp (D (qh (W.z (e (.inr t)))))
        exact ⟨a, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun h' => absurd hj h', ha⟩
      · exact ⟨0, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun _ => rfl,
          by rw [map_zero, hDw _ hj]⟩
  choose d hd1 hd2 hd3 using hd
  obtain ⟨L, hL, hLX, hLs⟩ := rp_ex d
  have hren : ∀ g, L (MvPowerSeries.rename (fun s => e (.inl s)) g) = D₁ (WB.π g) :=
    rp_ext (L ∘ₗ (MvPowerSeries.rename (fun s => e (.inl s)) : MvPowerSeries WB.σ O →ₐ[O] _).toLinearMap)
      (D₁ ∘ₗ WB.π.toLinearMap)
      (fun f g => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hL,
          MvPowerSeries.constantCoeff_rename])
      (fun f g => by
        have h1 : D₁ (WB.π f * WB.π g) = _ := hD₁ _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, h1, WB.origin_π])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPowerSeries.rename_X, hLX]
        exact hd1 _ s rfl)
  have hk : ∀ f, W.π f = 0 → L f = 0 := fun f hf => by
    have hf' : f ∈ RingHom.ker W.π := hf
    have key : ∀ f ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)), L f = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hg' : WB.π g = 0 := hg
        rw [hren, hg', map_zero]
      | zero => exact map_zero L
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x hx hx' =>
        have : x ∈ RingHom.ker W.π := by rw [hker]; exact hx
        rw [smul_eq_mul, hL, hx', h x this, smul_zero, zero_smul, add_zero]
    exact key f (hker ▸ hf')
  have hs : Function.Surjective W.π.toLinearMap := W.surj
  let E : R →ₗ[O] O := ((LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)) ∘ₗ
    (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hE : ∀ f, E (W.π f) = L f := fun f => by
    have : (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)
      ((W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f)) = _
    rw [this]
    rfl
  have hEd : ∀ a b, E (a * b) = W.origin h a • E b + W.origin h b • E a := fun a b => by
    obtain ⟨f, rfl⟩ := W.surj a
    obtain ⟨g, rfl⟩ := W.surj b
    rw [← map_mul, hE, hE, hE, hL, W.origin_π, W.origin_π]
  have hxo : ∀ f, x₀ (qh (W.π f)) = MvPowerSeries.constantCoeff f := fun f => by
    rw [← AlgHom.comp_apply, hx, W.origin_π]
  have hred : ∀ f, D (qh (W.π f)) = p (L f) :=
    rp_ext (D ∘ₗ (qh.comp W.π).toLinearMap) (p ∘ₗ L)
      (fun f g => by
        have h1 : D (qh (W.π f) * qh (W.π g)) = _ := hD _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_mul, h1, hxo])
      (fun f g => by simp only [LinearMap.comp_apply, hL, map_add, map_smul])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, hLX, hd3]
        rfl)
  refine ⟨E, hEd, fun i hi a ha => ?_, fun a => ?_⟩
  · obtain ⟨f, hf, hfa⟩ := ha
    have hfa' : W.π f = a := hfa
    rw [← hfa', hE, hLs]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : W.wt s = j
    · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
    · rw [hd2 s hs, smul_zero]
  · obtain ⟨f, hf⟩ := W.surj a
    rw [← hf, hE, hred]

private theorem rp_rename_mem {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ τ : Type} [Finite σ]
    (u : σ → τ) (wt : τ → X) (ws : σ → X) (h : ∀ s, wt (u s) = ws s) {j : X} {g : MvPowerSeries σ O}
    (hg : g ∈ wtPart O ws j) : MvPowerSeries.rename u g ∈ wtPart O wt j := fun n hn => by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun d hd => hg d fun hj => hn ?_
  have hd' : Finsupp.mapDomain u d = n := by simpa using hd
  rw [← hd', ← hj, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul])]
  simp [h]

private theorem rp_homog {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ : Type} [Fintype σ]
    (wt : σ → X) {κ : Type} [Finite κ] (g : κ → MvPowerSeries σ O) (c : κ → X)
    (hg : ∀ i, g i ∈ wtPart O wt (c i)) : IsHomog O wt (Ideal.span (Set.range g)) := by
  have hp : ∀ i, g i ∈ (WPres.free O wt).part (c i) := fun i => ⟨g i, hg i, rfl⟩
  exact (homog_span O _ X (WPres.free O wt) κ (fun i => ⟨g i, (WPres.free O wt).part_le_A (hp i)⟩) c hp).1

private theorem rp_card {α β X : Type} [Finite α] [Finite β] (a : α → X) (b : β → X) (j : X) :
    Nat.card {i // Sum.elim a b i = j} = Nat.card {i // a i = j} + Nat.card {i // b i = j} := by
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  rfl

theorem UpperTheory.nonempty_cover_of_relative_presentation_smoothPt :
    ∀ (O X : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X] (B U : Type) [CommRing B] [Algebra O B] [CommRing U] [Algebra O U] (WB : WPres O X B) (hB : WB.HasOrigin) (i : B →ₐ[O] U) (W : WPres O X U) (h : W.HasOrigin) (τ κ : Type) [Fintype τ] (e : WB.σ ⊕ τ ≃ W.σ) (f : κ → MvPowerSeries W.σ O) (wf : κ → X) (n : X → ℕ), IsRelPres WB i W e f wf → SmoothPt WB.part (WB.origin hB) n → Nonempty (Cover WB hB i W h e wf n) := by
  intro O X _ _ _ _ _ _ _ _ _ B U _ _ _ _ WB hB i W h τ κ _ e f wf n hrel hsm
  obtain ⟨he1, he2, hf, hker⟩ := hrel
  obtain ⟨τ₀, _, w, φ, hφ, hdim⟩ := hsm
  set J : Ideal (MvPowerSeries W.σ O) := (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) with hJ
  have hJh : IsHomog O W.wt J := by
    obtain ⟨k, f0, c0, hf0, h0⟩ := ker_gen O X WB.σ WB.wt _ WB.homog
    rw [hJ, h0, Ideal.map_span, ← Set.range_comp]
    exact rp_homog W.wt _ c0 fun t => rp_rename_mem _ W.wt WB.wt he1 (hf0 t)
  have hle : ∀ F ∈ J, W.π F = 0 := fun F hF => (hker ▸ Ideal.mem_sup_left hF : F ∈ RingHom.ker W.π)
  let qh : (MvPowerSeries W.σ O ⧸ J) →ₐ[O] U := Ideal.Quotient.liftₐ J W.π hle
  have hqh : ∀ F, qh (Ideal.Quotient.mk J F) = W.π F := fun _ => rfl
  haveI : Nontrivial (MvPowerSeries W.σ O ⧸ J) := ((W.origin h).comp qh).toRingHom.domain_nontrivial
  haveI := co_mvps O O W.σ
  haveI : IsCO O (MvPowerSeries W.σ O ⧸ J) :=
    co_quot O _ _ (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hkm : RingHom.ker (Ideal.Quotient.mkₐ O J) = J := Ideal.Quotient.mkₐ_ker O J
  let WA : WPres O X (MvPowerSeries W.σ O ⧸ J) :=
    { σ := W.σ, wt := W.wt, π := Ideal.Quotient.mkₐ O J, surj := Ideal.Quotient.mkₐ_surjective O J
      homog := by rw [hkm]; exact hJh }
  obtain ⟨h', ψ, hψ, -⟩ := chart_add O X _ WB hB τ₀ w φ hφ _ WA τ e he1 hkm
  let ρ : MvPowerSeries WB.σ O →ₐ[O] (MvPowerSeries W.σ O ⧸ J) :=
    (Ideal.Quotient.mkₐ O J).comp (MvPowerSeries.rename fun s => e (.inl s))
  have hρ : ∀ F ∈ RingHom.ker WB.π, ρ F = 0 := fun F hF =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hF)
  let iP : B →ₐ[O] (MvPowerSeries W.σ O ⧸ J) :=
    (Ideal.Quotient.liftₐ (RingHom.ker WB.π) ρ hρ).comp
      (Ideal.quotientKerAlgEquivOfSurjective WB.surj).symm.toAlgHom
  have hiP : ∀ F, iP (WB.π F) = ρ F := fun F => by
    have : (Ideal.quotientKerAlgEquivOfSurjective WB.surj).symm (WB.π F) = Ideal.Quotient.mk _ F := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show Ideal.Quotient.liftₐ (RingHom.ker WB.π) ρ hρ
      ((Ideal.quotientKerAlgEquivOfSurjective WB.surj).symm (WB.π F)) = _
    rw [this]
    rfl
  have hor : (W.origin h).comp qh = WA.origin h' := AlgHom.ext fun y => by
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (W.origin_π h F).trans (WA.origin_π h' F).symm
  have hzl : ∀ s, W.z (e (.inl s)) = i (WB.z s) := fun s => by
    rw [WPres.z, WPres.z, ← he2, MvPowerSeries.rename_X]
  refine ⟨{
    P := MvPowerSeries W.σ O ⧸ J
    WP := WA
    org := h'
    p := qh
    iP := iP
    g := fun u => Ideal.Quotient.mk J (f u)
    wts := fun s => ⟨s, rfl⟩
    surj := fun y => ?_
    part := fun j => ?_
    comp := AlgHom.ext fun y => ?_
    org_p := hor
    hg := fun u => ⟨_, hf u, rfl⟩
    ker := ?_
    smooth := ⟨τ₀ ⊕ τ, inferInstance, _, ψ, hψ, fun j => ?_⟩
    der := fun a j Db hDb DB hDB hw hi hz => ?_ }⟩
  · obtain ⟨F, rfl⟩ := W.surj y
    exact ⟨_, hqh F⟩
  · ext y
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
      exact ⟨F, hF, rfl⟩
  · obtain ⟨F, rfl⟩ := WB.surj y
    rw [AlgHom.comp_apply, hiP, ← he2]
    rfl
  · refine le_antisymm (fun y hy => ?_) (Ideal.span_le.2 ?_)
    · obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
      have h3 : F ∈ J ⊔ Ideal.span (Set.range f) := by
        rw [← hker]
        exact hy
      have h4 : J ⊔ Ideal.span (Set.range f) ≤
          (Ideal.span (Set.range fun k => Ideal.Quotient.mk J (f k))).comap (Ideal.Quotient.mk J) := by
        refine sup_le (fun y hy => ?_) (Ideal.span_le.2 ?_)
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
          exact zero_mem _
        · rintro _ ⟨k, rfl⟩
          exact Ideal.subset_span ⟨k, rfl⟩
      exact h4 h3
    · rintro _ ⟨k, rfl⟩
      exact (hker ▸ Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩) : f k ∈ RingHom.ker W.π)
  · rw [rp_card, hdim]
  · have hB0 : ∀ s, WB.wt s ≠ j → DB (WB.z s) = 0 := fun s hs => hw _ hs _ (WB.z_mem s)
    refine rp_lift WB hB WA h' e he1 hkm qh (W.origin h) hor (Ideal.Quotient.mkₐ O _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective O _) j Db hDb (fun s hs => ?_) DB hDB hB0 fun s => ?_
    · obtain ⟨s | t, rfl⟩ := e.surjective s
      · show Db (W.z (e (.inl s))) = 0
        rw [hzl, hi, hB0 s (by rw [← he1]; exact hs), map_zero]
      · exact hz t hs
    · show _ = Db (W.z (e (.inl s)))
      rw [hzl, hi]
      rfl
