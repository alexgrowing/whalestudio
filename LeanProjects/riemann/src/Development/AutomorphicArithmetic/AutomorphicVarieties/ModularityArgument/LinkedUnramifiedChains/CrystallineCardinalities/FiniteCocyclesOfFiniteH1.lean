import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnrLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LevelS
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply

noncomputable section Helpers

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Z.J

section Count

variable {k G M : Type} [CommRing k] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k G M)

private def cls (L : Submodule k (H1 ρ)) : Set (G → M) :=
  {z | ∃ hz : z ∈ Z1 ρ, (Submodule.Quotient.mk ⟨z, hz⟩ : H1 ρ) ∈ L}

private theorem card_cls (h : ContAction ρ) (L : Submodule k (H1 ρ)) :
    (cls ρ L).ncard = Nat.card (B1 ρ) * Nat.card L := by
  have e1 : cls ρ L = Subtype.val '' ((fun z : Z1 ρ => (Submodule.Quotient.mk z : H1 ρ)) ⁻¹' (L : Set (H1 ρ))) := by
    ext z
    constructor
    · rintro ⟨hz, h⟩; exact ⟨⟨z, hz⟩, h, rfl⟩
    · rintro ⟨z, h, rfl⟩; exact ⟨z.2, h⟩
  have e2 := (Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet
    ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup (L : Set (H1 ρ)))).trans (Nat.card_prod _ _)
  have e3 : Nat.card ((B1 ρ).comap (Z1 ρ).subtype) = Nat.card (B1 ρ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles ρ h)).toEquiv
  rw [e1, Set.ncard_image_of_injective _ Subtype.val_injective, ← e3]
  exact e2

omit [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] in
private theorem card_coboundaries_mul_card_h0 : Nat.card (B1 ρ) * Nat.card (H0 ρ) = Nat.card M := by
  have e : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext m
    rw [LinearMap.mem_ker, funext_iff]
    exact forall_congr' fun g => sub_eq_zero
  rw [← e, Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 ρ)), mul_comm]
  congr 1
  exact (Nat.card_congr (d0 ρ).quotKerEquivRange.toEquiv).symm

private theorem finite_z1_of_finite_h1 [Finite M] [Finite (H1 ρ)] : Finite (Z1 ρ) := by
  have : Finite (B1 ρ) := Finite.of_surjective _ (d0 ρ).surjective_rangeRestrict
  have : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  exact Finite.of_equiv (H1 ρ × (B1 ρ).comap (Z1 ρ).subtype)
    (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup)).symm

private theorem zc_iff (τ : Representation ℤ G M) (e : ∀ g m, ρ g m = τ g m) (z : G → M) : z ∈ Zc τ ↔ z ∈ Z1 ρ :=
  and_congr (IsLocallyConstant.iff_continuous z) (by simp only [← e])

end Count

private theorem ex_cls {n : ℕ} {G M : Type} [Group G] [TopologicalSpace G] [AddCommGroup M] [Module (ZMod n) M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod n) G M) (N : AddSubgroup (G → M))
    (h1 : ∀ z ∈ B1 ρ, z ∈ N) (h2 : ∀ z ∈ N, z ∈ Z1 ρ) :
    ∃ L : Submodule (ZMod n) (H1 ρ), cls ρ L = N := by
  refine ⟨((AddSubgroup.toZModSubmodule n N).comap (Z1 ρ).subtype).map (Submodule.mkQ _), ?_⟩
  ext z
  constructor
  · rintro ⟨hz, y, hy, e⟩
    have e' : y.1 - z ∈ B1 ρ := (Submodule.Quotient.eq ((B1 ρ).comap (Z1 ρ).subtype)).1 e
    have := N.sub_mem hy (h1 _ e')
    simpa using this
  · intro hz
    exact ⟨h2 z hz, ⟨z, _⟩, hz, rfl⟩

private theorem core {n : ℕ} {Γ M W : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module (ZMod n) M]
    [TopologicalSpace M] [DiscreteTopology M] [Finite M] [Fintype W] {D : W → Type} [∀ w, Group (D w)]
    [∀ w, TopologicalSpace (D w)] (ρ : Representation (ZMod n) Γ M) (τ : Representation ℤ Γ M) (e : ∀ g m, ρ g m = τ g m)
    (ι : ∀ w, D w →* Γ) (hι : ∀ w, Continuous (ι w)) (a b : ℕ) (h : ContAction ρ) [Finite (H1 ρ)]
    (gw : ∀ L : LocCond ρ ι, Nat.card (H0 ρ) * ∏ w, Nat.card (L w) ≤
      Nat.card (Sel ρ ι hι L) * b * (∏ w, Nat.card (H0 (ρ.comp (ι w)))) * a)
    (Z : ∀ w, AddSubgroup (D w → M)) (h1 : ∀ w, (Z w : Set (D w → M)) ⊆ Zc (τ.comp (ι w)))
    (h2 : ∀ w (Y : M), (fun s => τ (ι w s) Y - Y) ∈ Z w) :
    (Zc τ).Finite ∧ Nat.card M * ∏ w, Nat.card (Z w) ≤
      {z | z ∈ Zc τ ∧ ∀ w, (fun s => z (ι w s)) ∈ Z w}.ncard * b * a * Nat.card M ^ Fintype.card W := by
  have f := finite_z1_of_finite_h1 ρ
  refine ⟨(Set.toFinite (Z1 ρ : Set (Γ → M))).subset fun z hz => (zc_iff ρ τ e z).1 hz, ?_⟩
  choose L hL using fun w => ex_cls (ρ.comp (ι w)) (Z w)
    (fun z hz => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
      have : z = fun s => τ (ι w s) m - m := funext fun s => (hm s).trans (by rw [← e]; rfl)
      exact this ▸ h2 w m)
    (fun z hz => (zc_iff _ (τ.comp (ι w)) (fun g m => e _ m) z).1 (h1 w hz))
  have e1 : {z | z ∈ Zc τ ∧ ∀ w, (fun s => z (ι w s)) ∈ Z w} = cls ρ (Sel ρ ι hι L) := by
    ext z
    constructor
    · rintro ⟨hz, hw⟩
      refine ⟨(zc_iff ρ τ e z).1 hz, (mem_Sel _ _ _ _ _).2 fun w => ?_⟩
      have : z ∘ ι w ∈ cls (ρ.comp (ι w)) (L w) := by rw [hL]; exact hw w
      exact this.2
    · rintro ⟨hz, hw⟩
      refine ⟨(zc_iff ρ τ e z).2 hz, fun w => ?_⟩
      have : z ∘ ι w ∈ cls (ρ.comp (ι w)) (L w) := ⟨(restrictCocycles1 ρ (ι w) (hι w) ⟨z, hz⟩).2, (mem_Sel _ _ _ _ _).1 hw w⟩
      rwa [hL] at this
  have e4 : ∀ w, Nat.card (Z w) = Nat.card (B1 (ρ.comp (ι w))) * Nat.card (L w) := fun w => by
    rw [← card_cls _ (h.comp' (hι w)), hL]; rfl
  have e5 : Nat.card M ^ Fintype.card W =
      (∏ w, Nat.card (B1 (ρ.comp (ι w)))) * ∏ w, Nat.card (H0 (ρ.comp (ι w))) := by
    rw [← Finset.prod_mul_distrib]
    simp only [card_coboundaries_mul_card_h0, Finset.prod_const, Finset.card_univ]
  rw [e1, card_cls _ h, e5]
  simp only [e4, Finset.prod_mul_distrib]
  have e6 := Nat.mul_le_mul_left (Nat.card (B1 ρ) * ∏ w, Nat.card (B1 (ρ.comp (ι w)))) (gw L)
  rw [← card_coboundaries_mul_card_h0 ρ]
  convert e6 using 1 <;> ring

private theorem desc {Γ' Γ N : Type} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [Group Γ]
    [TopologicalSpace Γ] [T2Space Γ] [AddCommGroup N] (p : Γ' →* Γ) (hp : Continuous p) (hs : Function.Surjective p)
    (ρ : Representation ℤ Γ N) (T : Set Γ') (hT : p.ker = (Subgroup.normalClosure T).topologicalClosure)
    (z : Γ' → N) (hz : z ∈ Zc (ρ.comp p)) (h0 : ∀ g ∈ T, z g = 0) : ∃ y ∈ Zc ρ, ∀ g, y (p g) = z g := by
  have hm : ∀ s t, z (s * t) = z s + ρ (p s) (z t) := hz.2
  have h1 : z 1 = 0 := by simpa using hm 1 1
  let H : Subgroup Γ' :=
    { carrier := {g | p g = 1 ∧ z g = 0}
      one_mem' := ⟨map_one p, h1⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, mul_one], by rw [hm, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨by rw [map_inv, ha.1, inv_one], by
        have := hm a⁻¹ a
        rw [inv_mul_cancel, h1, ha.2, map_zero, add_zero] at this
        exact this.symm⟩ }
  haveI : H.Normal := ⟨fun a ha g => ⟨by simp [ha.1], by
    rw [hm, hm, ha.2, map_zero, add_zero, map_mul, ha.1, mul_one, ← hm, mul_inv_cancel, h1]⟩⟩
  have hH : p.ker ≤ H := by
    have hT' : T ⊆ p.ker := by
      rw [hT]
      exact Subgroup.subset_normalClosure.trans (Subgroup.le_topologicalClosure _)
    rw [hT]
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => ⟨hT' hg, h0 g hg⟩)
      ((isClosed_singleton.preimage hp).inter (hz.1.isClosed_fiber 0))
  have hy : ∀ g, z (Function.surjInv hs (p g)) = z g := fun g => by
    have : z (g⁻¹ * Function.surjInv hs (p g)) = 0 :=
      (hH (by rw [MonoidHom.mem_ker, map_mul, Function.surjInv_eq hs, map_inv, inv_mul_cancel])).2
    conv_lhs => rw [← mul_inv_cancel_left g (Function.surjInv hs (p g)), hm, this, map_zero, add_zero]
  refine ⟨fun g => z (Function.surjInv hs g), ⟨fun s => ?_, fun s t => ?_⟩, hy⟩
  · rw [← (hp.isClosedMap.isQuotientMap hp hs).isOpen_preimage]
    convert hz.1 s using 1
    ext g
    simp only [Set.mem_preimage, hy]
  · obtain ⟨s, rfl⟩ := hs s
    obtain ⟨t, rfl⟩ := hs t
    beta_reduce
    rw [← map_mul, hy, hy, hy, hm]

private theorem tran {D G N : Type} [Group D] [TopologicalSpace D] [CompactSpace D] [Group G] [TopologicalSpace G] [T2Space G]
    [AddCommGroup N] (ι : D →* G) (hc : Continuous ι) (hi : Function.Injective ι) (H : Subgroup G) (hH : ι.range = H)
    (τ : Representation ℤ G N) (Z : AddSubgroup (D → N)) (h1 : (Z : Set (D → N)) ⊆ Zc (τ.comp ι))
    (h2 : ∀ Y : N, (fun s => τ (ι s) Y - Y) ∈ Z) :
    ∃ Z' : AddSubgroup (H → N), (Z' : Set (H → N)) ⊆ Zc (τ.comp H.subtype) ∧ (∀ Y : N, (fun s : H => τ s.1 Y - Y) ∈ Z') ∧
      Nat.card Z = Nat.card Z' ∧ ∀ z : G → N, (fun s : H => z s.1) ∈ Z' → (fun s => z (ι s)) ∈ Z := by
  subst hH
  have hj : Continuous ι.rangeRestrict := hc.subtype_mk _
  have hb : Function.Bijective ι.rangeRestrict :=
    ⟨fun a b h => hi (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  let r : (ι.range → N) →+ (D → N) :=
    { toFun := fun z s => z (ι.rangeRestrict s), map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨Z.comap r, fun z hz => ⟨fun s => ?_, fun s t => ?_⟩, h2, ?_, fun z hz => hz⟩
  · rw [← (hj.isClosedMap.isQuotientMap hj hb.2).isOpen_preimage]
    exact (h1 hz).1 s
  · obtain ⟨s, rfl⟩ := hb.2 s
    obtain ⟨t, rfl⟩ := hb.2 t
    rw [← map_mul]
    exact (h1 hz).2 s t
  · exact (Nat.card_congr (((Equiv.ofBijective _ hb).symm.arrowCongr (Equiv.refl N)).subtypeEquiv fun z => Iff.rfl)).symm

private theorem numer {V W : Type} [Fintype V] [Fintype W] (m : V → W) (hm : Function.Injective m) (f : V → ℕ) (g : W → ℕ)
    (n x : ℕ) (hn : 0 < n) (h1 : ∀ v, f v = g (m v)) (h2 : ∀ w, w ∉ Set.range m → n ≤ g w)
    (h : n * ∏ w, g w ≤ x * n ^ Fintype.card W) : n * ∏ v, f v ≤ x * n ^ Fintype.card V := by
  classical
  let T : Finset W := Finset.univ.map ⟨m, hm⟩
  have e1 : ∏ w ∈ T, g w = ∏ v, f v := by simp [T, h1]
  have e2 : n ^ Tᶜ.card ≤ ∏ w ∈ Tᶜ, g w := Finset.pow_card_le_prod _ _ _ fun w hw => h2 w (by simpa [T] using hw)
  have e3 : T.card = Fintype.card V := by simp [T]
  rw [← Finset.prod_mul_prod_compl T, ← Finset.card_add_card_compl T, e1, e3, pow_add, ← mul_assoc, ← mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right ((Nat.mul_le_mul_left _ e2).trans h) (Nat.pow_pos hn)

private def zrep (n : ℕ) {Γ M : Type} [Group Γ] [AddCommGroup M] [Module (ZMod n) M] (ρ : Representation ℤ Γ M) :
    Representation (ZMod n) Γ M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    change ρ 1 m = m
    simp
  map_mul' g h := LinearMap.ext fun m => by
    change ρ (g * h) m = ρ g (ρ h m)
    simp

private theorem lc_orb {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M]
    (ρ : Representation ℤ Γ M) (h : IsOpen (ρ.ker : Set Γ)) (m : M) : IsLocallyConstant fun g => ρ g m := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' (ρ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have : ρ (g⁻¹ * x) = 1 := hx
  rw [← mul_inv_cancel_left g x, map_mul, this, mul_one]

private theorem bare (P : GC.Hypotheses₂) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ContainsAbove T l)
    (ε : GS Ω (T : Set (HeightOneSpectrum (𝓞 F))) →* ℤ_[l]ˣ) (hε : ∀ g, ε (toGS Ω _ g) = cycZ F Ω l g)
    (A : T → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (A v) v.1) (c : InfinitePlace F → G F Ω) (hc : ∀ w, IsCCAt w (c w))
    (k : ℕ) (hk0 : 0 < k) (N : Type) [AddCommGroup N] [Finite N]
    (τ : Representation ℤ (GS Ω (T : Set (HeightOneSpectrum (𝓞 F)))) N) (hk : ∀ x : N, l ^ k • x = 0)
    (ho : IsOpen (τ.ker : Set (GS Ω (T : Set (HeightOneSpectrum (𝓞 F))))))
    (Z : ∀ w : T, AddSubgroup (Dec (F := F) (A w) → N)) (h1 : ∀ w, (Z w : Set _) ⊆ Zc (τ.comp (locFam T A w)))
    (h2 : ∀ w (Y : N), (fun s => τ (locFam T A w s) Y - Y) ∈ Z w) :
    (Zc τ).Finite ∧ Nat.card N * ∏ w, Nat.card (Z w) ≤
      {z | z ∈ Zc τ ∧ ∀ w, (fun s => z (locFam T A w s)) ∈ Z w}.ncard * (HomMu l k ε τ).ncard *
        (∏ w, {x : N | τ (toGS Ω _ (c w)) x = x}.ncard) * Nat.card N ^ Fintype.card T := by
  classical
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ k)) N) := ⟨AddCommGroup.zmodModule hk⟩
  letI : TopologicalSpace N := ⊥
  haveI : DiscreteTopology N := ⟨rfl⟩
  let ρ := zrep (l ^ k) τ
  have hρ : ∀ g m, ρ g m = τ g m := fun _ _ => rfl
  have hcont : ContAction ρ := continuous_prod_of_discrete_right.2 fun m => (lc_orb τ ho m).continuous
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := k) (S := T) hT
  have hcont' : ContAction (twDual μ ρ) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hcont
  have hμε : ∀ g, ((μ g : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) = PadicInt.toZModPow k ((ε g : ℤ_[l]ˣ) : ℤ_[l]) := fun g => by
    obtain ⟨g, rfl⟩ : ∃ s, toGS Ω _ s = g := QuotientGroup.mk_surjective g
    rw [hε, ← MonoidHom.comp_apply, hμ]
    rfl
  haveI : Finite (TDual (ZMod (l ^ k)) N) := GlobalTheory.DualSide.finite_TDual
  haveI := (P.gf F Ω l k N T ρ hk0 hT hcont).2.1
  haveI := (P.gf F Ω l k _ T (twDual μ ρ) hk0 hT hcont').2.1
  have harch : archH0Card T ρ c = ∏ w, {x : N | τ (toGS Ω _ (c w)) x = x}.ncard := by
    rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
      Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w]
    rfl
  have hdual : Nat.card (H0 (twDual μ ρ)) ≤ (HomMu l k ε τ).ncard := by
    haveI : Finite (N →+ ZMod (l ^ k)) := DFunLike.finite _
    refine Nat.card_le_card_of_injective (β := HomMu l k ε τ)
      (fun y => ⟨AddMonoidHom.mk' (fun x => y.1 x) (fun a b => map_add (show N →ₗ[ZMod (l ^ k)] ZMod (l ^ k) from y.1) a b), fun s x => ?_⟩) fun a b h => ?_
    · have := congrArg (fun φ : TDual (ZMod (l ^ k)) N => φ (ρ s x)) (y.2 s)
      beta_reduce at this
      rw [twDual_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hμε] at this
      exact this.symm
    · exact Subtype.ext (TDual.ext fun x => DFunLike.congr_fun (congrArg Subtype.val h) x)
  refine core ρ τ hρ (locFam T A) (continuous_locFam T A) _ _ hcont (fun L => ?_) Z h1 h2
  have h := P.gw F Ω l k N T ρ hk0 hl hT hcont μ hμ A hA c (fun w _ => hc w) L
  rw [← harch]
  refine le_trans ?_ (h.ge.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdual))))
  exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ Nat.card_pos)

end Helpers

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

theorem UpperTheory.V.Z.J.gwlOf :
    GC.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (κ : Type) [Field κ] (Φ : Frame l κ) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] S K π ι A pl e c, GC.FLink (F := F) (Ω := Ω) l Φ S K π ι A pl e c → GWL Φ := by
  intro P l _ κ _ Φ F Ω _ _ _ _ _ S K π ι A pl e c h k hk0 N _ _ ρ hk ho Z h1 h2
  classical
  haveI := h.real
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨A', hA', hAA⟩ : ∃ A' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ValuationSubring Ω,
      (∀ v, IsPlaceOver (A' v) v) ∧ ∀ v, A' (pl v) = A v := by
    refine ⟨Function.extend pl A fun v => (exists_isPlaceOver Ω v).choose, fun q => ?_, h.loc.inj.extend_apply _ _⟩
    by_cases hq : ∃ v, pl v = q
    · obtain ⟨v, rfl⟩ := hq
      rw [h.loc.inj.extend_apply]
      exact h.loc.isOver v
    · rw [Function.extend_apply' _ _ _ hq]
      exact (exists_isPlaceOver Ω q).choose_spec
  obtain ⟨S', p, hSS, hp, hps, hπ, hker⟩ := GC.levelS F Ω l S K Φ.Γ π h.g
  have hS' : ContainsAbove S' l := fun v hv => hSS (h.g.above v hv)
  have hS : ∀ q, q ∈ S ↔ ∃ v, pl v = q := fun q =>
    ⟨fun hq => (h.loc.mem q).2 (h.only q hq), fun hq => h.g.above q ((h.loc.mem q).1 hq)⟩
  have hZ : ∀ q : S', ∃ Z' : AddSubgroup (Dec (F := F) (A' q.1) → N),
      (Z' : Set _) ⊆ Zc ((ρ.comp π).comp (Dec (F := F) (A' q.1)).subtype) ∧
      (∀ Y : N, (fun s : Dec (F := F) (A' q.1) => ρ (π s.1) Y - Y) ∈ Z') ∧
      (∀ v, pl v = q.1 → Nat.card (Z v) = Nat.card Z' ∧
        ∀ z : G F Ω → N, (fun s : Dec (F := F) (A' q.1) => z s.1) ∈ Z' → (fun s => z (ι v s)) ∈ Z v) ∧
      (q.1 ∉ S → Nat.card N ≤ Nat.card Z' ∧
        ∀ z ∈ Z', ∃ Y : N, ∀ s : Dec (F := F) (A' q.1), s.1 ∈ Ine (F := F) (A' q.1) → z s = ρ (π s.1) Y - Y) := by
    rintro ⟨q, hq'⟩
    by_cases hq : q ∈ S
    · obtain ⟨v, rfl⟩ := (hS q).1 hq
      have hl : Φ.loc v = π.comp (ι v) := MonoidHom.ext (h.loc_eq v)
      obtain ⟨Z', a1, a2, a3⟩ := tran (ι v) (h.loc.cont v) (h.loc.ι_inj v) (Dec (F := F) (A' (pl v)))
        (by rw [hAA, h.loc.range]) (ρ.comp π) (Z v) (by have := h1 v; rwa [hl] at this)
        (by have := h2 v; rwa [hl] at this)
      refine ⟨Z', a1, a2, fun v' hv => ?_, fun hq' => absurd hq hq'⟩
      obtain rfl := h.loc.inj hv
      exact a3
    · obtain ⟨Z', -, a1, a2, a3, a4⟩ := unrLow F Ω (A' q) q (hA' q) N ((ρ.comp π).comp (Dec (F := F) (A' q)).subtype)
        (ho.preimage (h.g.cont.comp continuous_subtype_val))
      exact ⟨Z', a1, a2, fun v hv => absurd ((hS q).2 ⟨v, hv⟩) hq, fun _ => ⟨a4, a3⟩⟩
  choose Z' b1 b2 b3 b4 using hZ
  subst hπ
  obtain ⟨f, hb⟩ := bare P l h.g.odd S' hS' (Φ.eps.comp p) h.eps (fun q => A' q.1) (fun q => hA' q.1)
    (fun w => c (e.symm w)) (fun w => by simpa using h.cc (e.symm w)) k hk0 N (ρ.comp p) hk (ho.preimage hp) Z' b1 b2
  have hinj : Function.Injective fun z : Φ.Γ → N => z ∘ p := hps.injective_comp_right
  have hf : (ZL Φ ρ fun v => Z v).Finite :=
    Set.Finite.of_finite_image (f.subset (by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨hz.1.1.comp_continuous hp, fun s t => by simpa using hz.1.2 (p s) (p t)⟩)) hinj.injOn
  refine ⟨hf, numer (fun v => (⟨pl v, hSS ((hS _).2 ⟨v, rfl⟩)⟩ : S')) (fun a b hab => h.loc.inj (congrArg Subtype.val hab))
    _ (fun q => Nat.card (Z' q)) _ _ Nat.card_pos (fun v => (b3 _ v rfl).1)
    (fun q hq => (b4 q fun hq' => hq (let ⟨v, hv⟩ := (hS _).1 hq'; ⟨v, Subtype.ext hv⟩)).1) (hb.trans ?_)⟩
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul ?_ (le_of_eq ?_)) (le_of_eq ?_))
  · refine le_trans (Set.ncard_le_ncard ?_ (hf.image fun z => z ∘ p)) (Set.ncard_image_le hf)
    rintro z ⟨hz, hw⟩
    obtain ⟨y, hy, hyz⟩ := desc p hp hps ρ _ (hker A' hA') z hz (by
      intro x hx
      obtain ⟨q, g, hg, rfl⟩ := Set.mem_iUnion.1 hx
      obtain ⟨Y, hY⟩ := (b4 ⟨q.1, q.2.1⟩ q.2.2).2 _ (hw _)
      have hg1 : g ∈ (p.comp (toGS Ω _)).ker := by
        rw [h.g.ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨q.1, q.2.2, A' q.1, hA' q.1, hg⟩
      have := hY ⟨g, Ine_le_Dec _ hg.1⟩ hg.1
      rw [MonoidHom.mem_ker.1 hg1, map_one, Module.End.one_apply, sub_self] at this
      exact this)
    refine ⟨y, ⟨hy, fun v => ?_⟩, funext hyz⟩
    have := (b3 ⟨pl v, hSS ((hS _).2 ⟨v, rfl⟩)⟩ v rfl).2 (fun g => z (toGS Ω _ g)) (hw _)
    simpa only [h.loc_eq, MonoidHom.comp_apply, hyz, SetLike.mem_coe] using this
  · congr 1
    ext φ
    exact (hps.forall (p := fun s => ∀ x, φ (ρ s x) = PadicInt.toZModPow k (Φ.eps s : ℤ_[l]) * φ x)).symm
  · exact Fintype.prod_equiv e.symm _ _ fun w => by rw [h.cw]; rfl
