import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem pullHQ_comp_apply (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (a : E ⟶ E') (b : E' ⟶ E'') (n i : ℤ)
    (x : HQ l E'' n i) : pullHQ l (a ≫ b) n i x = pullHQ l a n i (pullHQ l b n i x) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]
  rfl

private theorem galHQ_eq_pullHQ_galMap (l : ℕ) [Fact l.Prime] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    {X : Scheme} (t : X ⟶ Spec (CommRingCat.of k)) (n i : ℤ) (σ : Gal(Ω/k)) (x : HQ l (sch.obj (geom Ω t)) n i) :
    galHQ l Ω t n i σ x = pullHQ l (sch.map (galMap Ω t σ)) n i x := rfl

private theorem pullHQ_surjective_of_forall_pull_bijective (l : ℕ) [Fact l.Prime] {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (h : ∀ k : ℕ, Function.Bijective (GlobalTheory.EtC.pull (ZMod (l ^ k)) f (tw (l ^ k) i) n)) :
    Function.Surjective (pullHQ l f n i) := by
  have hs : Function.Surjective (pullHl l f n i) := by
    intro y
    let x : (k : ℕ) → HtL l k E' n i := fun k => (Equiv.ofBijective _ (h k)).symm (y.1 k)
    have hx : ∀ k, GlobalTheory.EtC.pull (ZMod (l ^ k)) f (tw (l ^ k) i) n (x k) = y.1 k := fun k =>
      Equiv.ofBijective_apply_symm_apply _ (h k) (y.1 k)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · intro k
      apply (h k).1
      rw [pull_red, hx, hx]
      exact y.2 k
    · apply Subtype.ext
      funext k
      exact hx k
  unfold pullHQ
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ hs

theorem UpperTheory.Gal.Mod.esGen :
    SpecGood → ESPt → NwtOne → FrobQ → BaseFacts → DenseGen → FrEx → CorrPull → CorrComm → ESGen := by
  intro hSG hES hNwt hFQ hBF hDG hFrEx hCP hCC
  intro l _ p f n hp O _ _ _ ϖ hϖ hpu K _ _ κ _ _ hp0 hκ hfin Ω _ _ _ V hV kb _ _ _ r hr hrc hl Y g _ _ T hT hPt c hc σ hσ k
  let ρ : O →+* V := ((algebraMap K Ω).comp (algebraMap O K)).codRestrict V hV
  have hρ : CommRingCat.ofHom (algebraMap O κ) ≫ CommRingCat.ofHom (algebraMap κ kb) =
      CommRingCat.ofHom ρ ≫ CommRingCat.ofHom r := by
    ext a
    exact (hrc a).symm
  have hρK : CommRingCat.ofHom (algebraMap O K) ≫ CommRingCat.ofHom (algebraMap K Ω) =
      CommRingCat.ofHom ρ ≫ CommRingCat.ofHom V.subtype := by
    ext a
    rfl
  let iY : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom r)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρ])
  let jY : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom V.subtype)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρK])
  have HSG := @hSG O _ K _ _ κ _ _ Ω _ _ _ V hV kb _ _ _ r hr hrc Y g _ _ iY jY
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨sp, hsp1, hsp2⟩ := HSG.2 l hl k 0
  have hpO : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hpκ : (p : κ) = 0 := by
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hpO
    rw [← map_natCast (algebraMap O κ), ← hu, map_mul, hκ, mul_zero]
  have hpkb : (p : kb) = 0 := by
    rw [← map_natCast (algebraMap κ kb), hpκ, map_zero]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP kb p := (CharP.charP_iff_prime_eq_zero hp).2 hpkb
  let τ : Gal(kb/κ) := AlgEquiv.ofRingEquiv (f := iterateFrobeniusEquiv kb p f) (fun a => by
    show iterateFrobenius kb p f _ = _
    rw [iterateFrobenius_def, ← map_pow, hfin])
  have hτ : ∀ a, τ a = a ^ p ^ f := fun a => iterateFrobeniusEquiv_apply kb p f a
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := sp.surjective x
    have e := hsp2 σ 1 hσ (fun v => by rw [h1 v]; rfl) y
    rw [map_one] at e
    exact e.symm
  · have hcomp : ∀ x, sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ x) =
        galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ (sp x) :=
      hsp2 σ τ hσ (fun v => by rw [h2 v, hτ])
    let φG : kb →+* Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤) :=
      (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom
    have hpG : ((p : ℕ) : Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤)) = 0 := by
      rw [← map_natCast φG p, hpkb, map_zero]
    have hlG : IsUnit ((l : ℕ) : Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤)) := by
      rw [← map_natCast φG l]
      exact hl.map φG
    obtain ⟨Fr, hFr1, hFr2, hFr3⟩ := hFrEx p f hp κ kb hfin _
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) hpG τ hτ
    have hAF := hFQ l (geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))) p f hp hpG hlG k
    have hFG : ∀ x, pullHQ l (sch.map Fr) k 0
        (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ x) = x := by
      intro x
      rw [galHQ_eq_pullHQ_galMap, ← pullHQ_comp_apply, ← Functor.map_comp, hFr2, hAF]
      rfl
    have hinvτ : ∀ x, galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ
        (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x) = x := by
      intro x
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have hsemi : ∀ x, sp (pullHQ l (sch.map Fr) k 0 x) =
        galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (sp x) := by
      intro x
      calc sp (pullHQ l (sch.map Fr) k 0 x)
          = sp (pullHQ l (sch.map Fr) k 0
              (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ
                (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x))) := by
            rw [hinvτ]
        _ = sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x) := by
            rw [hFG]
        _ = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹
              (galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ
                (sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x))) := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl
        _ = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (sp x) := by
            rw [← hcomp, hinvτ]
    have hpO0 : (p : O) ≠ 0 := by
      intro h0
      apply hp0
      rw [← map_natCast (algebraMap O K), h0, map_zero]
    obtain ⟨hLoc, hGen, hSpe, hBO⟩ := hBF p O ϖ hϖ hpO0 hpu Y g
    have hOne : ∀ j, Mod.One (T j) (nwt (T j).p) := fun j => hNwt p Y (T j) hLoc hGen
    have hβ : Spec.map (CommRingCat.ofHom (algebraMap κ kb)) ≫ Spec.map (CommRingCat.ofHom (algebraMap O κ)) =
        Spec.map (CommRingCat.ofHom ((algebraMap κ kb).comp (algebraMap O κ))) := by
      rw [← Spec.map_comp]
      rfl
    have hPBS : IsPullback
        (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
        g (Mod.sp ((algebraMap κ kb).comp (algebraMap O κ))) := by
      have e := IsPullback.paste_horiz (IsPullback.of_hasPullback
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
        (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
      rw [hβ] at e
      exact e
    have hDense := hDG O ϖ hϖ kb ((algebraMap κ kb).comp (algebraMap O κ)) (by simp [hκ]) Y _ g _ _ hPBS
    have hSep : ∀ (Ω' : Type) [Field Ω'] (x x' : gp Ω' ⟶ geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))),
        x ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) =
        x' ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) →
        x ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) =
        x' ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) → x = x' := by
      intro Ω' _ x x' e1 e2
      apply pullback.hom_ext _ e2
      apply pullback.hom_ext
      · simpa only [Category.assoc] using e1
      · simp only [Category.assoc, pullback.condition]
        rw [← Category.assoc, e2, Category.assoc]
    have hTw : ∀ (Ω' : Type) [Field Ω'] (φ : Ω' →+* Ω'), (∀ a, φ a = a ^ p ^ f) →
        ∀ (x : gp Ω' ⟶ geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))),
        x ≫ Fr ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) =
        twist φ Y (x ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))) := by
      intro Ω' _ φ hφ x
      have e := hFr3 Ω' φ hφ x
      calc _ = (x ≫ Fr ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
              (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))) := by
            simp only [Category.assoc]
        _ = _ := by
            rw [e]
            simp only [Category.assoc]
            rfl
    have hc' := fun j => hCP p g _ _ _ hPBS (T j) (nwt (T j).p) (hOne j).1 (hT j)
    choose c' hc'' using hc'
    choose v hv using hc''
    have hE := hES l p f n hp Y (fn g ϖ) T (fun j => nwt (T j).p) hOne hPt hSpe hBO _ _ _ _ Fr hlG hDense hSep hFr1 hTw c' v
      (fun j => (hv j).1) (fun j => (hv j).2.1) (fun j => (hv j).2.2.1) (fun j => (hv j).2.2.2) k 0
    have hPBV := IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom ρ))
    have hcV := fun j => hCP p g _ _ _ hPBV (T j) (nwt (T j).p) (hOne j).1 (hT j)
    choose cV hcV' using hcV
    have hlVV : IsUnit ((l : ℕ) : V) := by
      by_contra h
      have hm : ((l : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := h
      have hk : RingHom.ker r = IsLocalRing.maximalIdeal V :=
        IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr)
      rw [← hk, RingHom.mem_ker, map_natCast] at hm
      exact hl.ne_zero hm
    let φV : V →+* Γ(pullback g (Spec.map (CommRingCat.ofHom ρ)), ⊤) :=
      (pullback.snd g (Spec.map (CommRingCat.ofHom ρ))).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    have hlV : IsUnit ((l : ℕ) : Γ(pullback g (Spec.map (CommRingCat.ofHom ρ)), ⊤)) := by
      rw [← map_natCast φV l]
      exact hlVV.map φV
    have CCi := fun j => hCC l p g _ _ _ hPBV iY _ (Spec.map (CommRingCat.ofHom r)) (pullback.lift_snd _ _ _) hlV
      (T j) (nwt (T j).p) (cV j) (c' j) (hcV' j) (by rw [pullback.lift_fst]; exact ⟨v j, hv j⟩) k 0
    have hcN : ∀ j, IsBC (T j) (nwt (T j).p) (jY ≫ pullback.fst g (Spec.map (CommRingCat.ofHom ρ)))
        (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) (c j) := by
      intro j
      obtain ⟨vK, e1, e2, e3, e4⟩ := hc j
      refine ⟨vK, ?_, ?_, e3, ?_⟩
      · rw [pullback.lift_fst]
        exact e1
      · rw [pullback.lift_fst]
        exact e2
      · rw [e4]
        funext Ω' i1 i2 z
        symm
        apply (hOne j).2 Ω' (z ≫ vK)
        intro h0
        let φ := Spec.preimage (z ≫ (c j).p ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
        have h1 : φ.hom (p : Ω) = 0 := by
          rw [map_natCast]
          exact h0
        have h2 : (p : Ω) = 0 := φ.hom.injective (by rw [h1, map_zero])
        apply hp0
        apply (algebraMap K Ω).injective
        rw [map_natCast, h2, map_zero]
    have CCj := fun j => hCC l p g _ _ _ hPBV jY _ (Spec.map (CommRingCat.ofHom V.subtype)) (pullback.lift_snd _ _ _) hlV
      (T j) (nwt (T j).p) (cV j) (c j) (hcV' j) (hcN j) k 0
    have hunit : ∀ m : ℕ, IsUnit (((l ^ m : ℕ)) : kb) := fun m => by
      rw [Nat.cast_pow]
      exact hl.pow m
    have hPs := pullHQ_surjective_of_forall_pull_bijective l (sch.map iY) k 0 (fun m => (HSG.1 (l ^ m) (hunit m) 0).1 k)
    have hopc : ∀ j x, TranscendenceTraces.Corr.opQ l (c j) k 0 (sp x) = sp (TranscendenceTraces.Corr.opQ l (c' j) k 0 x) := by
      intro j x
      obtain ⟨y, rfl⟩ := hPs x
      have e1 := LinearMap.congr_fun (CCi j) y
      have e2 := LinearMap.congr_fun (CCj j) y
      simp only [LinearMap.comp_apply] at e1 e2
      rw [hsp1, ← e2, ← hsp1, e1]
    have hpow : ∀ (m : ℕ) y, (galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ ^ m) (sp y) =
        sp ((pullHQ l (sch.map Fr) k 0 ^ m) y) := by
      intro m
      induction m with
      | zero => intro y; rfl
      | succ m ih =>
        intro y
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← hsemi, ih]
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := sp.surjective x
    have hE' := LinearMap.congr_fun hE y
    rw [LinearMap.zero_apply] at hE' ⊢
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at hE' ⊢
    simp only [hpow, hopc]
    rw [← map_zero sp, ← hE', map_sum]
    simp only [map_smul]
