import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardOfAddEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DecSplit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

noncomputable section

namespace UpperTheory.V.Pa.B2

private abbrev ckPull {A Γ Γ' : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
    (p : Γ →* Γ') (hp : Continuous p) (M : FRep A Γ') : FRep A Γ where
  X := M.X
  ρ := M.ρ.comp p
  cont := M.cont.comp (hp.prodMap continuous_id)

private theorem ck_card {X Y C : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup C] [Finite Y]
    (t : X →+ Y) (q : X →+ C) (hq : Function.Surjective q) (h : ∀ x, t x = 0 → q x = 0) :
    Nat.card C ≤ Nat.card Y := by
  choose s hs using hq
  refine Nat.card_le_card_of_injective (fun c => t (s c)) fun c c' e => ?_
  have := h (s c - s c') (by rw [map_sub]; exact sub_eq_zero.2 e)
  rwa [map_sub, hs, hs, sub_eq_zero] at this

private theorem ck_onto (l : ℕ) {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} (D : Dat A P)
    (hM : ∀ m : D.M.X, l • m = 0) {I : Type} (E : I → Type) [∀ i, Group (E i)] [∀ i, TopologicalSpace (E i)]
    (φ : ∀ i, E i →* Γ) (hφ : ∀ i, Continuous (φ i)) (j : P.ι → I) (hj : Function.Injective j)
    (α : ∀ w, P.G w ≃ₜ* E (j w)) (hα : ∀ w g, φ (j w) (α w g) = P.φ w g) (ho : ∀ w, SecondCohomologyRightExactModL l (P.G w)) :
    ∃ q : (∀ i, H2 (ckPull (φ i) (hφ i) D.M).ρ) →ₗ[A] ∀ w, H2 (D.Q w).ρ, Function.Surjective q ∧
      ∀ z : H2 D.M.ρ, q (fun i => resH2 D.M.ρ (φ i) (hφ i) z) = D.loc2 z := by
  classical
  let q1 : ∀ w, H2 (ckPull (φ (j w)) (hφ _) D.M).ρ →ₗ[A] H2 (D.Q w).ρ := fun w =>
    compatiblePairH2 (ckPull (φ (j w)) (hφ _) D.M).ρ (D.Q w).ρ (α w).toMulEquiv.toMonoidHom (α w).continuous (D.π w)
      continuous_of_discreteTopology fun g m => by
        rw [← D.equiv, ← hα]; rfl
  have hq1 : ∀ w, Function.Surjective (q1 w) := by
    intro w y
    obtain ⟨x, rfl⟩ := ho w A (ckPull (P.φ w) (P.cont w) D.M) (D.Q w) hM (D.π w) (D.equiv w) (D.surj w) y
    refine ⟨compatiblePairH2 (ckPull (P.φ w) (P.cont w) D.M).ρ (ckPull (φ (j w)) (hφ _) D.M).ρ
      (α w).symm.toMulEquiv.toMonoidHom (α w).symm.continuous LinearMap.id continuous_id (fun g m => ?_) x, ?_⟩
    · show D.M.ρ (P.φ w ((α w).symm g)) m = D.M.ρ (φ (j w) g) m
      rw [← hα, (α w).apply_symm_apply]
    · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      show D.π w (f.1 ((α w).symm (α w g.1), (α w).symm (α w g.2))) = D.π w (f.1 g)
      rw [(α w).symm_apply_apply, (α w).symm_apply_apply]
  refine ⟨LinearMap.pi fun w => (q1 w).comp (LinearMap.proj (j w)), fun y => ?_, fun z => ?_⟩
  · choose x hx using fun w => hq1 w (y w)
    refine ⟨∑ w, Pi.single (j w) (x w), funext fun w => ?_⟩
    rw [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Finset.sum_apply,
      Finset.sum_eq_single w (fun w' _ h => Pi.single_eq_of_ne (fun e => h (hj e).symm) _) (by simp),
      Pi.single_eq_same, hx]
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    funext w
    refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
    show D.π w (f.1 (φ (j w) (α w g.1), φ (j w) (α w g.2))) = D.π w (f.1 (P.φ w g.1, P.φ w g.2))
    rw [hα, hα]

private theorem ck_castMod (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) :
    ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l) (PadicInt.toZModPow 1 x) = PadicInt.toZMod x := by
  have h : (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).comp (PadicInt.toZModPow 1) = PadicInt.toZMod := by
    ext y
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 y)
    rw [sub_add_cancel y (PadicInt.appr y 1 : ℤ_[l]) |>.symm, ← hc]
    simp only [map_add, map_mul, map_pow, map_natCast]
    rw [ZMod.natCast_self]; simp
  exact RingHom.congr_fun h x

open GlobalTheory.Published GlobalTheory.Published.PoitouTate in

private theorem ck_pt (hP : GlobalTheory.Published.PoitouTateNormalised) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (h2 : l ≠ 2) (S : Set (HeightOneSpectrum (𝓞 F))) (hf : S.Finite)
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (B : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω) (hB : ∀ v, IsPlaceOver (B v) v)
    (ε : GS Ω S →* ℤ_[l]ˣ) (hε : ε.comp (toGS Ω S) = cycZ F Ω l)
    (A : Type) [CommRing A] (M : FRep A (GS Ω S)) (hM : ∀ m : M.X, l • m = 0) (C : Type) [AddCommGroup C]
    (q : (∀ v : S, H2 (ckPull (locHom S (B v)) (continuous_locHom S (B v)) M).ρ) →+ C) (hq : Function.Surjective q)
    (h0 : ∀ z : H2 M.ρ, q (fun v => resH2 M.ρ (locHom S (B v)) (continuous_locHom S (B v)) z) = 0) :
    Nat.card C ≤ Nat.card {f : M.X →+ ZMod l // ∀ g m, f (M.ρ g m) = PadicInt.toZMod ((ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} := by
  obtain ⟨S, rfl⟩ := hf.exists_finset_coe
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  obtain ⟨inst⟩ : Nonempty (Module (ZMod (l ^ 1)) M.X) := ⟨AddCommGroup.zmodModule (by simpa using hM)⟩
  obtain ⟨hρ, -, -, e, he⟩ := scal A _ M (l ^ 1)
  have hv := fun v : S => (@scal A _ _ _ _ (ckPull (locHom (S : Set (HeightOneSpectrum (𝓞 F))) (B v)) (continuous_locHom _ (B v)) M) (l ^ 1) inst).2.2.2
  choose ev hev using hv
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero ((l ^ 1 : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ hl.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
  let μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ 1))ˣ :=
    (Units.map (PadicInt.toZModPow 1 : ℤ_[l] →+* ZMod (l ^ 1)).toMonoidHom).comp ε
  have hμ : μ.comp (toGS Ω _) = cycMod F Ω l 1 := by
    rw [cycMod, ← hε]; rfl
  let ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M.X := zmodRep (l ^ 1) M.ρ
  obtain ⟨inv, -, hN⟩ := hP F Ω l 1 (Or.inl h2) one_pos ζ hζ
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hex, -⟩, -⟩ :=
    hN S (fun v hv => hS v hv) (fun v => B v) (fun v => hB v) μ hμ M.X ρ' hρ
  haveI : Finite (TDual (ZMod (l ^ 1)) M.X) :=
    (Finite.of_injective _ (DFunLike.coe_injective (F := M.X →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1))) :
      Finite (M.X →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
  haveI : Finite (H0 (twDual μ ρ')) := Subtype.finite
  haveI : Finite (Module.Dual (ZMod (l ^ 1)) (H0 (twDual μ ρ'))) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := H0 (twDual μ ρ') →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
  refine (ck_card ((tr2 S (fun v => B v) μ (invAt S (fun v => B v) μ hμ inv) ρ').toAddMonoidHom.comp
    (AddEquiv.piCongrRight ev).toAddMonoidHom) q hq fun x hx => ?_).trans ?_
  · obtain ⟨z, hz⟩ := (hex _).1 hx
    obtain ⟨z, rfl⟩ := e.surjective z
    rw [← h0 z]
    congr 1
    funext v
    apply (ev v).injective
    refine (congrFun hz v).symm.trans ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [he f ⟨f.1, f.2⟩ rfl]
    exact (hev v (restrictCocycles2 M.ρ _ (continuous_locHom _ (B v)) f) _ rfl).symm
  · rw [Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)), Subspace.dual_finrank_eq,
      ← Module.natCard_eq_pow_finrank]
    let c := ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)
    haveI : Finite (M.X →+ ZMod l) := Finite.of_injective _ (DFunLike.coe_injective (F := M.X →+ ZMod l))
    refine Nat.card_le_card_of_injective (fun y => ⟨c.toAddMonoidHom.comp
      (show M.X →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) from y.1).toAddMonoidHom, fun g m => ?_⟩) fun y y' h => ?_
    · have e := congrArg (fun φ : TDual (ZMod (l ^ 1)) M.X => φ (M.ρ g m)) (y.2 g)
      simp only [twDual_apply] at e
      have e2 : zmodRep (l ^ 1) M.ρ g⁻¹ (M.ρ g m) = m := by
        show M.ρ g⁻¹ (M.ρ g m) = m
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [e2] at e
      show c (y.1 (M.ρ g m)) = _ * c (y.1 m)
      rw [← e, map_mul, ← ck_castMod]
      rfl
    · refine Subtype.ext (TDual.ext fun m => c.injective ?_)
      exact DFunLike.congr_fun (congrArg Subtype.val h) m

end UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arCk :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (A : Type) [CommRing A] (D : Dat A (plOf (globOf r V))), (∀ m : D.M.X, l • m = 0) → Nat.card D.Ck2 ≤ Nat.card {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod (((globOf r V).ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r A _ D hM
  let j : (plOf (globOf r V)).ι → V.S' := fun w => match w with
    | .inl v => ⟨Subtype.val v, V.sub (Or.inl v.2)⟩
    | .inr u => ⟨Subtype.val u, V.sub (Or.inr (Or.inl u.2))⟩
  have hj : Function.Injective j := by
    rintro (v | u) (v' | u') h <;> have h' := congrArg Subtype.val h
    · exact congrArg Sum.inl (Subtype.ext h')
    · exact absurd (h' ▸ v.2 : ((l : ℕ) : 𝓞 (Lp L)) ∈ (Subtype.val u').asIdeal) (s.St_l _ u'.2)
    · exact absurd (h'.symm ▸ v'.2 : ((l : ℕ) : 𝓞 (Lp L)) ∈ (Subtype.val u).asIdeal) (s.St_l _ u.2)
    · exact congrArg Sum.inr (Subtype.ext h')
  choose β hβ using fun v : V.S' => decSplit L Ω (s.A v) (V.split v v.2)
  let α : ∀ w, (plOf (globOf r V)).G w ≃ₜ* Dec (F := Lp L) (s.A (j w)) := fun w => match w with
    | .inl v => β (j (.inl v))
    | .inr u => β (j (.inr u))
  obtain ⟨q, hq, hz⟩ := ck_onto l D hM (fun v : V.S' => Dec (F := Lp L) (s.A v)) (fun v => locHom V.S' (s.A v))
    (fun v => continuous_locHom V.S' (s.A v)) j hj α
    (by
      rintro (v | u) g
      · exact congrArg (toGS Ω V.S') (hβ (j (.inl v)) g)
      · exact congrArg (toGS Ω V.S') (hβ (j (.inr u)) g))
    (by
      rintro (v | u)
      · exact (arLoc hP L Ω l _ _ (s.hw (Subtype.val v))).2.1
      · exact (arLoc hP L Ω l _ _ (s.hw (Subtype.val u))).2.1)
  refine ck_pt hP.pt (Lp L) Ω l s.odd V.S' V.fin (fun v hv => V.sub (Or.inl hv)) s.A s.hA V.ε V.hε A D.M hM D.Ck2
    ((LinearMap.range D.loc2).mkQ.comp q).toAddMonoidHom ((Submodule.mkQ_surjective _).comp hq) fun z => ?_
  exact (congrArg (LinearMap.range D.loc2).mkQ (hz z)).trans ((Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩)
