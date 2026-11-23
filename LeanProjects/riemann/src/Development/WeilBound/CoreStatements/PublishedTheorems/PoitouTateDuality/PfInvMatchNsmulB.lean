import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 1000000 in

theorem loc_act_rootOf (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] [NeZero (l ^ r)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ))
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    (w : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))
    (hwQ : ((((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ) (σ : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) (c : ZMod (l ^ r)) :
    (gsRoots S (l ^ r)).ρ (gsFinFamily S ιs v σ) (rootOf w c) =
      rootOf w (((cycMod Kf.1 (AlgebraicClosure ℚ) l r (ev σ : Dec (F := Kf.1) A) : (ZMod (l ^ r))ˣ) :
        ZMod (l ^ r)) * c) := by
  have hζN : ζ ^ (l ^ r) = 1 := hζ.pow_eq_one
  have hmod : ∀ k : ℕ, ζ ^ (k % (l ^ r)) = ζ ^ k := fun k => by
    conv_rhs => rw [← Nat.mod_add_div k (l ^ r), pow_add, pow_mul, hζN, one_pow, mul_one]
  have hτ : ((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) ζ =
      ζ ^ ((cycMod Kf.1 (AlgebraicClosure ℚ) l r (ev σ : Dec (F := Kf.1) A) : (ZMod (l ^ r))ˣ) :
        ZMod (l ^ r)).val :=
    cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
      (MulSemiringAction.toRingAut (G Kf.1 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)
        (ev σ : Dec (F := Kf.1) A)) ζ hζN
  have hact : ∀ y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S,
      ((gsFinFamily S ιs v σ y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
        ((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) (y : AlgebraicClosure ℚ) := by
    intro y
    apply (ιs v).toRingHom.injective
    show ιs v _ = ιs v _
    rw [gsFinFamily_apply, hev]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  show ((gsFinFamily S ιs v σ ((((w ^ c.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
      maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
    ((((w ^ (((cycMod Kf.1 (AlgebraicClosure ℚ) l r (ev σ : Dec (F := Kf.1) A) : (ZMod (l ^ r))ˣ) :
      ZMod (l ^ r)) * c).val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ)
  rw [hact]
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwQ, map_pow, hτ]
  rw [← pow_mul, ZMod.val_mul, hmod]

theorem eq_rootOf_of_coe {Kf : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 Kf.1))} {l r : ℕ}
    [NeZero (l ^ r)] {ζ : AlgebraicClosure ℚ} {w : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)}
    (hwQ : ((((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ)
    (a : Additive (rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))) (c : ZMod (l ^ r))
    (h : ((((Additive.toMul a : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) :
      AlgebraicClosure ℚ) = ζ ^ c.val) : a = rootOf w c := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  rw [h]
  show ζ ^ c.val = ((((w ^ c.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ)
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwQ]

theorem cls_nsmul_of_match {L D : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ψ : L →* D) (hψ : Continuous ψ)
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho0 : Representation R D M) (A : Rep.{0} (ULift.{0} ℤ) L) [IsDiscreteRep A] (e : M ≃+ A.V)
    (he : ∀ g m, e ((rho0.comp ψ) g m) = A.ρ g (e m)) (z z' : Z2 rho0) (x x' : cocycles A 2)
    (hzx : ∀ s, cochainOf A (cocycleι A 2 x) s = e (z.1 (ψ (s 0), ψ (s 1))))
    (hzx' : ∀ s, cochainOf A (cocycleι A 2 x') s = e (z'.1 (ψ (s 0), ψ (s 1)))) (n : ℕ)
    (h : (Submodule.Quotient.mk z : H2 rho0) = n • Submodule.Quotient.mk z') :
    cohomologyπ A 2 x = n • cohomologyπ A 2 x' := by
  obtain ⟨e2, -, hchar⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 L R M (rho0.comp ψ) A e he
  have h' : resH2 rho0 ψ hψ (Submodule.Quotient.mk z) = n • resH2 rho0 ψ hψ (Submodule.Quotient.mk z') := by
    rw [h, map_nsmul]
  rw [← hchar (restrictCocycles2 rho0 ψ hψ z) x hzx, ← hchar (restrictCocycles2 rho0 ψ hψ z') x' hzx']
  exact (congrArg e2 h').trans (map_nsmul e2 n _)

set_option maxHeartbeats 1000000 in

theorem invMatch_nsmul_B (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (hS : ∀ v : HeightOneSpectrum (𝓞 Kf.1), ((l : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal → v ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : InvNormalised ζ inv)
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v.1)
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))

    (hevc : Continuous ev) (z z' : Z2 (muLoc Kf.1 l r A)) (x x' : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2)
    (hzx : (∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)), ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) = ζ ^ (z.1 (ev (s 0), ev (s 1))).val)) (hzx' : (∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)), ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x') s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) = ζ ^ (z'.1 (ev (s 0), ev (s 1))).val)) (n : ℕ)
    (h : (Submodule.Quotient.mk z : H2 (muLoc Kf.1 l r A)) = n • Submodule.Quotient.mk z') :
    cohomologyπ _ 2 x = n • cohomologyπ _ 2 x' := by
  classical
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hmem : ζ ∈ maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S := by
    haveI : IsGalois Kf.1 (AlgebraicClosure ℚ) := IsAlgClosure.isGalois _ _
    refine mem_maxUnramifiedOutside_of_pow_eq_one S (pow_ne_zero r (Fact.out : l.Prime).ne_zero) ?_
      hζ.pow_eq_one
    intro w hw hm
    apply hw
    apply hS
    have h' : ((l : 𝓞 Kf.1)) ^ r ∈ w.asIdeal := by simpa [Nat.cast_pow] using hm
    exact w.isPrime.mem_of_pow_mem r h'
  have hζK : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) (l ^ r) :=
    IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S).val) hζ (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S).val.toRingHom.injective
  have hex := exists_root_of_primitive (L := ↥(maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) (N := l ^ r)
    (pow_ne_zero r (Fact.out : l.Prime).ne_zero) hζK
  obtain ⟨w, hwv⟩ := hex
  have hw : IsPrimitiveRoot (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) (l ^ r) := by
    rw [hwv]; exact hζK
  have hwQ : ((((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ := congrArg Subtype.val hwv
  let eA : ZMod (l ^ r) ≃+ (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))).V :=
    AddEquiv.ofBijective (rootOf w) (rootOf_bijective w hw)
  have hM : ∀ g m, eA (((muLoc Kf.1 l r A).comp ev.toMonoidHom) g m) =
      (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))).ρ g (eA m) := fun g m => by
    show rootOf w (((cycMod Kf.1 (AlgebraicClosure ℚ) l r (ev g : Dec (F := Kf.1) A) : (ZMod (l ^ r))ˣ) :
        ZMod (l ^ r)) * m) = (gsRoots S (l ^ r)).ρ (gsFinFamily S ιs v g) (rootOf w m)
    exact (loc_act_rootOf Kf S ζ hζ ιs v A ev hev w hwQ g m).symm
  exact cls_nsmul_of_match ev.toMonoidHom hevc (muLoc Kf.1 l r A)
    (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) eA hM z z' x x'
    (fun s => eq_rootOf_of_coe hwQ _ _ (hzx s)) (fun s => eq_rootOf_of_coe hwQ _ _ (hzx' s)) n h

end PositivityTheory.Lit1.PTN
