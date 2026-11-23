import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.UnipPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.IpEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.StableIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TypeIDisc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ThickNonSS
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CoefficientExtensionPreservesConditionsAndDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConstMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

theorem chain_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) (P : CohP)
    (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (hn : 0 < n) (hS : V0.S' = s.S)
    (hL : LocCFT s) (hμ : ∃ g : V0.frame.G₀, PadicInt.toZMod ((V0.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) (hA : HasAut B J)
    (h : ℕ) (x : Fin (h + 1) → Point r) (f : ∀ i, B.B →ₐ[O] (x i).A) (hx : ∀ i, (x i).NiceI ∨ (x i).NiceE)
    (hf : ∀ i, B.IsPt (x i) (f i)) :
    ChainConcl (pairOf B.u) J (fun i => RingHom.ker (f i)) ∧
      ∀ i, (x i).TypeI → ∀ q : Ideal B.B, q ≤ RingHom.ker (f i) → DiscSt B.u.D q := by
  haveI := IsCoef.char (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.complete (l := l) (O := O)
  obtain ⟨hΦ, hT⟩ := hP P l L Ω s V0 O n r hS
  have hI := (ipEq l L Ω s V0 O n r).1
  choose y j jinj jloc _ jD jψ y3 y4 yI using fun i => hN l V0.frame O n r (x i) (globOf r V0).frame.Iu s.odd hn
    (fun u => ((hI u).2.symm.trans (hI u).1).le) (hx i)
  obtain ⟨q, sg, z, j', k, al, hsg, hE, hcard, hdet, heig⟩ := hC l (globOf r V0).frame n h y s.odd hΦ hμ y3
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := hT q sg hsg
  obtain rfl : T.sg = sg := funext hTs
  obtain ⟨A⟩ := hA T Pl
  choose ι hι using fun i => Det.constMap ((j' i).comp (j i))
  have hD : ∀ i, GDet.ofRep (mat (z i).ρ) = (GDet.ofRep (mat (x i).ρ)).map ((j' i).comp (j i)) := fun i => by
    exact (Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).2.2.trans (congrArg (·.map (j' i)) (jD i))
  have hker : ∀ i, ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → (z i).ρ g = 1 := fun i => by
    refine rhoPL l (globOf r V0).frame n (z i) T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    refine ⟨e1, ?_⟩
    have hcc : (PowerSeries.constantCoeff : (z i).A →+* (z i).K).comp ((j' i).comp (j i)) =
        (ι i).comp PowerSeries.constantCoeff := RingHom.ext fun a => by
      haveI := jloc i
      haveI := (hE i).2.1
      have m1 : ¬ IsUnit (a - PowerSeries.C (PowerSeries.constantCoeff a)) := by
        simp [PowerSeries.isUnit_iff_constantCoeff]
      have m2 : ¬ IsUnit (j' i (j i (a - PowerSeries.C (PowerSeries.constantCoeff a)))) := fun u =>
        m1 (IsLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ u))
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not, map_sub, map_sub, map_sub, sub_eq_zero] at m2
      have m3 := congrArg PowerSeries.constantCoeff (hι i (PowerSeries.constantCoeff a))
      exact m2.trans (m3.trans (PowerSeries.constantCoeff_C _))
    have e3 : (GDet.ofRep (mat (z i).ρ)).map (PowerSeries.constantCoeff : (z i).A →+* (z i).K) =
        r.Dbar.map ((ι i).comp (algebraMap (ResidueField O) (x i).K)) := by
      rw [hD i]
      refine Eq.trans (b := (GDet.ofRep (mat (x i).ρ)).map ((ι i).comp PowerSeries.constantCoeff)) (by rw [← hcc]; rfl) ?_
      exact congrArg (·.map (ι i)) (x i).red
    rw [map_ofRep, Resid.Dbar, map_ofRep] at e3
    have e4 := congrArg (·.chi (MonoidAlgebra.single ⟨g, e1⟩ 1)) e3
    simp only [chi_ofRep] at e4
    refine e4.trans ?_
    have e5 : W.diagRep r.chib ⟨g, e1⟩ = 1 := by
      change Matrix.diagonal _ = _
      simp only [e2, Units.val_one, Matrix.diagonal_one]
    refine (chi_ofRep _ _).trans ?_
    change ((RingHom.mapMatrix ((ι i).comp (algebraMap (ResidueField O) (x i).K))) (W.diagRep r.chib ⟨g, e1⟩)).charpoly = _
    rw [e5, map_one, Matrix.charpoly_one, Fintype.card_fin]
  let pt : ∀ i, Pt T (pairOf B.u) (n * Module.finrank ℚ (Lp L) + n * T.q) := fun i =>
    letI : Algebra O (z i).K := ((ι i).comp (algebraMap O (x i).K)).toAlgebra
    { x := z i
      k := k i
      al := al i
      eig := heig i
      b1 := h1 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hL hμ (hker i)
        ((Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).1 _ (y4 i)) (heig i) (hdet i)
      b2 := h2 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hμ (hker i) (heig i)
      f := { ((j' i).comp (j i)).comp (f i : B.B →+* (x i).A) with
        commutes' := fun a => by
          change ((j' i).comp (j i)) (f i (algebraMap O B.B a)) = _
          rw [AlgHom.commutes]
          rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
          exact hι i _ }
      maps := ⟨by rw [hD i, ← (hf i).1]; rfl, fun v a => by
        rw [(hE i).2.2.2.2.2 v a, jψ i v a, ← (hf i).2 v a]; rfl⟩ }
  have hk : ∀ i, RingHom.ker (pt i).f = RingHom.ker (f i) := fun i => by
    ext b
    change j' i (j i (f i b)) = 0 ↔ f i b = 0
    rw [map_eq_zero_iff _ (hE i).1, map_eq_zero_iff _ (jinj i)]
  refine ⟨?_, fun i hi q hq => ?_⟩
  · have := hR l _ (globOf r V0) T n O (residOf r) B.B (pairOf B.u) J _ A s.odd
      ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
      (fun N b => by
        obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
        refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
        rintro _ (⟨a, g, -, -, rfl⟩ | e)
        · exact Or.inl ⟨a, g, rfl⟩
        · exact Or.inr e) h pt hcard
    simpa only [hk] using this
  · exact Det.typeIDisc (z i) B.u.D (((j' i).comp (j i)).comp (f i : B.B →+* (x i).A)) ((hE i).2.2.2.2.1.trans (yI i hi)) (pt i).maps.1 q (hq.trans (hk i).ge)

theorem pFromAut_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) : PfromAut := by
  intro P l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J hn hS hL hμ hA
  have key := chain_of hN hC hP h1 h2 hR P l L Ω s V0 O n r B J hn hS hL hμ hA
  have hE : augmentationIdealKernel (pairOf B.u) = augmentationIdealKernel B.u := by
    rw [(ipEq l L Ω s V0 O n r).2 B]
    ext z
    simp only [augmentationIdealKernel, UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal, GDet.chBar, pairGens, UniversalOrdinaryDeterminantRing.E0gens, Set.mem_setOf_eq, Set.union_assoc]
  refine ⟨fun x f hx hf hJ q hq => ?_, fun h x f e hx hf he h₁ q hq hs => ?_⟩
  · obtain ⟨k1, k2⟩ := key 0 (fun _ => x) (fun _ => f) (fun _ => Or.inl hx) fun _ => hf
    exact k1 Fin.elim0 (fun i => i.elim0) ⟨_, RingHom.ker_isPrime f, k2 0 hx.2.1 _ le_rfl, hJ, le_rfl⟩ q.asIdeal q.isPrime hq
      (Or.inl (k2 0 hx.2.1 _ hq))
  · obtain ⟨k1, -⟩ := key h x f (fun i => Or.inr (hx i)) hf
    obtain ⟨q₁, a1, a2, a3⟩ := h₁
    refine k1 (fun i => (e i).asIdeal) (fun i => ⟨(e i).isPrime, hE ▸ Det.thickNonSS B _ (he i).1, (he i).2⟩)
      ⟨_, q₁.isPrime, (Det.stableIff B _).1 a1, a2, a3⟩ q.asIdeal q.isPrime hq ?_
    exact hs.imp (Det.stableIff B _).1 fun t => hE ▸ Det.thickNonSS B _ t

end UpperTheory.V.Pa
