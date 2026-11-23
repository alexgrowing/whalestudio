import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyModPrimeUniversalCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankZmodTensorHomologyZeroOfNoPTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRatHomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexLineBundleTermTorsionFreeCharZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

noncomputable section

namespace GlobalTheory.ChiFibre

open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.FieldChangeInter

theorem alternating_sum_range_telescoping_identity (a r : ℕ → ℤ) (m : ℕ) :
    ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * (a n + a (n + 1) - r (n + 1)) =
      ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * r n + (a 0 - r 0) + (-1) ^ m * (r m - a m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
    ring

theorem homology_subsingleton {R : Type} [Ring R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (h : IsZero (K.X n)) : Subsingleton (K.homology n) :=
  ModuleCat.subsingleton_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) h)

theorem finite_int_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Finite ℤ M _ _ i₁) : @Module.Finite ℤ M _ _ i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact h

theorem altSum (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime]
    (hinj : ∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0)
    (hfin : ∀ n, Module.Finite ℤ (C.homology n)) (m : ℕ) (hz : ∀ n, m ≤ n → IsZero (C.X n)) :
    ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank (ZMod p) ((((ModuleCat.extendScalars
      (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
    ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank ℚ ((((ModuleCat.extendScalars
      (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) := by
  set a : ℕ → ℤ := fun n => Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n))
  set r : ℕ → ℤ := fun n => Module.finrank ℤ (C.homology n)
  have hsub : ∀ n, m ≤ n → Subsingleton (C.homology n) :=
    fun n hn => homology_subsingleton C n (hz n hn)
  have hr0 : ∀ n, m ≤ n → r n = 0 := fun n hn => by
    haveI := hsub n hn
    simp only [r]
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  have ha0 : ∀ n, m ≤ n → a n = 0 := fun n hn => by
    haveI := hsub n hn
    have : Subsingleton (TensorProduct ℤ (ZMod p) (C.homology n)) := inferInstance
    simp only [a]
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  have hext : ∀ (F : Type) [Field F] (g : ℤ →+* F) (n : ℕ), m ≤ n →
      Module.finrank F ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).homology n) = 0 := by
    intro F _ g n hn
    have hZ : IsZero ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).X n) :=
      (ModuleCat.extendScalars g).map_isZero (hz n hn)
    haveI := homology_subsingleton _ n hZ
    exact Module.finrank_zero_of_subsingleton
  have hsupp : ∀ (F : Type) [Field F] (g : ℤ →+* F),
      (Function.support fun n => (-1 : ℤ) ^ n * (Module.finrank F ((((ModuleCat.extendScalars
        g).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ)) ⊆
        ↑(Finset.range m) := by
    intro F _ g n hn
    by_contra h
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
    exact hn (by simp [hext F g n h])
  rw [finsum_eq_sum_of_support_subset _ (hsupp (ZMod p) _),
    finsum_eq_sum_of_support_subset _ (hsupp ℚ _)]
  have h1 : ∀ n ∈ Finset.range m, (-1 : ℤ) ^ n * (Module.finrank (ZMod p) ((((ModuleCat.extendScalars
      (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
      (-1 : ℤ) ^ n * (a n + a (n + 1) - r (n + 1)) := fun n _ => by
    rw [GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients C p hinj hfin n]
  have h2 : ∀ n ∈ Finset.range m, (-1 : ℤ) ^ n * (Module.finrank ℚ ((((ModuleCat.extendScalars
      (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
      (-1 : ℤ) ^ n * r n := fun n _ => by
    rw [GlobalTheory.T.finrank_rat_homology_eq_finrank_int C n (hfin n)]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, alternating_sum_range_telescoping_identity]
  have h0 : a 0 = r 0 := by
    simp only [a, r]
    exact_mod_cast GlobalTheory.T.finrank_zmod_tensor_homology_zero_of_noPTorsion C p (hinj 0) (hfin 0)
  rw [h0, hr0 m le_rfl, ha0 m le_rfl]
  ring

theorem hdim_fibre {X X' : Scheme.{0}} {F : Type} [Field F] (g : ℤ →+* F) (f : X ⟶ Sp ℤ)
    (f' : X' ⟶ Sp F) (π : X' ⟶ X) (H : IsPullback π f' f (spMap g)) {κ : Type} [LinearOrder κ]
    [Finite κ] (D : κ → X.Opens) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (M : LB X) (hM : M.IsLB)
    (n : ℕ) :
    (letI := GlobalTheory.algebraΓOfHom f'; hdim F (toMod (M.pull π)) n) =
      Module.finrank F ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechLB f M D)).homology n) := by
  letI := GlobalTheory.algebraΓOfHom f'
  have hM' := LB.isLB_pull hM π
  haveI := LB.isQuasicoherent_toMod hM'
  have hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  have hD' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ D i) :=
    fun s hs => isAffineOpen_biInf_preimage H (hD s hs)
  have e₁ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (cechIso f' (M.pull π) (fun i => π ⁻¹ᵁ D i))).toLinearEquiv ≪≫ₗ
    cechHEquivCoh F hc' hD' (toMod (M.pull π)) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (cechLBBaseChangeIso hM H hD)).toLinearEquiv
  rw [hdim_def, ← e₁.finrank_eq, ← e₄.finrank_eq]
  rfl

theorem chi_fibres_LB {X Xp Xq : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : CharZero Γ(X, ⊤))
    (f : X ⟶ Sp ℤ) (p : ℕ) [Fact p.Prime]
    (fp : Xp ⟶ Sp (ZMod p)) (πp : Xp ⟶ X) (Hp : IsPullback πp fp f (spMap (Int.castRingHom (ZMod p))))
    (fq : Xq ⟶ Sp ℚ) (πq : Xq ⟶ X) (Hq : IsPullback πq fq f (spMap (Int.castRingHom ℚ)))
    (M : LB X) (hM : M.IsLB)
    (hfin : ∀ n, letI := GlobalTheory.algebraΓOfHom f; Module.Finite ℤ (coh (twist (structureModule X) M) n)) :
    (letI := GlobalTheory.algebraΓOfHom fp; chi (ZMod p) (toMod (M.pull πp))) =
      (letI := GlobalTheory.algebraΓOfHom fq; chi ℚ (toMod (M.pull πq))) := by
  obtain ⟨m, Dc, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have hinj : ∀ (n : ℕ) (x : (cechLB f M Dc).X n), (p : ℤ) • x = 0 → x = 0 :=
    fun n x => GlobalTheory.T.cechComplexLineBundle_term_torsionFree_charZero hX f M Dc n (p : ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero) x
  have hz : ∀ n, m ≤ n → IsZero ((cechLB f M Dc).X n) :=
    fun n hn => isZero_cechLB_X f M Dc (by simpa using hn)
  have hfin' : ∀ n, Module.Finite ℤ ((cechLB f M Dc).homology n) := by
    intro n
    letI := GlobalTheory.algebraΓOfHom f
    obtain ⟨e⟩ := nonempty_coh_equiv f hM hc hD' n
    letI : Module ℤ (coh (twist (structureModule X) M) n) := cohOn.instModule ℤ _ ⊤ n
    haveI hf1 : Module.Finite ℤ (coh (twist (structureModule X) M) n) := finite_int_congr (hfin n)
    exact finite_int_congr (Module.Finite.equiv e.symm)
  letI := GlobalTheory.algebraΓOfHom fp
  letI := GlobalTheory.algebraΓOfHom fq
  rw [chi_def, chi_def]
  have hp := fun n => hdim_fibre (Int.castRingHom (ZMod p)) f fp πp Hp Dc hc hD' M hM n
  have hq := fun n => hdim_fibre (Int.castRingHom ℚ) f fq πq Hq Dc hc hD' M hM n
  simp only [hp, hq]
  exact altSum (cechLB f M Dc) p hinj hfin' m hz

theorem chi_structureModule_eq {X X' : Scheme.{0}} (F : Type) [Field F] [Algebra F Γ(X', ⊤)]
    (π : X' ⟶ X) : chi F (structureModule X') = chi F (toMod ((LB.triv X).pull π)) := by
  have h₀ := LB.isLB_triv X
  have h₁ := Semi.LB.isLB_pull h₀ π
  obtain ⟨e'⟩ := nonempty_twist_iso_of_cls_eq_zero (structureModule X') h₁
    ((CechPic.cls_pull h₀ π h₁).trans (map_zero _))
  rw [← chi_congr F e', chi_congr F (Twist.unitTwistIso _)]

theorem chi_fibre_eq : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (p : ℕ) [Fact p.Prime] (N : LB W), N.IsLB → (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); chi (ZMod p) (toMod (N.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) = chi ℚ (toMod (N.pull (ratFibre.fst q))) ∧ chi (ZMod p) (structureModule (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))) = chi ℚ (structureModule (ratFibre q))) := by
  intro k _ W q D hq p _ N hN
  haveI := hq.isDomain
  haveI := hq.finite
  haveI := hq.isIntegral
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hproj := hq.isProjOver
  haveI : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace q
  haveI := isAffineHom_diagonal_of_isSeparated q
  have hX : CharZero Γ(W, ⊤) := (flat_int_iff_charZero _).1 hq.flat
  have hfin : ∀ M : LB W, M.IsLB → ∀ n,
      letI := GlobalTheory.algebraΓOfHom (q ≫ spMap (Int.castRingHom k))
      Module.Finite ℤ (coh (twist (structureModule W) M) n) := by
    intro M hM n
    letI := GlobalTheory.algebraΓOfHom q
    have h1 : Module.Finite k (coh (twist (structureModule W) M) n) :=
      (((serre_finiteness_vanishing k W (structureModule W)).2 q (fun _ => rfl)).2
        (Or.inl hproj)).2.1 M hM n
    have h2 : Module.Finite ℤ (coh (twist (structureModule W) M) n) := Module.Finite.trans k _
    exact finite_int_congr h2
  refine ⟨chi_fibres_LB hX _ p _ _ (IsPullback.of_hasPullback _ _) _ _ (ratFibre.isPullback q) N hN
    (hfin N hN), ?_⟩
  letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom (ZMod p))))
  rw [chi_structureModule_eq (ZMod p) (pullback.fst _ _), chi_structureModule_eq ℚ (ratFibre.fst q)]
  exact chi_fibres_LB hX _ p _ _ (IsPullback.of_hasPullback _ _) _ _ (ratFibre.isPullback q) _
    (LB.isLB_triv W) (hfin _ (LB.isLB_triv W))

end GlobalTheory.ChiFibre
