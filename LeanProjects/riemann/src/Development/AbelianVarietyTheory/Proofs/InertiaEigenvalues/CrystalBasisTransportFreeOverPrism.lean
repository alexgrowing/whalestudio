import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysIndep

theorem exists_read {Z O S W R N ι : Type} [CommRing Z] [CommRing O] [CommRing S] [CommRing W] [CommRing R]
    [Algebra Z O] [Algebra Z S] [Algebra Z W] [Algebra O R] [Module.Flat Z O] [AddCommGroup N]
    (ρ : S →ₐ[Z] W) (hρ : Function.Injective ρ) (g : S →+* R)
    (hg : ∀ z, g (algebraMap Z S z) = algebraMap O R (algebraMap Z O z)) (D : N →+ (ι → O ⊗[Z] W))
    (hD : ∀ x i, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) ρ z = D x i) :
    ∃ V : N →+ (ι → R), (∀ s x x' i, D x' i = ((1 : O) ⊗ₜ[Z] ρ s) * D x i → V x' i = g s * V x i) ∧
      (∀ (c : O) x i, D x i = algebraMap O _ c → V x i = algebraMap O R c) := by
  letI : Algebra Z R := ((algebraMap O R).comp (algebraMap Z O)).toAlgebra
  haveI : IsScalarTower Z O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g' : S →ₐ[Z] R := { toRingHom := g, commutes' := hg }
  let Ψ : O ⊗[Z] S →ₐ[O] R :=
    Algebra.TensorProduct.lift (Algebra.ofId O R) g' fun _ _ => Commute.all _ _
  have hi : Function.Injective (Algebra.TensorProduct.map (AlgHom.id O O) ρ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := O) ρ.toLinearMap hρ
  choose C hC using hD
  refine ⟨AddMonoidHom.mk' (fun x i => Ψ (C x i)) fun x y => funext fun i => ?_, fun s x x' i h => ?_,
    fun c x i h => ?_⟩
  · have : C (x + y) i = C x i + C y i := hi (by rw [map_add, hC, hC, hC, map_add, Pi.add_apply])
    change Ψ (C (x + y) i) = Ψ (C x i) + Ψ (C y i)
    rw [this, map_add]
  · have : C x' i = ((1 : O) ⊗ₜ[Z] s) * C x i := hi (by
      rw [map_mul, hC, hC, h, Algebra.TensorProduct.map_tmul]; rfl)
    change Ψ (C x' i) = g s * Ψ (C x i)
    rw [this, map_mul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · have : C x i = algebraMap O _ c := hi (by rw [hC, h, AlgHom.commutes])
    change Ψ (C x i) = _
    rw [this, AlgHom.commutes]

theorem indep_of_coord {Z O S W B R M N ι : Type} [CommRing Z] [CommRing O] [CommRing S] [CommRing W] [CommRing B]
    [CommRing R] [Algebra Z O] [Algebra Z S] [Algebra Z W] [Algebra O R] [Module.Flat Z O] [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module B N] [Fintype ι] [DecidableEq ι] {f : S →+* B} {u : M →ₛₗ[f] N}
    (hu : SemiBC u) (ρ : S →ₐ[Z] W) (hρ : Function.Injective ρ) (ψ : B →+* R)
    (hψ : ∀ z, ψ (f (algebraMap Z S z)) = algebraMap O R (algebraMap Z O z)) (D : M →+ (ι → O ⊗[Z] W))
    (hD : ∀ x i, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) ρ z = D x i)
    (hs : ∀ (s : S) x, D (s • x) = ((1 : O) ⊗ₜ[Z] ρ s) • D x) (m : O → ι → M)
    (hm : ∀ o j k, D (m o j) k = o • if k = j then 1 else 0) :
    ∃ lam : N →+ (ι → R), ∀ (Q : Type) [Fintype Q] (c : ι → Q → O) (y : ι → Q → B) (i : ι),
      lam (∑ j, ∑ q, y j q • u (m (c j q) j)) i = ∑ q, c i q • ψ (y i q) := by
  obtain ⟨V, hV1, hV2⟩ := exists_read ρ hρ (ψ.comp f) hψ D hD
  have hVb : ∀ (o : O) j k, V (m o j) k = algebraMap O R (if k = j then o else 0) := fun o j k => by
    refine hV2 _ _ _ ?_
    rw [hm]
    split_ifs
    · exact (Algebra.algebraMap_eq_smul_one o).symm
    · rw [smul_zero, map_zero]
  let V' : M →+ (Unit → ι → R) := AddMonoidHom.mk' (fun x _ => V x)
    fun x y => funext fun _ => map_add V x y
  obtain ⟨lam, hl1, hl2⟩ := CrysExt.exists_ext hu (fun _ : Unit => ψ) V' fun w x _ k =>
    hV1 w x (w • x) k (by rw [hs]; rfl)
  refine ⟨(Pi.evalAddMonoidHom _ ()).comp lam, fun Q _ c y i => ?_⟩
  have h3 : ∀ j q, lam (y j q • u (m (c j q) j)) () i =
      if i = j then c j q • ψ (y j q) else 0 := fun j q => by
    rw [hl1, hl2]
    change _ * V _ i = _
    rw [hVb]
    split_ifs
    · rw [Algebra.smul_def, mul_comm]
    · rw [map_zero, mul_zero]
  change lam _ () i = _
  simp only [map_sum, Finset.sum_apply, h3]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]

variable (a) in

noncomputable def evW (ϖ : PiSys l e) : (Wq l a)⟦X⟧ →ₐ[ℤ_[l]] WCb l where
  toRingHom := (inclW l).comp (ϖ.ev a)
  commutes' z := by
    change inclW l (ϖ.ev a (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = _
    rw [PowerSeries.algebraMap_apply, PiSys.ev_C, AlgHom.commutes]
    exact (inclWA l).commutes z

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι}

theorem exists_toW_eq {m : Vec K a ι} (hm : m ∈ P.M) (i : ι) :
    ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) (evW a ϖ) z = toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i := by
  have h1 : toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i =
      OfCrystal.iR K t ϖ fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩ :=
    ϖ.iW_of_mem t K fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩
  obtain ⟨s, hs⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O)
    (fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩)
  refine ⟨∑ k, Module.Free.chooseBasis ℤ_[l] O k • ((1 : O) ⊗ₜ[ℤ_[l]] s k), ?_⟩
  rw [h1, hs, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, OfCrystal.iR_toAc]
  rfl

theorem toW_bas (j : ι) (hm : (bas j : Vec K a ι) ∈ P.M) (i : ι) :
    toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩ i = if i = j then 1 else 0 := by
  rw [toW_apply]
  split_ifs with h
  · rw [← map_one (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [bas, h]))
  · rw [← map_zero (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [bas, h]))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → (∀ i, (oE 1).u (ϖ.prism a) (b i) = b i) ∧ ∀ (P' : Obj l ↥(OL (ϖ.field a))) (f : GlobalTheory.Prism.Hom (ϖ.prism a) P') (Q Q' : Type) [Fintype Q] [Fintype Q'] (c : ι → Q → O) (y : ι → Q → P'.A) (c' : ι → Q' → O) (y' : ι → Q' → P'.A), ∑ i, ∑ q, y i q • (oE (c i q)).u P' (E.tr f (b i)) = ∑ i, ∑ q, y' i q • (oE (c' i q)).u P' (E.tr f (b i)) → ∀ (R : Type) [CommRing R] [Algebra O R] (ψ : P'.A →+* R), (∀ z : ℤ_[l], ψ (f.f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = algebraMap O R (algebraMap ℤ_[l] O z)) → ∀ i, ∑ q, c i q • ψ (y i q) = ∑ q, c' i q • ψ (y' i q) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE b hb
  have h0 : ∃ J : E.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (jA (E.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have hi : Function.Injective J := by
    have := E.proj (ainfObj (ϖ.field a))
    have := E.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact BKCoord.semiBC_injective (E.tr_bc (ϖ.toAinf a)) (BKCoord.ev_injective ϖ)
      (BKCoord.semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  have hJo : ∀ c x, J ((oE c).u (ϖ.prism a) x) = c • J x := fun c x => by
    have h3 := (congrArg jA ((oE c).u_tr (ϖ.toAinf a) x)).symm.trans (hoE c _)
    have h4 := (congrArg (kappa T) h3).trans (OfCrystal.kappa_mulZ T c _)
    rewrite [hJ, hJ]
    exact h4
  have hJs : ∀ (w : (ϖ.prism a).A) x, J (w • x) = ((1 : O) ⊗ₜ[ℤ_[l]] evW a ϖ w : OW l O) • J x :=
    fun w x => by
    have h3 := congrArg jA ((E.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (BKCoord.kappa_smul T _ _)
    rewrite [hJ, hJ]
    exact h5
  refine ⟨fun i => hi (by rw [hJo, one_smul]), ?_⟩
  intro P' f Q Q' _ _ c y c' y' heq R _ _ ψ hψ i
  have h1 : ∃ D : E.M (ϖ.prism a) →+ (ι → OW l O), ∀ x, D x = I.j.symm (J x) :=
    ⟨I.j.symm.toLinearMap.toAddMonoidHom.comp J, fun _ => rfl⟩
  obtain ⟨D, hD⟩ := h1
  have h2 : ∀ x k, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) (evW a ϖ) z = D x k := fun x k => by
    obtain ⟨m, hm, h⟩ := (him (J x)).1 ⟨x, hJ x⟩
    rw [hD, h, LinearEquiv.symm_apply_apply]
    exact exists_toW_eq t ϖ hm k
  have h3 : ∀ (w : (ϖ.prism a).A) x, D (w • x) = ((1 : O) ⊗ₜ[ℤ_[l]] evW a ϖ w : OW l O) • D x :=
    fun w x => (hD _).trans ((congrArg I.j.symm (hJs w x)).trans
      ((I.j.symm.map_smul _ _).trans (congrArg _ (hD x).symm)))
  have h4 : ∀ (o : O) j k, D ((oE o).u (ϖ.prism a) (b j)) k = o • if k = j then 1 else 0 := fun o j k => by
    obtain ⟨hm, h⟩ := hb j
    have h5 : I.j.symm (J (b j)) = toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩ :=
      I.j.symm_apply_eq.2 ((hJ _).trans h)
    have h6 : I.j.symm (o • J (b j)) = o • I.j.symm (J (b j)) := LinearMapClass.map_smul_of_tower _ _ _
    have h7 := ((hD _).trans (congrArg I.j.symm (hJo o (b j)))).trans (h6.trans (congrArg (o • ·) h5))
    exact (congrFun h7 k).trans (congrArg (o • ·) (toW_bas t ϖ j hm k))
  letI : Algebra ℤ_[l] (ϖ.prism a).A := (inferInstance : Algebra ℤ_[l] (Wq l a)⟦X⟧)
  obtain ⟨lam, hlam⟩ := indep_of_coord (Z := ℤ_[l]) (S := (ϖ.prism a).A) (E.tr_bc f) (evW a ϖ)
    (OfCrystal.ev_injective ϖ t K) ψ hψ D h2 h3 (fun o j => (oE o).u (ϖ.prism a) (b j)) h4
  simp only [FHom.u_tr] at heq
  exact (hlam Q c y i).symm.trans ((congrArg (lam · i) heq).trans (hlam Q' c' y' i))

end GlobalTheory.CrysIndep
