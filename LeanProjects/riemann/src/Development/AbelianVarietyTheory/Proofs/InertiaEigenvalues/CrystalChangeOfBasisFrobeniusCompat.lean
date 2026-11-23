import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExists
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysEpsFrob

set_option maxHeartbeats 1000000 in

theorem eps_frob_compat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), PP.I = Ideal.span {(l : PP.A)} → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ κ τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → (∀ τ y, κ τ (PP.D.φ y) = φ₂ (κ (τ - 1) y)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)) * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (Matrix.of fun i j => ∑ q, c i j q • κ (τ - 1) (y i j q)).map φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  intro EE jA hR him oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hI hκ hκφ Q _ c y hy τ
  letI := zlLat T
  haveI hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

  obtain ⟨J, hJ⟩ : ∃ J : EE.M (ϖ.prism a) →+ TW (OW l O) T,
      ∀ x, J x = kappa T (jA (EE.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (EE.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  have h1 : ∀ z : TW (OW l O) T, (∃ x, z = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), z = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun z => by
    simp only [hJ]
    exact him z
  obtain ⟨cc, hcM, hcJ, hsurj⟩ := GlobalTheory.BKCoord.exists_coord I J h1
  have hJi : Function.Injective J := by
    have := EE.proj (ainfObj (ϖ.field a))
    have := EE.proj (ϖ.prism a)
    intro u v huv
    rw [hJ, hJ] at huv
    exact GlobalTheory.BKCoord.semiBC_injective (EE.tr_bc (ϖ.toAinf a)) (GlobalTheory.BKCoord.ev_injective ϖ)
      (GlobalTheory.BKCoord.semiBC_injective hR.bc inclW_injective ((kappa_bijective T).1 huv))
  have hinj : Function.Injective cc := fun x x' h => hJi (by rw [hcJ, hcJ]; simp only [h])
  have hw : ∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)),
      cc (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * cc x τ i := by
    intro w x
    refine GlobalTheory.BKCoord.eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hcM x)⟩ ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := congrArg jA ((EE.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  have hU : ∀ (o : O) x, cc ((oE o).u (ϖ.prism a) x) =
      fun τ i => PowerSeries.C (algebraMap O K o) * cc x τ i := by
    intro o x
    refine GlobalTheory.BKCoord.eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hcM x)⟩ ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := (congrArg jA ((oE o).u_tr (ϖ.toAinf a) x)).symm.trans (hoE o _)
    have h4 := (congrArg (kappa T) h3).trans (GlobalTheory.BKCoord.kappa_mulZ T o _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  have hΦ : ∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k →
      cc m = fun τ i => E K l e ^ k * P.phi (cc x) τ i := by
    intro x m k h
    refine GlobalTheory.BKCoord.eq_of_j_eq_phi I k (hcM x) ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := (congrArg (kappa T) (GlobalTheory.BKCoord.j_frob hR x m k h)).trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    have h4 := GlobalTheory.BKCoord.kappa_frob T (jA (EE.tr (ϖ.toAinf a) x))
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h3.trans (congrArg _ h4)
  have hcb : ∀ j, cc (b j) = bas j := by
    intro j
    obtain ⟨hm, hbj⟩ := hb j
    have h2 := (hcJ (b j)).symm.trans ((hJ (b j)).trans hbj)
    exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h2))

  obtain ⟨lam₀, hl₀, ht₀⟩ := GlobalTheory.CrysExt.exists_coord l a e O K t ϖ ι EE cc hw PP p₀ κ PowerSeries.C
    (fun τ w => (hκ τ w).1)
  obtain ⟨lam₁, hl₁, ht₁⟩ := GlobalTheory.CrysExt.exists_coord l a e O K t ϖ ι EE cc hw PP p₁ κ sh
    (fun τ w => (hκ τ w).2)
  obtain ⟨ε', hε'⟩ := GlobalTheory.BKGal.CrysEps.exists_eps l a e O K t ϖ ι P EE cc hinj hcM hsurj hw
    (fun o => ⟨oE o, hU o⟩) sh hsh PP p₀ p₁ κ hκ lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  have hsh1 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by simpa using hsh f 0
  have hshinj : Function.Injective sh := fun f g h => by rw [← hsh1 f, ← hsh1 g, h]
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := fun h => hl0 (by simpa using congrArg PowerSeries.constantCoeff h)
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := fun h => hl1 (by simpa using congrArg PowerSeries.constantCoeff h)
  have hE : E K l e ≠ 0 := fun h => hl0 (by
    simpa [E, NeZero.ne e] using congrArg PowerSeries.constantCoeff h)
  have hshE : sh (frob K l (E K l e)) ≠ 0 := by
    rw [map_ne_zero_iff _ hshinj, map_ne_zero_iff _ (frob_injective l)]; exact hE
  have hl : (l : PP.A) ∈ PP.I := hI ▸ Ideal.mem_span_singleton_self _
  have hfb : ∀ (j : ι) (σ : ZMod a) (i : ι), frob K l (bas j σ i) = bas j σ i := by
    intro j σ i
    rcases eq_or_ne i j with rfl | h
    · simp [bas]
    · simp [bas, Pi.single_eq_of_ne h]

  have hl1b : ∀ j σ, lam₁ (EE.tr p₁ (b j)) σ = Pi.single j 1 := by
    intro j σ; funext i
    rw [ht₁, hcb, hfb]
    rcases eq_or_ne i j with rfl | h
    · simp [bas]
    · simp [bas, Pi.single_eq_of_ne h]

  have hε'col : ∀ σ i j, ε' σ i j = lam₀ (EE.tr p₁ (b j)) σ i := by
    intro σ i j
    rw [hε' _ σ, hl1b, Matrix.mulVec_single_one]; rfl

  have hEps : ∀ σ i j, lam₀ (EE.tr p₁ (b j)) σ i = ∑ q, c i j q • κ σ (y i j q) := by
    intro σ i j
    have hU0 : ∀ (o : O) (i' : ι), lam₀ ((oE o).u PP (EE.tr p₀ (b i'))) σ i =
        if i = i' then PowerSeries.C (PowerSeries.C (algebraMap O K o)) else 0 := by
      intro o i'
      rw [(oE o).u_tr, ht₀, hU, hcb]
      rcases eq_or_ne i i' with rfl | h
      · simp [bas]
      · simp [bas, Pi.single_eq_of_ne h, h]
    rw [hy j, map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hl₀, hU0, if_pos rfl, Algebra.smul_def, PowerSeries.algebraMap_apply,
        PowerSeries.algebraMap_apply, mul_comm]
    · intro i' _ h
      rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hl₀, hU0, if_neg (Ne.symm h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  refine Matrix.ext fun i j => ?_
  obtain ⟨n, k, hn⟩ := exists_isFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ (EE.tr p₁ (b j)))

  have hA := GlobalTheory.CrysFrobCoord.frob_in_coordinates l a e O K t ϖ ι P EE cc hw hΦ PP hl p₀ κ
    PowerSeries.C φ₂ (fun τ w => (hκ τ w).1) hκφ hφC PowerSeries.C_injective lam₀ hl₀ ht₀ _ n k hn τ i

  obtain ⟨m', k', hm'⟩ := exists_isFrac (A := (ϖ.prism a).A) (eis l a e)
    (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ (b j))
  obtain ⟨r, hr⟩ := EE.Φ_nat p₁ ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ ⟨l, hl⟩ (b j) m' k' n k hm' hn
  have hκE : κ τ (p₁.f (eis l a e)) = sh (frob K l (E K l e)) := by
    rw [(hκ τ _).2, ← GlobalTheory.CrysFrobCoord.frob_toAc, GlobalTheory.CrysFrobCoord.coe_toAc_eis]
  have hJl : κ τ (l : PP.A) = l := map_natCast _ _
  have hB : ∀ i', lam₁ n τ i' = (l : K⟦X⟧⟦X⟧) ^ k * sh (frob K l (P.mx (τ - 1) i' j)) := by
    intro i'
    have h1 := congrArg (fun z => lam₁ z τ i') hr
    simp only [hl₁, map_sub, Pi.sub_apply, map_zero, Pi.zero_apply, map_pow, map_mul, hJl, hκE] at h1
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (mul_ne_zero hshE hl2)))
    have hm'c : cc m' (τ - 1) i' = E K l e ^ k' * P.mx (τ - 1) i' j := by
      rw [hΦ _ _ _ hm', hcb]
      simp only [PhiMod.phi_apply]
      congr 1
      have : frobV l (bas j (τ - 1 - 1) : ι → K⟦X⟧) = Pi.single j 1 := funext fun i'' => by
        rw [frobV_apply, hfb]; rfl
      rw [this, Matrix.mulVec_single_one]; rfl
    rw [ht₁, hm'c, map_mul, map_mul, map_pow, map_pow] at h2
    refine mul_left_cancel₀ (pow_ne_zero k' hshE) ?_
    rw [← h2]; ring
  have hlk : ((l : K⟦X⟧⟦X⟧) ^ k) ≠ 0 := pow_ne_zero k hl2
  refine mul_left_cancel₀ hlk ?_
  have hC := congrFun (hε' n τ) i
  rw [hA] at hC
  simp only [Matrix.mulVec, dotProduct, hB, hε'col, hEps, Matrix.map_apply, Matrix.of_apply] at hC
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  rw [hC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.CrysEpsFrob
