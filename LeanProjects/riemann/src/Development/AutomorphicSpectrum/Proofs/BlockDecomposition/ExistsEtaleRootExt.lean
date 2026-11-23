import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemSpanOfEtale
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UZeroApplySelf
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open TensorProduct

namespace GlobalTheory.CompanionTheory.RootPerf

theorem pf_rootExt (p : ℕ) (hp : p.Prime) {k : Type} [CommRing k] (hk : D.Pf p k) {d : ℕ}
    (Y : RootExt p (MvPolynomial (Fin d) k) (MvPolynomial.X : Fin d → MvPolynomial (Fin d) k)) :
    D.Pf p Y.E := by
  classical
  obtain ⟨hchar, hbij⟩ := hk
  rcases subsingleton_or_nontrivial k with hsub | hnt
  · have h10 : (1 : MvPolynomial (Fin d) k) = 0 := by
      rw [← map_one (MvPolynomial.C (σ := Fin d) (R := k)), Subsingleton.elim (1 : k) 0, map_zero]
    have hE : Subsingleton Y.E := subsingleton_of_zero_eq_one (by
      have h := congrArg (algebraMap (MvPolynomial (Fin d) k) Y.E) h10
      rw [map_one, map_zero] at h
      exact h.symm)
    exact ⟨Subsingleton.elim _ _, ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨y, Subsingleton.elim _ _⟩⟩⟩
  · haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 hchar
    haveI : ExpChar k p := ExpChar.prime hp
    haveI : Nontrivial Y.E := nontrivial_of_ne 1 0 (by rw [← Y.b_a₀]; exact Y.b.ne_zero _)
    have hcE : ((p : ℕ) : Y.E) = 0 := by
      rw [← map_natCast (algebraMap (MvPolynomial (Fin d) k) Y.E),
        ← map_natCast (MvPolynomial.C (σ := Fin d) (R := k)), hchar, map_zero, map_zero]
    haveI : CharP Y.E p := (CharP.charP_iff_prime_eq_zero hp).2 hcE
    haveI : ExpChar Y.E p := ExpChar.prime hp
    have hfk : ⇑(frobenius k p) = fun x => x ^ p := funext (frobenius_def p)
    let σ : k ≃+* k := RingEquiv.ofBijective (frobenius k p) (by rw [hfk]; exact hbij)
    have hσ : ∀ a : k, σ.symm a ^ p = a := fun a =>
      (frobenius_def p (σ.symm a)).symm.trans (σ.apply_symm_apply a)
    let f : MvPolynomial (Fin d) k →+* Y.E :=
      MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial (Fin d) k) Y.E).comp
        (MvPolynomial.C.comp σ.symm.toRingHom)) (fun j => Y.r j 1)
    obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := Y.univ Y.E f (fun j m => Y.r j (m + 1))
      (fun j => by
        show Y.r j (0 + 1) = MvPolynomial.eval₂Hom _ _ (MvPolynomial.X j)
        rw [MvPolynomial.eval₂Hom_X'])
      (fun j m => Y.r_succ j (m + 1))
    let F := frobenius Y.E p
    have hF : ∀ x : Y.E, F x = x ^ p := frobenius_def p
    have hFf : F.comp f = algebraMap (MvPolynomial (Fin d) k) Y.E := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [RingHom.comp_apply, hF]
        show ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.C a)) ^ p = _
        rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, RingHom.comp_apply,
          ← map_pow (algebraMap (MvPolynomial (Fin d) k) Y.E), ← map_pow MvPolynomial.C]
        rw [show σ.symm.toRingHom a = σ.symm a from rfl, hσ]
      · intro j
        rw [RingHom.comp_apply, hF]
        show ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.X j)) ^ p = _
        rw [MvPolynomial.eval₂Hom_X', Y.r_succ, Y.r_zero]
    obtain ⟨u, -, hu⟩ := Y.univ Y.E (algebraMap (MvPolynomial (Fin d) k) Y.E) Y.r Y.r_zero Y.r_succ
    have hid : RingHom.id Y.E = u := hu _ ⟨RingHom.id_comp _, fun _ _ => rfl⟩
    have h1 : F.comp g = u := hu _ ⟨by rw [RingHom.comp_assoc, hg1, hFf],
      fun j m => by rw [RingHom.comp_apply, hg2, hF]; exact Y.r_succ j m⟩
    have h2 : g.comp F = u := by
      refine hu _ ⟨RingHom.ext fun x => ?_, fun j m => ?_⟩
      · rw [RingHom.comp_apply, RingHom.comp_apply, hF, map_pow]
        have hx := congrArg (fun φ => φ x) hg1
        simp only [RingHom.comp_apply] at hx
        rw [hx, ← hF, ← RingHom.comp_apply, hFf]
      · rw [RingHom.comp_apply, hF, map_pow, hg2]
        exact Y.r_succ j m
    refine ⟨hcE, Function.bijective_iff_has_inverse.2 ⟨g, fun x => ?_, fun x => ?_⟩⟩
    · have hx := congrArg (fun φ => φ x) (h2.trans hid.symm)
      simpa [hF] using hx
    · have hx := congrArg (fun φ => φ x) (h1.trans hid.symm)
      simpa [hF] using hx

theorem exists_etale_rootExt (p : ℕ) {P E₀ : Type} [CommRing P] [CommRing E₀] (ψ : P →+* E₀)
    (hψ : ψ.Etale) {d : ℕ} (s : Fin d → P) (t : Fin d → E₀) (hst : ∀ j, ψ (s j) = t j)
    (Y : RootExt p P s) (X : RootExt p E₀ t) : ∃ ψ' : Y.E →+* X.E, ψ'.Etale := by
  classical
  letI : Algebra P E₀ := ψ.toAlgebra
  haveI : Algebra.Etale P E₀ := hψ
  letI : Algebra P X.E := ((algebraMap E₀ X.E).comp ψ).toAlgebra
  haveI hbc : Algebra.Etale Y.E (Y.E ⊗[P] E₀) := Algebra.Etale.baseChange P E₀ Y.E
  obtain ⟨gY, ⟨hgY1, hgY2⟩, -⟩ := Y.univ X.E ((algebraMap E₀ X.E).comp ψ) X.r
    (fun k => by rw [X.r_zero, RingHom.comp_apply, hst]) X.r_succ
  let gYa : Y.E →ₐ[P] X.E := AlgHom.mk gY (fun r => by
    change gY (algebraMap P Y.E r) = _
    rw [← RingHom.comp_apply, hgY1]
    rfl)
  let gE : E₀ →ₐ[P] X.E := AlgHom.mk (algebraMap E₀ X.E) (fun r => rfl)
  let χ : Y.E ⊗[P] E₀ →ₐ[P] X.E := Algebra.TensorProduct.lift gYa gE (fun _ _ => Commute.all _ _)
  have hχ : ∀ (y : Y.E) (e : E₀), χ (y ⊗ₜ[P] e) = gY y * algebraMap E₀ X.E e := fun y e =>
    Algebra.TensorProduct.lift_tmul _ _ _ y e
  have hpow : ∀ k m, (Y.r k (m + 1) ⊗ₜ[P] (1 : E₀)) ^ p = Y.r k m ⊗ₜ[P] (1 : E₀) := by
    intro k m
    rw [Algebra.TensorProduct.tmul_pow, one_pow, Y.r_succ]
  obtain ⟨φ, ⟨hφ1, hφ2⟩, -⟩ := X.univ (Y.E ⊗[P] E₀)
    (Algebra.TensorProduct.includeRight : E₀ →ₐ[P] Y.E ⊗[P] E₀).toRingHom
    (fun k m => Y.r k m ⊗ₜ[P] (1 : E₀))
    (fun k => by
      show Y.r k 0 ⊗ₜ[P] (1 : E₀) = (1 : Y.E) ⊗ₜ[P] t k
      rw [Y.r_zero, Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra, hst])
    hpow
  obtain ⟨u, -, hu⟩ := X.univ X.E (algebraMap E₀ X.E) X.r X.r_zero X.r_succ
  have hc1 : (χ.toRingHom.comp φ).comp (algebraMap E₀ X.E) = algebraMap E₀ X.E := by
    rw [RingHom.comp_assoc, hφ1]
    refine RingHom.ext fun e => ?_
    show χ ((1 : Y.E) ⊗ₜ[P] e) = algebraMap E₀ X.E e
    rw [hχ, map_one, one_mul]
  have hc2 : ∀ k m, (χ.toRingHom.comp φ) (X.r k m) = X.r k m := by
    intro k m
    show χ (φ (X.r k m)) = X.r k m
    rw [hφ2]
    show χ (Y.r k m ⊗ₜ[P] (1 : E₀)) = X.r k m
    rw [hχ, map_one, mul_one, hgY2]
  have h1 : χ.toRingHom.comp φ = RingHom.id X.E :=
    (hu _ ⟨hc1, hc2⟩).trans (hu _ ⟨RingHom.id_comp _, fun _ _ => rfl⟩).symm
  have hL : φ.comp gY = (Algebra.TensorProduct.includeLeft (S := P) : Y.E →ₐ[P] Y.E ⊗[P] E₀).toRingHom := by
    obtain ⟨v, -, hv⟩ := Y.univ (Y.E ⊗[P] E₀)
      ((Algebra.TensorProduct.includeLeft (S := P) : Y.E →ₐ[P] Y.E ⊗[P] E₀).toRingHom.comp
        (algebraMap P Y.E))
      (fun k m => Y.r k m ⊗ₜ[P] (1 : E₀))
      (fun k => by
        show Y.r k 0 ⊗ₜ[P] (1 : E₀) = _
        rw [Y.r_zero]
        rfl)
      hpow
    refine (hv _ ⟨?_, ?_⟩).trans (hv _ ⟨rfl, fun _ _ => rfl⟩).symm
    · rw [RingHom.comp_assoc, hgY1, ← RingHom.comp_assoc, hφ1]
      refine RingHom.ext fun x => ?_
      show (1 : Y.E) ⊗ₜ[P] ψ x = algebraMap P Y.E x ⊗ₜ[P] (1 : E₀)
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]
    · intro k m
      show φ (gY (Y.r k m)) = Y.r k m ⊗ₜ[P] (1 : E₀)
      rw [hgY2, hφ2]
  have h2 : φ.comp χ.toRingHom = RingHom.id (Y.E ⊗[P] E₀) := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul y e =>
      show φ (χ (y ⊗ₜ[P] e)) = y ⊗ₜ[P] e
      rw [hχ, map_mul, ← RingHom.comp_apply φ gY, hL, ← RingHom.comp_apply φ (algebraMap E₀ X.E), hφ1]
      show (y ⊗ₜ[P] (1 : E₀)) * ((1 : Y.E) ⊗ₜ[P] e) = y ⊗ₜ[P] e
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  let e : (Y.E ⊗[P] E₀) ≃+* X.E := RingEquiv.ofRingHom χ.toRingHom φ h1 h2
  refine ⟨e.toRingHom.comp (algebraMap Y.E (Y.E ⊗[P] E₀)), ?_⟩
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.2 hbc)
    (RingHom.Etale.of_bijective e.bijective)

theorem root_perf : ∀ (p : ℕ), p.Prime → ∀ {k E₀ : Type} [CommRing k] [CommRing E₀] (i : k →+* E₀) {d : ℕ} (t : Fin d → E₀), (MvPolynomial.eval₂Hom i t).Etale → D.Pf p k → ∀ X : RootExt p E₀ t, D.Pf p X.E ∧ ∀ π ∈ nonZeroDivisors k, algebraMap E₀ X.E (i π) ∈ nonZeroDivisors X.E := by
  intro p hp k E₀ instk instE i d t het hk X
  have hflat : i.Flat := GlobalTheory.CompanionTheory.LiftFlat.flat_of_eval₂Hom_etale i t het
  obtain ⟨Y⟩ := GlobalTheory.CompanionTheory.RootAdjoin.nonempty_rootExt p hp (MvPolynomial (Fin d) k)
    (MvPolynomial.X : Fin d → MvPolynomial (Fin d) k)
  have hY : D.Pf p Y.E := pf_rootExt p hp hk Y
  obtain ⟨ψ', hψ'⟩ := exists_etale_rootExt p (MvPolynomial.eval₂Hom i t) het MvPolynomial.X t
    (fun j => MvPolynomial.eval₂Hom_X' i t j) Y X
  refine ⟨GlobalTheory.CompanionTheory.EtalePerfect.pf_of_etale p hp ψ' hψ' hY, fun π hπ => ?_⟩
  letI : Algebra k E₀ := i.toAlgebra
  haveI : Module.Flat k E₀ := hflat
  have hreg : IsSMulRegular E₀ π := Module.Flat.isSMulRegular_of_nonZeroDivisors hπ
  haveI : Module.Free E₀ X.E := Module.Free.of_basis X.b
  haveI : Module.Flat E₀ X.E := Module.Flat.of_free
  have hreg' : IsSMulRegular E₀ (i π) := by
    rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg ⊢
    intro m hm
    apply hreg m
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simpa [smul_eq_mul] using hm
  have hreg'' := IsSMulRegular.of_flat (S := X.E) hreg'
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  apply hreg''.right_eq_zero_of_smul
  rw [Algebra.smul_def, mul_comm]
  exact hz

end GlobalTheory.CompanionTheory.RootPerf
