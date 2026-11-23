import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentMulOfMapsToParabolicInduction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationUnitsMapEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

noncomputable section

namespace GlobalTheory.RegType

section Finite

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def AllLab (L : LabelDatum g) : Prop := ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → ∃ P, IsCuspOf L P χ

theorem label_exists (L : LabelDatum g) (hA : AllLab L) {n : ℕ} (χ : Gn g n → ℂ)
    (hχ : IsIrr χ) : ∃ f, HasLabel L χ f := by
  obtain ⟨C, hC, hd, hi⟩ := GlobalTheory.T.exists_cuspidal_list_harishChandra_pairing_ne_zero g n χ hχ
  have hs : (C.map fun c => (Label.lab L c, c)).map Prod.snd = C := by
    rw [List.map_map]; exact List.map_id' C
  refine ⟨_, C.map fun c => (Label.lab L c, c), ?_, ?_, rfl, ?_⟩
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
    have h4 := hA c.1 c.2 (hC c hc)
    show IsCuspOf L (Label.lab L c) c.2
    rw [Label.lab, dif_pos h4]; exact h4.choose_spec
  · rw [hs]; exact hd
  · rw [hs]; exact hi

theorem label_mon (L : LabelDatum g) {n : ℕ} (χ : Gn g n → ℂ) (f : (ZMod g)[X]) (h : HasLabel L χ f) :
    f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
  obtain ⟨Q, hQ, hd, rfl, -⟩ := h
  exact hd ▸ Label.prod_props L Q hQ

theorem eSerC_laws (L : LabelDatum g) (hg : 5 ≤ g) (hA : AllLab L) (n : ℕ) :
    (∀ f, eSerC L n f * eSerC L n f = eSerC L n f) ∧ (∀ f a, eSerC L n f * a = a * eSerC L n f) ∧
    (∀ f f', f ≠ f' → eSerC L n f * eSerC L n f' = 0) ∧
    (∀ f, ¬ (f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) → eSerC L n f = 0) ∧
    ∃ S : Finset (ZMod g)[X], ∑ f ∈ S, eSerC L n f = 1 := by
  have huniq : ∀ χ : Gn g n → ℂ, IsIrr χ → ∃! f, HasLabel L χ f := fun χ hχ => by
    obtain ⟨f, hf⟩ := label_exists L hA χ hχ
    exact ⟨f, hf, fun f' hf' => Label.label_unique L hg χ hχ f' f hf' hf⟩
  have hmon := label_mon L (n := n)
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  have horth := GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central (Gn g n)
  have hmem : ∀ f χ, χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f) ↔ IsIrr χ ∧ HasLabel L χ f := by
    intro f χ; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [eSerC_eq_sum L n hfin, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Finset.sum_congr rfl fun χ' hχ' =>
      (horth χ χ' ((hmem f χ).1 hχ).1 ((hmem f χ').1 hχ').1).1]
    rw [Finset.sum_eq_single_of_mem χ hχ]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
  · intro f a
    rw [eSerC_eq_sum L n hfin, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    exact (horth χ χ ((hmem f χ).1 hχ).1 ((hmem f χ).1 hχ).1).2.1 a
  · intro f f' hne
    rw [eSerC_eq_sum L n hfin, eSerC_eq_sum L n hfin, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun χ hχ => Finset.sum_eq_zero fun χ' hχ' => ?_
    obtain ⟨h1, h2⟩ := (hmem f χ).1 hχ
    obtain ⟨h3, h4⟩ := (hmem f' χ').1 hχ'
    rw [(horth χ χ' h1 h3).1, if_neg]
    rintro rfl
    exact hne ((huniq χ h1).unique h2 h4)
  · intro f hf
    rw [eSerC_eq_sum L n hfin]
    refine Finset.sum_eq_zero fun χ hχ => ?_
    exact absurd (hmon χ f ((hmem f χ).1 hχ).2) hf
  · have hS : {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0}.Finite :=
      (finite_natDegree_eq n).subset fun f hf => hf.2.1
    refine ⟨hS.toFinset, ?_⟩
    have h1 : ∑ χ ∈ hfin.toFinset, zOf χ = 1 := by
      rw [← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [← h1]
    simp only [eSerC_eq_sum L n hfin, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hirr : IsIrr χ := by simpa using hχ
    obtain ⟨f, hf, hu⟩ := huniq χ hirr
    rw [Finset.sum_eq_single_of_mem f (by simpa using hmon χ f hf), if_pos hf]
    intro b _ hb
    exact if_neg fun h => hb (hu b h)

theorem ser_vanish (L : LabelDatum g) (h5 : 5 ≤ g) {k l n : ℕ} (σ : Fin k ⊕ Fin l ≃ Fin n)
    (f f₁ f₂ : (ZMod g)[X]) (hf : f ≠ f₁ * f₂) :
    eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁) * mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂) *
      eSerC L n f = 0 := by
  have hn : n = k + l := by simpa using (Fintype.card_congr σ).symm
  refine finsum_mem_induction (fun a => eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) a *
    mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂) * eSerC L n f = 0) (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, mul_add, add_mul, hx, hy, add_zero]
  rintro α ⟨hα, hα'⟩
  refine finsum_mem_induction (fun b => eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) (zOf α) *
    mapDomainAlgHom ℂ ℂ (inB σ) b * eSerC L n f = 0) (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, mul_add, add_mul, hx, hy, add_zero]
  rintro β ⟨hβ, hβ'⟩
  refine finsum_mem_induction (fun c => eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) (zOf α) *
    mapDomainAlgHom ℂ ℂ (inB σ) (zOf β) * c = 0) (by simp) ?_ ?_
  · intro x y hx hy
    simp only [mul_add, hx, hy, add_zero]
  rintro χ ⟨hχ, hχ'⟩
  refine irr_vanish σ χ α β hχ hα hβ ?_
  by_contra hne
  exact hf (Label.label_unique L h5 χ hχ _ _ hχ'
    (GlobalTheory.T.harishChandraSeriesLabel_mul_of_constituent g L k l n χ α β f₁ f₂ hn hχ hα hβ hα' hβ' hne))

theorem ser_vanish' (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L) {k l n : ℕ} (σ : Fin k ⊕ Fin l ≃ Fin n)
    (f f₁ f₂ : (ZMod g)[X]) (hf : f ≠ f₁ * f₂) :
    eSerC L n f * mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂) * mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁) *
      eN g σ = 0 := by
  have cA : Commute (eN g σ) (mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁)) :=
    commute_map (inA σ) (eN g σ) (fun x c => eN_comm σ x 1 c) _
  have cB : Commute (eN g σ) (mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂)) :=
    commute_map (inB σ) (eN g σ) (fun x c => eN_comm σ 1 x c) _
  rw [mul_assoc, mul_assoc, (eSerC_laws L h5 hA n).2.1, ← mul_assoc, ← (commute_AB σ _ _).eq,
    ← (cA.mul_right cB).eq, ← mul_assoc]
  exact ser_vanish L h5 σ f f₁ f₂ hf

def sysOf (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L) : Sys g where
  e := eSerC L
  idem n := (eSerC_laws L h5 hA n).1
  central n := (eSerC_laws L h5 hA n).2.1
  orth n := (eSerC_laws L h5 hA n).2.2.1
  label n f h := by by_contra h'; exact h ((eSerC_laws L h5 hA n).2.2.2.1 f h')
  sum n := (eSerC_laws L h5 hA n).2.2.2.2
  mul a b n hn f f' V _ _ ρ v h0 h1 h2 := by
    subst hn
    have hN : ρ.asAlgebraHom (eN g (finSumFinEquiv (m := a) (n := b))) v = v := eN_right _ ρ v fun B => by
      refine h0 _ (fun i j hj hi => ?_) ?_ ?_
      · rw [← ParInd.entN_self (par finSumFinEquiv (1 : Gn g a) B (1 : Gn g b)).val]
        exact (Supp.entN_par _ _ _ i j).2.1 hi hj
      · ext i j
        rw [tl, (Supp.entN_par _ _ _ i j).1 i.2 j.2, ParInd.entN_self]; rfl
      · ext i j
        rw [br, (Supp.entN_par _ _ _ i j).2.2.1, ParInd.entN_self]; rfl
    have hA' : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (eSerC L a f)) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [OfLabel.blk_eq_par] at h1; exact h1
    have hB : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (eSerC L b f')) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [OfLabel.blk_eq_par] at h2; exact h2
    obtain ⟨S, hS⟩ := (eSerC_laws L h5 hA (a + b)).2.2.2.2
    have hz : ∀ F, F ≠ f * f' → ρ.asAlgebraHom (eSerC L (a + b) F) v = 0 := fun F hF => by
      have hv := ser_vanish' L h5 hA (finSumFinEquiv (m := a) (n := b)) F f f' hF
      have := congrArg (fun z => ρ.asAlgebraHom z v) hv
      simpa only [map_mul, Module.End.mul_apply, hN, hA', hB, map_zero, LinearMap.zero_apply] using this
    have e : v = ∑ F ∈ S, ρ.asAlgebraHom (eSerC L (a + b) F) v := by
      rw [← LinearMap.sum_apply, ← map_sum, hS, map_one, Module.End.one_apply]
    by_cases hm : f * f' ∈ S
    · rw [Finset.sum_eq_single_of_mem _ hm fun F _ hF => hz F hF] at e; exact e.symm
    · rw [Finset.sum_eq_zero fun F hF => hz F (by rintro rfl; exact hm hF)] at e; rw [e]; simp

theorem isCuspOf_of_series (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L) {d : ℕ} (τ : FDRep ℂ (Gn g d))
    (hc : IsCusp τ.character) (f : (ZMod g)[X])
    (he : Representation.asAlgebraHom τ.ρ ((sysOf L h5 hA).e d f) = 1) : IsCuspOf L f τ.character := by
  obtain ⟨P, hP⟩ := hA d _ hc
  have : f = P := by
    by_contra hne
    obtain ⟨h1, h2⟩ := Bridge.tr_eSerC_eq L hP.2.1.2.1 (Bridge.hasLabel_of_isCuspOf L hP)
    rw [← Bridge.trace_alg] at h1
    have h0 : Representation.asAlgebraHom τ.ρ ((sysOf L h5 hA).e d P) = 0 := by
      rw [← one_mul (Representation.asAlgebraHom τ.ρ _), ← he, ← map_mul, (sysOf L h5 hA).orth _ _ _ hne, map_zero]
    exact h2 (h1.symm.trans ((congrArg _ h0).trans (map_zero _)))
  exact this ▸ hP

theorem eSerC_mul_zOf (L : LabelDatum g) {n : ℕ} {χ : Gn g n → ℂ} {f : (ZMod g)[X]} (hχ : IsIrr χ)
    (hf : HasLabel L χ f) : eSerC L n f * zOf χ = zOf χ := by
  have hfin := (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1
  rw [eSerC_eq_sum L n hfin, Finset.sum_mul, Finset.sum_eq_single_of_mem χ (by simp [hχ, hf])]
  · simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).1
  · intro b hb hne
    have hb' : IsIrr b := by simpa using (Finset.mem_filter.1 hb).1
    rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ b χ hb' hχ).1, if_neg hne]

end Finite

section Padic

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.SerSys.Prod Formalism.MainNotions.ArithmeticCylinders TensorProduct GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem series_of_sep (S : Sys g) (a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
    [Module ℂ W'] (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W') (h1 : IsUnram ν₁) (h2 : IsUnram ν₂)
    (hsep : ∀ v, (∀ h, Λ (π h v) = 0) → v = 0)
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (F : (ZMod g)[X]) (hF : Has S π F) :
    ∃ f f', Has S σ f ∧ Has S ρ f' ∧ F = f * f' := by
  have hint : ∀ x B y v, Λ (π (inc g _ (parZ x B y)) v) =
      TensorProduct.map (σ (inc g a x)) (ρ (inc g b y)) (Λ v) := by
    intro x B y v
    rw [hΛ _ (inc g a x) (inc g b y), ParInd.det_inc, ParInd.det_inc, h1, h2, one_mul, Units.val_one, one_smul]
    · intro i j hj hi
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      rw [ParInd.inc_val, Matrix.map_apply, parZ_apply]
      rcases i with i | i
      · have := i.2
        simp at hi
        omega
      rcases j with j | j
      · simp
      · simp at hj
    · intro i j
      rw [ParInd.entN_tl, ParInd.inc_val, ParInd.inc_val, Matrix.map_apply, Matrix.map_apply]
      exact congrArg _ (parZ_apply x B y (.inl i) (.inl j)).symm
    · intro i j
      rw [ParInd.entN_br, ParInd.inc_val, ParInd.inc_val, Matrix.map_apply, Matrix.map_apply]
      exact congrArg _ (parZ_apply x B y (.inr i) (.inr j)).symm
  let T : fixK1 π →ₗ[ℂ] W ⊗[ℂ] W' := Λ ∘ₗ (fixK1 π).subtype

  obtain ⟨w, hw0⟩ : ∃ w : fixK1 π, T ((repK π).asAlgebraHom (S.e _ F) w) ≠ 0 := by
    obtain ⟨v₀, hv₀, hne⟩ := hF
    let v : fixK1 π := (repK π).asAlgebraHom (S.e _ F) ⟨v₀, hv₀⟩
    have hv0 : (v : V) ≠ 0 := by rwa [repK_alg]
    by_contra hcon
    push Not at hcon
    have hk : ∀ k, Λ (π (inc g _ k) v) = 0 := by
      intro k
      rw [← repK_red, ← hcon (repK π (red g _ k) ⟨v₀, hv₀⟩), ← Representation.asAlgebraHom_single_one,
        ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, S.central]
      rfl
    let U : Submodule ℂ V := ⨅ h : GL (Fin (a + b)) ℚ_[g], LinearMap.ker (Λ ∘ₗ π h)
    have hU : ∀ w, w ∈ U ↔ ∀ h, Λ (π h w) = 0 := by
      intro w; simp [U, Submodule.mem_iInf]
    have hvU : (v : V) ∈ U := by
      rw [hU]
      intro h
      obtain ⟨p, k, hp, rfl⟩ := GlobalTheory.GLp.exists_upper_mul_inc g _ h
      have hp' : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → p.val i j = 0 :=
        fun i j hj hi => hp i j (by rw [Fin.lt_def]; omega)
      obtain ⟨x, y, hx, hy⟩ := ParInd.exists_blocks p hp'
      rw [map_mul, Module.End.mul_apply, hΛ p x y hp' hx hy, hk, map_zero, smul_zero]
    exact hv0 (hsep _ ((hU _).1 hvU))
  have hT : ∀ x (B : Matrix (Fin a) (Fin b) ℤ_[g]) y u,
      T (repK π (par finSumFinEquiv (red g a x) (B.map (PadicInt.toZMod (p := g))) (red g b y)) u) =
      TensorProduct.map (σ (inc g a x)) (ρ (inc g b y)) (T u) := fun x B y u => by
    rw [← red_parZ]
    exact (congrArg Λ (repK_red π _ u)).trans (hint x B y u)
  have hN : ∀ u, T ((repK π).asAlgebraHom (eN g finSumFinEquiv) u) = T u := eN_left _ _ T fun B => by
    have hs := ZMod.ringHom_surjective (PadicInt.toZMod (p := g))
    have e : (B.map (Function.surjInv hs)).map (PadicInt.toZMod (p := g)) = B := by
      ext i j; exact Function.surjInv_eq hs _
    ext1 u
    have := hT 1 (B.map (Function.surjInv hs)) 1 u
    simpa [e, TensorProduct.map_one] using this
  have hsum : ∀ {m : ℕ} (i : Gn g m →* Gn g (a + b)) (u : fixK1 π), T u ≠ 0 →
      ∃ f, T ((repK π).asAlgebraHom (mapDomainAlgHom ℂ ℂ i (S.e m f)) u) ≠ 0 := by
    intro m i u hu
    obtain ⟨R, hR⟩ := S.sum m
    have e : u = ∑ f ∈ R, (repK π).asAlgebraHom (mapDomainAlgHom ℂ ℂ i (S.e m f)) u := by
      rw [← LinearMap.sum_apply, ← map_sum, ← map_sum, hR, map_one, map_one, Module.End.one_apply]
    rw [e, map_sum] at hu
    obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
    exact ⟨f, hf⟩
  obtain ⟨f₂, hf₂⟩ := hsum (inB finSumFinEquiv) _ hw0
  obtain ⟨f₁, hf₁⟩ := hsum (inA finSumFinEquiv) _ hf₂
  refine ⟨f₁, f₂, ?_, ?_, ?_⟩
  · obtain ⟨P, hP, hP'⟩ := exists_dual_right _ hf₁
    refine has_of_eqv S π σ (inA finSumFinEquiv) (P ∘ₗ T) (fun x u => ?_) f₁ _ hP
    have := hT x 0 1 u
    rw [map_one, map_one, map_one, Matrix.map_zero _ (map_zero _)] at this
    exact (congrArg P this).trans (hP' _ _)
  · obtain ⟨P, hP, hP'⟩ := exists_dual_left _ hf₂
    refine has_of_eqv S π ρ (inB finSumFinEquiv) (P ∘ₗ T) (fun y u => ?_) f₂ _ hP
    have := hT 1 0 y u
    rw [map_one, map_one, map_one, Matrix.map_zero _ (map_zero _)] at this
    exact (congrArg P this).trans (hP' _ _)
  · by_contra h12
    apply hf₁
    rw [← hN, ← Module.End.mul_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      ← map_mul, vanish S _ F f₁ f₂ h12, map_zero]

open GlobalTheory.SmGL GlobalTheory.PRep in

theorem series_prod₂ (S : Sys g) {a b : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
    [Module ℂ W'] (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (F : (ZMod g)[X]) (hF : Has S (prod₂ σ ρ) F) : ∃ f f', Has S σ f ∧ Has S ρ f' ∧ F = f * f' := by
  have h : a + b = a + b := rfl
  let Λ : IndSp (two (stdSum h)) ((extTensor σ ρ).comp (leviTwo ℚ_[g] (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ]
      W ⊗[ℂ] W' := { toFun := fun f => f.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine series_of_sep S a b _ (prod₂ σ ρ) W W' σ ρ (absPow ℚ_[g] ((b : ℂ) / 2)) (absPow ℚ_[g] (-(a : ℂ) / 2)) Λ
    (fun u => isUnram_absPow ℚ_[g] _ _ (valuation_units_map_eq_one u))
    (fun u => isUnram_absPow ℚ_[g] _ _ (valuation_units_map_eq_one u)) (fun v hv => ?_) ?_ F hF
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have := hv x
    change v.1.1 (1 * x) = 0 at this
    rw [one_mul] at this
    exact this
  · intro p x y h0 hx hy v
    have hp : p ∈ parab ℚ_[g] (two (stdSum h)) := by
      rw [mem_parab_iff]
      rintro (_|_) (_|_) i j hlt
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · apply h0
        · show ((stdSum h (Sum.inl j) : Fin (a + b)) : ℕ) < a
          rw [stdSum_inl]; exact j.isLt
        · show a ≤ ((stdSum h (Sum.inr i) : Fin (a + b)) : ℕ)
          rw [stdSum_inr]; omega
      · exact absurd hlt (by decide)
    have hl : leviProj ℚ_[g] (two (stdSum h)) ⟨p, hp⟩ = leviTwo ℚ_[g] (Fin a) (Fin b) (x, y) := by
      funext c
      cases c
      · refine Units.ext (Matrix.ext fun i j => ?_)
        rw [leviProj_apply]
        show _ = (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j
        have hi : (i : ℕ) < a + b := by omega
        have hj : (j : ℕ) < a + b := by omega
        rw [hx]
        simp only [Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
        rfl
      · refine Units.ext (Matrix.ext fun i j => ?_)
        rw [leviProj_apply]
        show _ = (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j
        have hi : a + (i : ℕ) < a + b := by omega
        have hj : a + (j : ℕ) < a + b := by omega
        rw [hy]
        simp only [Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
        rfl
    have key := parInd_law _ _ v ⟨p, hp⟩ 1
    rw [hl, deltaHalf_two] at key
    simp only [Fintype.card_fin, mul_one] at key
    change v.1.1 (1 * p) = _
    rw [one_mul, key]
    congr 1

theorem actK_map {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} {π' : Representation ℂ (GL (Fin n) ℚ_[g]) V'} (T : V →ₗ[ℂ] V')
    (hT : ∀ x v, T (π x v) = π' x (T v)) (a : MonoidAlgebra ℂ (Gn g n)) (v : V) :
    T (actK π a v) = actK π' a (T v) := by
  simp only [actK, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hT]

open GlobalTheory.SmGL GlobalTheory.PRep in

theorem has_of_isSubquotient (S : Sys g) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} {π' : Representation ℂ (GL (Fin n) ℚ_[g]) V'}
    (hs : IsSmooth π') (h : IsSubquotient π π') {F : (ZMod g)[X]} (hF : Has S π F) : Has S π' F := by
  obtain ⟨U, T, hT⟩ := h
  obtain ⟨v, hv, hv0⟩ := hF
  obtain ⟨u, rfl⟩ := hT v
  have hU : IsSmooth U.toRepresentation := fun y => by
    have := hs y.1
    convert this using 3 with x
    exact Subtype.ext_iff
  obtain ⟨y, hy, hyu⟩ := IwahoriOnto.exists_fixed_map_eq hU (GlobalTheory.DepthZeroCusp.isCompact_KOne (g := g) (n := n))
    T.toLinearMap u fun x hx => by
      obtain ⟨k, hk, rfl⟩ := hx
      exact (T.isIntertwining _ _ _ u).trans ((Model.mem_principalCongruenceFixedVectors_iff π _).1 hv k hk)
  refine ⟨y.1, (Model.mem_principalCongruenceFixedVectors_iff π' _).2 fun k hk => ?_, fun h0 => hv0 ?_⟩
  · have := hy ⟨inc g n k, k, hk, rfl⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at this
    exact congrArg Subtype.val this
  · have e1 : (actK U.toRepresentation (S.e n F) y).1 = actK π' (S.e n F) y.1 :=
      actK_map U.toSubmodule.subtype (fun _ _ => rfl) _ y
    have e2 : actK U.toRepresentation (S.e n F) y = 0 := Subtype.ext (e1.trans h0)
    have e3 := actK_map T.toLinearMap (fun x v => T.isIntertwining _ _ x v) (S.e n F) y
    rw [e2, map_zero, hyu] at e3
    exact e3.symm

open GlobalTheory.SmGL GlobalTheory.PRep in

theorem series_multiProd_std (S : Sys g) {s : ℕ} : ∀ {d : Fin s → ℕ} {X : Fin s → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] {N : ℕ} (hd : ∑ i, d i = N)
    (σ : ∀ i, Representation ℂ (GL (Fin (d i)) ℚ_[g]) (X i)) (F : (ZMod g)[X]),
    Has S (multiProd (stdBlocks d hd) σ) F → ∃ f : Fin s → (ZMod g)[X], (∀ i, Has S (σ i) (f i)) ∧ F = ∏ i, f i := by
  induction s with
  | zero =>
    intro d X _ _ N hd σ F hF
    obtain rfl : N = 0 := by simpa using hd.symm
    obtain ⟨v, -, hv⟩ := hF
    have he : S.e 0 F ≠ 0 := fun e => hv (by rw [e]; simp [actK])
    obtain ⟨hm, hdg, -⟩ := S.label _ _ he
    exact ⟨fun i => i.elim0, fun i => i.elim0, by simpa using hm.natDegree_eq_zero.1 hdg⟩
  | succ s ih =>
    intro d X _ _ N hd σ F hF
    obtain rfl : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨E⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have h1 := has_of_isSubquotient S (isSmooth_prod₂ _ _)
      (IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective) hF
    obtain ⟨f, f', hf, hf', rfl⟩ := series_prod₂ S _ _ F h1
    obtain ⟨fs, hfs, rfl⟩ := ih (d := fun i => d i.succ) (X := fun i => X i.succ) rfl (fun i => σ i.succ) f' hf'
    refine ⟨Fin.cons f fs, fun i => ?_, by rw [Fin.prod_univ_succ]; rfl⟩
    induction i using Fin.cases with
    | zero => exact hf
    | succ i => exact hfs i

open GlobalTheory.SmGL GlobalTheory.PRep in

theorem series_of_isSubquotient (S : Sys g) {s N : ℕ} {d : Fin s → ℕ} {X : Fin s → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (e : (Σ a, Fin (d a)) ≃ Fin N)
    (σ : ∀ i, Representation ℂ (GL (Fin (d i)) ℚ_[g]) (X i)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) ℚ_[g]) V} (h : IsSubquotient π (multiProd e σ)) (F : (ZMod g)[X])
    (hF : Has S π F) : ∃ f : Fin s → (ZMod g)[X], (∀ i, Has S (σ i) (f i)) ∧ F = ∏ i, f i := by
  have hd : ∑ a, d a = N := by simpa using Fintype.card_congr e
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing ℚ_[g] _ _ _ e (stdBlocks d hd) _).1 (piTensor σ)
  exact series_multiProd_std S hd σ F (has_of_isSubquotient S (isSmooth_parInd _ _)
    (h.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)) hF)

end Padic

end GlobalTheory.RegType

end
