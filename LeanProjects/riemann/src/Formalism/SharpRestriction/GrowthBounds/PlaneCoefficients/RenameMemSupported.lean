import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TensZeroRight
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembVB
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.FrameZeroLe

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

namespace T5

theorem algHom_mem_supported {σ τ R : Type*} [CommSemiring R] (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (s : Set τ)
    (h : ∀ v, φ (X v) ∈ supported R s) (A : MvPolynomial σ R) : φ A ∈ supported R s := by
  induction A using MvPolynomial.induction_on with
  | C a =>
    rw [← algebraMap_eq, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq =>
    rw [map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ hp (h v)

theorem supp_zero {τ R : Type*} [CommSemiring R] {s : Set τ} {P : MvPolynomial τ R} (hP : P ∈ supported R s)
    {d : τ →₀ ℕ} (hd : d ∈ P.support) {v : τ} (hv : v ∉ s) : d v = 0 := by
  by_contra h
  exact hv ((mem_supported.1 hP) (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨d, hd, Finsupp.mem_support_iff.2 h⟩)))

theorem rename_mem_supported {σ τ R : Type*} [CommSemiring R] (f : σ → τ) (s : Set σ) (t : Set τ)
    (hst : ∀ v ∈ s, f v ∈ t) (A : MvPolynomial σ R) (hA : A ∈ supported R s) : rename f A ∈ supported R t := by
  rw [mem_supported] at hA ⊢
  intro w hw
  have h1 := vars_rename f A (Finset.mem_coe.1 hw)
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h1
  exact hst v (hA (Finset.mem_coe.2 hv))

end T5

section Main

variable (p : ℕ) {n' m r K : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K) (F : Frames n' r)

theorem plPart_supported (j : ℤ) (A : MvPolynomial (ℤ × Fin r) O) :
    rename (castV hk) (phSeg O K p F j (plEmb O r K A)) ∈ supported O {v : TV n' (m + 1) | v.2.val < r} := by
  have := T5.algHom_mem_supported (((rename (castV hk)).comp (phSeg O K p F j)).comp (plEmb O r K))
    {v : TV n' (m + 1) | v.2.val < r} (fun v => by
      simp only [AlgHom.comp_apply, plEmb, phSeg, rename_X, aeval_X, map_pow]
      refine Subalgebra.pow_mem _ (X_mem_supported.2 ?_) _
      show (Fin.cast hk.symm (Fin.castAdd K v.2)).val < r
      simp) A
  exact this

theorem noPart_supported (j : ℤ) (G : MvPolynomial (ℤ × Fin K) O) :
    rename (castV hk) (phSeg O K p F j (nmEmb O r K G)) ∈ supported O {v : TV n' (m + 1) | r ≤ v.2.val} := by
  have := T5.algHom_mem_supported (((rename (castV hk)).comp (phSeg O K p F j)).comp (nmEmb O r K))
    {v : TV n' (m + 1) | r ≤ v.2.val} (fun v => by
      simp only [AlgHom.comp_apply, nmEmb, phSeg, rename_X, aeval_X, map_pow]
      refine Subalgebra.pow_mem _ (X_mem_supported.2 ?_) _
      show r ≤ (Fin.cast hk.symm (Fin.natAdd r v.2)).val
      simp) G
  exact this

theorem symG_eq_mul (A : ℤ → MvPolynomial (ℤ × Fin r) O) (G : ℤ → MvPolynomial (ℤ × Fin K) O)
    (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) :
    symG p O hk F l ga (fun z => plEmb O r K (A z) * nmEmb O r K (G z)) = zPl p O hk F A l ga * zNo p O hk F G := by
  unfold symG zPl zNo
  rw [← map_mul]
  congr 1
  simp only [map_mul, Finset.prod_mul_distrib]
  ring

end Main

theorem restT_of (hGeo : RestGeo) : RestT := by
  intro p _ n' r K m _ _ _ O _ _ hk Fr L₁ N₁ hV J _ nL hJ hnL A G hA hG l hl ga hga rho dPl dNo
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hr : 1 ≤ r := NeZero.pos r
  have hGO : GeoOK Fr p nL := hGeo Fr L₁ N₁ hV p nL hJ hnL
  rw [symG_eq_mul]
  refine T5.lev_mul Fr p hk nL hp (l.mapDomain (castV hk) + ga) _ _ ?_ ?_ ?_ rho dPl dNo
  ·
    intro a ha
    have hLD : LD Fr p hk nL (rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (plEmb O r K (A j)))) := by
      rw [map_prod]
      refine LD_prod Fr p hk nL _ _ fun j hj => LD_phSeg Fr p hk nL hGO j (Finset.mem_range.1 hj) _ ?_
      exact T5.rename_mem_supported (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) _ _ (fun v hv => hv) _
        (hA j (Finset.mem_range.1 hj))
    have hSu : rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (plEmb O r K (A j))) ∈
        supported O {v : TV n' (m + 1) | v.2.val < r} := by
      rw [map_prod]
      exact Subalgebra.prod_mem _ fun j _ => plPart_supported p O hk Fr j (A j)
    have e1 : rename (castV hk) ((∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (plEmb O r K (A j))) * monomial l 1) *
        monomial ga 1 = rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (plEmb O r K (A j))) *
          monomial (l.mapDomain (castV hk) + ga) 1 := by
      rw [map_mul, MvPolynomial.rename_monomial, mul_assoc, monomial_mul, one_mul]
    have h1 := MvPolynomial.support_map_subset (algebraMap O (KK O)) _ ha
    rw [e1] at h1
    obtain ⟨d, hd, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ h1)
    have hb' := MvPolynomial.support_monomial_subset hb
    rw [Finset.mem_singleton] at hb'
    subst hb'
    refine ⟨d, hLD d hd, fun x c => T5.supp_zero hSu hd ?_, add_comm _ _⟩
    show ¬ (Fin.cast hk.symm (Fin.natAdd r c)).val < r
    simp
  ·
    intro b hb
    have hLD : LD Fr p hk nL (rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (nmEmb O r K (G j)))) := by
      rw [map_prod]
      refine LD_prod Fr p hk nL _ _ fun j hj => LD_phSeg Fr p hk nL hGO j (Finset.mem_range.1 hj) _ ?_
      exact T5.rename_mem_supported (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) _ _ (fun v hv => hv.1) _
        (hG j (Finset.mem_range.1 hj))
    have hSu : rename (castV hk) (∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (nmEmb O r K (G j))) ∈
        supported O {v : TV n' (m + 1) | r ≤ v.2.val} := by
      rw [map_prod]
      exact Subalgebra.prod_mem _ fun j _ => noPart_supported p O hk Fr j (G j)
    have h1 := MvPolynomial.support_map_subset (algebraMap O (KK O)) _ hb
    refine ⟨hLD b h1, fun x a => T5.supp_zero hSu h1 ?_⟩
    show ¬ r ≤ (Fin.cast hk.symm (Fin.castAdd K a)).val
    simp
  ·
    intro x c
    have h0 : ga (noVar Fr hk nL x c) = 0 := by
      by_contra h
      have := (hga _ h).1
      have h2 : (noVar Fr hk nL x c).2.val = r + c.val := by
        show (Fin.cast hk.symm (Fin.natAdd r c)).val = _
        simp
      omega
    have h1 : (l.mapDomain (castV hk)) (noVar Fr hk nL x c) = l (posOf n' (posTL Fr x), Fin.natAdd r c) :=
      Finsupp.mapDomain_apply (castV_inj hk) l (posOf n' (posTL Fr x), Fin.natAdd r c)
    rw [Finsupp.add_apply, h0, add_zero, h1]
    have h3 := Formalism.MainNotions.Proposition5Numerics.tl_mem_letters hV hr hnL x
    exact hl (segZ x.1) (posTL Fr x) h3.1 h3.2 _

theorem restT : RestT := restT_of restGeo

end Formalism.MainNotions.PairMembershipBlocks
