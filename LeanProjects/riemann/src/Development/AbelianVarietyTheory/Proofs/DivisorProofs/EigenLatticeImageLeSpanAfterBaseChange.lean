import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.LieSpanBaseChange

open GlobalTheory.CM.LieBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {j : K →+* K'}

theorem exists_genFib_baseChange (T : PAT H (Sp (𝓞 K))) (T' : PAT H (Sp (𝓞 K')))
    (m : SABMap T'.t T.t (spMap (RingOfIntegers.mapRingHom j))) (F : GenFib T.pol) :
    ∃ (Q : Out.PolAV (Sp K')) (hd : SmoothOfRelativeDimension F.P₀.g Q.A.hom) (φ' : Q.A.left ⟶ T'.t.G.left)
      (fib : IsPolFibre (algebraMap (𝓞 K') K') T'.pol (withDim Q F.P₀.g hd) φ')
      (v' : Fin F.P₀.g → (epsR K' ⟶ Q.A)) (basis : IsLieBasis v'),
      (∀ τ : 𝓞 E →+* 𝓞 K, (GenFib.mk (withDim Q F.P₀.g hd) φ' fib v' basis : GenFib T'.pol).eigLat T'.t.act
          ((RingOfIntegers.mapRingHom j).comp τ) =
        Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K)))) ∧
      ∀ (u : epsR (𝓞 K) ⟶ T.t.G) (c : Fin F.P₀.g → K), F.IsCoord u c → ∀ u' : epsR (𝓞 K') ⟶ T'.t.G,
        IsVecOver (RingOfIntegers.mapRingHom j) m.φ u u' →
        (GenFib.mk (withDim Q F.P₀.g hd) φ' fib v' basis : GenFib T'.pol).IsCoord u' (fun i => j (c i)) := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hB : Out.PolBaseChangeSt := hL.polBaseChange
  have hdT : SmoothOfRelativeDimension T.g T'.t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m.cart.1 T.dim
  have hξ : IsPolFibre (RingOfIntegers.mapRingHom j) T.pol T'.pol m.φ :=
    ⟨H1.dim_unique _ T'.dim hdT (eSec T'.t.G (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (𝓞 K'))), m.cart,
      (PAT.exists_of_sabMap E H _ _ _ T T'.t m).2⟩
  obtain ⟨F'⟩ := GenFib.nonempty_of_baseChange hB K' T'.pol
  have hg : F'.P₀.g = F.P₀.g := F'.fib.1.trans (hξ.1.trans F.fib.1.symm)
  have hd : SmoothOfRelativeDimension F.P₀.g F'.P₀.A.hom := hg ▸ F'.P₀.smoothDim
  have fib : IsPolFibre (algebraMap (𝓞 K') K') T'.pol (withDim F'.P₀ F.P₀.g hd) F'.φ := ⟨hg.symm.trans F'.fib.1, F'.fib.2⟩
  obtain ⟨ψ, hψ, w⟩ := PolFibre.cancel (g := j) F.fib (PolFibre.comp hξ fib)
  haveI := F.P₀.isAb.comm
  haveI := F'.P₀.isAb.comm
  haveI := F.P₀.smoothDim
  obtain ⟨v', basis, hv⟩ := exists_isLieBasis_baseChange K K' j F.P₀.A F'.P₀.A ψ hψ.2.1
    (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
  refine ⟨F'.P₀, hd, F'.φ, fib, v', basis, fun τ => ?_, fun u c hc u' hu => ?_⟩
  · exact eigLat_eq_span hB hξ hψ.2.1 w hv T.t.act T'.t.act m.act τ
  · exact isCoord_over hξ.2.1 hψ.2.1 w hv hc hu

end GlobalTheory.CM.LieSpanBaseChange
end

noncomputable section
namespace GlobalTheory.CM.LieSpanBaseChange

open GlobalTheory.CM.LieBaseChange GlobalTheory.CM.IntCoord

theorem eigLat_image_le_span_diff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G))
    (f' : Fin n → (A'.t.G ⟶ B'.t.G)) (g' : Fin n → (B'.t.G ⟶ A'.t.G)),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) → (∀ i, Serre.IsLinearHom A'.t.act B'.t.act (f' i)) →
    (∀ i, Serre.IsLinearHom B'.t.act A'.t.act (g' i)) → (∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) →
    ∏ i, (g' i ≫ f' i) = 𝟙 B'.t.G →
    ∀ (FA : GenFib A.pol) (FB : GenFib B.pol) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
    (∀ i, FA.IsDiffOf FB (f i) (M i)) → ∀ (τ : 𝓞 E →+* 𝓞 K), ∀ w ∈ FB.eigLat B.t.act τ,
    (fun k => j (w k)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) := by
  intro E _ _ _ H K K' _ _ _ _ j A B A' B' mA mB n f f' g' _ hf' hg' hff' hid FA FB M hM τ w hw
  obtain ⟨QA, hdA, φA, fibA, vA, bA, hA1, hA2⟩ := exists_genFib_baseChange A A' mA FA
  obtain ⟨QB, hdB, φB, fibB, vB, bB, hB1, hB2⟩ := exists_genFib_baseChange B B' mB FB
  let F₁A : GenFib A'.pol := GenFib.mk (withDim QA FA.P₀.g hdA) φA fibA vA bA
  let F₁B : GenFib B'.pol := GenFib.mk (withDim QB FB.P₀.g hdB) φB fibB vB bB
  have hcB := GlobalTheory.T.integral_tangent_vector_coordinates K' _ F₁B
  choose M' hM' using fun i =>
    ((DiffCoord.existsUnique_isDiffOf K' A'.pol F₁A B'.pol F₁B (f' i) (hf' i).isMonHom).1).exists
  choose N' hN' using fun i =>
    ((DiffCoord.existsUnique_isDiffOf K' B'.pol F₁B A'.pol F₁A (g' i) (hg' i).isMonHom).1).exists
  set S := Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) with hSdef
  have hjadd : ∀ {m : ℕ} (x y : Fin m → K), (fun k => j ((x + y) k)) = (fun k => j (x k)) + (fun k => j (y k)) :=
    fun x y => funext fun k => by simp
  have hjsmul : ∀ {m : ℕ} (r : 𝓞 K) (x : Fin m → K),
      (fun k => j ((r • x) k)) = (RingOfIntegers.mapRingHom j r) • (fun k => j (x k)) :=
    fun r x => funext fun k => by
      rw [← algebraMap_smul K r x, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, ← algebraMap_smul K',
        smul_eq_mul]
      rfl
  have hcomp : ∀ i, ∀ e ∈ FA.eigLat A.t.act τ, M' i (fun k => j (e k)) = fun k => j (M i e k) := by
    intro i e he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, -⟩ := hx
      obtain ⟨u', hu', -⟩ := existsUnique_isVecOver mA.cart.1 u
      have h1 := hM' i u' _ (hA2 u x hu u' hu')
      have h2 := hB2 (u ≫ f i) (M i x) (hM i u x hu) (u' ≫ f' i) (by
        unfold IsVecOver at hu' ⊢
        rw [Over.comp_left, Over.comp_left, Category.assoc, hff' i, ← Category.assoc, hu', Category.assoc])
      exact (hcB.1 _ h1.1).unique h1 h2
    | zero =>
      have h0 : (fun k => j ((0 : Fin FA.P₀.g → K) k)) = 0 := funext fun k => by simp
      rw [h0, map_zero, map_zero]
      funext k
      simp
    | add x y _ _ hx hy =>
      rw [hjadd, map_add, hx, hy, map_add, hjadd]
    | smul r x _ hx =>
      rw [hjsmul, ← algebraMap_smul K' (RingOfIntegers.mapRingHom j r), map_smul, hx, algebraMap_smul,
        ← algebraMap_smul K r x, map_smul, algebraMap_smul, hjsmul]
  have hS : ∀ i, ∀ x ∈ Submodule.span (𝓞 K') ((fun (c : Fin FA.P₀.g → K) k => j (c k)) ''
      (FA.eigLat A.t.act τ : Set (Fin FA.P₀.g → K))), M' i x ∈ S := by
    intro i x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      rw [hcomp i e he]
      exact Submodule.subset_span ⟨M i e, ⟨i, e, he, rfl⟩, rfl⟩
    | zero =>
      rw [map_zero]
      exact S.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact S.add_mem hx hy
    | smul s x _ hx =>
      rw [← algebraMap_smul K' s x, map_smul, algebraMap_smul]
      exact S.smul_mem s hx
  have hkey : F₁B.eigLat B'.t.act ((RingOfIntegers.mapRingHom j).comp τ) ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro c' ⟨u', hu', heig⟩
    have hN'mem : ∀ i, N' i c' ∈ F₁A.eigLat A'.t.act ((RingOfIntegers.mapRingHom j).comp τ) := fun i =>
      Indep.map_eigLat_le (hg' i).comm (hN' i) _
        (Submodule.mem_map_of_mem (f := (N' i).restrictScalars (𝓞 K')) (Submodule.subset_span ⟨u', hu', heig⟩))
    have hs : ∀ i, F₁B.IsCoord (u' ≫ (g' i ≫ f' i)) (M' i (N' i c')) := fun i => by
      rw [← Category.assoc]
      exact hM' i _ _ (hN' i _ _ hu')
    have hprod : ∀ s : Finset (Fin n),
        F₁B.IsCoord (u' ≫ ∏ i ∈ s, (g' i ≫ f' i)) (∑ i ∈ s, M' i (N' i c')) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.sum_empty, comp_one]
        exact isCoord_one F₁B
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
        exact isCoord_mul F₁B (hs a) ih
    have h1 := hprod Finset.univ
    rw [hid, Category.comp_id] at h1
    have heq : c' = ∑ i, M' i (N' i c') := (hcB.1 _ hu'.1).unique hu' h1
    rw [heq]
    refine S.sum_mem fun i _ => hS i _ ?_
    rw [← hA1 τ]
    exact hN'mem i
  have hw' : (fun k => j (w k)) ∈ F₁B.eigLat B'.t.act ((RingOfIntegers.mapRingHom j).comp τ) := by
    rw [hB1 τ]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  exact hkey hw'

end GlobalTheory.CM.LieSpanBaseChange
end
