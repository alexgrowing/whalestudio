import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgEqLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintEqOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkOneVal

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagAvg

theorem avg_conj {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') (f : G → ℂ) (hl : ∀ u ∈ K', ∀ g, f (u * g) = f g ∧ f (g * u) = f g)
    (g : G) :
    avg (fun k : K => f ((k : G)⁻¹ * g * k)) = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, f (x⁻¹ * g * x) := by
  set S : Subgroup K := K'.subgroupOf K with hSdef
  set u : K → ℂ := fun k => f ((k : G)⁻¹ * g * k) with hu
  have hS : S ≤ rStab u := by
    intro s hs k
    have hs' : (s : G) ∈ K' := Subgroup.mem_subgroupOf.1 hs
    show f (((k * s : K) : G)⁻¹ * g * ((k * s : K) : G)) = f ((k : G)⁻¹ * g * k)
    have e : ((k * s : K) : G)⁻¹ * g * ((k * s : K) : G) = (s : G)⁻¹ * ((k : G)⁻¹ * g * k) * s := by
      simp only [Subgroup.coe_mul]; group
    rw [e, (hl _ hs' _).2, (hl _ (K'.inv_mem hs') _).1]
  let φ : {x // x ∈ X} → K ⧸ S := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ S)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := by
        have h2 := QuotientGroup.eq.1 hxy
        exact Subgroup.mem_subgroupOf.1 h2
      have hy := hX y.1 (hXK _ y.2)
      exact Subtype.ext (hy.unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  let e := Equiv.ofBijective φ hφ
  have hindex : S.index = X.card := by
    show Nat.card (K ⧸ S) = _
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hne : S.index ≠ 0 := by
    rw [hindex]
    obtain ⟨x, ⟨hxX, -⟩, -⟩ := hX 1 K.one_mem
    exact (Finset.card_pos.2 ⟨x, hxX⟩).ne'
  rw [GlobalTheory.CompanionTheory.AvgLevel.avg_eq_level S u hS hne, hindex]
  congr 1
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort X]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (⟨x.1, hXK _ x.2⟩ : K)
  show u (φ x).out = u ⟨x.1, hXK _ x.2⟩
  have hφx : (φ x).out = (⟨x.1, hXK _ x.2⟩ : K) * s := hs
  rw [hφx]
  exact hS s.2 _

theorem hint_const_mul_sum {H ι : Type} [Group H] (A L : Subgroup H) (hLA : L ≤ A) (hfin : L.relIndex A ≠ 0)
    (s : Finset ι) (v : ι → H → ℂ) (c : ℂ) (hst : ∀ i ∈ s, L ≤ rStab (v i))
    (hsupp : ∀ i ∈ s, (Function.support fun q : H ⧸ L => v i q.out).Finite) :
    hint A (fun z => c * ∑ i ∈ s, v i z) = c * ∑ i ∈ s, hint A (v i) := by
  have hL : L ≤ rStab (fun z => c * ∑ i ∈ s, v i z) := by
    intro l hl z
    show c * ∑ i ∈ s, v i (z * l) = c * ∑ i ∈ s, v i z
    congr 1
    exact Finset.sum_congr rfl fun i hi => hst i hi hl z
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H A L _ hLA hL hfin,
    Finset.sum_congr rfl fun i hi => GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H A L (v i) hLA (hst i hi) hfin,
    ← Finset.mul_sum]
  have h1 : ∑ᶠ q : H ⧸ L, c * ∑ i ∈ s, v i q.out = c * ∑ i ∈ s, ∑ᶠ q : H ⧸ L, v i q.out := by
    simp only [Finset.mul_sum]
    rw [finsum_sum_comm s (fun (q : H ⧸ L) i => c * v i q.out) fun i hi =>
      (hsupp i hi).subset fun q hq => right_ne_zero_of_mul hq]
    exact Finset.sum_congr rfl fun i _ => (mul_finsum _ _).symm
  rw [h1]
  ring

theorem support_finite {G H : Type} [Group G] [Group H] (L : Subgroup H) (K' : Subgroup G) (θ : H → G)
    (hθ : ∀ z z', (θ z)⁻¹ * θ z' ∈ K' → z⁻¹ * z' ∈ L) (f : G → ℂ) (hr : ∀ u ∈ K', ∀ g, f (g * u) = f g)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite) :
    (Function.support fun q : H ⧸ L => f (θ q.out)).Finite := by
  refine Set.Finite.of_finite_image (f := fun q : H ⧸ L => ((θ q.out : G) : G ⧸ K')) (hfin.subset ?_) ?_
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (θ q.out)
    show f ((θ q.out : G) : G ⧸ K').out ≠ 0
    rw [hs, hr _ s.2]
    exact hq
  · intro q _ q' _ hqq
    have h2 : ((q.out : H) : H ⧸ L) = q'.out := QuotientGroup.eq.2 (hθ _ _ (QuotientGroup.eq.1 hqq))
    simpa using h2

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K' : Subgroup G)
    (ho : IsOpen (K' : Set G)) (f : G → ℂ) (hc : HasCompactSupport f) : {q : G ⧸ K' | f q.out ≠ 0}.Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun i : G ⧸ K' => {g : G | i.out⁻¹ * g ∈ K'})
    (fun i => ho.preimage (continuous_const.mul continuous_id)) fun g _ =>
      Set.mem_iUnion.2 ⟨(g : G ⧸ K'), QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ K'))⟩
  refine t.finite_toSet.subset fun q hq => ?_
  obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport f hq))
  have h1 : ((i.out : G) : G ⧸ K') = q.out := QuotientGroup.eq.2 hqi
  have h2 : i = q := by simpa using h1
  exact h2 ▸ hi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_toAdd_mul {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (Z l : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    blk h w m (Multiplicative.toAdd (Z * l)) =
      blk h w m (Multiplicative.toAdd Z) * blk h w 1 (Multiplicative.toAdd l) := by
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simp [add_comm]

theorem ct_eq_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ m, ct h w f m = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, phi3 h w f x x m := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX f hf m
  have hbi : ∀ u ∈ K', ∀ g, f (u * g) = f g ∧ f (g * u) = f g := fun u hu g =>
    ⟨by simpa using hf.2.2.2 u hu 1 K'.one_mem g, by simpa using hf.2.2.2 1 K'.one_mem u hu g⟩
  have hcos := finite_cosets K' hopen f hf.2.2.1
  obtain ⟨hLA, hfin⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hopen hle
  set L := (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) with hLdef
  have hmem : ∀ Y, Y ∈ L ↔ blk h w 1 (Multiplicative.toAdd Y) ∈ K' := fun Y => Iff.rfl
  have hstep : (fun Z : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      avg fun k : GlobalTheory.LFun.KGL w n => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Z) * k)) =
      fun Z => ((X.card : ℂ))⁻¹ * ∑ x ∈ X, f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) :=
    funext fun Z => avg_conj _ K' X hXK hX f hbi _
  have hst : ∀ x ∈ X, L ≤ rStab (fun Z : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)) := by
    intro x hx l hl Z
    show f (x⁻¹ * blk h w m (Multiplicative.toAdd (Z * l)) * x) = f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)
    have hU : x⁻¹ * blk h w 1 (Multiplicative.toAdd l) * x ∈ K' := by
      simpa using hnorm x⁻¹ ((GlobalTheory.LFun.KGL w n).inv_mem (hXK x hx)) _ ((hmem l).1 hl)
    have e : x⁻¹ * blk h w m (Multiplicative.toAdd (Z * l)) * x =
        (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) * (x⁻¹ * blk h w 1 (Multiplicative.toAdd l) * x) := by
      rw [blk_toAdd_mul]; group
    rw [e]
    exact (hbi _ hU _).2
  have hsupp : ∀ x ∈ X, (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ L =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd q.out) * x)).Finite := by
    intro x hx
    refine support_finite L K' (fun Z => x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) ?_ f
      (fun u hu g => (hbi u hu g).2) hcos
    intro z z' hz
    rw [hmem]
    have hb : blk h w m (Multiplicative.toAdd z') =
        blk h w m (Multiplicative.toAdd z) * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by
      rw [← blk_toAdd_mul, mul_inv_cancel_left]
    have e : (x⁻¹ * blk h w m (Multiplicative.toAdd z) * x)⁻¹ * (x⁻¹ * blk h w m (Multiplicative.toAdd z') * x) =
        x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x := by
      rw [hb]; group
    have hz' : x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x ∈ K' := e ▸ hz
    have := hnorm x (hXK x hx) _ hz'
    have e2 : x * (x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x) * x⁻¹ =
        blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by group
    rwa [e2] at this
  simp only [ct, phi3]
  rw [hstep, hint_const_mul_sum (intMat a b w) L hLA hfin X
    (fun x Z => f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)) _ hst hsupp, ← Finset.mul_sum]
  ring

end GlobalTheory.CompanionTheory.DiagAvg
