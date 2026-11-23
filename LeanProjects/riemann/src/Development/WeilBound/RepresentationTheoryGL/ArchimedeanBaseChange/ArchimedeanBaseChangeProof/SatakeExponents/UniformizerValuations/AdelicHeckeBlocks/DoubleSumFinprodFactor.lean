import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMemKGL

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Fm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem lev_iInf {n : ℕ} {J : Type} [Finite J] [Nonempty J] {K : J → ∀ w : Pl E, Subgroup (GLw n w)}
    (h : ∀ j, IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) (K j)) :
    IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) (fun w => ⨅ j, K j w) := by
  refine ⟨fun w => ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite fun j => ((h j).1 w).1
  · obtain ⟨j⟩ := ‹Nonempty J›; exact (iInf_le _ j).trans ((h j).1 w).2.1
  · intro k hk; rw [Subgroup.mem_iInf] at hk ⊢; exact fun j => ((h j).1 w).2.2 k (hk j)
  · filter_upwards [Filter.eventually_all.2 fun j => (h j).2] with w hw
    simp only [hw, iInf_const]

theorem isTestFunction_linearCombination {J : Type} [Fintype J] [Nonempty J] (T : J → ∀ w : Pl E, LF a b w)
    (hT : ∀ j, IsTestP (T j)) (φ : ∀ w : Pl E, LF a b w)
    (hφ : ∀ w, ∃ (ι : Type) (_ : Fintype ι) (j : ι → J) (c : ι → ℂ), φ w = ∑ i, c i • T (j i) w)
    (hc : ∀ᶠ w in cofinite, φ w = ((K2 a b w : Subgroup _) : Set _).indicator 1) : IsTestP φ := by
  choose K₁ K₂ h₁ h₂ h₃ using hT
  refine ⟨fun w => ⨅ j, K₁ j w, fun w => ⨅ j, K₂ j w, lev_iInf h₁, lev_iInf h₂, fun w => ?_, hc⟩
  obtain ⟨ι, _, j, c, hw⟩ := hφ w
  rw [hw]
  refine ⟨HasCompactSupport.finset_sum fun i _ => ?_, fun k hk x => ?_⟩
  · exact (((h₃ (j i)).1 w).1).mul_left (f := fun _ => c i)
  · have hk' : ∀ i, k ∈ (K₁ (j i) w).prod (K₂ (j i) w) := fun i => by
      rw [Subgroup.mem_prod] at hk ⊢
      exact ⟨Subgroup.mem_iInf.1 hk.1 _, Subgroup.mem_iInf.1 hk.2 _⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact ⟨Finset.sum_congr rfl fun i _ => by rw [(((h₃ (j i)).1 w).2 k (hk' i) x).1],
      Finset.sum_congr rfl fun i _ => by rw [(((h₃ (j i)).1 w).2 k (hk' i) x).2]⟩

theorem isTestFunction_star {φ : ∀ w : Pl E, LF a b w} (h : IsTestP φ) : IsTestP (fun w => lfStar (φ w)) := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃, h₄⟩ := h
  refine ⟨K₁, K₂, h₁, h₂, ⟨fun w => ⟨?_, fun k hk x => ?_⟩, ?_⟩⟩
  · exact ((h₃ w).1.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)
  · have hk' : k⁻¹ ∈ (K₁ w).prod (K₂ w) := inv_mem hk
    simp only [lfStar, _root_.mul_inv_rev]
    exact ⟨by rw [((h₃ w).2 _ hk' _).2], by rw [((h₃ w).2 _ hk' _).1]⟩
  · filter_upwards [h₄] with w hw
    funext y
    simp only [lfStar, hw, Set.indicator_apply, SetLike.mem_coe, inv_mem_iff]
    split_ifs <;> simp

theorem atW_int (y : Gf E a b) : ∀ᶠ w in cofinite, atW w y ∈ K2 a b w := by
  filter_upwards [GlobalTheory.EulerTw.Fact.eventually_mem_KGL y.1, GlobalTheory.EulerTw.Fact.eventually_mem_KGL y.2] with w h1 h2
  exact Subgroup.mem_prod.2 ⟨h1, h2⟩

theorem atW_inv (w : Pl E) (y : Gf E a b) : atW w y⁻¹ = (atW w y)⁻¹ := by
  simp [atW, map_inv]

def fac (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (y : Gf E a b) (w : Pl E) : ℂ :=
  φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1

theorem finFn_eq (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (y : Gf E a b) :
    finFn S φ₁ φ₂ y = ∏ᶠ w ∈ S, fac φ₁ φ₂ y w := rfl

theorem fac_fin (S : Set (Pl E)) {φ₁ φ₂ : ∀ w : Pl E, LF a b w}
    (h₁ : ∀ᶠ w in cofinite, φ₁ w = ((K2 a b w : Subgroup _) : Set _).indicator 1)
    (h₂ : ∀ᶠ w in cofinite, φ₂ w = ((K2 a b w : Subgroup _) : Set _).indicator 1) (y : Gf E a b) :
    (S ∩ Function.mulSupport (fac φ₁ φ₂ y)).Finite := by
  refine (Filter.eventually_cofinite.1 ?_).subset fun w hw => hw.2
  filter_upwards [h₁, h₂, atW_int y, atW_int (thP E a b y)] with w e1 e2 k1 k2
  simp only [fac, e1, e2, Set.indicator_of_mem (SetLike.mem_coe.2 k1), Set.indicator_of_mem (SetLike.mem_coe.2 k2)]
  split_ifs <;> simp

theorem cof_of_test {φ : ∀ w : Pl E, LF a b w} (h : IsTestP φ) :
    ∀ᶠ w in cofinite, φ w = ((K2 a b w : Subgroup _) : Set _).indicator 1 := by
  obtain ⟨_, _, _, _, _, h4⟩ := h; exact h4

theorem fp_split {ι : Type} (S : Set ι) (P : Finset ι) (hPS : (↑P : Set ι) ⊆ S) (F c : ι → ℂ)
    (hF : ∀ i ∉ P, F i = c i) (hc : (S ∩ Function.mulSupport c).Finite) :
    ∏ᶠ i ∈ S, F i = (∏ i : P, F i) * ∏ᶠ i ∈ S \ ↑P, c i := by
  conv_lhs => rw [← Set.union_diff_cancel hPS]
  rw [finprod_mem_union' Set.disjoint_sdiff_right (P.finite_toSet.inter_of_left _), finprod_mem_coe_finset,
    Finset.prod_coe_sort]
  · congr 1
    exact finprod_mem_congr rfl fun i hi => hF i hi.2
  · refine hc.subset fun i hi => ⟨hi.1.1, ?_⟩
    have := hi.2; rwa [Function.mem_mulSupport, hF i hi.1.2] at this

theorem cof_off (P : Finset (Pl E)) {φ ψ : ∀ w : Pl E, LF a b w} (h : IsTestP φ) (hψ : ∀ w ∉ P, ψ w = φ w) :
    ∀ᶠ w in cofinite, ψ w = ((K2 a b w : Subgroup _) : Set _).indicator 1 := by
  filter_upwards [cof_of_test h, P.finite_toSet.compl_mem_cofinite] with w h1 h2
  rw [hψ w h2, h1]

theorem cont_of_level {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : H → ℂ) (U : Subgroup H)
    (hU : IsOpen (U : Set H)) (hf : ∀ u ∈ U, ∀ h, f (h * u) = f h) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq f).2 fun h₀ => ?_)
  have ht : Filter.Tendsto (fun y => h₀⁻¹ * y) (nhds h₀) (nhds 1) := by
    simpa using (continuous_const_mul h₀⁻¹).tendsto h₀
  filter_upwards [ht.eventually (hU.mem_nhds U.one_mem)] with y hy
  simpa using hf _ hy h₀

theorem single_sum_finprod_factor {κ : Pl E → Type} [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E))
    (hPS : (↑P : Set (Pl E)) ⊆ S) (c : Pl E → ℂ) (hc : (S ∩ Function.mulSupport c).Finite) (f : ∀ i : P, κ i → ℂ)
    (F : (∀ i : P, κ i) → Pl E → ℂ) (hF : ∀ Z, ∀ i ∉ P, F Z i = c i) (hFP : ∀ Z (i : P), F Z i = f i (Z i))
    (G : Pl E → ℂ) (hG : ∀ i ∉ P, G i = c i) (hGP : ∀ i : P, G i = ∑ z, f i z) :
    ∑ Z, ∏ᶠ w ∈ S, F Z w = ∏ᶠ w ∈ S, G w := by
  have hs : ∀ Z, ∏ᶠ w ∈ S, F Z w = (∏ i : P, F Z i) * ∏ᶠ i ∈ S \ ↑P, c i := fun Z =>
    fp_split S P hPS (F Z) c (hF Z) hc
  rw [fp_split S P hPS G c hG hc]
  simp only [hs, ← Finset.sum_mul, hFP, hGP]
  rw [Fintype.prod_sum (κ := fun i : P => κ i) f]

theorem double_sum_finprod_factor {κ : Pl E → Type} [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E))
    (hPS : (↑P : Set (Pl E)) ⊆ S) (c : Pl E → ℂ) (hc : (S ∩ Function.mulSupport c).Finite)
    (f Nf : ∀ i : P, κ i → κ i → ℂ) (F : (∀ i : P, κ i) → (∀ i : P, κ i) → Pl E → ℂ)
    (hF : ∀ X Y, ∀ i ∉ P, F X Y i = c i) (hFP : ∀ X Y (i : P), F X Y i = f i (X i) (Y i))
    (G : Pl E → ℂ) (hG : ∀ i ∉ P, G i = c i) (hGP : ∀ i : P, G i = ∑ x, ∑ y, f i x y * Nf i x y) :
    ∑ X, ∑ Y, (∏ᶠ w ∈ S, F X Y w) * ∏ i : P, Nf i (X i) (Y i) = ∏ᶠ w ∈ S, G w := by
  have hs : ∀ X Y, (∏ᶠ w ∈ S, F X Y w) * ∏ i : P, Nf i (X i) (Y i) =
      (∏ i : P, (f i (X i) (Y i) * Nf i (X i) (Y i))) * ∏ᶠ i ∈ S \ ↑P, c i := fun X Y => by
    rw [fp_split S P hPS (F X Y) c (hF X Y) hc, Finset.prod_mul_distrib]; simp only [hFP]; ring
  rw [fp_split S P hPS G c hG hc]
  simp only [hs, ← Finset.sum_mul, hGP]
  congr 1
  rw [Fintype.prod_sum (κ := fun i : P => κ i) (fun i x => ∑ y, f i x y * Nf i x y)]
  exact Finset.sum_congr rfl fun X _ =>
    (Fintype.prod_sum (κ := fun i : P => κ i) (fun i y => f i (X i) y * Nf i (X i) y)).symm

theorem adj_ent {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E)) (L : LM κ a b) (X Y : ∀ w : P, κ w) :
    L.adj.ent P X Y = fun w => lfStar (L.ent P Y X w) := by
  funext w; simp only [LM.ent, LM.adj]; split_ifs <;> rfl

theorem vol_conj (B : Block E) : starRingEnd ℂ B.vol = B.vol := by simp [Block.vol]

theorem map_conj_finprod (S : Set (Pl E)) (F : Pl E → ℂ) (hF : (S ∩ Function.mulSupport F).Finite) :
    starRingEnd ℂ (∏ᶠ w ∈ S, F w) = ∏ᶠ w ∈ S, starRingEnd ℂ (F w) :=
  MonoidHom.map_finprod_mem' (starRingEnd ℂ : ℂ →+* ℂ).toMonoidHom hF

end Fm

open Fm in
theorem fmTr (h3 : Slots) : FmTr := by
  intro E _ _ _ κ _ S P B e hPS hne L N hL
  have x₀ : ∀ w : P, κ w := fun w => Classical.choice (hne w w.2)
  have hs : ∀ w ∉ P, L.s w = L.ent P x₀ x₀ w := fun w hw => by simp [LM.ent, hw]
  have htr : IsTestP (L.tr P N) := by
    refine isTestFunction_linearCombination (J := Option (Σ i : P, κ i × κ i))
      (fun j => Option.elim j (L.ent P x₀ x₀)
        (fun q => L.ent P (Function.update x₀ q.1 q.2.1) (Function.update x₀ q.1 q.2.2)))
      (fun j => by cases j <;> exact hL.1 _ _) _ (fun w => ?_) ?_
    · by_cases hw : w ∈ P
      · refine ⟨κ w × κ w, inferInstance, fun p => some ⟨⟨w, hw⟩, p⟩, fun p => N w p.2 p.1, ?_⟩
        simp only [LM.tr, if_pos hw, Option.elim_some, LM.ent, dif_pos hw, Function.update_self]
        exact (Fintype.sum_prod_type' (fun x y => N w y x • L.m w x y)).symm
      · refine ⟨Unit, inferInstance, fun _ => none, fun _ => 1, ?_⟩
        simp [LM.tr, hw, LM.ent]
    · exact cof_off P (hL.1 x₀ x₀) fun w hw => by simp [LM.tr, LM.ent, hw]
  refine ⟨htr, fun h => ?_⟩
  have hre : ∑ x, ∑ y, fm S P B e L x y h * tenN P B e N y x = ∑ X, ∑ Y,
      B.vol⁻¹ * ((∏ᶠ w ∈ S, fac (L.ent P X Y) L.t h w) * ∏ i : P, N i (Y i) (X i)) := by
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [fm, tenN, finFn_eq]; ring
  rw [hre]
  simp only [← Finset.mul_sum]
  congr 1
  rw [finFn_eq]
  have hsc : ∀ᶠ w in cofinite, L.s w = ((K2 B.a B.b w : Subgroup _) : Set _).indicator 1 := cof_off P (hL.1 x₀ x₀) hs
  refine double_sum_finprod_factor S P hPS (fac L.s L.t h) (fac_fin S hsc (cof_of_test hL.2) h)
    (fun i x y => L.m i x y (atW (i : Pl E) h) *
      if IsSplitAt (i : Pl E) then L.t i (atW (i : Pl E) (thP E B.a B.b h)) else 1)
    (fun i x y => N i y x) (fun X Y => fac (L.ent P X Y) L.t h) (fun X Y i hi => by simp [fac, LM.ent, hi])
    (fun X Y i => by simp [fac, LM.ent, i.2]) _ (fun i hi => by simp [fac, LM.tr, hi]) (fun i => ?_)
  simp only [fac, LM.tr, if_pos i.2, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

open Fm in
theorem fmAlg (h1 : FinConv) (h3 : Slots) : FmAlg := by
  intro E _ _ _ κ _ S P B e hS hPS L L' hL hL'
  obtain ⟨hv, hC⟩ := h1 E B S hS
  have hm : ∀ φ φ' : ∀ w : Pl E, LF B.a B.b w, IsTestP φ → IsTestP φ' → IsTestP (fun w => mconv (φ w) (φ' w)) :=
    fun φ φ' h h' => ((hC φ φ h h).2.2 φ' φ' h' h').1
  have hfin : IsFinM (fm S P B e L) := fun x y => by
    obtain ⟨hcs, ⟨U, hU, hinv⟩, -⟩ := hC _ _ (hL.1 (e x) (e y)) hL.2
    exact ⟨continuous_const.mul (cont_of_level _ U hU fun u hu h => (hinv u hu h).2), hcs.mul_left⟩
  have hmul : (L.mul L').Ok P := by
    refine ⟨fun X Y => ?_, hm _ _ hL.2 hL'.2⟩
    refine isTestFunction_linearCombination (J := Option (Σ i : P, κ i))
      (fun j => Option.elim j (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w))
        (fun q => fun w => mconv (L.ent P X (Function.update X q.1 q.2) w) (L'.ent P (Function.update X q.1 q.2) Y w)))
      (fun j => by cases j <;> exact hm _ _ (hL.1 _ _) (hL'.1 _ _)) _ (fun w => ?_) ?_
    · by_cases hw : w ∈ P
      · refine ⟨κ w, inferInstance, fun z => some ⟨⟨w, hw⟩, z⟩, fun _ => 1, ?_⟩
        simp [LM.mul, LM.ent, hw]
      · refine ⟨Unit, inferInstance, fun _ => none, fun _ => 1, ?_⟩
        simp [LM.mul, LM.ent, hw]
    · exact cof_off P (hm _ _ (hL.1 X X) (hL'.1 Y Y)) fun w hw => by simp [LM.mul, LM.ent, hw]
  have hadj : L.adj.Ok P := ⟨fun X Y => by rw [adj_ent]; exact isTestFunction_star (hL.1 Y X), isTestFunction_star hL.2⟩
  refine ⟨hfin, hmul, ?_, hadj, ?_⟩
  · funext x y g
    have hk : ∀ u v : ℂ, B.vol⁻¹ * u * (B.vol⁻¹ * v) = B.vol⁻¹ * B.vol⁻¹ * (u * v) := fun u v => by ring
    have key : ∀ z, ∫ h, fm S P B e L x z h * fm S P B e L' z y (h⁻¹ * g) ∂B.ν = B.vol⁻¹ *
        finFn S (fun w => mconv (L.ent P (e x) (e z) w) (L'.ent P (e z) (e y) w)) (fun w => mconv (L.t w) (L'.t w)) g := by
      intro z
      have hI := ((hC _ _ (hL.1 (e x) (e z)) hL.2).2.2 _ _ (hL'.1 (e z) (e y)) hL'.2).2.2 g
      simp only [fm, hk, integral_const_mul, hI]
      rw [mul_assoc, ← mul_assoc B.vol⁻¹ B.vol, inv_mul_cancel₀ hv, one_mul]
    simp only [mulF, key, ← Finset.mul_sum]
    simp only [fm]
    congr 1
    rw [Equiv.sum_comp e (fun Z => finFn S (fun w => mconv (L.ent P (e x) Z w) (L'.ent P Z (e y) w))
      (fun w => mconv (L.t w) (L'.t w)) g)]
    simp only [finFn_eq]
    have hsc : ∀ᶠ w in cofinite, mconv (L.s w) (L'.s w) = ((K2 B.a B.b w : Subgroup _) : Set _).indicator 1 :=
      cof_off P (hm _ _ (hL.1 (e x) (e x)) (hL'.1 (e y) (e y))) fun w hw => by simp [LM.ent, hw]
    refine single_sum_finprod_factor S P hPS (fac (fun w => mconv (L.s w) (L'.s w)) (fun w => mconv (L.t w) (L'.t w)) g)
      (fac_fin S hsc (cof_of_test (hm _ _ hL.2 hL'.2)) g)
      (fun i z => mconv (L.m i (e x i) z) (L'.m i z (e y i)) (atW (i : Pl E) g) *
        if IsSplitAt (i : Pl E) then mconv (L.t i) (L'.t i) (atW (i : Pl E) (thP E B.a B.b g)) else 1)
      (fun Z => fac (fun w => mconv (L.ent P (e x) Z w) (L'.ent P Z (e y) w)) (fun w => mconv (L.t w) (L'.t w)) g)
      (fun Z i hi => by simp [fac, LM.ent, hi]) (fun Z i => by simp [fac, LM.ent, i.2]) _
      (fun i hi => by simp [fac, LM.ent, LM.mul, hi]) (fun i => ?_)
    simp only [fac, LM.ent, dif_pos i.2, LM.mul, Finset.sum_apply, Finset.sum_mul]
  · funext x y g
    simp only [adjF, fm, map_mul, map_inv₀, vol_conj]
    congr 1
    rw [adj_ent, finFn_eq, finFn_eq, map_conj_finprod S _ (fac_fin S (cof_of_test (hL.1 _ _)) (cof_of_test hL.2) _)]
    refine finprod_mem_congr rfl fun w _ => ?_
    simp only [fac, lfStar, atW_inv, map_inv, map_mul, LM.adj]
    split_ifs <;> simp

end PositivityTheory.Rg.BcB.F

end
