import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SingSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFrames
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HeightCancellation.G

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open SquareStatements.Sing
open scoped ComplexOrder

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {r : ℕ}

theorem val_inv {A : Matrix (Fin r) (Fin r) Ω} {h : Matrix (Fin r) (Fin r) ℂ} (hz : genPt ξ ⤳ centre z)
    (hv : ∀ p q, ValAt ξ z (A p q) (h p q)) (hd : h.det ≠ 0) :
    A.det ≠ 0 ∧ ∀ p q, ValAt ξ z (A⁻¹ p q) (h⁻¹ p q) := by
  choose _ s hs hs' using hv
  let S : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z)) := Matrix.of s
  let g : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, hz⟩
  let φ : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have e1 : S.map g = A := by ext p q; exact hs p q
  have e2 : S.map φ = h := by ext p q; exact hs' p q
  have hu : IsUnit S.det := CxVal.isUnit (z := z) _ (by
    show φ S.det ≠ 0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, e2]; exact hd)
  have i1 : (S⁻¹).map g * A = 1 := by
    rw [← e1, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have i2 : (S⁻¹).map φ * h = 1 := by
    rw [← e2, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨(Matrix.isUnit_det_of_left_inverse i1).ne_zero, fun p q => ⟨hz, S⁻¹ p q, ?_, ?_⟩⟩
  · rw [Matrix.inv_eq_left_inv i1]; rfl
  · rw [Matrix.inv_eq_left_inv i2]; rfl

theorem val_of_reg {A A' : Matrix (Fin r) (Fin r) Ω} (hξ : IsCptGen ξ) (hz : genPt ξ ⤳ centre z)
    (hA : ∀ p q, A p q ∈ regAt ξ ⟨centre z, hz⟩) (hA' : ∀ p q, A' p q ∈ regAt ξ ⟨centre z, hz⟩) (e : A' * A = 1) :
    ∃ h : Matrix (Fin r) (Fin r) ℂ, h.det ≠ 0 ∧ ∀ p q, ValAt ξ z (A p q) (h p q) := by
  choose s hs using hA
  choose s' hs' using hA'
  let S : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z)) := Matrix.of s
  let S' : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z)) := Matrix.of s'
  let g : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, hz⟩
  let φ : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have e1 : S.map g = A := by ext p q; exact hs p q
  have e2 : S'.map g = A' := by ext p q; exact hs' p q
  have e3 : S' * S = 1 := by
    have : (S' * S).map g = (1 : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z))).map g := by
      rw [Matrix.map_mul, e1, e2, e, Matrix.map_one _ (map_zero _) (map_one _)]
    ext p q
    exact hξ.inj ⟨centre z, hz⟩ (congrFun (congrFun this p) q)
  have e4 : S'.map φ * S.map φ = 1 := by
    rw [← Matrix.map_mul, e3, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨S.map φ, (Matrix.isUnit_det_of_left_inverse e4).ne_zero, fun p q => ⟨hz, s p q, hs p q, rfl⟩⟩

end Val

section Lin

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem colFrame_inj {c : Fin r → V} (hc : LinearIndependent Ω c) {A B : Matrix (Fin r) (Fin r) Ω}
    (e : colFrame c A = colFrame c B) : A = B := by
  ext p q
  exact congrFun (GrNorm.coeff_eq_of_li hc (c := fun l => A l q) (d := fun l => B l q) (congrFun e q)) p

theorem colFrame_li {c : Fin r → V} (hc : LinearIndependent Ω c) {A : Matrix (Fin r) (Fin r) Ω} (hA : A.det ≠ 0) :
    LinearIndependent Ω (colFrame c A) := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have h1 : ∑ l, (A *ᵥ g) l • c l = ∑ l, (0 : Fin r → Ω) l • c l := by
    rw [show ∑ l, (0 : Fin r → Ω) l • c l = 0 by simp, ← hg]
    simp only [colFrame, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h2 := GrNorm.coeff_eq_of_li hc h1
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hA h2)

theorem colFrame_mem (A : Subring Ω) {c : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω} (hT : ∀ p q, T p q ∈ A)
    (k : Fin r) : colFrame c T k ∈ Submodule.span A (Set.range c) :=
  Submodule.sum_mem _ fun l _ =>
    (Submodule.span A (Set.range c)).smul_mem (⟨T l k, hT l k⟩ : A) (Submodule.subset_span ⟨l, rfl⟩)

theorem exists_colFrame (A : Subring Ω) {c b : Fin r → V} (h : ∀ k, b k ∈ Submodule.span A (Set.range c)) :
    ∃ T : Matrix (Fin r) (Fin r) Ω, (∀ p q, T p q ∈ A) ∧ b = colFrame c T := by
  choose t ht using fun k => (Submodule.mem_span_range_iff_exists_fun A).1 (h k)
  exact ⟨Matrix.of fun p q => (t q p : Ω), fun p q => (t q p).2, funext fun k => (ht k).symm⟩

theorem step_le {b : Fin r → V} {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (s : ℕ) :
    flagStep Ω (colFrame b U) s ≤ flagStep Ω b s := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases h : k < l
  · rw [hU h, zero_smul]; exact zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, lt_of_le_of_lt (show (l : ℕ) ≤ k from not_lt.1 h) hk, rfl⟩)

theorem step_eq {b : Fin r → V} {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (hd : U.det ≠ 0) (s : ℕ) :
    flagStep Ω (colFrame b U) s = flagStep Ω b s := by
  refine le_antisymm (step_le hU s) ?_
  letI := Matrix.invertibleOfIsUnitDet U hd.isUnit
  have h := step_le (b := colFrame b U) (blockTriangular_inv_of_blockTriangular hU) s
  rwa [← colFrame_mul, Matrix.mul_nonsing_inv _ hd.isUnit, colFrame_one] at h

theorem sub_mem_step {b : Fin r → V} {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (k : Fin r) :
    colFrame b U k - U k k • b k ∈ flagStep Ω b k := by
  have e : colFrame b U k - U k k • b k = ∑ l ∈ Finset.univ.erase k, U l k • b l := by
    rw [colFrame, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    abel
  rw [e]
  refine Submodule.sum_mem _ fun l hl => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, h, rfl⟩)
  · rw [hU h, zero_smul]; exact zero_mem _

theorem exists_upper {b b₀ : Fin r → V} (h : ∀ s, flagStep Ω b s = flagStep Ω b₀ s) :
    ∃ U : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ b = colFrame b₀ U := by
  have hm : ∀ k : Fin r, b k ∈ flagStep Ω b₀ (k + 1) := fun k =>
    h _ ▸ Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩
  choose d hd hd' using fun k => GrNorm.exists_coeff_of_mem_flagStep (hm k)
  exact ⟨Matrix.of fun p q => d q p, fun p q hpq => hd q p hpq, funext hd'⟩

theorem map_colFrame {Ω' V' : Type} [Field Ω'] [AddCommGroup V'] [Module Ω' V'] {i : Ω →+* Ω'} {j : V →+ V'}
    (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e) (c : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) :
    (fun k => j (colFrame c T k)) = colFrame (fun k => j (c k)) (T.map i) := by
  funext k
  simp [colFrame, map_sum, hj]

end Lin

section Frame

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {r : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]

theorem frame_change {L : Lat ξ V} (hz : genPt ξ ⤳ centre z) {c : Fin r → V} (hc : L.IsFrameAt c ⟨centre z, hz⟩)
    {A : Matrix (Fin r) (Fin r) Ω} {h : Matrix (Fin r) (Fin r) ℂ} (hv : ∀ p q, ValAt ξ z (A p q) (h p q))
    (hd : h.det ≠ 0) : L.IsFrameAt (colFrame c A) ⟨centre z, hz⟩ := by
  obtain ⟨hA, hi⟩ := val_inv hz hv hd
  have r1 : ∀ p q, A p q ∈ regAt ξ ⟨centre z, hz⟩ := fun p q => let ⟨_, s, hs, _⟩ := hv p q; ⟨s, hs⟩
  have r2 : ∀ p q, A⁻¹ p q ∈ regAt ξ ⟨centre z, hz⟩ := fun p q => let ⟨_, s, hs, _⟩ := hi p q; ⟨s, hs⟩
  refine ⟨colFrame_li hc.1 hA, hc.2.trans (le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_))⟩
  · rintro _ ⟨k, rfl⟩
    have := colFrame_mem _ (c := colFrame c A) r2 k
    rwa [← colFrame_mul, Matrix.mul_nonsing_inv _ hA.isUnit, colFrame_one] at this
  · rintro _ ⟨k, rfl⟩
    exact colFrame_mem _ r1 k

theorem exists_adapt {L : Lat ξ V} (hξ : IsCptGen ξ) (hz : genPt ξ ⤳ centre z) {c b₀ : Fin r → V}
    (hc : L.IsFrameAt c ⟨centre z, hz⟩) (hb : L.IsFlagVBOn Set.univ b₀) {Q : Matrix (Fin r) (Fin r) Ω}
    (hQ : b₀ = colFrame c Q) : ∃ (U : Matrix (Fin r) (Fin r) Ω) (h : Matrix (Fin r) (Fin r) ℂ),
      U.BlockTriangular id ∧ U.det ≠ 0 ∧ h.det ≠ 0 ∧ ∀ p q, ValAt ξ z ((Q * U) p q) (h p q) := by
  obtain ⟨W, hW, b, hflag, hb'⟩ := hb ⟨centre z, hz⟩ trivial
  have hfr := hb' ⟨centre z, hz⟩ trivial hW
  obtain ⟨U, hU, eU⟩ := exists_upper hflag
  obtain ⟨A, rA, eA⟩ := exists_colFrame (regAt ξ ⟨centre z, hz⟩) (c := c) (b := b) fun k => by
    rw [← hc.2, hfr.2]; exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨A', rA', eA'⟩ := exists_colFrame (regAt ξ ⟨centre z, hz⟩) (c := b) (b := c) fun k => by
    rw [← hfr.2, hc.2]; exact Submodule.subset_span ⟨k, rfl⟩
  have e1 : A' * A = 1 := colFrame_inj hfr.1 (by rw [colFrame_mul, ← eA', ← eA, colFrame_one])
  have e2 : A = Q * U := colFrame_inj hc.1 (by rw [colFrame_mul, ← hQ, ← eU, ← eA])
  obtain ⟨h, hd, hv⟩ := val_of_reg hξ hz rA rA' e1
  refine ⟨U, h, hU, fun h0 => ?_, hd, e2 ▸ hv⟩
  have := (Matrix.isUnit_det_of_left_inverse e1).ne_zero
  rw [e2, Matrix.det_mul, h0, mul_zero] at this
  exact this rfl

end Frame

section Gram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω']
  {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
  {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'}

theorem gram_change (A : HodgeCpt Y S x) {z : Spec (CommRingCat.of ℂ) ⟶ A.X} {r : ℕ} {b : Fin r → A.Li}
    {Γ : Matrix (Fin r) (Fin r) ℂ} (hG : A.M.GramAt A.t.PP.L z b Γ) {T : Matrix (Fin r) (Fin r) Ω}
    {h : Matrix (Fin r) (Fin r) ℂ} (hv : ∀ p q, ValAt A.ξ z (T p q) (h p q)) :
    A.M.GramAt A.t.PP.L z (colFrame b T) (hᴴ * Γ * h) := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists A.X A.t.G ℂ z
  obtain ⟨v, hv', hΓ⟩ := hG
  choose u hu using fun p => Mz.onto (v p) (GrNorm.tan_of_valAt (hv' p))
  refine ⟨fun q => Mz.pt (∑ p, h p q • u p), fun q => ?_, fun p q => ?_⟩
  · exact HodgeMetric.valAt_sum_smul A.M Mz (A.all _) Finset.univ b u (fun p => by rw [hu]; exact hv' p)
      (fun p => T p q) (fun p => h p q) (fun p => hv p q)
  · exact HodgePull.gram_comb Mz u Γ p (fun p q => by rw [hu, hu]; exact hΓ p q) (HodgePull.hodgeInnerProduct_unique A.m) h p q

theorem gram_pull {A : HodgeCpt Y S x} {A' : HodgeCpt Y S x'} {pr : A'.X ⟶ A.X} {i : Ω →+* Ω'} {j : A.Li →+ A'.Li}
    (ho : HodgeOver A' A pr i j) {z : Spec (CommRingCat.of ℂ) ⟶ A'.X} {r : ℕ} {b : Fin r → A.Li}
    {Γ : Matrix (Fin r) (Fin r) ℂ} (hG : A.M.GramAt A.t.PP.L (z ≫ pr) b Γ) :
    A'.M.GramAt A'.t.PP.L z (fun k => j (b k)) Γ := by
  obtain ⟨m, hm⟩ := Chg.exists_sabMap A A' pr ho.2.1
  have hpt : ∀ e, (A'.M.pt (j e)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (A.M.pt e).left := by
    intro e
    have h1 := ho.2.2.2.2 e
    rw [hm] at h1
    refine A.m.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using h1
    · have w1 := Over.w (A'.M.pt (j e))
      have w2 := Over.w (A.M.pt e)
      have w3 : m.φ ≫ A.t.G.hom = A'.t.G.hom ≫ pr := m.cart.1.w
      have hd : A'.ξ ≫ pr = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := ho.1
      rw [Category.assoc, Category.assoc, w3, ← Category.assoc, w1, w2]
      simp only [Over.mk_hom]
      rw [Category.assoc, hd, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      exact congrArg CommRingCat.ofHom (FlagPull.dualMap_algebraMap i).symm
  obtain ⟨v, hv, hΓ⟩ := hG
  have hp : genPt A.ξ ⤳ pr (centre z) := A.all _
  have hL : ∀ k, b k ∈ A.M.lat ⟨pr (centre z), hp⟩ := fun k => by
    obtain ⟨_, u, hu, -⟩ := hv k
    exact Submodule.subset_span ⟨u, hu⟩
  choose w w' hw hw' hww using fun k =>
    HodgePull.value_pull (M' := A'.M) (j := j) ho.1 m.cart hpt (A'.all _) hp (hL k)
  refine ⟨w', hw', fun p q => ?_⟩
  have e : ∀ k, w k = v k := fun k => (hw k).unique A.tie.gen (hv k)
  refine ((GlobalTheory.T.hodge_inner_product_pullback_unique E H A'.X A.X A'.t A.t pr m z (w' p) (w' q) (w p) (w q) (hww p) (hww q)).1 _).2 ?_
  rw [e, e]
  exact hΓ p q

theorem grNorm_of (A : HodgeCpt Y S x) {z : Spec (CommRingCat.of ℂ) ⟶ A.X} {r : ℕ} {L : Lat A.ξ A.Li}
    {b b₀ : Fin r → A.Li} (hb : L.IsFrameAt b ⟨centre z, A.all _⟩) {Γ : Matrix (Fin r) (Fin r) ℂ}
    (hG : A.M.GramAt A.t.PP.L z b Γ) (hP : Γ.PosDef) {Q U : Matrix (Fin r) (Fin r) Ω} (hQ : b₀ = colFrame b Q)
    (hU : U.BlockTriangular id) (dU : U.det ≠ 0) {h : Matrix (Fin r) (Fin r) ℂ} (hd : h.det ≠ 0)
    (hv : ∀ p q, ValAt A.ξ z ((Q * U) p q) (h p q)) (k : Fin r) :
    A.M.IsGrNorm A.t.PP.L L b₀ k z (U k k) (grN (hᴴ * Γ * h) k) := by
  have e : colFrame b (Q * U) = colFrame b₀ U := by rw [colFrame_mul, ← hQ]
  refine ⟨A.all _, colFrame b₀ U, hᴴ * Γ * h, step_eq hU dU, e ▸ frame_change _ hb hv hd, sub_mem_step hU k,
    e ▸ gram_change A hG hv, hP.conjTranspose_mul_mul_same ?_, rfl⟩
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit)

end Gram

end HeightCancellation.G
