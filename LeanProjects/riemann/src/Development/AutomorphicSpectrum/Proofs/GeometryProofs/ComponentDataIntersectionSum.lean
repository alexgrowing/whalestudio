import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueLatOfChartBundle
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BigBlock

theorem iotaMulti_comb {Ω Q : Type} [Field Ω] [AddCommGroup Q] [Module Ω Q] {r : ℕ} (T : Matrix (Fin r) (Fin r) Ω)
    (w : Fin r → Q) :
    exteriorPower.ιMulti Ω r (fun k => ∑ k', T k' k • w k') = T.det • exteriorPower.ιMulti Ω r w := by
  have h := alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω r (M := Q)) T.transpose w
  simpa [Matrix.det_transpose] using h

theorem unitAt_div_of_span_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {t t' : Ω} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (h : Submodule.span (regAt ξ p) {t} = Submodule.span (regAt ξ p) {t'}) : unitAt ξ p (t / t') := by
  have h1 : t ∈ Submodule.span (regAt ξ p) {t'} := h ▸ Submodule.mem_span_singleton_self t
  have h2 : t' ∈ Submodule.span (regAt ξ p) {t} := h ▸ Submodule.mem_span_singleton_self t'
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.1 h2
  have ha1 : (a : Ω) * t' = t := ha
  have ha2 : (a' : Ω) * t = t' := ha'
  refine ⟨div_ne_zero ht ht', ?_, ?_⟩
  · rw [← ha1, mul_div_cancel_right₀ _ ht']
    exact a.2
  · rw [inv_div, ← ha2, mul_div_cancel_right₀ _ ht]
    exact a'.2

theorem exists_open_le {X : Scheme.{0}} {I : Type} [Fintype I] (U : I → X.Opens) {x : X} (h : ∀ i, x ∈ U i) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ i, V ≤ U i := by
  classical
  refine ⟨Finset.univ.inf U, ?_, fun i => Finset.inf_le (Finset.mem_univ i)⟩
  have : ∀ s : Finset I, x ∈ s.inf U := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      rw [Finset.inf_insert]
      exact ⟨h a, ih⟩
  exact this _

theorem exists_nonzero_cover {Ω : Type} [Field Ω] (R : Subring Ω) (Pr : Ω → Prop) {k : ℕ} (f g : Fin k → Ω)
    (hf : ∀ l, f l ∈ R) (hg : ∀ l, g l ∈ R) (hsum : ∑ l, g l * f l = 1) (hP : ∀ l, f l ≠ 0 → Pr (f l)) :
    ∃ (f' g' : Fin k → Ω), (∀ l, f' l ∈ R) ∧ (∀ l, g' l ∈ R) ∧ ∑ l, g' l * f' l = 1 ∧ ∀ l, Pr (f' l) := by
  classical
  obtain ⟨l₀, hl₀⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hsum
  refine ⟨fun l => if f l = 0 then f l₀ else f l, fun l => if f l = 0 then 0 else g l, fun l => ?_, fun l => ?_, ?_,
    fun l => ?_⟩
  · dsimp only; split_ifs <;> exact hf _
  · dsimp only; split_ifs
    · exact zero_mem _
    · exact hg l
  · rw [← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : f l = 0 <;> simp [h]
  · dsimp only; split_ifs with h
    · exact hP _ hl₀
    · exact hP _ h

end GlobalTheory.CompanionTheory.Ar.BigBlock

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BigBlock

theorem zpow_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {a : Ω}
    (h : unitAt ξ p a) (n : ℤ) : a ^ n ∈ regAt ξ p := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using pow_mem h.2.1 n
  · simpa using pow_mem h.2.2 n

theorem tens_isGenAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (t : I → Ω), (∀ i, (Λ i).IsGenAt p (t i)) → (Lat.tens Λ a).IsGenAt p (∏ i, t i ^ a i) := by
  intro X Ω _ ξ I _ Λ a p t ht
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (ht i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro x ⟨s', hs', rfl⟩
    have hu : ∀ i, unitAt ξ p (s' i / t i) := fun i =>
      unitAt_div_of_span_eq (hs' i).1 (ht i).1 ((hs' i).2.symm.trans (ht i).2)
    have hreg : ∏ i, (s' i / t i) ^ a i ∈ regAt ξ p := prod_mem fun i _ => zpow_mem_regAt (hu i) (a i)
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hreg⟩, ?_⟩
    show (∏ i, (s' i / t i) ^ a i) * ∏ i, t i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (ht i).1]
  · refine Submodule.span_le.2 ?_
    rintro _ rfl
    exact Submodule.subset_span ⟨t, ht, rfl⟩

theorem detLat_isGenAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P : Type) [AddCommGroup P] [Module Ω P] (L : Lat ξ P) (r : ℕ) (s b : Fin r → P) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω s → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • s k') → (Cusp.detLat L s).IsGenAt p T.det := by
  intro X Ω _ ξ P _ _ L r s b T p hs hb hT
  have hdet : T.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine hv (funext fun k => Fintype.linearIndependent_iff.1 hb.1 v ?_ k)
    have h1 : ∑ k, v k • b k = ∑ a, (T.mulVec v a) • s a := by
      simp_rw [hT, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]
    rw [h1, hTv]
    simp
  refine ⟨hdet, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro t ⟨b', T', hb', hT', rfl⟩
    have hex : ∀ k, ∃ A : Fin r → regAt ξ p, ∑ k', A k' • b k' = b' k := fun k => by
      have h := ChartTie.frame_mem hb' k
      rw [hb.2] at h
      exact (Submodule.mem_span_range_iff_exists_fun _).1 h
    choose A hA using hex
    have hcoef : ∀ k a, T' a k = ∑ m, T a m * (A k m : Ω) := by
      intro k
      have h := Fintype.linearIndependent_iff.1 hs (fun a => T' a k - ∑ m, T a m * (A k m : Ω)) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hT' k, ← hA k, sub_eq_zero]
        have e : ∀ m, A k m • b m = (A k m : Ω) • b m := fun _ => rfl
        simp_rw [e, hT, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by rw [mul_comm])
      exact fun a => sub_eq_zero.1 (h a)
    let M : Matrix (Fin r) (Fin r) (regAt ξ p) := Matrix.of fun m k => A k m
    have hTT : T' = T * (regAt ξ p).subtype.mapMatrix M := by
      ext a k
      rw [hcoef, Matrix.mul_apply]
      rfl
    refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
    show ((M.det : regAt ξ p) : Ω) * T.det = T'.det
    rw [hTT, Matrix.det_mul, ← RingHom.map_det, mul_comm]
    rfl
  · rintro _ rfl
    exact Submodule.subset_span ⟨b, T, hb, hT, rfl⟩

theorem exists_block_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P Wv : Type) [AddCommGroup P] [Module Ω P] [AddCommGroup Wv] [Module Ω Wv] (i : Wv →ₗ[Ω] P) (A B : Lat ξ P) (Va Vb : Submodule Ω P) (N j : ℕ) (hj : j ≤ N), Function.Injective i → LinearMap.range i = Va ⊔ Vb → A.IsVB j Va → B.IsVB (N - j) Vb → (Lat.comap (fun p => A p ⊔ B p) i).IsVB N ⊤ → ∀ p : Cpt ξ, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin N → Wv, Submodule.span Ω (Set.range b) = ⊤ ∧ Submodule.span Ω (Set.range (b ∘ headIdx hj)) = Va.comap i ∧ (∀ a, i (b (tailIdx hj a)) ∈ Vb) ∧ ∀ q : Cpt ξ, q.1 ∈ U → (Lat.comap (fun p => A p ⊔ B p) i).IsFrameAt b q ∧ B.IsFrameAt (fun a => i (b (tailIdx hj a))) q := by
  intro X Ω _ ξ P Wv _ _ _ _ i A B Va Vb N j hj hinj hrange hA hB hL p
  obtain ⟨U1, hp1, b1, hs1, hf1⟩ := hA p trivial
  obtain ⟨U2, hp2, b2, hs2, hf2⟩ := hB p trivial
  obtain ⟨U3, hp3, b3, hs3, hf3⟩ := hL p trivial
  have hli3 := (hf3 p trivial hp3).1
  let B3 := Module.Basis.mk hli3 hs3.ge
  have : Module.Finite Ω Wv := Module.Finite.of_basis B3
  have hfin : Module.finrank Ω Wv = N := by simpa using Module.finrank_eq_card_basis B3
  let v : Fin N → P := fun k => if h : (k : ℕ) < j then b1 ⟨k, h⟩ else b2 ⟨k - j, by have := k.2; omega⟩
  have hvh : ∀ a, v (headIdx hj a) = b1 a := fun a => by
    have h : ((headIdx hj a : Fin N) : ℕ) < j := a.2
    simp only [v, dif_pos h]
    rfl
  have hvt : ∀ a, v (tailIdx hj a) = b2 a := fun a => by
    have h : ¬ ((tailIdx hj a : Fin N) : ℕ) < j := by simp [tailIdx]
    simp only [v, dif_neg h]
    congr 1
    ext
    simp [tailIdx]
  have hcase : ∀ k : Fin N, (∃ a, k = headIdx hj a) ∨ ∃ a, k = tailIdx hj a := fun k => by
    by_cases h : (k : ℕ) < j
    · exact Or.inl ⟨⟨k, h⟩, by ext; rfl⟩
    · exact Or.inr ⟨⟨k - j, by have := k.2; omega⟩, by ext; simp [tailIdx]; omega⟩
  have hspanv : Submodule.span Ω (Set.range v) = Va ⊔ Vb := by
    refine le_antisymm (Submodule.span_le.2 ?_) (sup_le ?_ ?_)
    · rintro _ ⟨k, rfl⟩
      rcases hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [hvh]
        exact Submodule.mem_sup_left (hs1 ▸ Submodule.subset_span ⟨a, rfl⟩)
      · rw [hvt]
        exact Submodule.mem_sup_right (hs2 ▸ Submodule.subset_span ⟨a, rfl⟩)
    · rw [← hs1]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨headIdx hj a, hvh a⟩
    · rw [← hs2]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨tailIdx hj a, hvt a⟩
  have hrank : Module.finrank Ω (Submodule.span Ω (Set.range v)) = N := by
    rw [hspanv, ← hrange, LinearMap.finrank_range_of_inj hinj, hfin]
  have hliv : LinearIndependent Ω v :=
    linearIndependent_iff_card_eq_finrank_span.2 (by simpa [Set.finrank] using hrank.symm)
  have hpre : ∀ k, ∃ w, i w = v k := fun k => by
    have h : v k ∈ LinearMap.range i := by
      rw [hrange, ← hspanv]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  choose b hb using hpre
  have hlib : LinearIndependent Ω b := LinearIndependent.of_comp i (by
    have : (i ∘ b) = v := funext hb
    rw [show (⇑i ∘ b) = v from this]
    exact hliv)
  have hspanb : Submodule.span Ω (Set.range b) = ⊤ :=
    hlib.span_eq_top_of_card_eq_finrank' (by simp [hfin])
  refine ⟨U1 ⊓ U2, ⟨hp1, hp2⟩, b, hspanb, ?_, fun a => ?_, fun q hq => ?_⟩
  · have hm : (Submodule.span Ω (Set.range (b ∘ headIdx hj))).map i = Va := by
      rw [Submodule.map_span, ← Set.range_comp, ← hs1]
      congr 2
      funext a
      simp [hb, hvh]
    rw [← hm, Submodule.comap_map_eq_of_injective hinj]
  · rw [hb, hvt, ← hs2]
    exact Submodule.subset_span ⟨a, rfl⟩
  · have e1 := (hf1 q trivial hq.1).2
    have e2 := (hf2 q trivial hq.2).2
    have hsum : A q ⊔ B q =
        (Submodule.span (regAt ξ q) (Set.range b)).map (i.restrictScalars (regAt ξ q)) := by
      rw [Submodule.map_span, e1, e2]
      refine le_antisymm (sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)
      · rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨b (headIdx hj a), ⟨_, rfl⟩, by simp [hb, hvh]⟩
      · rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨b (tailIdx hj a), ⟨_, rfl⟩, by simp [hb, hvt]⟩
      · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        show i (b k) ∈ _
        rw [hb]
        rcases hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · rw [hvh]
          exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
        · rw [hvt]
          exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
    refine ⟨⟨hlib, ?_⟩, ?_, ?_⟩
    · show (A q ⊔ B q).comap (i.restrictScalars (regAt ξ q)) = _
      rw [hsum]
      exact Submodule.comap_map_eq_of_injective (show Function.Injective (i.restrictScalars (regAt ξ q)) from hinj) _
    · have : (fun a => i (b (tailIdx hj a))) = b2 := funext fun a => by rw [hb, hvt]
      rw [this]
      exact (hf2 q trivial hq.2).1
    · have : (fun a => i (b (tailIdx hj a))) = b2 := funext fun a => by rw [hb, hvt]
      rw [this]
      exact e2

end GlobalTheory.CompanionTheory.Ar.BigBlock

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BigBlock

open GlobalTheory.CompanionTheory.Ar.ChartTie in

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (S₀ : Finset ℕ) (𝔐 : HodgeCpt Y S₀ Dc.y) (bg sm : CMType H → CMType H ⊕ CMType H) (i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li) (s : CMType H → Fin (Dc.N - Dc.j) → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), (∀ τ, Function.Injective (i τ)) → (∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)) → (∀ τ, bg τ ≠ sm τ) → (∀ τ, labelRk D (bg τ) = Dc.j) → (∀ τ, labelRk D (sm τ) = Dc.N - Dc.j) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsVB Dc.N ⊤) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat) → (∀ τ, LinearIndependent Ω (s τ)) → (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y aMu e₀ → ∃ Hd : HodgeData Dc, ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ) := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc S₀ 𝔐 bg sm i s aMu e₀ hinj hrange hne hbg hsm hvb hch hsli hsspan hdeg
  classical
  have hT : CoordTie ℤ 𝔐.ξ (segreCoord Dc.y) := 𝔐.tie
  have hVB : ∀ t, (𝔐.V t).IsVB (labelRk D t) (𝔐.Vgen t) := 𝔐.vb
  have hj := Dc.j_le_N
  have hpre : ∀ τ a, ∃ w, i τ w = s τ a := fun τ a => by
    have h : s τ a ∈ LinearMap.range (i τ) := by
      rw [hrange τ]
      exact Submodule.mem_sup_right (hsspan τ ▸ Submodule.subset_span ⟨a, rfl⟩)
    exact h
  choose w hw using hpre
  have he₀ : e₀ ≠ 0 := hdeg.1
  let F : ∀ τ, Submodule Ω (W τ) := fun τ => (𝔐.Vgen (bg τ)).comap (i τ)
  let Pw : PiTensorProduct Ω (fun τ => ⋀[Ω]^(Dc.N - Dc.j) (W τ ⧸ F τ)) :=
    PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω (Dc.N - Dc.j) fun a => (F τ).mkQ (w τ a)
  refine ⟨⟨F, aMu, e₀⁻¹ • Pw, ?_⟩, fun _ => rfl⟩
  intro c hc
  let Q : 𝔐.X.Opens → Prop := fun V => ∃ b : ∀ τ, Fin Dc.N → W τ,
    (∀ τ, Submodule.span Ω (Set.range (b τ)) = ⊤) ∧
    (∀ τ, Submodule.span Ω (Set.range (b τ ∘ headIdx hj)) = F τ) ∧
    (∀ τ a, i τ (b τ (tailIdx hj a)) ∈ 𝔐.Vgen (sm τ)) ∧
    ∀ τ (q : Cpt 𝔐.ξ), q.1 ∈ V →
      (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsFrameAt (b τ) q ∧
      (𝔐.V (sm τ)).IsFrameAt (fun a => i τ (b τ (tailIdx hj a))) q
  have hQ : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → ∃ V : 𝔐.X.Opens, p.1 ∈ V ∧ Q V := by
    intro p _
    have hloc := fun τ => exists_block_frame 𝔐.X Ω 𝔐.ξ 𝔐.Li (W τ) (i τ) (𝔐.V (bg τ)) (𝔐.V (sm τ)) (𝔐.Vgen (bg τ)) (𝔐.Vgen (sm τ))
      Dc.N Dc.j hj (hinj τ) (hrange τ) (hbg τ ▸ hVB (bg τ)) (hsm τ ▸ hVB (sm τ)) (hvb τ) p
    choose U hpU b hb1 hb2 hb3 hb4 using hloc
    obtain ⟨V, hpV, hVU⟩ := exists_open_le U hpU
    exact ⟨V, hpV, b, hb1, hb2, hb3, fun τ q hq => hb4 τ q (hVU τ hq)⟩
  obtain ⟨k, f, g, hf, hg, hsum, hl⟩ := exists_cover hT hc Q hQ
  let p₀ : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hreg₀ : ∀ a : Ω, a ∈ regAt 𝔐.ξ p₀ := TieVB.regAt_genPt hT.gen
  have hp₀ : InChart 𝔐.ξ (segreCoord Dc.y) c p₀ := ⟨hc, fun c' => hreg₀ _⟩
  have key : ∀ l, f l ≠ 0 → ∃ b : ∀ τ, Fin Dc.N → W τ,
      (∀ τ, IsAdaptedFrame Dc.y (Dc.W τ) (F τ) hj c (f l) (b τ)) ∧
      ∃ u : Ω, IsUnitOn Dc.y c (f l) u ∧
        e₀⁻¹ • Pw = (u * chartMono Dc.y c aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) hj (b τ) := by
    intro l hfl
    obtain ⟨V, ⟨b, hspan, hhead, hmem, hfr⟩, hV⟩ := hl l
    refine ⟨b, fun τ => ⟨(GlobalTheory.T.segre_chart_bundle 𝔐.X Ω 𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT (hvb τ) (hch τ) c (f l) (b τ) hc (hf l) hfl).2
      fun p hp hu => (hfr τ p (hV p hp hu)).1, hspan τ, hhead τ⟩, ?_⟩
    have hex : ∀ τ, ∃ T : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω,
        ∀ a, i τ (b τ (tailIdx hj a)) = ∑ a', T a' a • s τ a' := fun τ => by
      have h : ∀ a, ∃ v : Fin (Dc.N - Dc.j) → Ω, ∑ a', v a' • s τ a' = i τ (b τ (tailIdx hj a)) := fun a =>
        (Submodule.mem_span_range_iff_exists_fun Ω).1 (by rw [hsspan τ]; exact hmem τ a)
      choose v hv using h
      exact ⟨Matrix.of fun a' a => v a a', fun a => (hv a).symm⟩
    choose T hTs using hex
    have hbw : ∀ τ a, b τ (tailIdx hj a) = ∑ a', T τ a' a • w τ a' := fun τ a => hinj τ (by
      rw [hTs, map_sum]
      exact Finset.sum_congr rfl fun a' _ => by rw [map_smul, hw])
    have hq : ∀ τ, quotWedge (F τ) hj (b τ) =
        (T τ).det • exteriorPower.ιMulti Ω (Dc.N - Dc.j) fun a => (F τ).mkQ (w τ a) := fun τ => by
      rw [← iotaMulti_comb]
      unfold quotWedge
      congr 1
      funext a
      rw [hbw, map_sum]
      exact Finset.sum_congr rfl fun a' _ => by rw [map_smul]
    have htp : (PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) hj (b τ)) = (∏ τ, (T τ).det) • Pw := by
      simp_rw [hq]
      exact MultilinearMap.map_smul_univ _ _ _
    have hgen : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → unitAt 𝔐.ξ p (f l) →
        (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsGenAt p (∏ τ, (T τ).det ^ (-1 : ℤ)) :=
      fun p hp hu => tens_isGenAt 𝔐.X Ω 𝔐.ξ _ _ _ p _ fun τ => detLat_isGenAt 𝔐.X Ω 𝔐.ξ 𝔐.Li _ _ (s τ) _ (T τ) p (hsli τ)
        (hfr τ p (hV p hp hu)).2 (hTs τ)
    have hu₀ : unitAt 𝔐.ξ p₀ (f l) := ⟨hfl, hreg₀ _, hreg₀ _⟩
    have ht₀ : (∏ τ, (T τ).det ^ (-1 : ℤ)) ≠ 0 := (hgen p₀ hp₀ hu₀).1
    have hm₀ : chartMono Dc.y c aMu ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ ?_
      exact Finset.prod_ne_zero_iff.1 hc k' (Finset.mem_univ _)
    have hme : chartMono Dc.y c aMu * e₀ ≠ 0 := mul_ne_zero hm₀ he₀
    have hunit : ∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord Dc.y) c p → unitAt 𝔐.ξ p (f l) →
        unitAt 𝔐.ξ p ((∏ τ, (T τ).det ^ (-1 : ℤ)) / (chartMono Dc.y c aMu * e₀)) := fun p hp hu =>
      unitAt_div_of_span_eq ht₀ hme ((hgen p hp hu).2.symm.trans (hdeg.2 p trivial c hp))
    refine ⟨(∏ τ, (T τ).det ^ (-1 : ℤ)) / (chartMono Dc.y c aMu * e₀), ⟨div_ne_zero ht₀ hme, ?_, ?_⟩, ?_⟩
    · exact exists_pow_mul_mem hT hc (hf l) fun p hp hu => (hunit p hp hu).2.1
    · exact exists_pow_mul_mem hT hc (hf l) fun p hp hu => (hunit p hp hu).2.2
    · rw [htp, smul_smul]
      congr 1
      have hD : (∏ τ, (T τ).det ^ (-1 : ℤ)) * ∏ τ, (T τ).det = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun τ _ => ?_
        have : (T τ).det ≠ 0 := fun h0 => ht₀ (Finset.prod_eq_zero (Finset.mem_univ τ) (by simp [h0]))
        simp [this]
      generalize (∏ τ, (T τ).det ^ (-1 : ℤ)) = A at hD ⊢
      generalize (∏ τ, (T τ).det) = B at hD ⊢
      have h1 : A / (chartMono Dc.y c aMu * e₀) * chartMono Dc.y c aMu * B = (A * B) * e₀⁻¹ := by
        field_simp
      rw [h1, hD, _root_.one_mul]
  obtain ⟨f', g', hf', hg', hsum', hP⟩ := exists_nonzero_cover (chartRing ℤ (segreCoord Dc.y) c).toSubring
    (fun f₁ => ∃ b : ∀ τ, Fin Dc.N → W τ,
      (∀ τ, IsAdaptedFrame Dc.y (Dc.W τ) (F τ) hj c f₁ (b τ)) ∧
      ∃ u : Ω, IsUnitOn Dc.y c f₁ u ∧
        e₀⁻¹ • Pw = (u * chartMono Dc.y c aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) hj (b τ))
    f g hf hg hsum key
  exact ⟨k, f', g', hf', hg', hsum', hP⟩

end GlobalTheory.CompanionTheory.Ar.BigBlock
