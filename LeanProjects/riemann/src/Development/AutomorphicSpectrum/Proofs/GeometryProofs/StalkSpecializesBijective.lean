import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagPull

section Semi
variable {Ω Ω' E F : Type} [Field Ω] [Field Ω'] [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]

theorem map_mem_flagStep {i : Ω →+* Ω'} {j : E →+ F} (hj : ∀ (a : Ω) (e : E), j (a • e) = i a • j e) {r : ℕ}
    (b : Fin r → E) (s : ℕ) {x : E} (hx : x ∈ flagStep Ω b s) : j x ∈ flagStep Ω' (fun k => j (b k)) s := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx

theorem flagStep_map_eq {i : Ω →+* Ω'} {j : E →+ F} (hj : ∀ (a : Ω) (e : E), j (a • e) = i a • j e) {r : ℕ}
    {b b₀ : Fin r → E} (h : ∀ s, flagStep Ω b s = flagStep Ω b₀ s) (s : ℕ) :
    flagStep Ω' (fun k => j (b k)) s = flagStep Ω' (fun k => j (b₀ k)) s := by
  have key : ∀ {b b₀ : Fin r → E}, (∀ s, flagStep Ω b s = flagStep Ω b₀ s) →
      flagStep Ω' (fun k => j (b k)) s ≤ flagStep Ω' (fun k => j (b₀ k)) s := by
    intro b b₀ h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine map_mem_flagStep hj b₀ s ?_
    rw [← h]
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  exact le_antisymm (key h) (key fun s => (h s).symm)

end Semi

section Pull
variable {X X' : Scheme.{0}} {Ω Ω' E F : Type} [Field Ω] [Field Ω'] [AddCommGroup E] [Module Ω E] [AddCommGroup F]
  [Module Ω' F] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}
  {j : E →+ F}

theorem pull_isFrameAt (hd : Dominates ξ' ξ f i) (hj : IsExtOver i j) {L : Lat ξ E} {r : ℕ} {b : Fin r → E}
    (p' : Cpt ξ') (hp : genPt ξ ⤳ f p'.1) (hb : L.IsFrameAt b ⟨f p'.1, hp⟩) :
    (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) p' := by
  obtain ⟨hp2, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd p'
  refine ⟨hj.2 r b hb.1, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨h, e, he, rfl⟩
    have he' : e ∈ L ⟨f p'.1, hp⟩ := he
    rw [hb.2] at he'
    clear he
    show j e ∈ Submodule.span (regAt ξ' p') (Set.range fun k => j (b k))
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have : j (a • x) = (⟨i a, hreg a a.2⟩ : regAt ξ' p') • j x := hj.1 (a : Ω) x
      rw [this]
      exact Submodule.smul_mem _ _ hx
  · rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨hp, b k, ?_, rfl⟩
    rw [hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem pull_isFlagVB (hd : Dominates ξ' ξ f i) (hj : IsExtOver i j) {L : Lat ξ E} {r : ℕ} {b₀ : Fin r → E}
    (hL : L.IsFlagVBOn Set.univ b₀) : (L.pull ξ' f j).IsFlagVBOn Set.univ fun k => j (b₀ k) := by
  intro p' _
  obtain ⟨hp, -, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd p'
  obtain ⟨U, hU, b, hb, hfr⟩ := hL ⟨f p'.1, hp⟩ trivial
  refine ⟨f ⁻¹ᵁ U, hU, fun k => j (b k), flagStep_map_eq hj.1 hb, fun q _ hq => ?_⟩
  obtain ⟨hq2, -, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
  exact pull_isFrameAt hd hj q hq2 (hfr _ trivial hq)

theorem gr_gen_pull (hd : Dominates ξ' ξ f i) (hj : IsExtOver i j) {L : Lat ξ E} {r : ℕ} {b₀ : Fin r → E}
    (hb₀ : LinearIndependent Ω b₀) (hL : L.IsFlagVBOn Set.univ b₀) (p' : Cpt ξ') (hp : genPt ξ ⤳ f p'.1) (k : Fin r) :
    ∃ t : Ω, (L.gr b₀ k).IsGenAt ⟨f p'.1, hp⟩ t ∧ ((L.pull ξ' f j).gr (fun k => j (b₀ k)) k).IsGenAt p' (i t) := by
  obtain ⟨U, hU, b, hb, hfr⟩ := hL ⟨f p'.1, hp⟩ trivial
  have hfr0 := hfr _ trivial hU
  have hmem : b k ∈ flagStep Ω b₀ ((k : ℕ) + 1) := by
    rw [← hb]
    exact Submodule.subset_span ⟨k, by simp, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Ω, b k - t • b₀ k ∈ flagStep Ω b₀ k := by
    have hsub : flagStep Ω b₀ ((k : ℕ) + 1) ≤ Submodule.span Ω {b₀ k} ⊔ flagStep Ω b₀ k := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨l, hl, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨l, h, rfl⟩)
      · have : l = k := Fin.ext h
        subst this
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hsub hmem)
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨t, by rw [← e]; simpa using hz⟩
  refine ⟨t, FlagGrGen.gr_isGenAt X Ω ξ E L r b₀ b _ k t hb₀ hb hfr0 ht, ?_⟩
  refine FlagGrGen.gr_isGenAt X' Ω' ξ' F _ r _ (fun k => j (b k)) p' k (i t) (hj.2 r b₀ hb₀)
    (flagStep_map_eq hj.1 hb) (pull_isFrameAt hd hj p' hp hfr0) ?_
  have := map_mem_flagStep hj.1 b₀ k ht
  rwa [map_sub, hj.1] at this

end Pull

section Tens
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem tens_unit {Λ : Lat ξ Ω} {p : Cpt ξ} {t : Ω} (h : Λ.IsGenAt p t) (n : ℤ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {t ^ n} := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨u, hu, e⟩ := Flat.ZUnit.exists_of_span_eq (hs ()).1 ((hs ()).2.symm.trans h.2)
    have hun : (u ^ n) ∈ regAt ξ p := by
      obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
      · simpa using (Flat.ZUnit.pow hu m).2.1
      · simpa using (Flat.ZUnit.pow (Flat.ZUnit.inv hu) m).2.1
    have : ∏ i : Unit, s i ^ n = (⟨u ^ n, hun⟩ : regAt ξ p) • t ^ n := by
      show _ = u ^ n * t ^ n
      simp [e, mul_zpow]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rintro _ rfl
    exact Submodule.subset_span ⟨fun _ => t, fun _ => h, by simp⟩

end Tens

section Chart
variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}

theorem inChart_of_pull (hd : Dominates ξ' ξ f i) (hg' : IsCptGen ξ') {κ : Type} {x : κ → Ω}
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ x c p) (p' : Cpt ξ') (hp : genPt ξ ⤳ f p'.1) {d : κ} (hd0 : x d ≠ 0)
    (hr : ∀ c, i (x c / x d) ∈ regAt ξ' p') : InChart ξ x d ⟨f p'.1, hp⟩ := by
  obtain ⟨hp2, hreg, hunit⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd p'
  obtain ⟨c₀, hc₀, hrat⟩ := hcov ⟨f p'.1, hp⟩
  have ha : x d / x c₀ ∈ regAt ξ ⟨f p'.1, hp⟩ := hrat d
  have hu' : unitAt ξ' p' (i (x d / x c₀)) := by
    refine ⟨(map_ne_zero i).2 (div_ne_zero hd0 hc₀), hreg _ ha, ?_⟩
    rw [← map_inv₀, inv_div]
    exact hr c₀
  have hu := hunit hg' _ ha hu'
  refine ⟨hd0, fun c => ?_⟩
  have : x c / x d = x c / x c₀ * (x d / x c₀)⁻¹ := by field_simp
  rw [this]
  exact mul_mem (hrat c) hu.2.2

end Chart

section Block
variable {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
  [∀ k, Fintype (J' k)] {κ : K → K'} {v : (Σ k, J k) → (Σ k, J' k)}

theorem exists_chart (hv : AI.I1.IsBlockMap κ v) (c' : ∀ k', J' k') :
    ∃ d : ∀ k, J k, ∀ k, v ⟨k, d k⟩ = ⟨κ k, c' (κ k)⟩ := by
  have : ∀ k, ∃ dk : J k, v ⟨k, dk⟩ = ⟨κ k, c' (κ k)⟩ := by
    intro k
    obtain ⟨⟨k₀, d₀⟩, e⟩ := hv.2.2.2 ⟨κ k, c' (κ k)⟩ ⟨k, rfl⟩
    have h1 := hv.2.2.1 ⟨k₀, d₀⟩
    rw [e] at h1
    obtain rfl : k = k₀ := hv.1 h1
    exact ⟨d₀, e⟩
  choose d hd using this
  exact ⟨d, hd⟩

theorem exists_extend (hv : AI.I1.IsBlockMap κ v) (c' : ∀ k', J' k') (d' : ∀ k, J k) :
    ∃ c'' : ∀ k', J' k', (∀ k, (⟨κ k, c'' (κ k)⟩ : Σ k', J' k') = v ⟨k, d' k⟩) ∧
      ∀ k', k' ∉ Set.range κ → c'' k' = c' k' := by
  classical
  have hs : ∀ (s : Σ k', J' k') (k' : K') (e : s.1 = k'), (⟨k', e ▸ s.2⟩ : Σ k', J' k') = s := by
    rintro ⟨a, b⟩ k' rfl
    rfl
  refine ⟨fun k' => if h : ∃ k, κ k = k' then
      ((hv.2.2.1 ⟨h.choose, d' h.choose⟩).trans h.choose_spec) ▸ (v ⟨h.choose, d' h.choose⟩).2 else c' k', ?_, ?_⟩
  · intro k
    have h : ∃ k₀, κ k₀ = κ k := ⟨k, rfl⟩
    simp only [dif_pos h]
    rw [hs]
    have : h.choose = k := hv.1 h.choose_spec
    rw [this]
  · intro k' hk
    have : ¬ ∃ k, κ k = k' := hk
    simp only [dif_neg this]

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] {i : Ω →+* Ω'} {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}

theorem segre_split (c : ∀ k', J' k') (hκ : Function.Injective κ) [DecidableEq K'] :
    ∏ k', y' ⟨k', c k'⟩ = (∏ k, y' ⟨κ k, c (κ k)⟩) * ∏ k' ∈ (Finset.univ.image κ)ᶜ, y' ⟨k', c k'⟩ := by
  rw [← Finset.prod_mul_prod_compl (Finset.univ.image κ), Finset.prod_image fun a _ b _ h => hκ h]

theorem ratio_reg {X' : Scheme.{0}} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} (hv : AI.I1.IsBlockMap κ v)
    (hy : ∀ q, y' (v q) = i (y q)) {p' : Cpt ξ'} {c' : ∀ k', J' k'}
    (hc : InChart ξ' (fun c'' : ∀ k', J' k' => ∏ k', y' ⟨k', c'' k'⟩) c' p') {d : ∀ k, J k}
    (hd : ∀ k, v ⟨k, d k⟩ = ⟨κ k, c' (κ k)⟩) :
    (∏ k, y ⟨k, d k⟩) ≠ 0 ∧ ∀ d' : ∀ k, J k, i ((∏ k, y ⟨k, d' k⟩) / ∏ k, y ⟨k, d k⟩) ∈ regAt ξ' p' := by
  classical
  have hval : ∀ (c : ∀ k', J' k') (e : ∀ k, J k), (∀ k, (⟨κ k, c (κ k)⟩ : Σ k', J' k') = v ⟨k, e k⟩) →
      ∏ k, y' ⟨κ k, c (κ k)⟩ = i (∏ k, y ⟨k, e k⟩) := by
    intro c e h
    rw [map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [h k, hy]
  have h0 : (∏ k', y' ⟨k', c' k'⟩) ≠ 0 := hc.1
  have hdv := hval c' d fun k => (hd k).symm
  rw [segre_split c' hv.1, hdv] at h0
  have hA := left_ne_zero_of_mul h0
  have hB := right_ne_zero_of_mul h0
  refine ⟨fun h => hA (by rw [h, map_zero]), fun d' => ?_⟩
  obtain ⟨c'', h1, h2⟩ := exists_extend hv c' d'
  have hr := hc.2 c''
  have e1 := segre_split (y' := y') c'' hv.1
  have e2 := segre_split (y' := y') c' hv.1
  have e3 : ∏ k' ∈ (Finset.univ.image κ)ᶜ, y' ⟨k', c'' k'⟩ = ∏ k' ∈ (Finset.univ.image κ)ᶜ, y' ⟨k', c' k'⟩ := by
    refine Finset.prod_congr rfl fun k' hk => ?_
    rw [h2 k' fun ⟨k, hk'⟩ => by simp [← hk'] at hk]
  simp only [] at hr
  rw [e1, e2, e3, hval c'' d' h1, hdv, mul_div_mul_right _ _ hB, ← map_div₀] at hr
  exact hr

theorem monomial_pull (hv : AI.I1.IsBlockMap κ v) (hy : ∀ q, y' (v q) = i (y q)) (a : K → ℤ) {c' : ∀ k', J' k'}
    {d : ∀ k, J k} (hd : ∀ k, v ⟨k, d k⟩ = ⟨κ k, c' (κ k)⟩) :
    ∏ k', y' ⟨k', c' k'⟩ ^ AI.I1.pullDeg κ a k' = i (∏ k, y ⟨k, d k⟩ ^ a k) := by
  rw [map_prod]
  refine (Fintype.prod_of_injective κ hv.1 _ _ ?_ ?_).symm
  · intro k' hk
    have : AI.I1.pullDeg κ a k' = 0 := by
      unfold AI.I1.pullDeg
      rw [Function.extend_apply' _ _ _ fun ⟨k, h⟩ => hk ⟨k, h⟩]
      rfl
    rw [this, zpow_zero]
  · intro k
    have : AI.I1.pullDeg κ a (κ k) = a k := by
      unfold AI.I1.pullDeg
      exact hv.1.extend_apply _ _ _
    rw [this, map_zpow₀, ← hy, hd k]

theorem isDegOn_pull {X X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {f : X' ⟶ X} (hd : Dominates ξ' ξ f i) (hg' : IsCptGen ξ')
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    (hv : AI.I1.IsBlockMap κ v) (hy : ∀ q, y' (v q) = i (y q)) {Λ : Lat ξ Ω} {Λ' : Lat ξ' Ω'}
    (hΛ : ∀ (p' : Cpt ξ') (hp : genPt ξ ⤳ f p'.1), ∃ t, Λ.IsGenAt ⟨f p'.1, hp⟩ t ∧ Λ'.IsGenAt p' (i t)) (n : ℤ)
    {a : K → ℤ} {e : Ω} (h : (Lat.tens (fun _ : Unit => Λ) fun _ => n).IsDegOn Set.univ y a e) :
    (Lat.tens (fun _ : Unit => Λ') fun _ => n).IsDegOn Set.univ y' (AI.I1.pullDeg κ a) (i e) := by
  refine ⟨(map_ne_zero i).2 h.1, fun p' _ c' hc' => ?_⟩
  obtain ⟨hp, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd p'
  obtain ⟨t, ht, ht'⟩ := hΛ p' hp
  obtain ⟨d, hdv⟩ := exists_chart hv c'
  obtain ⟨hx0, hrat⟩ := ratio_reg hv hy hc' hdv
  have hch := inChart_of_pull hd hg' hcov p' hp hx0 hrat
  have h1 := h.2 ⟨f p'.1, hp⟩ trivial d hch
  rw [tens_unit ht] at h1
  rw [tens_unit ht', smul_eq_mul, monomial_pull hv hy a hdv, ← map_mul]
  obtain ⟨u, hu, hw⟩ := Flat.ZUnit.exists_of_span_eq (zpow_ne_zero n ht.1) h1
  simp only [smul_eq_mul] at h1 hw
  have hu' : (i u) ∈ regAt ξ' p' ∧ (i u)⁻¹ ∈ regAt ξ' p' :=
    ⟨hreg _ hu.2.1, by rw [← map_inv₀]; exact hreg _ hu.2.2⟩
  have hne : i u ≠ 0 := (map_ne_zero i).2 hu.1
  have e1 : (i t) ^ n = i u * i ((∏ k, y ⟨k, d k⟩ ^ a k) * e) := by
    rw [← map_zpow₀, hw, map_mul]
  rw [e1]
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨i u, hu'.1⟩, rfl⟩
  · refine ⟨⟨(i u)⁻¹, hu'.2⟩, ?_⟩
    show (i u)⁻¹ * (i u * _) = _
    rw [inv_mul_cancel_left₀ hne]

end Block

section Generic
variable {Ω₀ Ω₀' Ω Ω' : Type} [Field Ω₀] [Field Ω₀'] [Field Ω] [Field Ω']

theorem finrank_adjoin_pull (fn : Ω₀ →+* Ω) (fn' : Ω₀' →+* Ω') (ψ : Ω₀ ≃+* Ω₀') (i : Ω →+* Ω')
    (hc : fn'.comp ψ.toRingHom = i.comp fn) {T : Type} (w : T → Ω) :
    letI := fn.toAlgebra
    letI := fn'.toAlgebra
    Module.finrank (IntermediateField.adjoin Ω₀' (Set.range fun q => i (w q))) Ω' =
      Module.finrank i.fieldRange Ω' * Module.finrank (IntermediateField.adjoin Ω₀ (Set.range w)) Ω := by
  letI := fn.toAlgebra
  letI := fn'.toAlgebra
  set A := IntermediateField.adjoin Ω₀ (Set.range w) with hA
  set A' := IntermediateField.adjoin Ω₀' (Set.range fun q => i (w q)) with hA'
  have hQ : A'.toSubfield = A.toSubfield.map i := by
    show Subfield.closure _ = Subfield.map i (Subfield.closure _)
    rw [RingHom.map_field_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp]
    congr 2
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨ψ.symm a, ?_⟩
      show i (fn (ψ.symm a)) = fn' a
      have := RingHom.congr_fun hc (ψ.symm a)
      simpa using this.symm
    · rintro ⟨a, rfl⟩
      refine ⟨ψ a, ?_⟩
      exact RingHom.congr_fun hc a
  have hmem : ∀ x ∈ A, i x ∈ A' := fun x hx => by
    have : i x ∈ A'.toSubfield := by
      rw [hQ]
      exact ⟨x, hx, rfl⟩
    exact this
  have hsurj : ∀ x ∈ A', ∃ a ∈ A, i a = x := fun x hx => by
    have : x ∈ A'.toSubfield := hx
    rw [hQ] at this
    obtain ⟨a, ha, rfl⟩ := this
    exact ⟨a, ha, rfl⟩
  have hle : ∀ x ∈ A', x ∈ i.fieldRange := fun x hx => by
    obtain ⟨a, -, rfl⟩ := hsurj x hx
    exact ⟨a, rfl⟩
  let g : A' →+* i.fieldRange :=
    { toFun := fun x => ⟨x.1, hle x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI := g.toAlgebra
  haveI : IsScalarTower A' i.fieldRange Ω' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e₀ : A →+* A' :=
    { toFun := fun x => ⟨i x.1, hmem x.1 x.2⟩
      map_one' := Subtype.ext (map_one i)
      map_mul' := fun x y => Subtype.ext (map_mul i x.1 y.1)
      map_zero' := Subtype.ext (map_zero i)
      map_add' := fun x y => Subtype.ext (map_add i x.1 y.1) }
  let e₁ : A ≃+* A' := RingEquiv.ofBijective e₀
    ⟨fun x y h => Subtype.ext (i.injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨a, ha, e⟩ := hsurj x.1 x.2
      exact ⟨⟨a, ha⟩, Subtype.ext e⟩⟩
  let e₂ : Ω ≃+* i.fieldRange := RingEquiv.ofBijective i.rangeRestrictField
    ⟨fun x y h => i.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨a, Subtype.ext ha⟩⟩
  have h1 : Module.finrank A Ω = Module.finrank A' i.fieldRange :=
    Algebra.finrank_eq_of_equiv_equiv e₁ e₂ (by ext x; rfl)
  rw [← Module.finrank_mul_finrank A' i.fieldRange Ω', h1, mul_comm]

theorem genericFlag_pull (fn : Ω₀ →+* Ω) (fn' : Ω₀' →+* Ω') (ψ : Ω₀ ≃+* Ω₀') (i : Ω →+* Ω')
    (hc : fn'.comp ψ.toRingHom = i.comp fn) {E F F' : Type} [AddCommGroup E] [Module Ω₀ E] [Module Ω₀' E]
    (hs : ∀ (a : Ω₀) (e : E), ψ a • e = a • e) [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω' F']
    (j₀ : E →+ F) (j : F →+ F') (hj : IsExtOver i j) {S : Type} {r : S → ℕ} (V : S → Submodule Ω₀ E)
    (V' : S → Submodule Ω₀' E) (hV : ∀ s e, e ∈ V' s ↔ e ∈ V s) (b : ∀ s, Fin (r s) → F) (d : ℕ)
    [FiniteDimensional i.fieldRange Ω']
    (h : letI := fn.toAlgebra; IsGenericFlag (Ω' := Ω) j₀ V b d) :
    letI := fn'.toAlgebra
    IsGenericFlag (Ω' := Ω') (j.comp j₀) V' (fun s k => j (b s k)) (Module.finrank i.fieldRange Ω' * d) := by
  letI := fn.toAlgebra
  letI := fn'.toAlgebra
  obtain ⟨c, u, hcV, hlin, hcj, hb, hd1, hup, hfl, hai, hd0, hfr⟩ := h
  have hsurj : ∀ a : Ω₀', ψ (ψ.symm a) = a := ψ.apply_symm_apply
  have hs' : ∀ (a : Ω₀') (e : E), a • e = ψ.symm a • e := fun a e => by rw [← hs, hsurj]
  have hcomp : ∀ a : Ω₀', fn' a = i (fn (ψ.symm a)) := fun a => by
    have := RingHom.congr_fun hc (ψ.symm a)
    simpa using this
  have hjs : ∀ (a : Ω) (e : F), j (a • e) = i a • j e := hj.1
  refine ⟨c, fun σ => (u σ).map i, fun σ => ⟨?_, ?_⟩, fun a e => ?_, fun σ => ?_, fun σ => ?_, fun σ k => ?_,
    fun σ l k hlk => ?_, fun σ s => ?_, ?_, ?_, ?_⟩
  · rw [linearIndependent_iff']
    intro t g hg x hx
    have := (linearIndependent_iff'.1 (hcV σ).1) t (fun q => ψ.symm (g q)) (by simpa [hs'] using hg) x hx
    simpa using this
  · ext e
    rw [hV, ← (hcV σ).2]
    constructor
    · intro he
      induction he using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul a x _ hx => rw [hs']; exact Submodule.smul_mem _ _ hx
    · intro he
      induction he using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul a x _ hx => rw [← hs]; exact Submodule.smul_mem _ _ hx
  · show j (j₀ (a • e)) = fn' a • j (j₀ e)
    rw [hs', hlin, hcomp]
    exact hjs _ _
  · exact hj.2 _ _ (hcj σ)
  · exact hj.2 _ _ (hb σ)
  · simp [hd1]
  · simp [hup σ l k hlk]
  · rw [show (fun k => ∑ l, ((u σ).map i) l k • (j.comp j₀) (c σ l)) =
        fun k => j (∑ l, u σ l k • j₀ (c σ l)) by
      funext k
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => (hjs _ _).symm]
    exact flagStep_map_eq hj.1 (hfl σ) s
  · exact hai.ringHom_of_comp_eq ψ i ψ.surjective i.injective hc
  · exact Nat.mul_pos Module.finrank_pos hd0
  · have := finrank_adjoin_pull fn fn' ψ i hc (fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)
    rw [hfr] at this
    exact this

end Generic

section Point
variable {X : Scheme.{0}} {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂]

theorem stalkSpecializes_bijective {x y : X} (e : y = x) (h : y ⤳ x) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem genMap_bijective {ξ : Spec (CommRingCat.of Ω₁) ⟶ X} (hg : IsCptGen ξ) (p : Cpt ξ) (e : genPt ξ = p.1) :
    Function.Bijective (genMap ξ p) := by
  have h := hg.bij.comp (stalkSpecializes_bijective e p.2)
  exact h

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem mono_spec_comp {R : CommRingCat.{0}} (g : R →+* Ω₁) (hb : Function.Bijective g) (F : Spec R ⟶ X) [Mono F]
    {ξ : Spec (CommRingCat.of Ω₁) ⟶ X} (hξ : Spec.map (CommRingCat.ofHom g : R ⟶ CommRingCat.of Ω₁) ≫ F = ξ) :
    Mono ξ := by
  subst hξ
  haveI : IsIso (CommRingCat.ofHom g : R ⟶ CommRingCat.of Ω₁) := (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

theorem mono_of_isCptGen {ξ : Spec (CommRingCat.of Ω₁) ⟶ X} (hg : IsCptGen ξ) : Mono ξ := by
  have hb := genMap_bijective hg ⟨genPt ξ, specializes_rfl⟩ rfl
  have hs := RegAtDom.spec_genMap ξ (genPt ξ) specializes_rfl
  exact mono_spec_comp (R := X.presheaf.stalk (genPt ξ)) _ hb (X.fromSpecStalk (genPt ξ)) hs

theorem exists_field_iso_same_spec {R : CommRingCat.{0}} (g₁ : R →+* Ω₁) (g₂ : R →+* Ω₂) (b₁ : Function.Bijective g₁)
    (b₂ : Function.Bijective g₂) (F : Spec R ⟶ X) {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X}
    {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X} (a₁ : Spec.map (CommRingCat.ofHom g₁ : R ⟶ CommRingCat.of Ω₁) ≫ F = ξ₁)
    (a₂ : Spec.map (CommRingCat.ofHom g₂ : R ⟶ CommRingCat.of Ω₂) ≫ F = ξ₂) :
    ∃ ψ : Ω₁ ≃+* Ω₂, spMap ψ.toRingHom ≫ ξ₁ = ξ₂ := by
  subst a₁ a₂
  let e₁ := RingEquiv.ofBijective g₁ b₁
  let e₂ := RingEquiv.ofBijective g₂ b₂
  refine ⟨e₁.symm.trans e₂, ?_⟩
  have hc : (e₁.symm.trans e₂).toRingHom.comp g₁ = g₂ := by
    ext x
    show e₂ (e₁.symm (e₁ x)) = e₂ x
    rw [e₁.symm_apply_apply]
  rw [← Category.assoc]
  congr 1
  rw [← hc]
  exact (spMap_comp (A := R) g₁ _).symm

theorem exists_iso {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X} (h₁ : IsCptGen ξ₁)
    (h₂ : IsCptGen ξ₂) (e : genPt ξ₁ = genPt ξ₂) : ∃ ψ : Ω₁ ≃+* Ω₂, spMap ψ.toRingHom ≫ ξ₁ = ξ₂ := by
  have hs₁ : genPt ξ₁ ⤳ genPt ξ₁ := specializes_rfl
  have hs₂ : genPt ξ₂ ⤳ genPt ξ₁ := specializes_of_eq e.symm
  have b₁ := genMap_bijective h₁ ⟨genPt ξ₁, hs₁⟩ rfl
  have b₂ := genMap_bijective h₂ ⟨genPt ξ₁, hs₂⟩ e.symm
  have a₁ := RegAtDom.spec_genMap ξ₁ (genPt ξ₁) hs₁
  have a₂ := RegAtDom.spec_genMap ξ₂ (genPt ξ₁) hs₂
  exact exists_field_iso_same_spec (R := X.presheaf.stalk (genPt ξ₁)) _ _ b₁ b₂ (X.fromSpecStalk (genPt ξ₁)) a₁ a₂

end Point

section Transport
variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem alg_eq (a : R) : algebraMap R (DualNumber R) a = TrivSqZeroExt.inl a := rfl

theorem dualMap_comp (f : R →+* R') (g : R' →+* R'') : dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext a <;> simp [dualMap]

theorem dualMap_algebraMap (f : R →+* R') :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  ext a <;> simp [dualMap, alg_eq]

theorem dualMap_fst (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  ext a <;> simp [dualMap, alg_eq]

theorem dualMap_epsMul (ψ : R ≃+* R') (c : R') :
    (dualMap ψ.toRingHom).comp (epsMul (ψ.symm c)) = (epsMul c).comp (dualMap ψ.toRingHom) := by
  ext a <;> simp [dualMap, epsMul, alg_eq]

def epsMap (ψ : R ≃+* R') {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx : spMap ψ.toRingHom ≫ x = x') : epsAt x' ⟶ epsAt x :=
  Over.homMk (spMap (dualMap ψ.toRingHom)) (by
    subst hx
    show spMap (dualMap ψ.toRingHom) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap ψ.toRingHom ≫ x
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, dualMap_algebraMap])

theorem epsMap_left (ψ : R ≃+* R') {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx : spMap ψ.toRingHom ≫ x = x') : (epsMap ψ hx).left = spMap (dualMap ψ.toRingHom) := rfl

theorem symm_eq (ψ : R ≃+* R') {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx : spMap ψ.toRingHom ≫ x = x') : spMap ψ.symm.toRingHom ≫ x' = x := by
  subst hx
  have : ψ.symm.toRingHom.comp ψ.toRingHom = RingHom.id R := by ext; simp
  rw [← Category.assoc, ← spMap_comp, this]
  simp [spMap]

theorem epsMap_inv (ψ : R ≃+* R') {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx : spMap ψ.toRingHom ≫ x = x') (hx' : spMap ψ.symm.toRingHom ≫ x' = x) :
    epsMap ψ.symm hx' ≫ epsMap ψ hx = 𝟙 _ := by
  have h : ψ.symm.toRingHom.comp ψ.toRingHom = RingHom.id R := by ext; simp
  have h2 : dualMap (RingHom.id R) = RingHom.id _ := by ext a <;> simp [dualMap]
  apply Over.OverMorphism.ext
  show spMap (dualMap ψ.symm.toRingHom) ≫ spMap (dualMap ψ.toRingHom) = 𝟙 _
  rw [← spMap_comp, ← dualMap_comp, h, h2]
  simp [spMap]

theorem epsMap_inv' (ψ : R ≃+* R') {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx : spMap ψ.toRingHom ≫ x = x') (hx' : spMap ψ.symm.toRingHom ≫ x' = x) :
    epsMap ψ hx ≫ epsMap ψ.symm hx' = 𝟙 _ := by
  have h : ψ.toRingHom.comp ψ.symm.toRingHom = RingHom.id R' := by ext; simp
  have h2 : dualMap (RingHom.id R') = RingHom.id _ := by ext a <;> simp [dualMap]
  apply Over.OverMorphism.ext
  show spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap ψ.symm.toRingHom) = 𝟙 _
  rw [← spMap_comp, ← dualMap_comp, h, h2]
  simp [spMap]

variable {G : Over S} [GrpObj G]

theorem tan_comp (ψ : R ≃+* R') {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx : spMap ψ.toRingHom ≫ x = x') {v : epsAt x ⟶ G} (hv : IsTanAt G x v) :
    IsTanAt G x' (epsMap ψ hx ≫ v) := by
  let B : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap ψ.toRingHom) hx
  have h1 : (1 : Over.mk x' ⟶ G) = B ≫ 1 := (comp_one B).symm
  have h2 : (1 : Over.mk x' ⟶ G).left = spMap ψ.toRingHom ≫ (1 : Over.mk x ⟶ G).left :=
    congrArg (fun t => Over.Hom.left t) h1
  unfold IsTanAt at *
  rw [h2, ← hv]
  show spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap ψ.toRingHom) ≫ v.left =
    spMap ψ.toRingHom ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left
  rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, dualMap_fst]

def transport (ψ : R ≃+* R') {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx : spMap ψ.toRingHom ≫ x = x') {E : Type} [AddCommGroup E] [Module R E] [Module R' E]
    (hs : ∀ (a : R) (e : E), ψ a • e = a • e) (M : LieModel G x E) : LieModel G x' E where
  pt e := epsMap ψ hx ≫ M.pt e
  tan e := tan_comp ψ hx (M.tan e)
  inj e e' h := M.inj (by
    have := congrArg (fun t => epsMap ψ.symm (symm_eq ψ hx) ≫ t) h
    simpa only [← Category.assoc, epsMap_inv, Category.id_comp] using this)
  onto v hv := by
    obtain ⟨e, he⟩ := M.onto _ (tan_comp ψ.symm (symm_eq ψ hx) hv)
    exact ⟨e, by rw [he, ← Category.assoc, epsMap_inv', Category.id_comp]⟩
  add e e' := by rw [M.add, comp_mul]
  smul c e := by
    have h1 : c • e = ψ.symm c • e := by rw [← hs, ψ.apply_symm_apply]
    rw [h1, Over.comp_left, Over.comp_left, M.smul, epsMap_left, ← Category.assoc, ← Category.assoc]
    congr 1
    show spMap (dualMap ψ.toRingHom) ≫ spMap (epsMul (ψ.symm c)) = spMap (epsMul c) ≫ spMap (dualMap ψ.toRingHom)
    rw [← spMap_comp, ← spMap_comp, dualMap_epsMul]

end Transport

section Eig

theorem hom_ext_of_pullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (hc : IsPullback φ G'.hom G.hom f) {T : Over S'} {a b : T ⟶ G'} (h : a.left ≫ φ = b.left ≫ φ) : a = b := by
  apply Over.OverMorphism.ext
  exact hc.hom_ext h (by simp)

variable {Ω Ω' E F O : Type} [Field Ω] [Field Ω'] [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]
  [CommRing O]

theorem injective_of_isExtOver {i : Ω →+* Ω'} {j : E →+ F} (hj : IsExtOver i j) : Function.Injective j := by
  refine (injective_iff_map_eq_zero j).2 fun x hx => ?_
  by_contra h0
  have h1 : LinearIndependent Ω (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 h0
  exact (hj.2 1 _ h1).ne_zero 0 hx

theorem mem_eigSp_iff {i : Ω →+* Ω'} {j : E →+ F} (hj : IsExtOver i j) (ρ : O →+* Module.End Ω E)
    (ρ' : O →+* Module.End Ω' F) (σ : O →+* Ω) (hρ : ∀ a w, j (ρ a w) = ρ' a (j w)) (w : E) :
    j w ∈ eigSp ρ' (i.comp σ) ↔ w ∈ eigSp ρ σ := by
  have key : ∀ a, j (ρ a w - σ a • w) = ρ' a (j w) - i (σ a) • j w := fun a => by
    rw [map_sub, hρ, hj.1]
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, RingHom.comp_apply]
  refine forall_congr' fun a => ?_
  rw [← key]
  exact map_eq_zero_iff j (injective_of_isExtOver hj)

end Eig

theorem flag_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (h : A'.X ⟶ A.X) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t h) (κ : K → K') (v : (Σ k, J k) → (Σ k, J' k)) (Fl : A.Flag), AI.I1.IsBlockMap κ v → (∀ q, y' (v q) = i (y q)) → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ h i → A'.f = h ≫ A.f → A'.m.φ = m.φ ≫ A.m.φ → A'.cst = i.comp A.cst → IsExtOver i j → (∀ w, (A'.M.pt (j w)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt w).left) → (∀ s, A'.V s = (A.V s).pull A'.ξ h j) → FiniteDimensional i.fieldRange Ω' → ∃ Fl' : A'.Flag, (∀ s k, Fl'.b s k = j (Fl.b s k)) ∧ Fl'.deg = Module.finrank i.fieldRange Ω' * Fl.deg ∧ (∃ (ψ : A.Ω₀ ≃+* A'.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀), A'.fn.comp ψ.toRingHom = i.comp A.fn ∧ spMap ψ.toRingHom ≫ A.ξ₀ = A'.ξ₀ ∧ (∀ e, (Fl'.M₀.pt (θ e)).left = spMap (dualMap ψ.toRingHom) ≫ (Fl.M₀.pt e).left) ∧ ∀ e, Fl'.j (θ e) = j (Fl.j e)) ∧ ∀ xdeg e, Fl.RootLines xdeg e → Fl'.RootLines (fun r => AI.I1.pullDeg κ (xdeg r)) (fun r => i (e r)) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ i K K' _ _ J J' _ _ y y' A A' h j m κ v Fl hv hy hd hf hφ hcst hj hpt hV hfin
  haveI := hfin
  have hgen : genPt A.ξ₀ = genPt A'.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt A'.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_iso A.gen₀ A'.gen₀ hgen
  have hfn : A'.fn.comp ψ.toRingHom = i.comp A.fn := by
    haveI := mono_of_isCptGen A.gen₀
    have e1 : spMap A'.fn ≫ A'.ξ₀ = A'.ξ ≫ A'.f := A'.fn_over.symm
    have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
    have e3 : A'.ξ ≫ h = spMap i ≫ A.ξ := hd
    have e4 : spMap (A'.fn.comp ψ.toRingHom) = spMap (i.comp A.fn) := by
      refine (cancel_mono A.ξ₀).1 ?_
      rw [spMap_comp, spMap_comp, Category.assoc, Category.assoc, hψ, e1, e2, hf, ← Category.assoc, e3,
        Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  letI mod' : Module A'.Ω₀ Fl.Li₀ := Module.compHom _ ψ.symm.toRingHom
  have hs : ∀ (a : A.Ω₀) (e : Fl.Li₀), ψ a • e = a • e := fun a e => by
    show ψ.symm (ψ a) • e = a • e
    rw [ψ.symm_apply_apply]
  have hρ : ∀ (a : 𝓞 E) (w : A.Li), j (A.ρ a w) = A'.ρ a (j w) := by
    intro a w
    apply A'.M.inj
    apply hom_ext_of_pullback m.cart.1
    have a1 : A.M.pt (A.ρ a w) = A.M.pt w ≫ A.t.act.act a := A.act a w
    have a2 : A'.M.pt (A'.ρ a (j w)) = A'.M.pt (j w) ≫ A'.t.act.act a := A'.act a (j w)
    calc (A'.M.pt (j (A.ρ a w))).left ≫ m.cm.F = spMap (dualMap i) ≫ (A.M.pt (A.ρ a w)).left := hpt _
      _ = spMap (dualMap i) ≫ (A.M.pt w).left ≫ (A.t.act.act a).left := by rw [a1]; rfl
      _ = ((A'.M.pt (j w)).left ≫ m.cm.F) ≫ (A.t.act.act a).left := by
          rw [show (A'.M.pt (j w)).left ≫ m.cm.F = _ from hpt w, Category.assoc]
      _ = (A'.M.pt (j w)).left ≫ (A'.t.act.act a).left ≫ m.cm.F := by rw [m.act, Category.assoc]
      _ = (A'.M.pt (A'.ρ a (j w))).left ≫ m.cm.F := by rw [a2, Over.comp_left, Category.assoc]
  have hb₀ : ∀ s, LinearIndependent Ω (Fl.b s) := by
    letI := A.fn.toAlgebra
    obtain ⟨_, _, _, _, _, hb, _⟩ := Fl.generic
    exact hb
  have hemb : ∀ s, A'.emb s = i.comp (A.emb s) := fun s => by
    simp only [HodgeCpt.emb]
    rw [hcst]
    rfl
  have hVgen : ∀ s w, j w ∈ A'.Vgen s ↔ w ∈ A.Vgen s := fun s w => by
    show j w ∈ eigSp A'.ρ (A'.emb s) ↔ w ∈ eigSp A.ρ (A.emb s)
    rw [hemb]
    exact mem_eigSp_iff hj _ _ _ hρ w
  let V₀' : CMType H ⊕ CMType H → Submodule A'.Ω₀ Fl.Li₀ := fun s =>
    { carrier := (Fl.V₀ s : Set Fl.Li₀)
      add_mem' := fun ha hb => (Fl.V₀ s).add_mem ha hb
      zero_mem' := (Fl.V₀ s).zero_mem
      smul_mem' := fun c x hx => (Fl.V₀ s).smul_mem (ψ.symm c) hx }
  have hsq : spMap (dualMap i) ≫ spMap (dualMap A.fn) = spMap (dualMap A'.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    rw [← spMap_comp, ← spMap_comp, ← dualMap_comp, ← dualMap_comp, hfn]
  let Fl' : A'.Flag :=
    { b := fun s k => j (Fl.b s k)
      sub := fun s => by
        rw [hV s]
        exact pull_isFlagVB hd hj (Fl.sub s)
      Li₀ := Fl.Li₀
      acg := Fl.acg
      mod := mod'
      M₀ := transport ψ hψ hs Fl.M₀
      j := j.comp Fl.j
      j_pt := fun e => by
        show (A'.M.pt (j (Fl.j e))).left ≫ A'.m.φ =
          spMap (dualMap A'.fn) ≫ spMap (dualMap ψ.toRingHom) ≫ (Fl.M₀.pt e).left
        rw [hφ, ← Category.assoc, hpt, Category.assoc, Fl.j_pt, ← Category.assoc, hsq, Category.assoc]
      V₀ := V₀'
      V₀_mem := fun s e => (Fl.V₀_mem s e).trans (hVgen s _).symm
      deg := Module.finrank i.fieldRange Ω' * Fl.deg
      generic := genericFlag_pull A.fn A'.fn ψ i hfn hs Fl.j j hj Fl.V₀ V₀' (fun _ _ => Iff.rfl) Fl.b Fl.deg
        Fl.generic }
  refine ⟨Fl', fun _ _ => rfl, rfl, ⟨ψ, AddEquiv.refl _, hfn, hψ, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro xdeg e hR r
  refine isDegOn_pull hd A'.tie.gen A.tie.cover hv hy (fun p' hp => ?_) _ (hR r)
  have := gr_gen_pull hd hj (hb₀ _) (Fl.sub (HodgeCpt.rootIdx D r).1) p' hp (HodgeCpt.rootIdx D r).2
  rw [← hV] at this
  exact this

end GlobalTheory.CompanionTheory.Ar.FlagPull
