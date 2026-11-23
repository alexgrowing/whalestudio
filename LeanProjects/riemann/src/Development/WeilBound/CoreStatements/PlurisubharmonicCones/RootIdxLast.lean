import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ProdSqrtLead
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFlagTensorStatement

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Det

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] {j : V →+ V'}

theorem map_comb (hj : IsExtOver i j) {r : ℕ} {s c : Fin r → V} {b₀ : Fin r → V'} {T : Matrix (Fin r) (Fin r) Ω}
    {T₁ : Matrix (Fin r) (Fin r) Ω'} (hT : ∀ k, c k = ∑ l, T l k • s l) (hT₁ : ∀ k, j (s k) = ∑ l, T₁ l k • b₀ l) (k : Fin r) :
    j (c k) = ∑ l, (T₁ * i.mapMatrix T) l k • b₀ l := by
  rw [hT k, map_sum]
  simp only [hj.1, hT₁, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem det_pull' {L : Lat ξ V} {r : ℕ} {s : Fin r → V} {U : Submodule Ω V} (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i)
    (hj : IsExtOver i j) (hs : LinearIndependent Ω s) (hsU : ∀ k, s k ∈ U) (hL : L.IsVB r U)
    {b₀ : Fin r → V'} (hb₀ : LinearIndependent Ω' b₀) (hF : (L.pull ξ' f j).IsFlagVBOn Set.univ b₀) :
    ∃ T₁ : Matrix (Fin r) (Fin r) Ω', (∀ k, j (s k) = ∑ l, T₁ l k • b₀ l) ∧ T₁.det ≠ 0 ∧
      ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
        (detLat (L.pull ξ' f j) b₀).IsGenAt q (T₁.det * i t) := by
  let g : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  obtain ⟨hg, hgreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd g
  obtain ⟨U₀, hU₀, b, hb, hfr⟩ := hL ⟨f g.1, hg⟩ trivial
  have hbf := hfr _ trivial hU₀
  have hsU' : Submodule.span Ω (Set.range s) = U := by
    have : FiniteDimensional Ω U := hb ▸ FiniteDimensional.span_of_finite _ (Set.finite_range _)
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hsU k)) ?_
    rw [finrank_span_eq_card hs, ← hb, finrank_span_eq_card hbf.1]
  have hjb : ∀ k, j (b k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨U₁, hU₁, b', hb', hfr'⟩ := hF g trivial
    have e1 : ∀ c : Fin r → V', flagStep Ω' c r = Submodule.span Ω' (Set.range c) := fun c => by
      unfold flagStep
      congr 1
      ext x
      simp
    rw [← e1, ← hb', e1]
    have h1 : j (b k) ∈ (L.pull ξ' f j) g := by
      rw [(FlagPull.pull_isFrameAt hd hj g hg hbf).2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [(hfr' g trivial hU₁).2] at h1
    exact Submodule.span_le_restrictScalars (regAt ξ' g) Ω' _ h1
  have hjs : ∀ k, j (s k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := s) (s := b) fun k => by rw [hb]; exact hsU k
    rw [hT k, map_sum]
    exact Submodule.sum_mem _ fun k' _ => by rw [hj.1]; exact Submodule.smul_mem _ _ (hjb k')
  obtain ⟨T₁, hT₁⟩ := exists_mat hjs
  have main : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
      (detLat (L.pull ξ' f j) b₀).IsGenAt q (T₁.det * i t) := by
    intro q h
    obtain ⟨U₂, hU₂, c, hc, hcf⟩ := hL ⟨f q.1, h⟩ trivial
    have hcf' := hcf _ trivial hU₂
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := c) (s := s) fun k => by
      rw [hsU', ← hc]; exact Submodule.subset_span ⟨k, rfl⟩
    refine ⟨T.det, GlobalTheory.T.det_lattice_frame_gen X Ω ξ V L r s c T _ hs hcf' hT, ?_⟩
    have h2 := GlobalTheory.T.det_lattice_frame_gen X' Ω' ξ' V' (L.pull ξ' f j) r b₀ (fun k => j (c k)) (T₁ * i.mapMatrix T) q hb₀
      (FlagPull.pull_isFrameAt hd hj q h hcf') (map_comb hj hT hT₁)
    rwa [Matrix.det_mul, ← RingHom.map_det] at h2
  obtain ⟨t, -, ht⟩ := main g hg
  exact ⟨T₁, hT₁, left_ne_zero_of_mul ht.1, main⟩

variable {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)]
  {κ : K → K'} {v : (Σ k, J k) → Σ k, J' k} {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}

theorem deg_pull' {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {Λ' : I → Lat ξ' Ω'} {u : I → Ω'} (hu : ∀ τ, u τ ≠ 0)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hg' : IsCptGen ξ')
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p)
    (hΛ : ∀ τ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (Λ τ).IsGenAt ⟨f q.1, h⟩ t ∧ (Λ' τ).IsGenAt q (u τ * i t))
    (hv : IsBlockMap κ v) (hy : ∀ q, y' (v q) = i (y q)) {a : K → ℤ} {e₀ : Ω}
    (h : (Lat.tens Λ fun _ => -1).IsDegOn Set.univ y a e₀) :
    (Lat.tens Λ' fun _ => -1).IsDegOn Set.univ y' (pullDeg κ a) ((∏ τ, u τ)⁻¹ * i e₀) := by
  have hU : ∏ τ, u τ ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hu τ
  refine ⟨mul_ne_zero (inv_ne_zero hU) ((map_ne_zero i).2 h.1), fun q _ c' hc' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
  obtain ⟨d, hdv⟩ := FlagPull.exists_chart hv c'
  obtain ⟨r1, r2⟩ := FlagPull.ratio_reg hv hy hc' hdv
  have hc := FlagPull.inChart_of_pull hd hg' hcov q hq r1 r2
  choose t ht ht' using fun τ => hΛ τ q hq
  have g1 := uMap hreg (gen_unit (deg_gen h hc) (Flag.tens_gen Λ (fun _ => -1) _ t ht))
  have g2 := Flag.tens_gen Λ' (fun _ => -1) q _ ht'
  refine (gen_of_unit (s := (∏ k', y' ⟨k', c' k'⟩ ^ pullDeg κ a k') * ((∏ τ, u τ)⁻¹ * i e₀)) g2 ?_).2
  convert g1 using 1
  rw [FlagPull.monomial_pull hv hy a hdv]
  simp only [_root_.zpow_neg_one, mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib, map_div₀, map_mul, map_inv₀, map_prod i (s := Finset.univ (α := I))]
  field_simp

end Det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

def lastRoot (D : Datum H) (a : CMType H × Fin D.q) : CMType H × Fin (D.p + D.q) := (a.1, Fin.natAdd D.p a.2.rev)

theorem rootIdx_last (a : CMType H × Fin D.q) : HodgeCpt.rootIdx D (lastRoot D a) = ⟨.inr a.1, a.2⟩ := by
  unfold HodgeCpt.rootIdx lastRoot
  rw [dif_neg (by simp)]
  congr 1
  apply Fin.ext
  have := a.2.2
  simp only [Fin.val_natAdd, Fin.val_rev]
  omega

theorem rootSgn_last (a : CMType H × Fin D.q) : HodgeCpt.rootSgn D (lastRoot D a) = -1 := by
  simp [HodgeCpt.rootSgn, lastRoot]

theorem core (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (hB : Birational y) {e : CMType H × Fin (D.p + D.q) → Ω}
    (L : CMType H × Fin (D.p + D.q) → HermLine J) (hR : Fl.RootLines (fun r => (L r).a) e)
    (hH : ∀ r, Fl.IsHodgeLine r (e r) (L r))
    {X₂ : Scheme.{0}} (t₂ : SAB H X₂) {Ω₂ : Type} [Field Ω₂] {ξ₂ : Sp Ω₂ ⟶ X₂} (hξ₂ : IsCptGen ξ₂)
    {K₂ : Type} [Fintype K₂] {J₂ : K₂ → Type} [∀ k, Fintype (J₂ k)] {y₂ : (Σ k, J₂ k) → Ω₂}
    (hcov : ∀ p : Cpt ξ₂, ∃ c, InChart ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) c p)
    {Li₂ : Type} [AddCommGroup Li₂] [Module Ω₂ Li₂] (M₂ : LieModel t₂.G ξ₂ Li₂) (V₂ : CMType H → Lat ξ₂ Li₂)
    {g : 𝔐.X ⟶ X₂} {i : Ω₂ →+* Ω} (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ ξ₂ g i) (m : SABMap 𝔐.t t₂ g) (j : Li₂ →+ 𝔐.Li)
    (hj : IsExtOver i j)
    (hpt : ∀ a, (𝔐.M.pt (j a)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M₂.pt a).left)
    (hV : ∀ τ, 𝔐.V (.inr τ) = (V₂ τ).pull 𝔐.ξ g j) (U : CMType H → Submodule Ω₂ Li₂) (hvb : ∀ τ, (V₂ τ).IsVB D.q (U τ))
    {n : ℕ} (hn : n = D.q) (s : CMType H → Fin n → Li₂) (hs : ∀ τ, LinearIndependent Ω₂ (s τ)) (hsU : ∀ τ k, s τ k ∈ U τ)
    (A₂ : HermLine J₂) (e₀ : Ω₂)
    (hdeg : (Lat.tens (fun τ => detLat (V₂ τ) (s τ)) fun _ => -1).IsDegOn Set.univ y₂ A₂.a e₀)
    {κ : K₂ → K} {v : (Σ k, J₂ k) → Σ k, J k} (hv : IsBlockMap κ v) (hy : ∀ q, y (v q) = i (y₂ q))
    (hmet : ∀ (z : Sp ℂ ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      ∃ (h : genPt ξ₂ ⤳ centre (z ≫ g)) (b : CMType H → Fin n → Li₂) (T : CMType H → Matrix (Fin n) (Fin n) Ω₂)
        (Γ : CMType H → Matrix (Fin n) (Fin n) ℂ),
        (∀ τ, (V₂ τ).IsFrameAt (b τ) ⟨centre (z ≫ g), h⟩ ∧ (∀ k, b τ k = ∑ k', T τ k' k • s τ k') ∧
          M₂.GramAt t₂.PP.L (z ≫ g) (b τ) (Γ τ) ∧ (Γ τ).PosDef) ∧
        SecNorm ξ₂ y₂ A₂ e₀ (z ≫ g) (fun p => w (v p)) (∏ τ, (T τ).det)⁻¹ (∏ τ, Real.sqrt (Γ τ).det.re)⁻¹)
    (A A' : HermLine J) (ha : A.a = ∑ a, (L (lastRoot D a)).a) (hh : ∀ w, A.h w = ∏ a, (L (lastRoot D a)).h w)
    (hA' : IsPullHerm κ v A₂ A') :
    IsoLineOn (mCoordIdeal y) {w | ∃ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z} A A' := by
  classical
  subst hn
  have hb₀ : ∀ σ, LinearIndependent Ω (Fl.b σ) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  choose T₁ hT₁ hu hmain using fun τ => det_pull' (L := V₂ τ) hd hj (hs τ) (hsU τ) (hvb τ) (hb₀ (.inr τ))
    (by rw [← hV]; exact Fl.sub _)
  have D2 := deg_pull' hu hd 𝔐.tie.gen hcov hmain hv hy hdeg
  simp only [← hV] at D2
  rw [← hA'.1] at D2
  have hU : ∏ τ, (T₁ τ).det ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hu τ
  have he₁ : ∏ a, e (lastRoot D a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => (hR _).1
  have D1 : (Lat.tens (fun τ => detLat (𝔐.V (.inr τ)) (Fl.b (.inr τ))) fun _ => -1).IsDegOn Set.univ y A.a
      (∏ a, e (lastRoot D a)) := by
    refine ⟨he₁, fun q _ ch hch => ?_⟩
    have g1 : ∀ τ k, ((𝔐.V (.inr τ)).gr (Fl.b (.inr τ)) k).IsGenAt q
        (((∏ b, y ⟨b, ch b⟩ ^ (L (lastRoot D (τ, k))).a b) * e (lastRoot D (τ, k))) ^ (-1 : ℤ)) := fun τ k => by
      have h := deg_gen (hR (lastRoot D (τ, k))) hch
      unfold HodgeCpt.Flag.rootLat at h
      rw [rootIdx_last, rootSgn_last] at h
      exact gen_untens (by norm_num) h
    have g2 := Flag.tens_gen (fun τ => detLat (𝔐.V (.inr τ)) (Fl.b (.inr τ))) (fun _ => -1) q _ fun τ => by
      rw [GlobalTheory.T.det_lattice_flag_tensor _ _ _ _ _ _ _ (hb₀ _) (Fl.sub _)]
      exact Flag.tens_gen _ _ q _ (g1 τ)
    rw [g2.2, ha, mono_sum _ (chart_ne hch), smul_eq_mul, ← Finset.prod_mul_distrib, Fintype.prod_prod_type]
    simp only [_root_.zpow_neg_one, zpow_one, Finset.prod_inv_distrib, inv_inv]
    rfl
  set ρ : Ω := (∏ τ, (T₁ τ).det)⁻¹ * i e₀ / ∏ a, e (lastRoot D a) with hρ
  have hρe : ρ * ∏ a, e (lastRoot D a) = (∏ τ, (T₁ τ).det)⁻¹ * i e₀ := div_mul_cancel₀ _ he₁
  have hne : ∀ k, ∃ a, y ⟨k, a⟩ ≠ 0 := by
    obtain ⟨ch, hc⟩ := 𝔐.tie.cover ⟨genPt 𝔐.ξ, specializes_rfl⟩
    exact fun k => ⟨ch k, chart_ne hc k⟩
  obtain ⟨f₁, f₂, hfg, hval⟩ := GlobalTheory.T.degree_lattice_quotient_forms _ Ω 𝔐.ξ K J y Ω _ A.a A'.a _ ρ 𝔐.tie hB hne D1
    (by rw [smul_eq_mul, hρe]; exact D2)
  refine ⟨f₁, f₂, hfg, ?_⟩
  rintro w ⟨z, hzw, hzI⟩ u₁ u₂ huv hu₁
  have hq : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  obtain ⟨hp, b, T, Γ, hb, hsec⟩ := hmet z w hzw hzI
  obtain ⟨φ, hφ, hup⟩ := gram_up m hξ₂ 𝔐.tie.gen hd M₂ 𝔐.M j hpt z hq hp
  have hfl : ∀ τ, ∃ cc : Fin D.q → 𝔐.Li, (∀ k, flagStep Ω cc k = flagStep Ω (Fl.b (.inr τ)) k) ∧
      (𝔐.V (.inr τ)).IsFrameAt cc ⟨centre z, hq⟩ := fun τ => by
    obtain ⟨U₁, hU₁, cc, h1, h2⟩ := Fl.sub (.inr τ) ⟨centre z, hq⟩ trivial
    exact ⟨cc, h1, h2 _ trivial hU₁⟩
  choose cc hcf hcv using hfl
  have hjb : ∀ τ, (𝔐.V (.inr τ)).IsFrameAt (fun k => j (b τ k)) ⟨centre z, hq⟩ := fun τ => by
    rw [hV]
    exact FlagPull.pull_isFrameAt hd hj ⟨centre z, hq⟩ hp (hb τ).1
  choose P hP hPu using fun τ => frame_mat (regAt 𝔐.ξ ⟨centre z, hq⟩) (hcv τ).1 ((hjb τ).2.symm.trans (hcv τ).2)
  have hCd : ∀ τ, ((P τ).map φ).det ≠ 0 := fun τ => by
    have := ((hPu τ).map φ).ne_zero
    rwa [RingHom.map_det] at this
  have hpd : ∀ τ, (((P τ).map φ)ᴴ * Γ τ * (P τ).map φ).PosDef := fun τ =>
    (hb τ).2.2.2.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hCd τ))))
  choose tt htt using fun τ (k : Fin D.q) => GrNorm.exists_sub_mem_flagStep (b := Fl.b (.inr τ)) k (x := cc τ k) (by
    rw [← hcf]
    exact Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩)
  let ν : CMType H × Fin D.q → ℝ := fun a => Real.sqrt (leadMinor (((P a.1).map φ)ᴴ * Γ a.1 * (P a.1).map φ) (a.2 + 1) /
    leadMinor (((P a.1).map φ)ᴴ * Γ a.1 * (P a.1).map φ) a.2)
  have s0 : ∀ a : CMType H × Fin D.q, SecNorm 𝔐.ξ y (L (lastRoot D a)) (e (lastRoot D a)) z w (tt a.1 a.2)⁻¹ (ν a)⁻¹ := by
    intro a
    have h := hH (lastRoot D a) z w hzw hzI (tt a.1 a.2) (ν a)
    rw [rootIdx_last, rootSgn_last, _root_.zpow_neg_one, _root_.zpow_neg_one] at h
    exact h ⟨hq, cc a.1, _, hcf a.1, hcv a.1, htt a.1 a.2, hup _ _ _ _ _ (hb a.1).2.2.1 (hP a.1), hpd a.1, rfl⟩
  have s1 := secNorm_prod hq hzw s0 ha (hh w)
  have hcval : ValAt 𝔐.ξ z (∏ τ, ((P τ).det : Ω)) (∏ τ, ((P τ).map φ).det) := valAt_prod hq _ fun τ => by
    have := hφ (P τ).det
    rwa [RingHom.map_det] at this
  have s2 := RootIso.secNorm_scale (HodgePull.secNorm_pull hd hv hy hA' hq hzw hsec hcval
    (Finset.prod_ne_zero_iff.2 fun τ _ => hCd τ) (-1)) (inv_ne_zero hU)
  have et : ∀ τ, ∏ k, tt τ k = (T₁ τ).det * i (T τ).det * ((P τ).det : Ω) := fun τ => by
    have hm := map_comb hj (hb τ).2.1 (hT₁ τ)
    refine (det_tri (r := D.q) (hb₀ (.inr τ)) (htt τ)
      (T₁ τ * i.mapMatrix (T τ) * (regAt 𝔐.ξ ⟨centre z, hq⟩).subtype.mapMatrix (P τ)) fun k => ?_).symm.trans ?_
    swap
    · rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det]
      rfl
    · rw [hP τ k]
      simp only [hm, Finset.smul_sum, smul_smul, Matrix.mul_apply (N := (regAt 𝔐.ξ ⟨centre z, hq⟩).subtype.mapMatrix (P τ)),
        Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
      rw [mul_comm]
      rfl
  have eν : ∀ τ, ∏ k, ν (τ, k) = ‖((P τ).map φ).det‖ * Real.sqrt (Γ τ).det.re := fun τ =>
    (prod_sqrt_lead (hpd τ)).trans (sqrt_det_conj _ _)
  have e1 : ∏ a : CMType H × Fin D.q, (tt a.1 a.2)⁻¹ =
      (∏ τ, (T₁ τ).det)⁻¹ * ((∏ τ, ((P τ).det : Ω)) ^ (-1 : ℤ) * i (∏ τ, (T τ).det)⁻¹) := by
    rw [Finset.prod_inv_distrib, Fintype.prod_prod_type]
    simp only [et, Finset.prod_mul_distrib, map_inv₀, map_prod, _root_.zpow_neg_one, mul_inv]
    ring
  have e2 : ∏ a, (ν a)⁻¹ = ‖∏ τ, ((P τ).map φ).det‖ ^ (-1 : ℤ) * (∏ τ, Real.sqrt (Γ τ).det.re)⁻¹ := by
    rw [Finset.prod_inv_distrib, Fintype.prod_prod_type]
    simp only [eν, Finset.prod_mul_distrib, norm_prod, _root_.zpow_neg_one, mul_inv]
  rw [← e1, ← e2, ← hρe] at s2
  have hνpos : 0 < ∏ a, (ν a)⁻¹ := Finset.prod_pos fun a _ => inv_pos.2 (Real.sqrt_pos.2
    (div_pos (leadMinor_pos_of_posDef (hpd a.1) a.2.2) (leadMinor_pos_of_posDef (hpd a.1) a.2.2.le)))
  have key := GlobalTheory.T.section_norm_isomorphic_lines _ Ω _ K J y A A' _ ρ _ f₁ f₂ u₁ u₂ _ w _ 𝔐.tie.gen hzw he₁ hfg hval s1 s2 hνpos huv hu₁
  have hA := A.pos w fun k => (hzw.1 k).imp fun _ hc => hc.ne_zero
  have hu' : ‖evC w u₁‖ ≠ 0 := norm_ne_zero_iff.2 hu₁
  show (0 : ℝ) = Real.log (‖evC w u₂‖ / ‖evC w u₁‖ * A'.h w / A.h w)
  have : ‖evC w u₂‖ / ‖evC w u₁‖ * A'.h w / A.h w = 1 := by
    rw [div_mul_eq_mul_div, key]
    field_simp
  rw [this, Real.log_one]

end LevelTowerAlt.Comparison₂
