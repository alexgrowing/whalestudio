import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.SpanPairIff
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.SigSplitOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.ExistsAbsGt

noncomputable section

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG PositivityTheory.ThKEnd.Grp PositivityTheory.ThKG.Tow.Levi
open GlobalTheory.Doubling (absE)
open GlobalTheory.Eis.Conv (halfE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem split_move {a a' d₁ : ℕ} {W : Spc F E (a + a')} {W₁ : Spc F E d₁} {H : Plane E (a + a') d₁} {X : Chars F E}
    {f fa fb g : UA σ W.J → ℂ} (h : Split2 W₁ H X f fa fb) (c : ℂ) (y : UA σ W.J) (e : ∀ x, c * f (x * y) = g x) :
    Split2 W₁ H X g (fun x => c * fa (x * y)) fun x => c * fb (x * y) :=
  funext e ▸ split2_smul (f := fun x => f (x * y)) ⟨isCT_right h.1 y, hasLaw_right h.2.1 y, hasLaw_right h.2.2 y⟩ c

theorem twoStep_of' (hM : SigMod) (hS : SigSplit) (hI : Iwa) (hA : IAut) : TwoStep := by
  intro F E _ _ _ _ _ σ B b a' G G₁ X om om' om₁ om₁' H H' t t₁ hC hq f hf fa hs hlow k hk f₁ hf₁ hL
  have cm := t.base.cm
  have hJ := t.geo.hW.skew
  have hJ₁ := t₁.geo.hW.skew
  have hd := det_ne_zero t.geo.hW
  obtain ⟨pl, iw⟩ := hI F E σ B _ _ _ _ H' _ _ _ _ t.base t.geo.hW hC.hH'
  obtain ⟨d₂, W₂, H₁, pl₁, sp⟩ := hS F E σ B b a' G₁ X om₁ om₁' t₁ (by have := hC.eq; omega)
  have aut := sig_isAut hA t hf
  have h0 : IsCT H' f fa := by simpa using hs.1
  obtain ⟨lev, -, -, -, v1, -⟩ := levi_data cm hJ pl
  have com : ∀ {s m} y, IsLevi (W₁ := G₁.W) H' s 1 m → lev y * m = m * lev y := fun y hm =>
    levi_uniq cm hJ pl (by simpa using levi_mul (v1 y) hm) (by simpa using levi_mul hm (v1 y))
  have low : ∀ {k f₁}, IsLow H' fa k f₁ → ∀ y z, fa (lev z * (lev y * k)) = f₁ (z * y) := fun h y z => by
    rw [h _ _ (v1 _), map_mul, mul_assoc]
  have ex : ∀ x, ∃ A C, Split2 W₂ H₁ X (fun y => fa (lev y * x)) A C := fun x => by
    obtain ⟨u, hu, s, m, y, l, κ, hκ, hm, hl, rfl⟩ := iw x
    obtain rfl := levi_uniq cm hJ pl hl (v1 y)
    obtain ⟨g, hg, hg'⟩ := hlow κ hκ
    obtain ⟨A, C, h⟩ := sp g hg
    refine ⟨_, _, split_move h ((X.α s : ℂ) * (((absE F E s : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) y fun z => ?_⟩
    rw [← low hg', ← hs.2.1 s m hm, ← mul_assoc m, ← com z hm, ← ct_inv (unipGood cm (Or.inr hJ) hd pl) aut h0
      ((leviPlane F E σ cm _ _ _ _ H' hJ pl).2 _ _ _ (v1 z) u hu)]
    congr 1
    group
  choose A C hAC using ex
  obtain ⟨μ, 𝓕, m1, m2, m3⟩ := (unipGood cm (Or.inr hJ₁) pl.nondeg pl₁).ex
  have val : ∀ {x A' C'}, Split2 W₂ H₁ X (fun y => fa (lev y * x)) A' C' → A x 1 + C x 1 = A' 1 + C' 1 := fun {x _ _} h =>
    ((hAC x).1 μ 𝓕 m1 m2 m3 1).trans (h.1 μ 𝓕 m1 m2 m3 1).symm
  obtain ⟨u, hu⟩ : ∃ u, u = (halfE F E)⁻¹ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := (leviPlane F E σ cm _ _ _ W₂ H₁ hJ₁ pl₁).1 u⁻¹ 1
  obtain ⟨m₀, hm₀⟩ := (leviPlane F E σ cm _ _ _ G₁.W H' hJ pl).1 u 1
  have ea : m₀ * lev m = emb2 cm hJ pl pl₁ (dia u) :=
    levi_uniq cm hJ pl (by simpa using levi_mul hm₀ (v1 m)) (emb2_dia_isLevi cm hJ pl pl₁ hJ₁ u hm)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = absE F E u := ⟨_, rfl⟩
  have r1 : 1 < r := by
    rw [hr, hu, map_inv, GlobalTheory.Eis.Conv.absE_halfE F E σ cm, inv_inv]
    exact_mod_cast one_lt_pow₀ (by norm_num) Fintype.card_ne_zero
  have r0 : 0 < r := one_pos.trans r1
  obtain ⟨l, hl⟩ : ∃ l : ℂ, l = (X.α u : ℂ) * ((r ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((X.β u⁻¹ : ℂ) * ((r⁻¹ ^ ((b : ℝ) / 2) : ℝ) : ℂ)) :=
    ⟨_, rfl⟩
  have l1 : ‖l‖ < 1 := by
    have : (a' : ℝ) < b := by exact_mod_cast t₁.geo.lt
    rw [hl]
    simp only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), Real.inv_rpow r0.le, mul_inv_lt_iff₀ (by positivity),
      one_mul]
    exact Real.rpow_lt_rpow_of_exponent_lt r1 (by linarith)
  have step : ∀ {x A' C'}, Split2 W₂ H₁ X (fun y => fa (lev y * x)) A' C' → ∃ A'' C'',
      Split2 W₂ H₁ X (fun y => fa (lev y * (m₀ * lev m * x))) A'' C'' ∧ A'' 1 = A' 1 ∧ C'' 1 = l * C' 1 := fun {x A' C'} h => by
    refine ⟨_, _, split_move h ((X.α u : ℂ) * (((absE F E u : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) m fun z => ?_, ?_, ?_⟩
    · rw [← hs.2.1 u m₀ hm₀, map_mul, ← mul_assoc, ← mul_assoc, ← com z hm₀]
      simp only [mul_assoc]
    · have := h.2.1 _ m hm 1
      rw [mul_one] at this
      rw [one_mul, this, map_inv, map_inv, NNReal.coe_inv, ← hr, Real.inv_rpow r0.le, Circle.coe_inv, Complex.ofReal_inv]
      have a1 : (X.α u : ℂ) ≠ 0 := Circle.coe_ne_zero _
      have a2 : ((r ^ ((a' : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
      field_simp
    · have := h.2.2 _ m hm 1
      rw [mul_one] at this
      rw [one_mul, this, hl, map_inv (absE F E), NNReal.coe_inv, ← hr]
      ring
  have key := two_kill cm hJ pl pl₁ hd hJ₁ (c := fun x => A x 1 + C x 1) aut (hM F E σ B _ _ G X om om' t f hf) h0
    (fun lev' hv ν 𝓖 n1 n2 n3 x => by
      obtain rfl : lev' = lev := funext fun y => levi_uniq cm hJ pl (hv y) (v1 y)
      simpa using (hAC x).1 ν 𝓖 n1 n2 n3 1) l1 (hu ▸ ea) fun x => by
      obtain ⟨A₁, C₁, s1, e1, e2⟩ := step (hAC x)
      obtain ⟨A₂, C₂, s2, e3, e4⟩ := step s1
      rw [val s2, val s1, e3, e4, e1, e2]
      ring
  obtain ⟨A', C', h⟩ := sp f₁ hf₁
  have z : C' = 0 := funext fun y => by
    have s0 : Split2 W₂ H₁ X (fun z => fa (lev z * (lev y * k))) _ _ :=
      split_move h 1 y fun z => (one_mul _).trans (low hL y z).symm
    obtain ⟨A₁, C₁, s1, e1, e2⟩ := step s0
    have := key (lev y * k)
    simp only [val s1, val s0, e1, e2, one_mul, add_right_inj] at this
    have l2 : l - 1 ≠ 0 := sub_ne_zero.2 fun e => by simp [e] at l1
    exact (mul_eq_zero.1 (by linear_combination this : (l - 1) * C' y = 0)).resolve_left l2
  exact ⟨d₂, W₂, H₁, A', pl₁, by simpa [z] using h.1, h.2.1⟩

theorem twoStep_of (hW : WeilConv) (hD : KDecay) (hS : SplitEx) (hP : Tow.PlaneSkew) (hI : Iwa) (hA : IAut) (hR : SigRe) : TwoStep :=
  twoStep_of' (sigMod_of hW hD) (sigSplit_of hS hP hI ctBasic hA hR) hI hA

end PositivityTheory.ThKEnd.Two

end
