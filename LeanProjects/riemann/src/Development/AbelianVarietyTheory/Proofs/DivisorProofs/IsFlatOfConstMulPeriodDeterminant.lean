import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedChartSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigFrameMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerValMulWedgeCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVecEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsComponentSamePeriodSpaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOne

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.FlatMul

theorem eq_zero_of_real_smul_mem {g : ℕ} (S : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology S] {z : Fin g → ℂ}
    (h : ∀ t : ℝ, t • z ∈ S) : z = 0 := by
  by_contra h0
  have hc : Countable S := countable_of_Lindelof_of_discrete
  have : Countable ℝ := Function.Injective.countable (f := fun t : ℝ => (⟨t • z, h t⟩ : S))
    fun s t e => smul_left_injective ℝ h0 (congrArg Subtype.val e)
  exact not_countable this

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {z w : Fin g → ℂ}
    (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  have := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at this
  exact (u.ker _).1 (right_eq_mul.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

def Marked {s : Sp ℂ ⟶ Sp (KA l)} (o : Obj D l (baseKA l) s) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) (Di : Datum H)
    (t : D.La →ₗ[𝓞 E] Di.La) (P : Di.La →+ (Fin g → ℂ)) : Prop :=
  Function.Injective P ∧ (∀ z, z ∈ u.Λ ↔ z ∈ P.range) ∧
    (∀ a : 𝓞 E, ∃ T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ z, u.ex (T z) = u.ex z ≫ o.t.act.act a) ∧
      ∀ v, P (a • v) = T (P v)) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), u.ex ((l.M : ℝ)⁻¹ • P (t a)) = o.eta a

theorem exists_lev {s s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'} {Hm : Matrix (Fin g) (Fin g) ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (hφ : IsTransport o o' u u' Hm Hm' φ)
    {Di : Datum H} {t : D.La →ₗ[𝓞 E] Di.La} (ht : ∀ b, ∃ a e, b = t a + l.M' • e)
    {P : Di.La →+ (Fin g → ℂ)} {P' : Di.La →+ (Fin g' → ℂ)} (hP : Marked o u Di t P) (hP' : Marked o' u' Di t P') :
    ∃ gm : Di.La ≃ₗ[𝓞 E] Di.La, IsLev l Di gm ∧ ∀ a, φ (P a) = P' (gm a) := by
  obtain ⟨i1, r1, a1, e1⟩ := hP
  obtain ⟨i2, r2, a2, e2⟩ := hP'
  obtain ⟨hΛ, hact, -, heta, -⟩ := hφ
  choose f hf using fun a => (r2 _).1 ((hΛ (P a)).2 ((r1 _).2 ⟨a, rfl⟩))
  have hsm : ∀ (a : 𝓞 E) v, f (a • v) = a • f v := fun a v => by
    obtain ⟨T, hT, hTP⟩ := a1 a
    obtain ⟨T', hT', hTP'⟩ := a2 a
    have := u'.discrete
    refine i2 ?_
    rw [hf, hTP, hTP', hf, ← sub_eq_zero]
    refine eq_zero_of_real_smul_mem u'.Λ fun r => ?_
    rw [smul_sub, ← map_smul φ, ← map_smul T, ← map_smul T', ← map_smul φ]
    exact sub_mem_of_ex_eq u' ((hact a _ _ (hT _)).trans (hT' _).symm)
  let F : Di.La →ₗ[𝓞 E] Di.La := ⟨⟨f, fun a b => i2 (by rw [map_add, hf, hf, hf, map_add, map_add])⟩, hsm⟩
  have hb : Function.Bijective F := by
    refine ⟨fun a b h => i1 (φ.injective ?_), fun b => ?_⟩
    · rw [← hf, ← hf]; exact congrArg P' h
    · obtain ⟨a, ha⟩ := (r1 _).1 ((hΛ (φ.symm (P' b))).1 (by rw [φ.apply_symm_apply]; exact (r2 _).2 ⟨b, rfl⟩))
      exact ⟨a, i2 ((hf a).trans (by rw [ha, φ.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective F hb, fun a ha => ?_, fun a => (hf a).symm⟩
  have hM : (l.M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  show ∃ e, F a = a + l.M • e
  refine Submodule.smul_induction_on ha (fun r hr b _ => ?_) ?_
  · obtain ⟨a₀, e₀, rfl⟩ := ht b
    have hm := Submodule.smul_mem_smul hr (Submodule.mem_top (R := 𝓞 E) (x := a₀))
    obtain ⟨e, he⟩ := (r2 _).1 (sub_mem_of_ex_eq u' ((heta _ _ (e1 _ hm)).trans (e2 _ hm).symm))
    have h1 : F (t (r • a₀)) = t (r • a₀) + l.M • e := i2 (by
      rw [map_add, map_nsmul, he, map_smul φ, ← hf, ← smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_inv_smul₀ hM,
        add_sub_cancel]
      rfl)
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    refine ⟨e + k • (F (r • e₀) - r • e₀), ?_⟩
    rw [smul_add, ← map_smul t, smul_comm r l.M', map_add, h1, map_nsmul, hk, mul_smul, mul_smul, smul_add, smul_sub,
      smul_sub]
    abel
  · rintro a b ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem marked_of_cmp {σ' : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ' ty) (i : Fin Fu.n)
    {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) {y₀ : Sp ℂ ⟶ Xo.X} (hy : y₀ = Fu.u i P)
    {s : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} (m : ObjMap o Xo.univ y₀) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (h1 : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) (h2 : ∀ z, h z ∈ u.Λ ↔ z ∈ P.range) :
    Marked o u (Fu.Di i) (Fu.t i) (h.toLinearMap.toAddMonoidHom.comp P) := by
  subst hy
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x.left ≫ m.toSABMap.φ = y.left ≫ m.toSABMap.φ → x = y := fun x y h =>
    Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))
  refine ⟨h.injective.comp hP.2.1, fun z => ?_, fun a => ?_, fun a ha => inj _ _ ?_⟩
  · obtain ⟨z, rfl⟩ := h.surjective z
    rw [h2]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, congrArg h ha⟩, fun ⟨a, ha⟩ => ⟨a, h.injective ha⟩⟩
  · refine ⟨(h.toLinearMap ∘ₗ LinearMap.mulLeft ℂ (fun k => ty k (a : E)) ∘ₗ h.symm.toLinearMap).restrictScalars ℝ,
      fun z => inj _ _ ?_, fun v => ?_⟩
    · obtain ⟨z, rfl⟩ := h.surjective z
      show (u.ex (h ((fun k => ty k (a : E)) * h.symm (h z)))).left ≫ _ = _
      rw [h.symm_apply_apply, h1, Over.comp_left, Category.assoc, m.act, ← Category.assoc, h1]
      exact congrArg (fun z => z.left) (Fu.ex_lin i P hP a z)
    · show h (P (a • v)) = h ((fun k => ty k (a : E)) * h.symm (h (P v)))
      rw [h.symm_apply_apply]
      exact congrArg h (funext (hP.1 a v))
  · have e : (l.M : ℝ)⁻¹ • (h.toLinearMap.toAddMonoidHom.comp P) (Fu.t i a) = h ((l.M : ℂ)⁻¹ • P (Fu.t i a)) := by
      rw [map_smul, ← Complex.coe_smul]
      push_cast
      rfl
    rw [e, h1, ← Fu.ex_eta i P hP a ha, m.eta]
    rfl

theorem vec_eq {e : c.F →+* ℂ} {g₀ : ℕ} {en : Fin g₀ ≃ Pad.Letter D} (Fu : Fam Xo c e en) (i : Fin Fu.n)
    {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c e (en j).1) P)
    {y : Sp ℂ ⟶ Xo.XF c} (hy : y ≫ toX Xo c = Fu.u i P)
    {s : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} (m : ObjMap o Xo.univ (y ≫ toX Xo c)) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (h4 : ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ o.t.G), IsTangent v → (u.IsDiff (h w) v ↔
      IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v.left ≫ m.toSABMap.φ)))
    {v₀ : Sp (DualNumber ℂ) ⟶ Y.oF.t.G.left} {v₁ : epsAt y ⟶ Y.oF.t.G} {v' : epsR ℂ ⟶ o.t.G} {w : Fin g₀ → ℂ}
    {V : Fin g → ℂ} (k1 : v₀ ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (k2 : v₁.left ≫ Y.m.φ = v₀ ≫ Y.m.φ)
    (k3 : IsDerivAt0 (fun w => (Fu.ex i P w).left) w (v₀ ≫ Y.m0.toSABMap.φ))
    (k4 : v'.left ≫ m.toSABMap.φ = v₁.left ≫ Y.m0.toSABMap.φ) (k5 : u.IsDiff V v') : V = h w := by
  obtain rfl : v₀ = v₁.left := Y.m.cart.1.hom_ext k2.symm (k1.trans (Over.w v₁).symm)
  obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g₀ _ Fu i P hP
  have ht := t1 _ _ k3
  have hv : IsTangent v' := by
    have := (OpenReg.tan_iff m.toSABMap (x := 𝟙 _) ((Category.id_comp _).trans hy) (w := v'.left)
      ((Over.w v').trans (Category.comp_id _).symm)).1 (k4 ▸ ht)
    refine this.2.trans ?_
    rw [Hom.one_def]
    simp
  obtain ⟨V, rfl⟩ := h.surjective V
  have := (h4 V v' hv).1 k5
  rw [k4] at this
  rw [(t3 _ ht).unique this k3]

theorem exists_data {U : Set (Xo.XF c)} {τ : E →+* ℂ} {e : c.F →+* ℂ} {g₀ : ℕ} {en : Fin g₀ ≃ Pad.Letter D}
    (Fu : Fam Xo c e en) {x : ∀ i, Hor.Idx D τ → (Fu.Di i).La}
    {hm : Fin Fu.n → Matrix (Hor.Idx D τ) (Hor.Idx D τ) E} {σb : RuleY Y} {σ : RuleU Xo c} {κ : ℂ}
    (hτ : τ (H.rt : E) = H.rt0) (hx : ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) (hres : Restricts Y U τ σb σ)
    (hval : ∀ (a : CxFr Y e) v w i Q, Per Fu a i Q → FrY Y (compactOf Y U) τ e a.1.1 v w → Match τ a.2 v w →
      σb ℂ a.1.1 v w = κ * perVal c e τ (x i) (hm i) Q)
    {y : Sp ℂ ⟶ Xo.XF c} {v w} (hf : FrU Xo c U τ e y v w)
    {s : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} (m : ObjMap o Xo.univ (y ≫ toX Xo c)) {g : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    {V : Fin D.p → Fin g → ℂ} {W₀ : Fin D.q → Fin g → ℂ} (hV : IsVecs u m.toSABMap.φ v V)
    (hW₀ : IsVecs u m.toSABMap.φ w W₀) :
    ∃ (i : Fin Fu.n) (P₀ : (Fu.Di i).La →+ (Fin g₀ → ℂ)) (P : (Fu.Di i).La →+ (Fin g → ℂ))
      (W : Pad.Letter D → Fin g → ℂ) (Q : (Fu.Di i).La →+ (Pad.Letter D → ℂ)),
      IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c e (en j).1) P₀ ∧ y ≫ toX Xo c = Fu.u i P₀ ∧
      Marked o u (Fu.Di i) (Fu.t i) P ∧ PerData c e (Fu.Di i) Hm P W Q ∧ MatchVec τ W V W₀ ∧
      GoodPer c e τ (x i) (hm i) Q ∧ σ ℂ y v w = κ * perVal c e τ (x i) (hm i) Q := by
  obtain ⟨vb, wb, hfb, sv, sw⟩ := (frame_transfer E H D l Xo c O β Y U τ ℂ e y).1 v w hf
  obtain ⟨f₀⟩ := EigLoc.exists_eigFrame E H D l Xo c O β Y ℂ e (y ≫ Y.jQ) hfb.1
  obtain ⟨f, hmat⟩ := (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ _ ℂ e _ hfb.1 hfb.2.1 f₀).2 vb wb hfb
  let a : CxFr Y e := ⟨⟨y ≫ Y.jQ, hfb.1⟩, f⟩
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ toX Xo c) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hf.1, OpenReg.spMap_comp])
  obtain ⟨W, hW⟩ := exists_dirs (a := a) hP hu.symm rfl
  obtain ⟨b, rfl⟩ := dirs_basis (a := a) hP hu.symm rfl hW
  let Q := b.equivFun.toLinearMap.toAddMonoidHom.comp P
  have hPQ : ∀ v, P v = ∑ z, Q v z • b z := fun v => (b.sum_equivFun (P v)).symm
  have hper : Per Fu a i Q := ⟨P, b, y, hP, hu.symm, rfl, hW, hPQ⟩
  have hgood := goodPer_of_per E H D l Xo c O β Y e g₀ en Fu τ a i Q _ _ hper (hx i)
  obtain ⟨h, h1, h2, h3, h4⟩ := FibreCmp.exists_equiv_of_isAH E H D l Xo _ g₀ _ Fu i P _ s o m g u Hm χ hP hu.symm hAH
  have hmk := marked_of_cmp Fu i hP hu.symm m u h h1 h2
  refine ⟨i, P, _, fun z => h (b z), Q, hP, hu.symm, hmk, ⟨hAH.1, hAH.2.1, ?_, h3,
    b.linearIndependent.map' h.toLinearMap h.ker, fun v => ?_, hgood.1⟩, ⟨fun j k hk => ?_, fun j k hk => ?_⟩, hgood, ?_⟩
  · rw [← u.full]
    exact congrArg _ (Set.ext fun z => (hmk.2.1 z).symm)
  · show h (P v) = _
    rw [hPQ, map_sum]
    simp only [map_smul]
  · obtain ⟨v₀, k1, k2, k3⟩ := hW ⟨τ, k⟩
    obtain ⟨v₁, l1, l2⟩ := sv j
    obtain ⟨v', n1, n2⟩ := hV j
    exact vec_eq Fu i hP hu.symm m u h h4 k1 (l2.trans ((hmat.1 j k hk).trans k2.symm)) k3 (n1.trans l1.symm) n2
  · obtain ⟨v₀, k1, k2, k3⟩ := hW ⟨conjEmb τ, k⟩
    obtain ⟨v₁, l1, l2⟩ := sw j
    obtain ⟨v', n1, n2⟩ := hW₀ j
    exact vec_eq Fu i hP hu.symm m u h h4 k1 (l2.trans ((hmat.2 j k hk).trans k2.symm)) k3 (n1.trans l1.symm) n2
  · exact (hres ℂ e y v w vb wb hf hfb sv sw).symm.trans (hval a vb wb i Q hper hfb hmat)

theorem isFlatAt_of_eq_perVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (e : c.F →+* ℂ) (g : ℕ) (en : Fin g ≃ Pad.Letter D) (Fu : Fam Xo c e en) (x : ∀ i, Hor.Idx D τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Hor.Idx D τ) (Hor.Idx D τ) E) (σb : RuleY Y) (σ : RuleU Xo c) (κ : ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → (∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) → Restricts Y U τ σb σ → (∀ (a : CxFr Y e) v w i Q, Per Fu a i Q → FrY Y (compactOf Y U) τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * perVal c e τ (x i) (hm i) Q) → IsFlatAt Xo c U τ σ e := by
  intro E _ _ _ H D l Xo c O _ β Y U τ e g₀ en Fu x hm σb σ κ B io hU hio hr hs hτ hx hres hval
    y y' v w v' w' hf hf' o o' m m' g g' u u' Hm Hm' χ χ' φ V W₀ V' W₀' z Δ Δ' hAH hAH' hφ a1 a2 a3 a4 hΔ hΔ'
  obtain ⟨i, P₀, P, W, Q, p1, p2, p3, p4, p5, p6, p7⟩ := exists_data Fu hτ hx hres hval hf m hAH a1 a2
  obtain ⟨i', P₀', P', W', Q', q1, q2, q3, q4, q5, q6, q7⟩ := exists_data Fu hτ hx hres hval hf' m' hAH' a3 a4
  obtain rfl : i = i' := GlobalTheory.T.complexPoints_component_same_periodSpace E H D l Xo c O β Y U e g₀ _ Fu i i' P₀ P₀' y y' B io hU hio hr hs hf.1 hf'.1
    hf.2.1 hf'.2.1 p1 q1 p2 q2
  obtain ⟨gm, hlev, hgm⟩ := exists_lev hφ (Fu.t_surj i) p3 q3
  have hiso : IsIsom (Fu.Di i) gm := fun a b => by
    have := hφ.2.2.1 (P a) (P b)
    rw [hgm, hgm, p4.2.2.2.1, q4.2.2.2.1] at this
    exact_mod_cast this
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := q4
  have hpd : PerData c e (Fu.Di i) Hm' (P'.comp gm.toLinearMap.toAddMonoidHom) W'
      (Q'.comp gm.toLinearMap.toAddMonoidHom) :=
    ⟨r1, r2, by rw [← r3]; exact congrArg _ (gm.surjective.range_comp P'), fun a b => (r4 _ _).trans (congrArg _ (hiso a b)),
      r5, fun a => r6 _, fun a b k => (congrArg (Q' · k) (gm.map_smul a b)).trans (r7 a _ k)⟩
  have key := perVal_mul_wedgeCoord E H D l c e τ (Fu.Di i) (x i) (hm i) g g' Hm Hm' P _ W W' Q _ φ V W₀ V' W₀' z Δ Δ'
    hτ (hx i) p4 hpd p6 (HorIso.perVal_isom E H D l c e _ τ _ _ Q' gm (hx i) q6 hiso).1 hgm p5 q5 hΔ hΔ'
  rw [perVal_isLev (hx i) q6 hiso hlev] at key
  rw [p7, q7, _root_.mul_assoc, key, _root_.mul_assoc]

end GlobalTheory.DetLine.FlatMul
