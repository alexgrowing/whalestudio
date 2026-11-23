import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetLineTrivialOfToroidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVecEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedFibreOfFramedComplexPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducible
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameC

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows GlobalTheory.DetLine.GoodTransport

namespace GlobalTheory.DetLine.PeriodFlat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

section Linear

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem herm_map {La : Type} {g g' : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) {P : La → Fin g → ℂ} (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (he : ∀ a b, (herm Hm' (h (P a)) (h (P b))).im = (herm Hm (P a) (P b)).im) (z w : Fin g → ℂ) :
    herm Hm' (h z) (h w) = herm Hm z w := by
  have : (imHerm Hm').compl₁₂ (h.restrictScalars ℝ) (h.restrictScalars ℝ) = imHerm Hm :=
    LinearMap.ext_on_range hs fun x => LinearMap.ext_on_range hs fun y => he x y
  have k : ∀ z w, (herm Hm' (h z) (h w)).im = (herm Hm z w).im := fun z w =>
    LinearMap.congr_fun (LinearMap.congr_fun this z) w
  refine Complex.ext ?_ (k z w)
  have := k (Complex.I • z) w
  rw [map_smul] at this
  simpa [herm] using this

omit [IsCMField E] in

theorem eq_zero_of_eig {ρ : E →+* ℂ} {v : Fin g → ℂ} (hv : ∀ a : 𝓞 E, tyAct ty a v = ρ a • v) {n : Fin g}
    (hn : ty n ≠ ρ) : v n = 0 := by
  by_contra h0
  exact hn (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    (RingHom.ext fun a => mul_right_cancel₀ h0 (congrFun (hv a) n)))

theorem emb_bar (ρ : E →+* ℂ) (a : 𝓞 E) : ρ (H.bar a : 𝓞 E) = starRingEnd ℂ (ρ a) := by
  rw [H.bar_eq]
  exact IsCMField.complexEmbedding_complexConj E ρ _

theorem herm_eq_zero (hP : IsPeriod D ty P) (hE : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) {ρ : E →+* ℂ}
    {u v : Fin g → ℂ} (hu : ∀ n, ty n = ρ → u n = 0) (hv : ∀ a : 𝓞 E, tyAct ty a v = ρ a • v) :
    herm Hm u v = 0 := by
  refine Finset.sum_eq_zero (s := Finset.univ) (f := fun n => u n * Hm.mulVec (star v) n) fun n _ => ?_
  by_cases hn : ty n = ρ
  · rw [hu n hn, zero_mul]
  refine mul_eq_zero_of_right _ (eq_zero_of_eig (ty := ty) (ρ := ρ) (fun a => funext fun k => ?_) hn)
  have := hermForm_act Hm D ty P hP hE a (Pi.single k 1) v
  rw [hv, hermForm_smul_right, emb_bar, Complex.star_def, Complex.conj_conj] at this
  simpa [hermForm, tyAct, dotProduct, Pi.single_apply] using this

open Classical in

theorem flatCoord_ne_zero (hP : IsPeriod D ty P) (hE : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    {ρ : E →+* ℂ} {p q : ℕ} (hr : p + q = D.p + D.q) {x : Fin q ⊕ Fin p → D.La} (hx : LinearIndependent (𝓞 E) x)
    {V : Fin p → Fin g → ℂ} {W : Fin q → Fin g → ℂ} {C : Fin q ⊕ Fin p → Fin p → ℂ}
    (iV : LinearIndependent ℂ V) (iW : LinearIndependent ℂ W) (hV : ∀ b (a : 𝓞 E), tyAct ty a (V b) = ρ a • V b)
    (hW : ∀ b (a : 𝓞 E), tyAct ty a (W b) = conjEmb ρ a • W b)
    (hC : ∀ k n, (if ty n = ρ then P (x k) n else 0) = ∑ b, C k b * V b n) :
    FramedFlatCoordinates.flatCoord Hm (fun k => P (x k)) W C ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨lam, hlam⟩ : ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ b, lam (V b) = c (.inr b) := by
    obtain ⟨lam, hl⟩ := LinearMap.exists_extend ((Module.Basis.span iV).constr ℂ fun b => c (.inr b))
    refine ⟨lam, fun b => ?_⟩
    have := LinearMap.congr_fun hl (Module.Basis.span iV b)
    rw [Module.Basis.constr_basis] at this
    simpa using this
  let pr : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := LinearMap.pi fun n => if ty n = ρ then LinearMap.proj n else 0
  have hpr : ∀ z n, pr z n = if ty n = ρ then z n else 0 := fun z n => by
    simp only [pr, LinearMap.pi_apply]; split_ifs <;> rfl
  set z₀ := ∑ b, c (.inl b) • W b with hz₀
  have ez : ∀ a : 𝓞 E, tyAct ty a z₀ = conjEmb ρ a • z₀ := fun a => by
    funext n
    have := fun b => congrFun (hW b a) n
    simp only [tyAct, Pi.smul_apply, smul_eq_mul] at this
    simp only [hz₀, tyAct, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum, mul_left_comm _ (c _), this]
  let f : (Fin g → ℂ) →ₗ[ℝ] ℂ :=
    { toFun z := -(Real.pi : ℂ) * hermForm Hm z₀ z + lam (pr z)
      map_add' z w := by rw [hermForm_add_right, map_add, map_add]; ring
      map_smul' r z := by
        rw [← Complex.coe_smul, hermForm_smul_right, map_smul, map_smul]
        simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, RingHom.id_apply, Complex.real_smul]; ring }
  have hf : ∀ z, f z = -(Real.pi : ℂ) * hermForm Hm z₀ z + lam (pr z) := fun _ => rfl
  have fa : ∀ (a : 𝓞 E) y, f (P (a • y)) = ρ a * f (P y) := fun a y => by
    have e1 : P (a • y) = tyAct ty (H.bar (H.bar a)) (P y) := funext fun n => by
      rw [hP.1, tyAct, emb_bar, emb_bar, Complex.conj_conj]
    have e2 : pr (P (a • y)) = ρ a • pr (P y) := funext fun n => by
      rw [Pi.smul_apply, hpr, hpr, hP.1]; split_ifs with h <;> simp [*]
    rw [hf, hf, e2, e1, ← hermForm_act Hm D ty P hP hE, ez, hermForm_smul_left, emb_bar, map_smul]
    simp only [conjEmb, RingHom.comp_apply, Complex.conj_conj, smul_eq_mul]; ring
  have fx : ∀ k, f (P (x k)) = 0 := fun k => by
    have e : pr (P (x k)) = ∑ b, C k b • V b := funext fun n => by rw [hpr, hC]; simp
    have := congrFun hc k
    rw [hf, e, map_sum]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr] at this
    simp only [hz₀, hermForm, sum_dotProduct, smul_dotProduct, map_smul, hlam, smul_eq_mul, Finset.mul_sum]
    refine Eq.trans (congrArg (· + _) (Finset.sum_congr rfl fun b _ => ?_)) this
    rw [hermForm]; ring
  have fz : f = 0 := LinearMap.ext_on_range hP.2.2.2.1 fun y => by
    have := D.fin
    have hn : ¬ LinearIndependent (𝓞 E) (fun o : Option (Fin q ⊕ Fin p) => o.casesOn' y x) := fun h => by
      have := h.fintype_card_le_finrank
      rw [D.rank] at this
      simp at this
      omega
    obtain ⟨t, ht, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hn
    rw [Fintype.sum_option] at ht
    have h1 : t none ≠ 0 := fun h => hi (by
      rw [h, zero_smul, zero_add] at ht
      rcases i with _ | i
      · exact h
      · exact Fintype.linearIndependent_iff.1 hx (fun k => t (some k)) ht i)
    have h2 := congrArg (fun y => f (P y)) ht
    simp only [map_add, map_sum, fa, Option.casesOn'_none, Option.casesOn'_some, fx, mul_zero, Finset.sum_const_zero, add_zero, map_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_left (by simpa using h1)
  have both : ∀ z, hermForm Hm z₀ z = 0 ∧ lam (pr z) = 0 := fun z => by
    have h1 := (hf z).symm.trans (LinearMap.congr_fun fz z)
    have h2 := (hf _).symm.trans (LinearMap.congr_fun fz (Complex.I • z))
    rw [hermForm_smul_right, map_smul, map_smul, Complex.star_def, Complex.conj_I, smul_eq_mul, LinearMap.zero_apply] at h2
    rw [LinearMap.zero_apply] at h1
    have h3 : lam (pr z) = 0 := by linear_combination h1 / 2 - Complex.I * h2 / 2 + (lam (pr z) + Real.pi * hermForm Hm z₀ z) / 2 * Complex.I_sq
    rw [h3, add_zero] at h1
    exact ⟨(mul_eq_zero.1 h1).resolve_left (by simp), h3⟩
  obtain ⟨H₀, -, hpos, hE₀⟩ := hP.2.2.2.2
  have hz : z₀ = 0 := by
    by_contra hne
    have h1 := hpos z₀ hne
    have h2 : hermForm H₀ z₀ z₀ = hermForm Hm z₀ z₀ :=
      herm_map LinearMap.id hP.2.2.2.1 (fun a b => (hE₀ a b).trans (hE a b).symm) z₀ z₀
    rw [h2, (both z₀).1] at h1
    simp at h1
  refine hc0 (funext fun k => ?_)
  rcases k with b | b
  · exact Fintype.linearIndependent_iff.1 iW _ hz b
  · have e : pr (V b) = V b := funext fun n => by
      rw [hpr]; split_ifs with h
      · rfl
      · exact (eq_zero_of_eig (hV b) h).symm
    rw [← hlam, ← e]
    exact (both _).2

end Linear

section Fibre

variable {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)

theorem exists_transport_periods {P P' : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    (hP' : IsPeriod (Fu.Di i) ty P') {y₀ y₀' : Sp ℂ ⟶ Xo.X} (hy : y₀ = Fu.u i P) (hy' : y₀' = Fu.u i P')
    {s s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀)
    (m' : ObjMap o' Xo.univ y₀') {g g' : ℕ} (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (h' : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (hex : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) (hΛ : ∀ z, h z ∈ u.Λ ↔ z ∈ P.range)
    (hE : ∀ a b, (herm Hm (h (P a)) (h (P b))).im = (Fu.Di i).EF a b)
    (hex' : ∀ z, (u'.ex (h' z)).left ≫ m'.toSABMap.φ = (Fu.ex i P' z).left) (hΛ' : ∀ z, h' z ∈ u'.Λ ↔ z ∈ P'.range)
    (hE' : ∀ a b, (herm Hm' (h' (P' a)) (h' (P' b))).im = (Fu.Di i).EF a b) :
    ∃ φ, IsTransport o o' u u' Hm Hm' φ ∧ ∀ a, φ (h (P a)) = h' (P' a) := by
  obtain ⟨a1, a2, a3⟩ := fibre_marks Fu i hP hy m u h hex
  obtain ⟨b1, b2, b3⟩ := fibre_marks Fu i hP' hy' m' u' h' hex'
  obtain ⟨φ₀, hφ₀⟩ := exists_equiv_of_lattices P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ) :=
    ((h.symm.restrictScalars ℝ).trans φ₀).trans (h'.restrictScalars ℝ)
  have hφ : ∀ z, φ (h z) = h' (φ₀ z) := fun z => congrArg (fun t => h' (φ₀ t)) (h.symm_apply_apply z)
  have lat : ∀ z, φ z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by
    obtain ⟨z, rfl⟩ := h.surjective z
    rw [hφ, hΛ, hΛ']
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, φ₀.injective ((hφ₀ a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hφ₀ a).symm⟩
  have exq : ∀ z w, u.ex z = u.ex w → u'.ex (φ z) = u'.ex (φ w) := fun z w hzw => by
    rw [ex_eq_iff] at hzw ⊢
    rw [← map_sub, lat]
    exact hzw
  have lin : ∀ (a : 𝓞 E) z, φ₀ (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * φ₀ z k := fun a z => by
    let T : (Fin g₀ → ℂ) →ₗ[ℝ] (Fin g₀ → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have : φ₀.toLinearMap.comp T = T.comp φ₀.toLinearMap := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
      have e1 : T (P x) = P (a • x) := funext fun k => (hP.1 a x k).symm
      have e2 : T (P' x) = P' (a • x) := funext fun k => (hP'.1 a x k).symm
      change φ₀ (T (P x)) = T (φ₀ (P x))
      rw [e1, hφ₀, hφ₀, e2]
    exact LinearMap.congr_fun this z
  have dv : ∀ (n : ℕ) x, φ₀ ((n : ℂ)⁻¹ • P x) = (n : ℂ)⁻¹ • P' x := fun n x => by
    have e : ∀ v : Fin g₀ → ℂ, (n : ℂ)⁻¹ • v = (n : ℝ)⁻¹ • v := fun v => by
      rw [← Complex.coe_smul]; simp
    rw [e, e, map_smul, hφ₀]
  refine ⟨φ, ⟨lat, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩, fun a => by rw [hφ, hφ₀]⟩
  · obtain ⟨z, rfl⟩ := h.surjective z
    rw [a1] at hw
    rw [exq _ _ hw, hφ, hφ, b1, lin]
  · obtain ⟨z, rfl⟩ := h.surjective z
    obtain ⟨w, rfl⟩ := h.surjective w
    let j := (h.restrictScalars ℝ).toLinearMap
    have : (imHerm Hm').compl₁₂ (φ.toLinearMap.comp j) (φ.toLinearMap.comp j) = (imHerm Hm).compl₁₂ j j := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => LinearMap.ext_on_range hP.2.2.2.1 fun y => ?_
      change (herm Hm' (φ (h (P x))) (φ (h (P y)))).im = (herm Hm (h (P x)) (h (P y))).im
      rw [hφ, hφ, hφ₀, hφ₀, hE, hE']
    exact LinearMap.congr_fun (LinearMap.congr_fun this z) w
  · obtain ⟨a₁, ha₁, e⟩ := exists_eta_eq (l := l) a
    rw [e o, a2 a₁ ha₁] at hz
    rw [exq _ _ hz, e o', b2 a₁ ha₁, hφ, dv]
  · rw [a3] at hz
    rw [exq _ _ hz, b3, hφ, dv]

variable {Fu i} {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)}

theorem dir_unique (hP : IsPeriod (Fu.Di i) ty P) {w w' : Fin g₀ → ℂ} {v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left}
    (h : IsDerivAt0 (fun z => (Fu.ex i P z).left) w v) (h' : IsDerivAt0 (fun z => (Fu.ex i P z).left) w' v) :
    w = w' :=
  ((Fu.ex_diff i P hP).2 (Over.homMk v (derivAt_over Fu i P hP h)) h.1).unique h h'

theorem eig_of_dir (hP : IsPeriod (Fu.Di i) ty P) {w : Fin g₀ → ℂ} {v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left}
    (h : IsDerivAt0 (fun z => (Fu.ex i P z).left) w v) {a : 𝓞 E} {t : ℂ}
    (ha : v ≫ (Xo.univ.t.act.act a).left = spMap (epsScaleR t) ≫ v) : tyAct ty a w = t • w := by
  have h1 := isDerivAt0_comp_hom h (Xo.univ.t.act.act a).left
  have hfun : (fun z => (Fu.ex i P z).left ≫ (Xo.univ.t.act.act a).left) =
      fun z => (Fu.ex i P ((tyD ty a).toLinearMap z)).left := funext fun z => by
    exact congrArg Over.Hom.left (Fu.ex_lin i P hP a z).symm
  rw [hfun, ha] at h1
  exact dir_unique hP ((FibreCmp.isDerivAt0_comp_linear _ (GlobalTheory.EtaAn.isHolTo_ex_of_isPeriod Fu i P hP) _ _ _).1 h1)
    (isDerivAt0_smul h t)

theorem vecs_of_dir (hP : IsPeriod (Fu.Di i) ty P) {y₀ : Sp ℂ ⟶ Xo.X} {s : Sp ℂ ⟶ Sp (KA l)}
    {o : Obj D l (baseKA l) s} (m : ObjMap o Xo.univ y₀) {g n : ℕ} {u : HolUnif o.t.G o.t.PP.L g}
    (h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hex : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left)
    (hd : ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ o.t.G), IsTangent v →
      (u.IsDiff (h w) v ↔ IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v.left ≫ m.toSABMap.φ)))
    {v : Fin n → (epsAt y₀ ⟶ Xo.univ.t.G)} {V : Fin n → Fin g₀ → ℂ} {V' : Fin n → Fin g → ℂ}
    (hV : ∀ b, IsDerivAt0 (fun z => (Fu.ex i P z).left) (V b) (v b).left) (hV' : IsVecs u m.toSABMap.φ v V') :
    V' = fun b => h (V b) := by
  funext b
  obtain ⟨v', e, hv'⟩ := hV' b
  have ht : IsTangent v' := by
    have e0 : (u.ex (h 0)).left = η[o.t.G].left := by
      rw [map_zero, (u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
      simp
    refine m.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, e, ← e0, hex]
      exact (hV b).1
    · rw [Category.assoc, Over.w v', Over.w η[o.t.G]]
      exact (Spec.map_comp _ _).symm.trans (by
        rw [← CommRingCat.ofHom_comp]
        exact (congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun _ => rfl)).trans (Spec.map_id _))
  obtain ⟨w, hw⟩ := h.surjective (V' b)
  rw [← hw] at hv' ⊢
  rw [dir_unique hP (hV b) (e ▸ (hd w v' ht).1 hv')]

end Fibre

section Model

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

theorem frY_framed {R : Type} [CommRing R] {j : c.F →+* R} (a : FramedFlatCoordinates.Framed Y U τ R j) :
    FrY Y (compactOf Y U) τ j a.x a.v a.w :=
  ⟨a.x_over, a.x_mem, a.v_basis, by rw [comp_chi_bar]; exact a.w_basis⟩

theorem isDerivAt0_of_sameVecs {y : Sp ℂ ⟶ Xo.XF c} {g n : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)}
    {v : Fin n → (epsAt (y ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin n → (epsAt ((y ≫ Y.jQ) ≫ pullback.fst Y.s (spMap β)) ⟶ Y.t.G)} (h : SameVecs Y y v vb)
    {V : Fin n → Fin g → ℂ} (hV : ∀ b, FramedFlatCoordinates.IsDirection Y y e (V b) (vb b).left) (b : Fin n) :
    IsDerivAt0 e (V b) (v b).left := by
  obtain ⟨v₀, h1, h2⟩ := hV b
  obtain ⟨v₁, k1, k2⟩ := h b
  rw [← k1, ← Y.m.cart.1.hom_ext (h1.trans k2.symm) ((Over.w v₀).trans (Over.w v₁).symm)]
  exact h2

open Classical in

theorem exists_reading (hU : IsClosed (U : Set (Xo.XF c))) {σb : RuleY Y} {σ : RuleU Xo c}
    (hres : Restricts Y U τ σb σ) {s : c.F →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)}
    {Fu : FamilyUnif Xo (s.comp (IntermediateField.inclusion c.le).toRingHom) ty} {i : Fin Fu.n}
    {x : Fin D.q ⊕ Fin D.p → (Fu.Di i).La} (hx : LinearIndependent (𝓞 E) x) {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)}
    {Hm : Matrix (Fin g₀) (Fin g₀) ℂ} (hP : IsPeriod (Fu.Di i) ty P)
    (hE : ∀ a b, (hermForm Hm (P a) (P b)).im = (Fu.Di i).EF a b) {y : Sp ℂ ⟶ Xo.XF c}
    {a : FramedFlatCoordinates.Framed Y U τ ℂ s} (hy : y ≫ pullback.fst _ _ = Fu.u i P) (ha : a.x = y ≫ Y.jQ)
    {V : Fin D.p → Fin g₀ → ℂ} {W : Fin D.q → Fin g₀ → ℂ} {C : Fin D.q ⊕ Fin D.p → Fin D.p → ℂ}
    (hV : ∀ b, FramedFlatCoordinates.IsDirection Y y (fun z => (Fu.ex i P z).left) (V b) (a.v b).left)
    (hW : ∀ b, FramedFlatCoordinates.IsDirection Y y (fun z => (Fu.ex i P z).left) (W b) (a.w b).left)
    (hC : ∀ k n, (if ty n = s.comp (FramedFlatCoordinates.embCoeff c τ) then P (x k) n else 0) = ∑ b, C k b * V b n) :
    ∃ (v : _) (w : _) (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ)
      (u : HolUnif o.t.G o.t.PP.L g) (Hm' : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ)
      (h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), FrU Xo c U τ s y v w ∧ σb ℂ a.x a.v a.w = σ ℂ y v w ∧ u.IsAH Hm' κ ∧
      (∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) ∧ (∀ z, h z ∈ u.Λ ↔ z ∈ P.range) ∧
      (∀ a b, (herm Hm' (h (P a)) (h (P b))).im = (Fu.Di i).EF a b) ∧
      IsVecs u m.toSABMap.φ v (fun b => h (V b)) ∧ IsVecs u m.toSABMap.φ w (fun b => h (W b)) ∧
      IsWedgeCoord Hm' (fun b => h (V b)) (fun b => h (W b)) (fun k => h (P (x k)))
        (FramedFlatCoordinates.flatCoord Hm (fun k => P (x k)) W C) ∧ FramedFlatCoordinates.flatCoord Hm (fun k => P (x k)) W C ≠ 0 := by
  have hf := frY_framed a
  obtain ⟨ax, a1, a2, av, aw, a3, a4⟩ := a
  dsimp only at ha hV hW hf ⊢
  subst ha
  have hyU : Set.range y ⊆ U := by
    rintro _ ⟨z, rfl⟩
    have := Y.jQ_open
    have h1 : Y.jQ (y z) ∈ closure (Y.jQ '' (U : Set (Xo.XF c))) := by
      rw [← Scheme.Hom.comp_apply]; exact hf.2.1 ⟨z, rfl⟩
    rw [← hU.closure_eq, Y.jQ.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
    exact h1
  obtain ⟨v, w, hfr, sv, sw⟩ := (frame_transfer E H D l Xo c O β Y U τ ℂ s y).2 _ av aw hyU hf
  obtain ⟨o, m, g, u, Hm', κ, V', W', hA, vV, vW, iV, iW⟩ := exists_unif_of_frame E H D l Xo c U τ s y v w hfr
  obtain ⟨h, hex, hΛ, hE', hd⟩ := FibreCmp.exists_equiv_of_isAH E H D l Xo _ g₀ ty Fu i P _ _ o m g u Hm' κ hP hy hA
  have dV := isDerivAt0_of_sameVecs sv hV
  have dW := isDerivAt0_of_sameVecs sw hW
  obtain rfl := vecs_of_dir hP m h hex hd dV vV
  obtain rfl := vecs_of_dir hP m h hex hd dW vW
  have eV : ∀ b (a : 𝓞 E), tyAct ty a (V b) = s.comp (FramedFlatCoordinates.embCoeff c τ) a • V b := fun b a =>
    eig_of_dir hP (dV b) ((hfr.2.2.1.1 b).2 a)
  have eW : ∀ b (a : 𝓞 E), tyAct ty a (W b) = conjEmb (s.comp (FramedFlatCoordinates.embCoeff c τ)) a • W b := fun b a =>
    (eig_of_dir hP (dW b) ((hfr.2.2.2.1 b).2 a)).trans (congrArg (· • W b) (emb_bar (s.comp (FramedFlatCoordinates.embCoeff c τ)) a))
  have hh := herm_map h.toLinearMap hP.2.2.2.1 fun a b => (hE' a b).trans (hE a b).symm
  refine ⟨v, w, o, m, g, u, Hm', κ, h, hfr, hres ℂ s y v w av aw hfr hf sv sw, hA, hex, hΛ, hE', vV, vW,
    ⟨C, fun k j => ?_, ?_⟩, flatCoord_ne_zero hP hE (by rw [(Fu.sig i).1, (Fu.sig i).2]) hx
      (LinearIndependent.of_comp h.toLinearMap iV) (LinearIndependent.of_comp h.toLinearMap iW) eV eW hC⟩
  · simp only [← map_smul, ← map_sum, ← map_sub]
    refine (hh _ _).trans (herm_eq_zero hP hE (fun n hn => ?_) (eV j))
    have := hC k n
    rw [if_pos hn] at this
    simp [this]
  · refine congrArg (fun M => Matrix.det (Matrix.of M)) (funext fun k => congrArg (Sum.elim · _) (funext fun j => ?_))
    exact congrArg (_ * ·) (hh _ _).symm

theorem isHorizontal_of_isFlatAt (hU : IsClosed (U : Set (Xo.XF c))) {σb : RuleY Y} {σ : RuleU Xo c}
    (hres : Restricts Y U τ σb σ) (hz : NzY Y (compactOf Y U) τ σb) (hf : ∀ e, IsFlatAt Xo c U τ σ e) :
    FramedFlatCoordinates.IsHorizontal (Y := Y) (Xc := U) (τ := τ) fun R _ _ a => σb R a.x a.v a.w := by
  intro s _ g₀ ty _ Fu i x hx
  by_contra hn
  have h1 : ¬ _ := fun h => hn ⟨1, one_ne_zero, h⟩
  push Not at h1
  obtain ⟨P, Hm, hP, -, hE, y, a, hy, ha, V, W, C, hV, hW, hC, -⟩ := h1
  obtain ⟨v, w, o, m, g, u, K, κ, h, fr, val, hA, hex, hΛ, hK, vV, vW, wc, ne⟩ :=
    exists_reading hU hres hx hP hE hy ha hV hW hC
  refine hn ⟨σb ℂ a.x a.v a.w / FramedFlatCoordinates.flatCoord Hm (fun k => P (x k)) W C,
    div_ne_zero (hz ℂ s _ _ _ (frY_framed a)).ne_zero ne, ?_⟩
  intro P' Hm' hP' _ hE' y' a' hy' ha' V' W' C' hV' hW' hC'
  obtain ⟨v', w', o', m', g', u', K', κ', h', fr', val', hA', hex', hΛ', hK', vV', vW', wc', -⟩ :=
    exists_reading hU hres hx hP' hE' hy' ha' hV' hW' hC'
  obtain ⟨φ, hφ, hφP⟩ := exists_transport_periods Fu i hP hP' hy hy' m m' u u' h h' hex hΛ hK hex' hΛ' hK'
  have := hf s y y' v w v' w' fr fr' o o' m m' g g' u u' K K' κ κ' φ _ _ _ _ _ _ _ hA hA' hφ vV vW vV' vW' wc
    (by simpa only [hφP] using wc')
  rw [div_mul_eq_mul_div, eq_div_iff ne]
  exact (congrArg (· * _) val').trans (this.symm.trans (congrArg (· * _) val.symm))

end Model

end GlobalTheory.DetLine.PeriodFlat

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit in

theorem GlobalTheory.DetLine.PeriodFlat.exists_horizontal_section : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1), (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  intro hp _ _ E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨Y, -⟩ := hp.p1 E H Dw hL.pos l Xo c
  obtain ⟨V, hV, hirr⟩ := GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange E H Dw l Xo c hL.geo Z
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hG : GeometricallyConnected (V.ι ≫ toF Xo c) :=
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => by
      have := hirr K (algebraMap c.F K)
      exact (inferInstance : ConnectedSpace ↑(pullback (V.ι ≫ toF Xo c) (spMap (algebraMap c.F K))))⟩
  obtain ⟨-, σ, -, -, hf, -, hY⟩ := detLineTrivial_of_toroidal hp.p1 E H Dw l Xo c V hc hG τ.1 τ.2
  obtain ⟨σb, hs, hz, hres, -⟩ := hY _ _ Y (GlobalTheory.FlatRow.isNormal_genFibre Y)
  refine ⟨Y, V, fun R _ _ a => σb R a.x a.v a.w, hV, fun R R' _ _ j j' a a' f M N h => ?_,
    fun R _ j a => hz R j _ _ _ (PeriodFlat.frY_framed a), PeriodFlat.isHorizontal_of_isFlatAt hc hres hz hf⟩
  rw [mul_comm, mul_comm _ N.det]
  exact (sec_chg hs (PeriodFlat.frY_framed a) (PeriodFlat.frY_framed a') ⟨h.2.1, h.2.2⟩).symm
