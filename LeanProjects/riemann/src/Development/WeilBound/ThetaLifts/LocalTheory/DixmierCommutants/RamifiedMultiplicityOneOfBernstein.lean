import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.AtSingle
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.LocalMultiplicityOneIrreducibleGL

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix GlobalTheory.ThK
open PositivityTheory.KCo PositivityTheory.ThK PositivityTheory.ThK.SplitAsm ValuativeRel PositivityTheory.ThKG.Loc
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inP_det {k : Type} [Field k] [ValuativeRel k] {d d₁ : ℕ} {e : Fin d₁ ⊕ Bool ≃ Fin d} {h : Matrix (Fin d) (Fin d) k} (hh : InP e h) :
    h.det = h (e (.inr false)) (e (.inr false)) * h (e (.inr true)) (e (.inr true)) := by
  obtain ⟨p1, -, -, p3, p4⟩ := hh
  have e1 : h.submatrix e e = fromBlocks 1 (h.submatrix e e).toBlocks₁₂ (h.submatrix e e).toBlocks₂₁ (h.submatrix e e).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (h.submatrix e e)]
    congr 1
    ext s s'
    exact p3 s s'
  rw [← det_submatrix_equiv_self e, e1, det_fromBlocks_one₁₁, ← det_reindex_self finTwoEquiv.symm, det_fin_two]
  simp [finTwoEquiv, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, p1, p4]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

structure Eqv (om : Rep σ X W) (H : Plane E d d₁) (χ : Chr F E) (r : ℝ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (τ : UA σ W₁.J → Module.End ℂ P) (Λ : Fl F v n d →ₗ[ℂ] P) : Prop where
  aug : augAt om v ≤ LinearMap.ker Λ
  act : ∀ t h₁ m, IsLevi H t h₁ m → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ u ∈ unip σ W H, u ∈ UAt σ W (evFin F v) → m ∈ UAt σ W (evFin F v) →
    ∀ φ ∈ SB _, ∀ φ' ∈ SB _, Acts (evFin F v) (om (1, u * m)) φ φ' →
      Λ φ' = ((χ t : ℂ) * (((absE F E t : ℝ) ^ r : ℝ) : ℂ)) • τ h₁ (Λ φ)

theorem one_UAt {m : ℕ} (Y : Spc F E m) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem mul_UAt {m : ℕ} {Y : Spc F E m} {g g' : UA σ Y.J} (h : g ∈ UAt σ Y (evFin F v)) (h' : g' ∈ UAt σ Y (evFin F v)) :
    g * g' ∈ UAt σ Y (evFin F v) := fun u hu => by
  rw [show mat (g * g') - 1 = (mat g - 1) * mat g' + (mat g' - 1) by rw [show mat (g * g') = mat g * mat g' from rfl]; noncomm_ring,
    smul_add, ← Matrix.smul_mul, h u hu, h' u hu]
  simp

theorem ua_ext {t : E →ₐ[F] Fv F v} {sec} (h : IsSec σ t sec) (hJ : IsUnit W.J.det) {g g' : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v))
    (hg' : g' ∈ UAt σ W (evFin F v)) (e : (mat g).map (piW t) = (mat g').map (piW t)) : g = g' := by
  have u1 : ((mat g).map (piW t))ᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g
    rwa [incM_map h] at this
  have u2 : ((mat g').map (piW t))ᵀ * W.J.map t * (mat g').map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g'
    rwa [incM_map h] at this
  have un : IsUnit (((mat g).map (piW t))ᵀ * W.J.map t) :=
    ((isUnit_transpose _).2 (GeneralLinearGroup.map (piW t) g.1).isUnit).mul
      (((isUnit_iff_isUnit_det _).2 hJ).map (t : E →+* Fv F v).mapMatrix)
  refine Subtype.ext (Units.ext (h.extM (z := mat g) (z' := mat g') (fun u hu => ?_) e (un.mul_left_cancel (by rw [u1, e, u2]))))
  rw [show mat g - mat g' = (mat g - 1) - (mat g' - 1) by abel, smul_sub, hg u hu, hg' u hu, sub_zero]

theorem pair_multiplicity_one_ramified (hBe : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {B : Base F E} (hB : B.IsGood σ) {r₁ s₁ r₂ s₂ r₃ s₃ : ℕ}
    (hX : X.IsHerm σ B r₁ s₁) (hW : W.IsSkew σ B r₂ s₂) (hW₁ : W₁.IsSkew σ B r₃ s₃) {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E}
    (hom : M.IsWeil B.ψ χX χW om) (hk : IsHecke F E χW) {K : Subgroup (AF F)ˣ} {m : ℕ} (res : ResEtaPow K χX m) {H : Plane E d d₁} {i₀ i₁}
    (hH : H.IsAdapted σ B W W₁ i₀ i₁) (t : E →ₐ[F] Fv F v) (ram : ¬ GlobalTheory.SplitWeil.IsUnram (chrW χW t)) (hn : n ≤ d₁)
    (hS : ∀ h₀ : GL (Fin d₁) (Fv F v), ∃ h ∈ UAt σ W₁ (evFin F v), (mat h).map (piW t) = h₀)
    {P : Type} [AddCommGroup P] [Module ℂ P] {τ : UA σ W₁.J → Module.End ℂ P} (τ1 : τ 1 = 1) (hr : Module.rank ℂ P ≤ Cardinal.aleph0)
    (hi : ∀ N : Submodule ℂ P, (∀ h ∈ UAt σ W₁ (evFin F v), ∀ x ∈ N, τ h x ∈ N) → N = ⊥ ∨ N = ⊤) {r : ℝ} {Λ Λ' : Fl F v n d →ₗ[ℂ] P}
    (hΛ : Eqv om H χX r τ Λ) (hΛ' : Eqv om H χX r τ Λ') (h0 : ∃ φ ∈ SB _, Λ φ ≠ 0) : ∃ c : ℂ, ∀ φ ∈ SB _, Λ' φ = c • Λ φ := by
  obtain ⟨⟨sec, h⟩, hu⟩ := section_statement F E σ hB.cm v t
  obtain ⟨⟨ι₀, hι⟩, sX, sW, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨kX, kW⟩ := k ι₀ hι
  let e : Fin d₁ ⊕ Bool ≃ Fin d := Fintype.equivFinOfCardEq (by simp [hH.rank])
  have gr := fr_gram (e := e) hB.cm hH hW.skew
  have dC : ((fr H e).map t).det ≠ 0 := by
    have := congrArg det gr
    rw [det_mul, det_mul, det_transpose] at this
    have h1 : (fr H e).det ≠ 0 := fun h' => (gm_det (e := e) (Vac.skew_det hW₁)).ne_zero (by rw [← this, h', zero_mul, zero_mul])
    rw [show (fr H e).map t = (t : E →+* Fv F v).mapMatrix (fr H e) from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 h1
  let C : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero _ dC
  have hC : Fr σ t W W₁ H e C := ⟨rfl, gr, Vac.skew_det hW⟩
  let ι := chg 1 C⁻¹ 1 ι₀
  have bij : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) :=
    bij_smul (bij_comp hι.bij (lrH 1 C⁻¹)) one_ne_zero
  have rX : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1) := fun g₀ =>
    let ⟨g, hg, e1⟩ := sX g₀
    ⟨g, hg, reads_chg (kX g hg g₀ e1) fun Φ Y => B_left _ Φ Y (by simp) rfl⟩
  have rW : ∀ g ∈ UAt σ W (evFin F v), ∀ p : GL (Fin d) (Fv F v), (mat g).map (piW t) = (C * p * C⁻¹).val →
      Reads v ι (om (1, g)) (omB (chrW χW t) (chrW χX t) 1 p) := fun g hg p e1 =>
    reads_chg (kW g hg _ e1) fun Φ Y => B_right _ Φ Y (by rw [← Units.val_mul, ← Units.val_mul, mul_assoc C, inv_mul_cancel_left])
      (by simpa using gdet_conj C⁻¹ p)
  obtain ⟨s, hs⟩ := (ι ∘ₗ (SB _).subtype).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun a b hab =>
    Subtype.ext (bij.injOn a.2 b.2 hab))
  have s1 : ∀ φ ∈ SB _, (s (ι φ)).1 = φ := fun φ hφ => congrArg Subtype.val (LinearMap.congr_fun hs ⟨φ, hφ⟩)
  have rd : ∀ {T S}, Reads v ι T S → ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), S Φ ∈ SB _ ∧
      Acts (evFin F v) T (s Φ).1 (s (S Φ)).1 := fun {T S} hR Φ hΦ => by
    obtain ⟨φ, hφ, rfl⟩ := bij.surjOn hΦ
    obtain ⟨φ₁, h1, h2, h3⟩ := hR φ hφ
    rw [← h3, s1 φ hφ, s1 φ₁ h1]
    exact ⟨bij.mapsTo h1, h2⟩
  have eo : ∀ (p : GL (Fin d) (Fv F v)) (Φ : Matrix (Fin n) (Fin d) (Fv F v) → ℂ), omB (chrW χW t) (chrW χX t) 1 p Φ =
      ((chrW χX t (gdet p) : ℂ) * apow (gdet p) ((n : ℂ) / 2)) • fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * p.val) := fun p Φ => by
    funext Y
    simp [omB]
  have c0 : ∀ p : GL (Fin d) (Fv F v), ((chrW χX t (gdet p) : ℂ) * apow (gdet p) ((n : ℂ) / 2)) ≠ 0 := fun p =>
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have inv : ∀ {Λ : Fl F v n d →ₗ[ℂ] P}, Eqv om H χX r τ Λ → Inv e (chrW χW t) (Λ ∘ₗ (SB _).subtype ∘ₗ s) := fun {Λ} hΛ => by
    refine ⟨fun g₀ Φ hΦ => ?_, fun a ha Φ hΦ => ?_⟩
    · obtain ⟨g, hg, hR⟩ := rX g₀
      have e1 : omB (chrW χW t) 1 g₀ 1 Φ = omB (chrW χW t) (chrW χX t) g₀ 1 Φ := by
        funext Y
        simp [omB]
      have := hΛ.aug (Submodule.subset_span ⟨g, hg, _, (s Φ).2, _, (s _).2, (rd hR Φ hΦ).2, rfl⟩)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      rw [e1]
      exact this
    · have da := inP_det ha
      obtain ⟨p1, p2, p3, p4, p5⟩ := ha
      have x0 : a (e (.inr false)) (e (.inr false)) ≠ 0 := fun h => by simp [h] at p2
      have y0 : a (e (.inr true)) (e (.inr true)) ≠ 0 := fun h => by simp [h] at p3
      let x := Units.mk0 _ x0
      let y := Units.mk0 _ y0
      let p : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero a (da ▸ mul_ne_zero x0 y0)
      let pm : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero (bl e 1 x.val y.val) (by rw [usage₄]; simp)
      have im : (pm⁻¹).val = bl e 1 (x⁻¹).val (y⁻¹).val := by
        refine Units.inv_eq_of_mul_eq_one_right ?_
        ext i j
        obtain ⟨i, rfl⟩ := e.surjective i
        obtain ⟨j, rfl⟩ := e.surjective j
        rw [Matrix.mul_apply, sum_e' (e := e)]
        rcases i with i | _ | _ <;> rcases j with j | _ | _ <;> simp [pm, bl, Matrix.one_apply]
      have pu : ∀ i j, (p * pm⁻¹).val i (e j) = a i (e j) * Sum.elim (fun _ => 1) (fun b => cond b (y⁻¹).val (x⁻¹).val) j := fun i j => by
        rw [Units.val_mul, im, Matrix.mul_apply, sum_e' (e := e)]
        rcases j with j | _ | _ <;> simp [p, bl, Matrix.one_apply]
      obtain ⟨u, hu1, hu2⟩ := sW (C * (p * pm⁻¹) * C⁻¹)
      obtain ⟨m', hm1, hm2⟩ := sW (C * pm * C⁻¹)
      obtain ⟨z, z1, z2, z3, z4, z5⟩ := idele_two hB.cm t x y p2 p3
      have un := mem_unip h hC hu1 hu2 (fun i => by
        rw [pu]; split_ifs with hi
        · simp [hi, x, x0]
        · simp [p1 i hi]) (by rw [pu]; simp [y, y0]) (fun s s' => by rw [pu, p4, Matrix.one_apply]; simp) (fun s => by rw [pu, p5]; simp)
      have lv := is_levi h hC hm1 hm2 (one_UAt W₁) (x := x) (y := y) (by
        rw [show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; rfl) z1 z2 z3
      have hR := rW (u * m') (mul_UAt hu1 hm1) p (by
        rw [show mat (u * m') = mat u * mat m' from rfl, Matrix.map_mul, hu2, hm2, ← Units.val_mul]; congr 1; group)
      obtain ⟨q1, q2⟩ := rd hR Φ hΦ
      have := hΛ.act z 1 m' lv (one_UAt W₁) u un hu1 hm1 _ (s Φ).2 _ (s _).2 q2
      have dp : gdet p = x * y := Units.ext da
      have ap : apow (x * y) ((n : ℂ) / 2) = 1 := apow_of_valuation_eq_one (by simp [x, y, p2, p3]) _
      rw [eo] at q1 this
      rw [map_smul, Submodule.coe_smul, map_smul, dp, ap, z4, z5 _ _ _ res, τ1] at this
      refine ⟨(Submodule.smul_mem_iff _ (c0 p)).1 q1, ?_⟩
      have h9 : Λ (s fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * p.val)).1 = Λ (s Φ).1 := by simpa using this
      exact h9
  choose sc sc1 sc2 using hS
  have bd : ∀ g : GL (Fin d₁) (Fv F v), (bl e g.val 1 1).det ≠ 0 := fun g => by
    rw [usage₄, mul_one, mul_one]; exact g.det_ne_zero
  let pb : GL (Fin d₁) (Fv F v) → GL (Fin d) (Fv F v) := fun g => GeneralLinearGroup.mkOfDetNeZero _ (bd g)
  let ρ : GL (Fin d₁) (Fv F v) → Module.End ℂ P := fun g =>
    ((chrW χX t (gdet (pb g)) : ℂ) * apow (gdet (pb g)) ((n : ℂ) / 2))⁻¹ • τ (sc g)
  have lev : ∀ {Λ : Fl F v n d →ₗ[ℂ] P}, Eqv om H χX r τ Λ → ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
      (Λ ∘ₗ (SB _).subtype ∘ₗ s) (fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * blk e g.val)) = ρ g ((Λ ∘ₗ (SB _).subtype ∘ₗ s) Φ) := fun {Λ} hΛ g Φ hΦ => by
    obtain ⟨m', hm1, hm2⟩ := sW (C * pb g * C⁻¹)
    have lv := is_levi h hC hm1 hm2 (sc1 g) (x := 1) (y := 1) (by rw [sc2]; rfl) (z := 1) (fun u _ => by simp) (by simp) (by simp)
    obtain ⟨-, q2⟩ := rd (rW m' hm1 _ hm2) Φ hΦ
    have := hΛ.act 1 _ m' lv (sc1 g) 1 (one_mem _) (one_UAt W) hm1 _ (s Φ).2 _ (s _).2 (by rw [one_mul]; exact q2)
    have bb : blk e g.val = (pb g).val := by
      change _ = bl e g.val 1 1
      rw [blk, bl]
      congr 2
      ext (_ | _) (_ | _) <;> simp
    rw [eo, map_smul, Submodule.coe_smul, map_smul] at this
    rw [bb]
    apply smul_right_injective _ (c0 (pb g))
    simp only [ρ, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (c0 (pb g)), one_smul]
    simpa using this
  obtain ⟨l, hl, hν⟩ : ∃ l : (Fv F v)ˣ, valuation (Fv F v) (l : Fv F v) = 1 ∧ chrW χW t l ≠ 1 := by
    by_contra h'
    exact ram fun x hx => by by_contra h''; exact h' ⟨x, hx, h''⟩
  obtain ⟨c, hc⟩ := local_multiplicity_one_irreducible_GL hBe (inv hΛ) (inv hΛ') (hu χW hk) hl hν hn ρ hr (fun N hN => hi N fun g hg x hx => by
    have e1 : sc (GeneralLinearGroup.map (piW t) g.1) = g := ua_ext h (Vac.skew_det hW₁) (sc1 _) hg (sc2 _)
    have := N.smul_mem ((chrW χX t (gdet (pb (GeneralLinearGroup.map (piW t) g.1))) : ℂ) *
      apow (gdet (pb (GeneralLinearGroup.map (piW t) g.1))) ((n : ℂ) / 2)) (hN (GeneralLinearGroup.map (piW t) g.1) x hx)
    simpa only [ρ, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (c0 _), one_smul, e1] using this) (lev hΛ) (lev hΛ') (by
      obtain ⟨φ, hφ, h0⟩ := h0
      exact ⟨ι φ, bij.mapsTo hφ, by simpa [s1 φ hφ] using h0⟩)
  exact ⟨c, fun φ hφ => by simpa [s1 φ hφ] using hc (ι φ) (bij.mapsTo hφ)⟩

theorem acts_ex {B : Base F E} (hB : B.IsGood σ) {r₁ s₁ r₂ s₂ : ℕ} (hX : X.IsHerm σ B r₁ s₁) (hW : W.IsSkew σ B r₂ s₂)
    {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E} (hom : M.IsWeil B.ψ χX χW om) (t : E →ₐ[F] Fv F v) :
    (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ := by
  obtain ⟨⟨ι₀, hι⟩, -, sW, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  exact ⟨sW, fun h hh φ hφ => let ⟨φ₁, h1, h2, _⟩ := (k ι₀ hι).2 h hh (GeneralLinearGroup.map (piW t) h.1) rfl φ hφ; ⟨φ₁, h1, h2⟩⟩

theorem acts_zero {κ : Type} [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts (evFin F v) T 0 0 := fun r _ => by
  rw [show tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 from funext fun _ => zero_mul _, map_zero]

theorem acts_lin {κ : Type} [Fintype κ] {T : Module.End ℂ ((κ → AF F) → ℂ)} (ex : ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) T φ φ₁)
    {a b a₁ b₁ : (κ → Fv F v) → ℂ} (ha : a ∈ SB _) (hb : b ∈ SB _) (h1 : Acts (evFin F v) T a a₁) (h2 : Acts (evFin F v) T b b₁) (c : ℂ) :
    Acts (evFin F v) T (a + c • b) (a₁ + c • b₁) := fun r hr => by
  by_cases h0 : a + c • b = 0
  · have key : a₁ + c • b₁ = 0 := by
      by_cases hb0 : b = 0
      · rw [hb0] at h2 h0
        rw [smul_zero, add_zero] at h0
        rw [h0] at h1
        rw [action_uniqueness F κ v T 0 (zero_mem _) _ _ h1 (acts_zero T), action_uniqueness F κ v T 0 (zero_mem _) _ _ h2 (acts_zero T)]
        simp
      · have ea : a = (-c) • b := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0
        by_cases hc : c = 0
        · rw [hc, neg_zero, zero_smul] at ea
          rw [ea] at h1
          rw [action_uniqueness F κ v T 0 (zero_mem _) _ _ h1 (acts_zero T), hc]
          simp
        have : Acts (evFin F v) T a ((-c) • b₁) := fun r hr => by
          have hr' := adjoint_statement.rest F κ v r a ha (by rw [ea]; exact smul_ne_zero (neg_ne_zero.2 hc) hb0) hr b hb
          have e1 : ∀ f : (κ → Fv F v) → ℂ, tens (evFin F v) ((-c) • f) r = (-c) • tens (evFin F v) f r := fun f =>
            funext fun _ => by simp [tens, mul_assoc]
          rw [ea, e1, e1, map_smul, h2 r hr']
        rw [action_uniqueness F κ v T a ha _ _ h1 this]
        simp
    rw [h0, key]
    exact acts_zero T r (h0 ▸ hr)
  · have hs := add_mem ha ((SB _).smul_mem c hb)
    have e1 : ∀ f g : (κ → Fv F v) → ℂ, tens (evFin F v) (f + c • g) r = tens (evFin F v) f r + c • tens (evFin F v) g r := fun f g =>
      funext fun _ => by simp [tens, mul_assoc, add_mul]
    rw [e1, e1, map_add, map_smul, h1 r (adjoint_statement.rest F κ v r _ hs h0 hr a ha), h2 r (adjoint_statement.rest F κ v r _ hs h0 hr b hb)]

theorem ramifiedMultiplicityOne_of_bernstein (hBe : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : RamifiedMultiplicityOne := by
  intro F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H i₀ i₁ χ r m m₁ st hH v hv lam lam' hl hl' h0
  have T := m.triple
  have T₁ := m₁.triple
  have hB := T.base
  let t := B.τ ⟨v, T.chars.sub hv⟩
  obtain ⟨sW₁, ex₁⟩ := acts_ex hB T₁.geo.hV T₁.geo.hW T₁.weil t
  obtain ⟨-, ex⟩ := acts_ex hB T.geo.hV T.geo.hW T.weil t
  obtain ⟨-, -, hν, -, ram, -⟩ := split_character_facts F E B X a a' v t T.chars
  have onto₁ : ∀ x, ∃ φ ∈ SB _, Rf₁.p v φ = x := fun x => Submodule.mem_map.1 ((m₁.fin.onto v).symm ▸ Submodule.mem_top)
  have onto : ∀ x, ∃ φ ∈ SB _, Rf.p v φ = x := fun x => Submodule.mem_map.1 ((m.fin.onto v).symm ▸ Submodule.mem_top)
  have onto' : ∀ x, ∃ φ ∈ SB _, Rf.p' v φ = x := fun x => Submodule.mem_map.1 ((m.fin.onto' v).symm ▸ Submodule.mem_top)
  have wd : ∀ h ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB _, ∀ ψ ∈ SB _, ∀ φ₁ ∈ SB _, ∀ ψ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ →
      Acts (evFin F v) (om₁ (1, h)) ψ ψ₁ → Rf₁.p v φ = Rf₁.p v ψ → Rf₁.p v φ₁ = Rf₁.p v ψ₁ := fun h hh φ a1 ψ a2 φ₁ a3 ψ₁ a4 b1 b2 e => by
    have := m₁.fin.equiv v h hh _ (add_mem a1 ((SB _).smul_mem (-1) a2)) 0 (zero_mem _) _ (add_mem a3 ((SB _).smul_mem (-1) a4)) 0
      (zero_mem _) (acts_lin (ex₁ h hh) a1 a2 b1 b2 (-1)) (acts_zero _) (by simp [e])
    simpa [← sub_eq_add_neg, sub_eq_zero] using this
  have exτ : ∀ h : UA σ G₁.W.J, ∃ τ : Module.End ℂ (Rf₁.Pi v), h ∈ UAt σ G₁.W (evFin F v) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
      Acts (evFin F v) (om₁ (1, h)) φ φ₁ → τ (Rf₁.p v φ) = Rf₁.p v φ₁ := fun h => by
    by_cases hh : h ∈ UAt σ G₁.W (evFin F v)
    swap
    · exact ⟨0, fun h' => absurd h' hh⟩
    choose s s1 s2 using onto₁
    choose A A1 A2 using ex₁ h hh
    have k : ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ → Rf₁.p v (A _ (s1 (Rf₁.p v φ))) = Rf₁.p v φ₁ :=
      fun φ b1 φ₁ b2 b3 => wd h hh _ (s1 _) _ b1 _ (A1 _ _) _ b2 (A2 _ _) b3 (s2 _)
    have lin : ∀ x y (c : ℂ), Rf₁.p v (A _ (s1 (x + c • y))) = Rf₁.p v (A _ (s1 x)) + c • Rf₁.p v (A _ (s1 y)) := fun x y c => by
      have := k _ (add_mem (s1 x) ((SB _).smul_mem c (s1 y))) _ (add_mem (A1 _ (s1 x)) ((SB _).smul_mem c (A1 _ (s1 y))))
        (acts_lin (ex₁ h hh) (s1 x) (s1 y) (A2 _ _) (A2 _ _) c)
      rw [map_add, map_smul, s2, s2, map_add, map_smul] at this
      exact this
    obtain ⟨f, hf⟩ : ∃ f : Rf₁.Pi v → Rf₁.Pi v, ∀ x, f x = Rf₁.p v (A _ (s1 x)) := ⟨_, fun _ => rfl⟩
    have k' : ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ → f (Rf₁.p v φ) = Rf₁.p v φ₁ :=
      fun φ b1 φ₁ b2 b3 => (hf _).trans (k φ b1 φ₁ b2 b3)
    have lin' : ∀ x y (c : ℂ), f (x + c • y) = f x + c • f y := fun x y c => by rw [hf, hf, hf]; exact lin x y c
    have z : f 0 = 0 := by simpa using k' 0 (zero_mem _) 0 (zero_mem _) (acts_zero _)
    exact ⟨{ toFun := f, map_add' := fun x y => by simpa using lin' x y 1,
             map_smul' := fun c y => by simpa [z] using lin' 0 y c }, fun _ => k'⟩
  choose τ hτ using exτ
  have τ1 : τ 1 = 1 := LinearMap.ext fun x => by
    obtain ⟨φ, h1, rfl⟩ := onto₁ x
    exact hτ 1 (one_UAt _) φ h1 φ h1 fun r _ => by rw [show ((1 : UA σ G₁.V.J), (1 : UA σ G₁.W.J)) = 1 from rfl, map_one]; rfl
  have hr : Module.rank ℂ (Rf₁.Pi v) ≤ Cardinal.aleph0 := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Fv F v)
    refine le_trans ?_ (rank_SB (Fin a₁ × Fin (a₁ + a₁') → Fv F v))
    rw [← rank_top, ← m₁.fin.onto v]
    exact rank_map_le _ _
  have hi : ∀ N : Submodule ℂ (Rf₁.Pi v), (∀ h ∈ UAt σ G₁.W (evFin F v), ∀ x ∈ N, τ h x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    m₁.fin.irred v N fun h hh φ b1 φ₁ b2 b3 b4 => hτ h hh φ b1 φ₁ b2 b3 ▸ hN h hh _ b4
  have eq : ∀ {lam}, IsFiniteLocalEquivariantMap om om₁ H v χ r (Rf.p v) (Rf₁.p v) lam → Eqv om H χ r τ (lam ∘ₗ Rf.p v) := fun {lam} hl =>
    ⟨fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.comp_apply, m.fin.inv v hφ, map_zero],
      fun z h₁ m' lv hh u hu b1 b2 φ b3 φ' b4 b5 => by
        obtain ⟨φ₁, c1, c2⟩ := onto₁ (lam (Rf.p v φ))
        obtain ⟨φ₂, c3, c4⟩ := ex₁ h₁ hh φ₁ c1
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hl z h₁ m' lv u hu b1 b2 φ b3 φ' b4 φ₁ c1 φ₂ c3 b5 c4 c2.symm, ← c2,
          hτ h₁ hh φ₁ c1 φ₂ c3 c4]⟩
  have eq' : ∀ {lam}, IsFiniteLocalEquivariantMap om om₁ H v χ r (Rf.p v) (Rf₁.p v) lam → Eqv om' H χ r τ (lam ∘ₗ Rf.p' v) := fun {lam} hl =>
    ⟨fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.comp_apply, m.fin.inv' v hφ, map_zero],
      fun z h₁ m' lv hh u hu b1 b2 φ b3 φ' b4 b5 => by
        obtain ⟨ψ, c1, c2⟩ := onto (Rf.p' v φ)
        obtain ⟨ψ', c3, c4⟩ := ex _ (mul_UAt b1 b2) ψ c1
        rw [LinearMap.comp_apply, LinearMap.comp_apply, ← m.fin.equiv v _ (mul_UAt b1 b2) ψ c1 φ b3 ψ' c3 φ' b4 c4 b5 c2, ← c2]
        exact (eq hl).act z h₁ m' lv hh u hu b1 b2 ψ c1 ψ' c3 c4⟩
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h0 (LinearMap.ext h')
  rcases st with ⟨e1, e2, -, -, rfl, -⟩ | ⟨e1, e2, -, -, rfl, -⟩
  · obtain ⟨c, hc⟩ := pair_multiplicity_one_ramified hBe hB T.geo.hV T.geo.hW T₁.geo.hW T.weil
      (show IsHecke F E (X.β / X.α) from ⟨T.chars.heckeβ.1.div' T.chars.heckeα.1, fun x => by
        rw [MonoidHom.div_apply, T.chars.heckeβ.2, T.chars.heckeα.2, div_one]⟩) T.chars.resβ hH t
      (fun hu => ram hv fun y hy => by
        have := hu y hy
        rw [chrW_div] at this
        rw [Chars.ν, chrW_div, ← inv_div, this, inv_one]) (by omega) sW₁ τ1 hr hi (eq hl) (eq hl')
      (let ⟨φ, h1, h2⟩ := onto x; ⟨φ, h1, by rwa [LinearMap.comp_apply, h2]⟩)
    exact ⟨c, LinearMap.ext fun y => let ⟨φ, h1, h2⟩ := onto y; h2 ▸ hc φ h1⟩
  · obtain ⟨c, hc⟩ := pair_multiplicity_one_ramified hBe hB T.geo.hV' T.geo.hW T₁.geo.hW T.weil'
      (show IsHecke F E (X.α / X.β) from ⟨T.chars.heckeα.1.div' T.chars.heckeβ.1, fun x => by
        rw [MonoidHom.div_apply, T.chars.heckeβ.2, T.chars.heckeα.2, div_one]⟩) T.chars.resα hH t
      (ram hv) (by omega) sW₁ τ1 hr hi (eq' hl) (eq' hl')
      (let ⟨φ, h1, h2⟩ := onto' x; ⟨φ, h1, by rwa [LinearMap.comp_apply, h2]⟩)
    exact ⟨c, LinearMap.ext fun y => let ⟨φ, h1, h2⟩ := onto' y; h2 ▸ hc φ h1⟩

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
