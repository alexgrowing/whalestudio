import Development.WeilBound.CoreStatements.CentralCharts.PotLoc
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement

noncomputable section

namespace AnalyticReference

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB RootFieldNumerics
open scoped ComplexOrder

theorem top_le_iff_centre {X : Scheme.{0}} (z : Sp ℂ ⟶ X) (U : X.Opens) : ⊤ ≤ z ⁻¹ᵁ U ↔ centre z ∈ U := by
  constructor
  · exact fun h => h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  · intro h q _
    have e : q = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst e
    exact h

theorem eventually_centre {X : Scheme.{0}} {n : ℕ} {V : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo V z)
    {t₀ : Fin n → ℂ} (ht : t₀ ∈ V) (U : X.Opens) (h : centre (z t₀) ∈ U) : ∀ᶠ t in 𝓝 t₀, centre (z t) ∈ U := by
  filter_upwards [(hz U 0).1.mem_nhds ⟨ht, (top_le_iff_centre _ _).2 h⟩] with t h' using (top_le_iff_centre _ _).1 h'.2

theorem fibreLatVec_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ A₁ : Type}
    {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)} (h : FibreLatVec t z R x v) (f : A₁ → A₀) :
    FibreLatVec t z R (fun a => x (f a)) fun a => v (f a) := by
  obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun a => h6 _⟩

theorem exists_tr {Ω Li : Type} [Field Ω] [AddCommGroup Li] [Module Ω Li] {r : ℕ} (b b₀ : Fin r → Li)
    (h : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) : ∃ t : Ω, b i - t • b₀ i ∈ flagStep Ω b₀ i := by
  have h1 : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← h]
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
  have h2 : {k : Fin r | (k : ℕ) < i + 1} = insert i {k : Fin r | (k : ℕ) < i} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  rw [flagStep, h2, Set.image_insert_eq, Submodule.mem_span_insert] at h1
  obtain ⟨a, w, hw, e⟩ := h1
  exact ⟨a, by rw [e, add_sub_cancel_left]; exact hw⟩

theorem leadMinor_smul {r : ℕ} (c : ℝ) (Γ : Matrix (Fin r) (Fin r) ℂ) (k : ℕ) :
    leadMinor ((c : ℂ) • Γ) k = c ^ k * leadMinor Γ k := by
  unfold leadMinor
  split_ifs with h
  · rw [Matrix.submatrix_smul, Pi.smul_apply, Pi.smul_apply, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul]
  · simp

theorem log_nu {r : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ} (h : Γ.PosDef) (i : Fin r) :
    Real.log (Real.sqrt (leadMinor ((Real.pi : ℂ) • Γ) (i + 1) / leadMinor ((Real.pi : ℂ) • Γ) i)) =
      Real.log (Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i)) + Real.log (Real.sqrt Real.pi) := by
  have h1 := leadMinor_pos_of_posDef h (s := i + 1) i.2
  have h2 := leadMinor_pos_of_posDef h (s := i) i.2.le
  have hp := Real.pi_pos
  have e : leadMinor ((Real.pi : ℂ) • Γ) (i + 1) / leadMinor ((Real.pi : ℂ) • Γ) i =
      leadMinor Γ (i + 1) / leadMinor Γ i * Real.pi := by
    rw [leadMinor_smul, leadMinor_smul, pow_succ]
    field_simp
  rw [e, Real.sqrt_mul (div_pos h1 h2).le, Real.log_mul (Real.sqrt_pos.2 (div_pos h1 h2)).ne' (Real.sqrt_pos.2 hp).ne']

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}

def CountAt {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y ∅ y)
    (Fl : 𝔐.Flag) (U : 𝔐.X.Opens) : Prop :=
  ∀ (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (g : ℕ) (Λ : Type) [AddCommGroup Λ]
      [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (F : CMType H ⊕ CMType H → ℕ → Submodule ℂ (Fin g → ℂ)),
      (∀ s i, flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) →
      {z : Sp ℂ ⟶ 𝔐.X | centre z ∈ U ∧ 𝔐.Interior z ∧ (∀ s, (𝔐.V s).IsFrameAt (b s) ⟨centre z, 𝔐.all _⟩) ∧
        ∃ (x : (Σ s, Fin (labelRk D s)) → Fin g → ℂ) (v : (Σ s, Fin (labelRk D s)) → (epsAt z ⟶ 𝔐.t.G)),
          (∀ a, 𝔐.M.ValAt z (b a.1 a.2) (v a)) ∧ FibreLatVec 𝔐.t z R x v ∧
          ∀ s k, flagStep ℂ (fun i => x ⟨s, i⟩) k = F s k}.Countable

theorem root_log (Γ : ∀ s, Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ) (hΓ : ∀ s, (Γ s).PosDef) (τ : CMType H)
    (i : Fin (D.p + D.q)) :
    (HodgeCpt.rootSgn D (τ, i) : ℝ) * Real.log (Real.sqrt
      (leadMinor ((Real.pi : ℂ) • Γ (HodgeCpt.rootIdx D (τ, i)).1) ((HodgeCpt.rootIdx D (τ, i)).2 + 1) /
        leadMinor ((Real.pi : ℂ) • Γ (HodgeCpt.rootIdx D (τ, i)).1) (HodgeCpt.rootIdx D (τ, i)).2)) =
      grLog (p := D.p) (q := D.q) (Γ (.inl τ)) (Γ (.inr τ)) i +
        (HodgeCpt.rootSgn D (τ, i) : ℝ) * Real.log (Real.sqrt Real.pi) := by
  rw [log_nu (hΓ _), mul_add]
  congr 1
  let F : (Σ s, Fin (labelRk D s)) → ℝ := fun a => Real.log (Real.sqrt (leadMinor (Γ a.1) (a.2 + 1) / leadMinor (Γ a.1) a.2))
  show _ * F (HodgeCpt.rootIdx D (τ, i)) = _
  by_cases h : (i : ℕ) < D.p
  · have e : HodgeCpt.rootIdx D (τ, i) = ⟨.inl τ, ⟨i, h⟩⟩ := dif_pos h
    rw [e]
    simp only [HodgeCpt.rootSgn, grLog, if_pos h, F, Int.cast_one, one_mul]
    rfl
  · have e : HodgeCpt.rootIdx D (τ, i) = ⟨.inr τ, ⟨D.p + D.q - 1 - i, by have := i.2; show _ < D.q; omega⟩⟩ := dif_neg h
    rw [e]
    simp only [HodgeCpt.rootSgn, grLog, if_neg h, F, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    rfl

theorem locChart (hLP : LocPer) (hT : Transport) (hFV : FrameVals) (hPM : PerMat) (hG : Top.Given)
    (hN : 1 ≤ D.p + D.q) (Gr : RefGeo Y) (An : Gr.An)
    (ψ : An.Sys.X → An.Re.R.X) (hψ : HoloMap An.Sys.A An.Re.R.A ψ) (hπ : ∀ x, An.Re.π (ψ x) = x) (z : An.Sys.X → (Sp ℂ ⟶ Gr.𝔐.X))
    (hzi : Function.Injective z) (hzc : ∀ x, CoordsAt Gr.𝔐.ξ Gr.y (z x) (An.Re.R.lift (ψ x) (ψ x)))
    (k : Fin An.Sys.A.n) (hzh : IsHolTo (An.Sys.A.chart k).target fun t => z ((An.Sys.A.chart k).symm t))
    (U : Gr.𝔐.X.Opens) (x₀ : An.Sys.X) (hx₀ : x₀ ∈ An.Sys.open') (hk : x₀ ∈ (An.Sys.A.chart k).source) (hU : centre (z x₀) ∈ U) :
    ∃ (V : Set (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ))
      (gm : CMType H → (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
      IsOpen V ∧ An.Sys.A.chart k x₀ ∈ V ∧ V ⊆ (An.Sys.A.chart k).target ∧ (∀ t ∈ V, (An.Sys.A.chart k).symm t ∈ An.Sys.open') ∧
      (∀ τ a b, AnalyticOnNhd ℂ (fun t => gm τ t a b) V) ∧ (∀ t ∈ V, ∀ τ, InFlagDomain (D.p + D.q) D.p (gm τ t)) ∧
      (∀ t₁ ∈ V, ∀ p : RootIx D, ∃ G : (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
        (An.Sys.potH (some p)).φ ((An.Sys.A.chart k).symm t₁) ((An.Sys.A.chart k).symm t) =
          stepPot (D.p + D.q) D.p p.2 (gm p.1 t) + (G t).re) ∧
      (CountAt Gr.𝔐 Gr.Fl U → ∀ t ∈ V, {t' ∈ V | SameFl (fun τ => gm τ t) fun τ => gm τ t'}.Countable) := by
  classical
  set ch := An.Sys.A.chart k with hch
  let t₀ := ch x₀
  have hs₀ : ch.symm t₀ = x₀ := ch.left_inv hk
  have hop : IsOpen An.Sys.open' := (GlobalTheory.T.section_boundary_closed_and_codense _ _ An.Sys.A An.Sys.L An.Sys.s _ An.Sys.m An.Sys.W An.Sys.sec An.Sys.snc).1.isOpen_compl
  let V₁ := ch.target ∩ ch.symm ⁻¹' An.Sys.open'
  have hV₁ : IsOpen V₁ := ch.isOpen_inter_preimage_symm hop
  have ht₁ : t₀ ∈ V₁ := ⟨ch.map_source hk, by show ch.symm t₀ ∈ An.Sys.open'; rwa [hs₀]⟩
  let z' := fun t => z (ch.symm t)
  have hz₁ : IsHolTo V₁ z' := SheetDecomposition.vecMono hzh hV₁ Set.inter_subset_left
  have hint : ∀ t ∈ V₁, Gr.𝔐.Interior (z' t) := fun t ht =>
    (An.interior _ _ (hzc _)).2 (by rw [hπ]; exact ht.2)
  choose Us hUs b hb hfr using fun s => Gr.Fl.sub s ⟨centre (z' t₀), Gr.𝔐.all _⟩ trivial
  obtain ⟨g, Λ, _, _, R, V₂, σ, hV₂, ht₂, h21, hfam, hlab, hvec⟩ :=
    hLP hG E H D l Xo c Y ∅ Gr.Ω Gr.K Gr.J Gr.y Gr.𝔐 _ V₁ z' hN hV₁ hz₁ hint t₀ ht₁
  let I := Σ s : CMType H ⊕ CMType H, Fin (labelRk D s)
  let e := Fintype.equivFin I
  obtain ⟨xF, hxa, hxe⟩ := hvec _ (fun a => b (e.symm a).1 (e.symm a).2) fun a =>
    (hFV hG E H D l Xo c Y Gr.Ω Gr.K Gr.J Gr.y Gr.𝔐 (z' t₀) _ (b _) hN (hint _ ht₁) (hfr _ _ trivial (hUs _))).1 _
  let x : I → (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → Fin g → ℂ := fun a => xF (e a)
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ V₂ ∧ (∀ s, centre (z' t) ∈ Us s) ∧ centre (z' t) ∈ U ∧ (∀ a, AnalyticAt ℂ (x a) t) ∧
      ∃ v : I → (epsAt (z' t) ⟶ Gr.𝔐.t.G), (∀ a, Gr.𝔐.M.ValAt (z' t) (b a.1 a.2) (v a)) ∧
        FibreLatVec Gr.𝔐.t (z' t) (R t) (fun a => x a t) v := by
    filter_upwards [hV₂.mem_nhds ht₂, Filter.eventually_all.2 fun s => eventually_centre hz₁ ht₁ (Us s) (hUs s),
      eventually_centre hz₁ ht₁ U (by show centre (z (ch.symm t₀)) ∈ U; rwa [hs₀]),
      Filter.eventually_all.2 fun a : I => (hxa (e a)).eventually_analyticAt, hxe] with t h1 h2 h3 h4 ⟨v, hv, hf⟩
    refine ⟨h1, h2, h3, h4, fun a => v (e a), fun a => ?_, fibreLatVec_comp hf e⟩
    have := hv (e a)
    rwa [e.symm_apply_apply] at this
  obtain ⟨V₃, h3, hV₃, ht₃⟩ := eventually_nhds_iff.1 hev
  have hfr₃ : ∀ t ∈ V₃, ∀ s, (Gr.𝔐.V s).IsFrameAt (b s) ⟨centre (z' t), Gr.𝔐.all _⟩ := fun t ht s =>
    hfr s _ trivial ((h3 t ht).2.1 s)
  have hval : ∀ t ∈ V₃, ∀ s, LinearIndependent ℂ (fun i => x ⟨s, i⟩ t) ∧
      Submodule.span ℂ (Set.range fun i => x ⟨s, i⟩ t) = eigSp (R t).B (σ s) ∧
      Gr.𝔐.M.GramAt Gr.𝔐.t.PP.L (z' t) (b s) ((Real.pi : ℂ) • (R t).gram fun i => x ⟨s, i⟩ t) ∧
      ((R t).gram fun i => x ⟨s, i⟩ t).PosDef := fun t ht s => by
    obtain ⟨h1, -, -, -, v, hv, hf⟩ := h3 t ht
    exact (hFV hG E H D l Xo c Y Gr.Ω Gr.K Gr.J Gr.y Gr.𝔐 (z' t) s (b s) hN (hint _ (h21 h1)) (hfr₃ t ht s)).2 g Λ (R t) σ
      _ (fun i => v ⟨s, i⟩) (hlab t h1) (fun i => hv ⟨s, i⟩) (fibreLatVec_comp hf fun i => ⟨s, i⟩)
  obtain ⟨σ', -, hσu, -, -, -, hσ⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l Xo c Y ∅ Gr.Ω Gr.K Gr.J Gr.y Gr.𝔐 ℂ (z' t₀)
  obtain rfl := hσu σ (hlab _ ht₂)
  obtain ⟨hcm, -, hconj⟩ := hσ (RingHom.id ℂ)
  simp only [RingHom.id_comp] at hcm hconj
  have hfam₃ : IsHolFam V₃ R := ⟨fun t ht t' ht' => hfam.1 t (h3 t ht).1 t' (h3 t' ht').1,
    fun a => (hfam.2 a).mono fun t ht => (h3 t ht).1⟩
  obtain ⟨V, gm, hV, ht, hV3, hga, hgp, hrig⟩ := hPM E (CMType H) g _ D.p D.q Λ V₃ R (fun τ => σ (.inl τ))
    (fun τ i => x ⟨.inl τ, i⟩) (fun τ i => x ⟨.inr τ, i⟩) hV₃ hfam₃ hcm
    ⟨fun τ i t ht => (h3 t ht).2.2.2.1 _, fun τ i t ht => (h3 t ht).2.2.2.1 _, fun t ht τ =>
      ⟨⟨(hval t ht (.inl τ)).1, (hval t ht (.inl τ)).2.1⟩, (hval t ht (.inr τ)).1, by
        rw [← hconj]; exact (hval t ht (.inr τ)).2.1⟩⟩ t₀ ht₃
  have hV1 : V ⊆ V₁ := fun t ht => h21 (h3 t (hV3 ht)).1
  refine ⟨V, gm, hV, ht, fun t ht => (hV1 ht).1, fun t ht => (hV1 ht).2, hga, fun t ht τ => (hgp t ht τ).1,
    fun t₁ ht₁ p => ?_, fun hC t ht => ?_⟩
  · choose tr htr using fun a : I => exists_tr (b a.1) (Gr.Fl.b a.1) (hb a.1) a.2
    let Γ := fun t s => (R t).gram fun i => x ⟨s, i⟩ t
    let nu : I → (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → ℝ := fun a t =>
      Real.sqrt (leadMinor ((Real.pi : ℂ) • Γ t a.1) (a.2 + 1) / leadMinor ((Real.pi : ℂ) • Γ t a.1) a.2)
    obtain ⟨G, hGa, hGe⟩ := potLoc Gr An ψ k V z' (fun r => tr (HodgeCpt.rootIdx D r))
      (fun r => nu (HodgeCpt.rootIdx D r)) hψ hπ hV (fun t ht => (hV1 ht).1) (fun t ht => ⟨(hV1 ht).2, hzc _, fun r =>
        ⟨Gr.𝔐.all _, b _, _, hb _, hfr₃ t (hV3 ht) _, htr _, (hval t (hV3 ht) _).2.2.1,
          (hval t (hV3 ht) _).2.2.2.smul (by exact_mod_cast Real.pi_pos), rfl⟩⟩) t₁ ht₁ p
    let C : ℝ := ∑ i ∈ Finset.Iic p.2, (HodgeCpt.rootSgn D (p.1, i) : ℝ) * Real.log (Real.sqrt Real.pi)
    refine ⟨fun t => G t + C, hGa.add analyticAt_const, ?_⟩
    filter_upwards [hGe, hV.mem_nhds ht₁] with t h1 h2
    rw [h1, (hgp t h2 p.1).2 p.2, Complex.add_re, Complex.ofReal_re]
    have := fun i => root_log (Γ t) (fun s => (hval t (hV3 h2) s).2.2.2) p.1 i
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
    exact (add_right_comm _ _ _).trans (add_assoc _ _ _)
  · refine Set.MapsTo.countable_of_injOn (f := z') ?_ ?_ (hC b g Λ (R t) (fun s k => flagStep ℂ (fun i => x ⟨s, i⟩ t) k) hb)
    · rintro t' ⟨ht', hs⟩
      obtain ⟨h, hP, hfl⟩ := hrig t ht t' ht' hs
      obtain ⟨h1, -, hU', -, v, hv, hf⟩ := h3 t' (hV3 ht')
      refine ⟨hU', hint _ (hV1 ht'), hfr₃ t' (hV3 ht'), fun a => h.symm (x a t'), v, hv,
        hT E H _ _ _ g Λ (R t) (R t') h I _ v (hfam₃.1 t (hV3 ht) t' (hV3 ht')) hP hf, ?_⟩
      rintro (τ | τ) k
      · exact (hfl τ k).1
      · exact (hfl τ k).2
    · intro t₁ h₁ t₂ h₂ e
      exact ch.symm.injOn (hV1 h₁.1).1 (hV1 h₂.1).1 (hzi e)

end AnalyticReference
